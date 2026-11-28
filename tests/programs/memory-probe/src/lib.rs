//! Reads and writes around the end of an account's data.
//!
//! A program sees each account's data followed by 10,240 bytes of room to
//! grow into. Validators used to hand that room over as zeros; now it is not
//! there until the program writes to it, an account the program may not
//! change cannot be written at all, and both are errors the moment they
//! happen. This program does each of those things, one per instruction, so
//! two runtimes can be compared on the outcome.
//!
//! It takes one account with 16 bytes of data, and no SDK: the account's data
//! then lies 96 bytes into the input, its length 8 bytes before that, and the
//! instruction's data (one byte, what to do) at 10,368.

use core::ptr::{read_volatile, write_volatile};

extern "C" {
    fn sol_memcpy_(to: *mut u8, from: *const u8, count: u64);
    fn sol_memset_(at: *mut u8, value: u8, count: u64);
}

#[no_mangle]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    let data = input.add(96);
    let length = input.add(88) as *mut u64;
    let mut scratch = [0u8; 32];
    match *input.add(10368) {
        // reading: the last byte, the byte after it, eight bytes across the end, the last byte of the room
        0 => read_volatile(data.add(15)) as u64 & 0,
        1 => read_volatile(data.add(16)) as u64 & 0,
        2 => read_volatile(data.add(9) as *const u64) & 0,
        3 => read_volatile(data.add(16 + 10239)) as u64 & 0,
        // what follows the room is the program's again
        4 => read_volatile(data.add(16 + 10240) as *const u64) & 0,
        // writing a byte of the data back as it is
        5 => {
            write_volatile(data, read_volatile(data));
            0
        }
        // writing into the room, then reading elsewhere in it; the account's length stays
        6 => {
            write_volatile(data.add(16), 7);
            read_volatile(data.add(5000)) as u64 & 0
        }
        // writing into the room and making the account that much longer
        7 => {
            write_volatile(data.add(16), 7);
            write_volatile(length, 17);
            0
        }
        // eight bytes written across the end
        8 => {
            write_volatile(data.add(12) as *mut u64, 0x0807060504030201);
            write_volatile(length, 20);
            0
        }
        // making the account longer without touching the room, then reading it
        9 => {
            write_volatile(length, 24);
            read_volatile(data.add(20)) as u64 & 0
        }
        // the system calls that copy and fill: out of the data, across its end, into the room
        10 => {
            sol_memcpy_(scratch.as_mut_ptr(), data, 16);
            read_volatile(scratch.as_ptr().add(3)) as u64 & 0
        }
        11 => {
            sol_memcpy_(scratch.as_mut_ptr(), data.add(8), 16);
            0
        }
        12 => {
            sol_memset_(data.add(14), 9, 6);
            write_volatile(length, 20);
            0
        }
        // a copy that starts in the account's header and runs into its data
        13 => {
            sol_memcpy_(scratch.as_mut_ptr(), data.sub(8), 24);
            0
        }
        // an address where there is nothing at all
        14 => read_volatile(16 as *const u8) as u64 & 0,
        _ => 1,
    }
}
