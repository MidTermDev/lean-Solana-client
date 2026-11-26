//! Logs what a program can learn from the sysvars.
//!
//! A runtime's sysvars are only as right as programs find them, so this
//! program asks for all of them, in every way a program can, and logs what
//! it gets. Run on two runtimes, the logs must be the same.
//!
//! The first byte of the instruction data selects what to do:
//!   0  the dedicated system calls (clock, epoch schedule, rent, ...)
//!   1  the sysvar accounts passed in: owner, balance, size, hash of the data
//!   2  the transaction's own instructions, through the Instructions sysvar,
//!      and the instructions that ran before this one
//!   3  parts of sysvars fetched by address with the generic system call
//!   4  arithmetic on three numbers from the instruction data: the operations
//!      whose encoding and rounding differ between versions of sBPF

use solana_program::{
    account_info::AccountInfo,
    entrypoint,
    entrypoint::ProgramResult,
    hash::hashv,
    instruction::{get_processed_sibling_instruction, get_stack_height},
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
    sysvar::{
        self, clock::Clock, epoch_rewards::EpochRewards, epoch_schedule::EpochSchedule,
        instructions, last_restart_slot::LastRestartSlot, rent::Rent, Sysvar,
    },
};

entrypoint!(process);

// The SDK's own definitions, so that each version of sBPF calls them its own way
// (by symbol up to version 2, by hash from version 3).
#[cfg(target_os = "solana")]
use solana_program::syscalls::{sol_get_epoch_stake, sol_get_sysvar};

#[cfg(not(target_os = "solana"))]
unsafe fn sol_get_sysvar(_id: *const u8, _out: *mut u8, _offset: u64, _length: u64) -> u64 {
    2
}
#[cfg(not(target_os = "solana"))]
unsafe fn sol_get_epoch_stake(_vote_address: *const u8) -> u64 {
    0
}

/// Logs a hash as Base58, through the system call that logs addresses.
fn log_hash(data: &[u8]) {
    Pubkey::new_from_array(hashv(&[data]).to_bytes()).log();
}

fn fetch(name: &str, id: &Pubkey, offset: u64, length: usize) {
    let mut buffer = [0u8; 96];
    let code = unsafe { sol_get_sysvar(id.as_ref().as_ptr(), buffer.as_mut_ptr(), offset, length as u64) };
    msg!("{}: bytes {}..{} -> code {}", name, offset, offset + length as u64, code);
    log_hash(&buffer[..length]);
}

pub fn process(_program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    match data.first() {
        Some(0) => {
            let c = Clock::get()?;
            msg!("clock: slot {} epoch {} leader epoch {} time {} epoch start {}",
                c.slot, c.epoch, c.leader_schedule_epoch, c.unix_timestamp, c.epoch_start_timestamp);
            let e = EpochSchedule::get()?;
            msg!("epoch schedule: {} slots, offset {}, warmup {}, normal from epoch {} slot {}",
                e.slots_per_epoch, e.leader_schedule_slot_offset, e.warmup, e.first_normal_epoch, e.first_normal_slot);
            let r = Rent::get()?;
            msg!("rent: {} per byte, threshold bits {:x}, burn {}%, 100 bytes need {}",
                r.lamports_per_byte_year, r.exemption_threshold.to_bits(), r.burn_percent, r.minimum_balance(100));
            let w = EpochRewards::get()?;
            msg!("epoch rewards: start {}, partitions {}, points {}, total {}, distributed {}, active {}",
                w.distribution_starting_block_height, w.num_partitions, w.total_points, w.total_rewards,
                w.distributed_rewards, w.active);
            let l = LastRestartSlot::get()?;
            msg!("last restart slot: {}", l.last_restart_slot);
            msg!("stack height: {}", get_stack_height());
            msg!("cluster stake: {}", unsafe { sol_get_epoch_stake(core::ptr::null()) });
        }
        Some(1) => {
            for account in accounts {
                account.key.log();
                account.owner.log();
                msg!("  {} lamports, {} bytes, executable {}", account.lamports(), account.data_len(), account.executable);
                log_hash(&account.data.borrow());
            }
        }
        Some(2) => {
            let sysvar = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
            let current = instructions::load_current_index_checked(sysvar)?;
            msg!("this is instruction {} of the transaction", current);
            let mut index = 0;
            while let Ok(ix) = instructions::load_instruction_at_checked(index, sysvar) {
                msg!("instruction {}: {} accounts, {} bytes of data, hash of data below", index, ix.accounts.len(), ix.data.len());
                ix.program_id.log();
                log_hash(&ix.data);
                for meta in &ix.accounts {
                    meta.pubkey.log();
                    msg!("  signer {} writable {}", meta.is_signer, meta.is_writable);
                }
                index += 1;
            }
            let mut back = 0;
            while let Some(ix) = get_processed_sibling_instruction(back) {
                msg!("{} back: {} accounts, {} bytes of data", back + 1, ix.accounts.len(), ix.data.len());
                ix.program_id.log();
                for meta in &ix.accounts {
                    meta.pubkey.log();
                    msg!("  signer {} writable {}", meta.is_signer, meta.is_writable);
                }
                back += 1;
            }
        }
        Some(3) => {
            fetch("clock", &sysvar::clock::id(), 0, 40);
            fetch("clock, slot only", &sysvar::clock::id(), 0, 8);
            fetch("clock, past the end", &sysvar::clock::id(), 33, 8);
            fetch("epoch schedule", &sysvar::epoch_schedule::id(), 0, 33);
            fetch("epoch rewards", &sysvar::epoch_rewards::id(), 0, 81);
            fetch("rent", &sysvar::rent::id(), 0, 17);
            fetch("slot hashes", &sysvar::slot_hashes::id(), 0, 48);
            fetch("stake history", &sysvar::stake_history::id(), 0, 8);
            fetch("last restart slot", &sysvar::last_restart_slot::id(), 0, 8);
            fetch("recent blockhashes", &sysvar::recent_blockhashes::id(), 0, 8);
            fetch("slot history", &sysvar::slot_history::id(), 0, 8);
        }
        Some(4) if data.len() == 25 => {
            // three numbers from the instruction data, so that nothing is worked out at compile time
            let n = |i: usize| u64::from_le_bytes(data[1 + 8 * i..9 + 8 * i].try_into().unwrap());
            let (a, b, c) = (n(0), n(1), n(2));
            msg!("u64: {} {} {} {}", a.wrapping_mul(b), a / c, a % c, ((a as u128 * b as u128) >> 64) as u64);
            let (x, y, z) = (a as i64, b as i64, c as i64);
            msg!("i64: {} {} {} {}", x.wrapping_mul(y), x / z, x % z, ((x as i128 * y as i128) >> 64) as i64);
            let (p, q) = (a as u32, c as u32);
            msg!("u32: {} {} {} {} {}", p.wrapping_mul(b as u32), p / q, p % q, p.wrapping_sub(q), p.wrapping_add(q));
            let (s, t) = (a as i32, c as i32);
            msg!("i32: {} {} {} {} {}", s.wrapping_mul(b as i32), s / t, s % t, s.wrapping_sub(t), s.wrapping_add(t) as i64);
            msg!("u128: {} {}", (a as u128 * b as u128) / (c as u128 + 1), (a as u128 * b as u128) % (c as u128 + 1));
            msg!("bits: {} {} {} {} {}", a >> (c & 63), x >> (c & 63), a.rotate_left(c as u32 & 63), a.swap_bytes(), (a as u32).swap_bytes());
            msg!("mixed: {} {} {}", 1_000_000u64.wrapping_sub(a), 77u32.wrapping_sub(p), (s as i64).wrapping_neg());
        }
        _ => return Err(ProgramError::InvalidInstructionData),
    }
    Ok(())
}
