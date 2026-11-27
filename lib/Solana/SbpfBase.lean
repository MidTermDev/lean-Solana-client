import Crypto.Sha256
import Crypto.Ed25519
import Crypto.Keccak
import Crypto.Secp256k1
import Crypto.Poseidon
import Crypto.Bn254
import Crypto.Blake3
import Encoding.Base58
import Encoding.Base64
import Solana.Wire

/-!
# The parts of the virtual machine that do not execute anything

Loading programs (ELF files, sBPF versions 0 to 3), the address space, the
arithmetic of the instruction set, accounts and the rules about changing
them, program-derived addresses, and the layouts programs and the runtime
exchange. `Solana.Native` builds the programs that are part of the runtime
on this, and `Solana.Sbpf` the interpreter.
-/

namespace Sbpf

-- The virtual address space of a program.
def programStart : UInt64 := 0x100000000
def stackStart : UInt64 := 0x200000000
def inputStart : UInt64 := 0x400000000
def frameBytes : Nat := 4096
def maxDepth : Nat := 64
def stackBytes : Nat := 262144
def heapBytes : Nat := 32768
/-- How deep programs may call one another (the top-level instruction is 1). -/
def maxInstructionDepth : Nat := 5
/-- How much an account's data may grow within one instruction. -/
def maxGrowth : Nat := 10240

-- How processing an instruction ended.
def finished : UInt64 := 0
def accessViolation : UInt64 := 1
def divideByZero : UInt64 := 2
def unsupportedInstruction : UInt64 := 3
def callDepthExceeded : UInt64 := 4
def budgetExceeded : UInt64 := 5
def unsupportedSyscall : UInt64 := 6
def executionOverrun : UInt64 := 7
def aborted : UInt64 := 8
def programFailed : UInt64 := 9
def privilegeEscalation : UInt64 := 10
def unknownProgram : UInt64 := 11
def accountRule : UInt64 := 12
def unbalanced : UInt64 := 13
def missingAccount : UInt64 := 14
def invalidRealloc : UInt64 := 15
def invalidSeeds : UInt64 := 16
def meterExceeded : UInt64 := 17
def runtimeError : UInt64 := 18

def statusName (s : UInt64) : String :=
  if s == 0 then "finished"
  else if s == 1 then "access violation"
  else if s == 2 then "divide by zero"
  else if s == 3 then "unsupported instruction"
  else if s == 4 then "call depth exceeded"
  else if s == 5 then "compute budget exceeded"
  else if s == 6 then "unsupported system call"
  else if s == 7 then "execution ran past the end of the program"
  else if s == 8 then "program aborted"
  else if s == 9 then "program returned an error"
  else if s == 10 then "a call asked for a signature or write access the caller does not have"
  else if s == 11 then "call to a program that is not loaded"
  else if s == 12 then "account rule violated"
  else if s == 13 then "lamports were created or destroyed"
  else if s == 14 then "an account the call refers to was not passed in"
  else if s == 15 then "an account grew by more than 10240 bytes"
  else if s == 17 then "compute budget exceeded"
  else if s == 18 then "refused by the runtime"
  else "the seeds do not derive a valid program address"

-- System calls, numbered here; programs name them and the loader resolves the names.
def sysLog : UInt64 := 1
def sysLog64 : UInt64 := 2
def sysLogPubkey : UInt64 := 3
def sysMemcpy : UInt64 := 4
def sysMemmove : UInt64 := 5
def sysMemset : UInt64 := 6
def sysMemcmp : UInt64 := 7
def sysSha256 : UInt64 := 8
def sysClock : UInt64 := 9
def sysAbort : UInt64 := 10
def sysLogUnits : UInt64 := 11
def sysInvoke : UInt64 := 12
def sysRent : UInt64 := 13
def sysSetReturn : UInt64 := 14
def sysGetReturn : UInt64 := 15
def sysStackHeight : UInt64 := 16
def sysGetSysvar : UInt64 := 17
def sysFindAddress : UInt64 := 18
def sysCreateAddress : UInt64 := 19
def sysSibling : UInt64 := 20
def sysPanic : UInt64 := 21
def sysInvokeRust : UInt64 := 22
def sysLogData : UInt64 := 23
def sysRemaining : UInt64 := 24
def sysEpochSchedule : UInt64 := 25
def sysEpochRewards : UInt64 := 26
def sysLastRestart : UInt64 := 27
def sysEpochStake : UInt64 := 28
def sysKeccak : UInt64 := 29
def sysBlake3 : UInt64 := 30
def sysSecpRecover : UInt64 := 31
def sysCurveValidate : UInt64 := 32
def sysCurveOp : UInt64 := 33
def sysCurveMsm : UInt64 := 34
def sysPoseidon : UInt64 := 35
def sysAllocFree : UInt64 := 36
def sysBn128 : UInt64 := 37
def sysBn128Convert : UInt64 := 38
def sysUnknown : UInt64 := 255

/-- True when the NUL-terminated string at `b[o ..]` equals `name`. -/
def cstrIs (b : ByteArray) (o : Nat) (name : String) : Bool :=
  let n := name.toUTF8
  Wire.eqAt b o n 0 n.size && Wire.u8 b (o + n.size) == 0

def syscallId (b : ByteArray) (o : Nat) : UInt64 :=
  if cstrIs b o "sol_log_" then sysLog
  else if cstrIs b o "sol_log_64_" then sysLog64
  else if cstrIs b o "sol_log_pubkey" then sysLogPubkey
  else if cstrIs b o "sol_memcpy_" then sysMemcpy
  else if cstrIs b o "sol_memmove_" then sysMemmove
  else if cstrIs b o "sol_memset_" then sysMemset
  else if cstrIs b o "sol_memcmp_" then sysMemcmp
  else if cstrIs b o "sol_sha256" then sysSha256
  else if cstrIs b o "sol_keccak256" then sysKeccak
  else if cstrIs b o "sol_blake3" then sysBlake3
  else if cstrIs b o "sol_secp256k1_recover" then sysSecpRecover
  else if cstrIs b o "sol_curve_validate_point" then sysCurveValidate
  else if cstrIs b o "sol_curve_group_op" then sysCurveOp
  else if cstrIs b o "sol_curve_multiscalar_mul" then sysCurveMsm
  else if cstrIs b o "sol_poseidon" then sysPoseidon
  else if cstrIs b o "sol_alloc_free_" then sysAllocFree
  else if cstrIs b o "sol_alt_bn128_group_op" then sysBn128
  else if cstrIs b o "sol_alt_bn128_compression" then sysBn128Convert
  else if cstrIs b o "sol_get_clock_sysvar" then sysClock
  else if cstrIs b o "abort" then sysAbort
  else if cstrIs b o "sol_panic_" then sysPanic
  else if cstrIs b o "sol_log_compute_units_" then sysLogUnits
  else if cstrIs b o "sol_invoke_signed_c" then sysInvoke
  else if cstrIs b o "sol_invoke_signed_rust" then sysInvokeRust
  else if cstrIs b o "sol_log_data" then sysLogData
  else if cstrIs b o "sol_remaining_compute_units" then sysRemaining
  else if cstrIs b o "sol_get_epoch_schedule_sysvar" then sysEpochSchedule
  else if cstrIs b o "sol_get_epoch_rewards_sysvar" then sysEpochRewards
  else if cstrIs b o "sol_get_last_restart_slot" then sysLastRestart
  else if cstrIs b o "sol_get_epoch_stake" then sysEpochStake
  else if cstrIs b o "sol_get_rent_sysvar" then sysRent
  else if cstrIs b o "sol_set_return_data" then sysSetReturn
  else if cstrIs b o "sol_get_return_data" then sysGetReturn
  else if cstrIs b o "sol_get_stack_height" then sysStackHeight
  else if cstrIs b o "sol_get_sysvar" then sysGetSysvar
  else if cstrIs b o "sol_try_find_program_address" then sysFindAddress
  else if cstrIs b o "sol_create_program_address" then sysCreateAddress
  else if cstrIs b o "sol_get_processed_sibling_instruction" then sysSibling
  else sysUnknown

def storeAt (mem : ByteArray) (idx size : Nat) (v : UInt64) : ByteArray :=
  if size == 8 then Fast.put64 mem idx v
  else if size == 4 then Fast.put32 mem idx v
  else if size == 2 then Fast.put16 mem idx v
  else Id.run do
    let mut m := mem
    for i in [0:size] do
      m := m.set! (idx + i) (v >>> (8 * i).toUInt64).toUInt8
    return m

/-- A loaded program. `syscalls[pc]` is the system call made by the `call`
instruction at `pc` (or 0) and `calls[pc]` the function it calls by symbol
(as target + 1, or 0). Program memory is the relocated file itself: the
byte at file offset `x` is readable at address `programStart + x` for `x`
in `[roLow, roHigh)`. -/
structure Program where
  elf : ByteArray
  textOff : Nat
  count : Nat
  roLow : Nat
  roHigh : Nat
  entry : Nat
  syscalls : Array UInt64
  calls : Array UInt64
  error : String
  /-- How many bytes of heap this run of the program has (a transaction can ask for more than the default). -/
  heap : Nat
  /-- The sBPF version the program was compiled for, 0 to 3. -/
  version : Nat
  /-- The file offset that the read-only address `programStart + roLow` maps to. -/
  roFile : Nat
  /-- The address of the first instruction, for calls through a register. -/
  textAddr : UInt64
  /-- Which 4 GiB region of the address space the constants are in: 1, or 0 from sBPF v3. -/
  roRegion : UInt64
  /-- The first slot in which the program can be called: the one after it was deployed or upgraded. -/
  since : UInt64
  /-- a program of the first loader: it is given its accounts packed, with no room to grow and nothing aligned -/
  packed : Bool
  /-- For a program whose code is kept in a second account: that account's size (0 if it is gone). A
  transaction is charged for it against the amount of data it may load. -/
  holderSize : Nat
  /-- The instructions, eight bytes each, as words: read once here so that running one costs one lookup. -/
  code : Array UInt64
  /-- No instruction names a register above 10 (so running one need not check). -/
  tidy : Bool
  deriving Inhabited

/-- The `count` instructions at `textOff`, each as one little-endian word. -/
def instructionWords (elf : ByteArray) (textOff count : Nat) : Array UInt64 := Id.run do
  let mut code : Array UInt64 := Array.emptyWithCapacity count
  for i in [0:count] do
    code := code.push (Wire.u64 elf (textOff + 8 * i))
  return code

def tidyWords (code : Array UInt64) : Bool := Id.run do
  for word in code do
    if (word >>> 8) &&& 15 > 10 || (word >>> 12) &&& 15 > 10 then
      return false
  return true

def Program.failed (elf : ByteArray) (why : String) : Program :=
  ⟨elf, 0, 0, 0, 0, 0, Array.emptyWithCapacity 0, Array.emptyWithCapacity 0, why, 32768, 0, 0, 0, 1, 0, false, 0, Array.emptyWithCapacity 0, false⟩

/-- Where a section sits in the file, and the address it asks for. Size 0 means "absent". -/
structure Section where
  off : Nat
  size : Nat
  addr : UInt64

def findSection (elf : ByteArray) (shoff shnum strOff : Nat) (name : String) : Section := Id.run do
  for i in [0:shnum] do
    let h := shoff + 64 * i
    let nameOff := (Wire.u32 elf h).toNat
    if cstrIs elf (strOff + nameOff) name then
      let off := Wire.u64 elf (h + 24)
      let size := Wire.u64 elf (h + 32)
      -- lengths come from the file: check them before doing arithmetic with them
      if off > elf.size.toUInt64 || size > elf.size.toUInt64 || off.toNat + size.toNat > elf.size then
        return ⟨0, 0, 0⟩
      return ⟨off.toNat, size.toNat, Wire.u64 elf (h + 16)⟩
  return ⟨0, 0, 0⟩

/-- The 32-bit MurmurHash3 of a name. From sBPF v3 a program names a system
call by this hash, in the instruction itself, instead of by a symbol the
loader has to look up. -/
def murmur3 (b : ByteArray) : UInt64 := Id.run do
  let mask : UInt64 := 0xFFFFFFFF
  let mut h : UInt64 := 0
  let blocks := b.size / 4
  for i in [0:blocks] do
    let mut k := (Wire.u32 b (4 * i) * 0xcc9e2d51) &&& mask
    k := ((k <<< 15) ||| (k >>> 17)) &&& mask
    k := (k * 0x1b873593) &&& mask
    h := h ^^^ k
    h := ((h <<< 13) ||| (h >>> 19)) &&& mask
    h := (h * 5 + 0xe6546b64) &&& mask
  let mut k : UInt64 := 0
  let rest := b.size % 4
  for i in [0:rest] do
    k := k ||| (Wire.u8 b (4 * blocks + i) <<< (8 * i).toUInt64)
  if rest != 0 then
    k := (k * 0xcc9e2d51) &&& mask
    k := ((k <<< 15) ||| (k >>> 17)) &&& mask
    k := (k * 0x1b873593) &&& mask
    h := h ^^^ k
  h := h ^^^ b.size.toUInt64
  h := h ^^^ (h >>> 16)
  h := (h * 0x85ebca6b) &&& mask
  h := h ^^^ (h >>> 13)
  h := (h * 0xc2b2ae35) &&& mask
  return h ^^^ (h >>> 16)

def syscallNames : Array String := #["sol_log_", "sol_log_64_", "sol_log_pubkey", "sol_memcpy_", "sol_memmove_",
  "sol_memset_", "sol_memcmp_", "sol_sha256", "sol_get_clock_sysvar", "abort", "sol_panic_", "sol_log_compute_units_",
  "sol_invoke_signed_c", "sol_invoke_signed_rust", "sol_log_data", "sol_remaining_compute_units",
  "sol_get_epoch_schedule_sysvar", "sol_get_epoch_rewards_sysvar", "sol_get_last_restart_slot", "sol_get_epoch_stake",
  "sol_get_rent_sysvar", "sol_set_return_data", "sol_get_return_data", "sol_get_stack_height", "sol_get_sysvar",
  "sol_try_find_program_address", "sol_create_program_address", "sol_get_processed_sibling_instruction",
  "sol_keccak256", "sol_blake3", "sol_secp256k1_recover", "sol_curve_validate_point", "sol_curve_group_op",
  "sol_curve_multiscalar_mul", "sol_poseidon", "sol_alloc_free_", "sol_alt_bn128_group_op",
  "sol_alt_bn128_compression"]

/-- Every system call Agave's runtime registers (those above, and those this machine does not provide yet). -/
def allSyscallNames : Array String := #["sol_curve_pairing_map", "sol_get_fees_sysvar",
  "sol_big_mod_exp"]

/-- The system call a hash names, or `sysUnknown`. -/
def syscallByHash (hash : UInt64) : UInt64 := Id.run do
  for name in syscallNames do
    let bytes := name.toUTF8
    if murmur3 bytes == hash then
      return syscallId (bytes.push 0) 0
  return sysUnknown

/-- Loads an sBPF v3 program. Version 3 files are stricter and simpler than
the older ones. Program headers, in a fixed order and packed one after
another, say where the constants (optional) and the code are; nothing is
relocated; constants are addressed from 0 and code from `programStart`; and
a call instruction says in its source field whether it calls a function
(by relative offset) or a system call (by the hash of its name). -/
def loadStrict (elf : ByteArray) : Program := Id.run do
  let headers := (Wire.u16 elf 56).toNat
  if elf.size < 64 + 56 || Wire.u64 elf 32 != 64 || Wire.u16 elf 54 != 56 || headers < 1 || 64 + 56 * headers >= elf.size
      || (Wire.u16 elf 18 != 247 && Wire.u16 elf 18 != 263) || Wire.u8 elf 4 != 2 then
    return Program.failed elf "malformed sBPF v3 file header"
  -- the first header describes constants if it is marked read-only; otherwise there are none
  let constants := Wire.u32 elf (64 + 4) == 4
  if constants && headers < 2 then
    return Program.failed elf "malformed sBPF v3 file header"
  let mut expected := (64 + 56 * headers).toUInt64
  for k in [0:(if constants then 2 else 1)] do
    let h := 64 + 56 * k
    let code := k == 1 || !constants
    let offset := Wire.u64 elf (h + 8)
    let size := Wire.u64 elf (h + 32)
    let address := if code then programStart else 0
    if Wire.u32 elf h != 1 || Wire.u32 elf (h + 4) != (if code then 1 else 4) || offset != expected
        || offset >= elf.size.toUInt64 || offset % 8 != 0 || Wire.u64 elf (h + 16) != address
        || Wire.u64 elf (h + 24) != address || size != Wire.u64 elf (h + 40)
        || size > elf.size.toUInt64 - offset || size % 8 != 0 then
      return Program.failed elf "malformed sBPF v3 program header"
    expected := expected + size
  let codeHeader := if constants then 64 + 56 else 64
  let textOff := (Wire.u64 elf (codeHeader + 8)).toNat
  let count := (Wire.u64 elf (codeHeader + 32)).toNat / 8
  let roOff := if constants then (Wire.u64 elf (64 + 8)).toNat else 0
  let roSize := if constants then (Wire.u64 elf (64 + 32)).toNat else 0
  let entry := Wire.u64 elf 24
  if entry < programStart || (entry - programStart) % 8 != 0 || (entry - programStart) / 8 >= count.toUInt64 then
    return Program.failed elf "entry point is outside the code"
  let mut syscalls : Array UInt64 := Array.replicate count 0
  for pc in [0:count] do
    let o := textOff + 8 * pc
    if Wire.u8 elf o == 0x85 && Wire.u8 elf (o + 1) >>> 4 == 0 then
      let id := syscallByHash (Wire.u32 elf (o + 4))
      if id == sysUnknown then
        -- say which: by name if it is one of the runtime's, by its hash otherwise
        let mut which := s!"with hash {Wire.u32 elf (o + 4)}"
        for name in allSyscallNames do
          if murmur3 name.toUTF8 == Wire.u32 elf (o + 4) then
            which := name
        -- (not an error until the call is made: programs import calls they do not always use)
        if which.length > 60 then
          return Program.failed elf s!"the program makes a system call this machine does not provide ({which})"
        -- remembered by its hash, so that a call to it can say which it was
        syscalls := syscalls.set! pc (0x100000000 + Wire.u32 elf (o + 4))
      else
        syscalls := syscalls.set! pc id
  return ⟨elf, textOff, count, 0, roSize, ((entry - programStart) / 8).toNat, syscalls, Array.replicate count 0, "", 32768,
    3, roOff, programStart, 0, 0, false, 0, instructionWords elf textOff count, tidyWords (instructionWords elf textOff count)⟩

/-- Parses and relocates an sBPF ELF file as written by Solana toolchains. Versions 0 to 2 share
this loader; version 3 has its own. -/
def load (image : ByteArray) : Program := Id.run do
  let mut elf := image
  if elf.size < 64 || Wire.u32 elf 0 != 0x464c457f then
    return Program.failed elf "not an ELF file"
  let machine := Wire.u16 elf 18
  if Wire.u8 elf 4 != 2 || (machine != 247 && machine != 263) then
    return Program.failed elf "not a 64-bit sBPF program"
  let version := Wire.u32 elf 48
  if version > 3 then
    return Program.failed elf "unknown sBPF version (e_flags is more than 3)"
  if version == 3 then
    return loadStrict elf
  let shoff64 := Wire.u64 elf 40
  let shnum := (Wire.u16 elf 60).toNat
  let shstrndx := (Wire.u16 elf 62).toNat
  if shoff64 > elf.size.toUInt64 || shoff64.toNat + 64 * shnum > elf.size || shstrndx >= shnum then
    return Program.failed elf "malformed section table"
  let shoff := shoff64.toNat
  let strOff64 := Wire.u64 elf (shoff + 64 * shstrndx + 24)
  if strOff64 > elf.size.toUInt64 then
    return Program.failed elf "malformed section name table"
  let strOff := strOff64.toNat
  let text := findSection elf shoff shnum strOff ".text"
  if text.size == 0 || text.size % 8 != 0 then
    return Program.failed elf "no .text section"
  if text.off > elf.size || text.size > elf.size - text.off then
    return Program.failed elf "the .text section is not inside the file"
  -- everything read-only that a program can address: code and constants
  let mut roLow := text.off
  let mut roHigh := text.off + text.size
  for name in #[".text", ".rodata", ".data.rel.ro", ".eh_frame"] do
    let sec := findSection elf shoff shnum strOff name
    if sec.size != 0 then
      if sec.addr != sec.off.toUInt64 then
        return Program.failed elf "unsupported layout: a section's address differs from its file offset"
      if sec.off < roLow then
        roLow := sec.off
      if sec.off + sec.size > roHigh then
        roHigh := sec.off + sec.size
  let count := text.size / 8
  let entryAddr := Wire.u64 elf 24
  if entryAddr < text.addr || entryAddr >= text.addr + text.size.toUInt64 || (entryAddr - text.addr) % 8 != 0 then
    return Program.failed elf "entry point is outside .text"
  let mut syscalls : Array UInt64 := Array.replicate count 0
  let mut calls : Array UInt64 := Array.replicate count 0
  let rel := findSection elf shoff shnum strOff ".rel.dyn"
  let syms := findSection elf shoff shnum strOff ".dynsym"
  let names := findSection elf shoff shnum strOff ".dynstr"
  for i in [0:rel.size / 16] do
    let site64 := Wire.u64 elf (rel.off + 16 * i)
    let info := Wire.u64 elf (rel.off + 16 * i + 8)
    let kind := info &&& 0xFFFFFFFF
    let sym := info >>> 32
    if site64 < elf.size.toUInt64 && site64.toNat + 16 <= elf.size then
      let site := site64.toNat
      let inText := site >= text.off && site < text.off + text.size
      let symValue := if sym < (syms.size / 24).toUInt64 then Wire.u64 elf (syms.off + 24 * sym.toNat + 8) else 0
      if kind == 8 then
        -- R_BPF_64_RELATIVE: an address that must be moved into the program region
        if inText then
          let lo := Wire.u32 elf (site + 4)
          let va := lo ||| (Wire.u32 elf (site + 12) <<< 32)
          let moved := if va < programStart then va + programStart else va
          elf := storeAt elf (site + 4) 4 moved
          elf := storeAt elf (site + 12) 4 (moved >>> 32)
        else
          elf := storeAt elf site 8 (programStart + Wire.u32 elf (site + 4))
      else if kind == 1 && inText then
        -- R_BPF_64_64: the address of a symbol, loaded by a two-slot instruction
        let va := symValue + Wire.u32 elf (site + 4)
        let moved := if va < programStart then va + programStart else va
        elf := storeAt elf (site + 4) 4 moved
        elf := storeAt elf (site + 12) 4 (moved >>> 32)
      else if kind == 10 && inText && sym < (syms.size / 24).toUInt64 then
        -- R_BPF_64_32: a call by name, to a function of the program or to a system call
        let symInfo := Wire.u8 elf (syms.off + 24 * sym.toNat + 4)
        let nameOff := (Wire.u32 elf (syms.off + 24 * sym.toNat)).toNat
        let pc := (site - text.off) / 8
        if symInfo &&& 15 == 2 && symValue >= text.addr && symValue < text.addr + text.size.toUInt64 then
          calls := calls.set! pc ((symValue - text.addr) / 8 + 1)
        else if nameOff < names.size then
          syscalls := syscalls.set! pc (syscallId elf (names.off + nameOff))
  return ⟨elf, text.off, count, roLow, roHigh, ((entryAddr - text.addr) / 8).toNat, syscalls, calls, "", 32768,
    version.toNat, roLow, programStart + text.off.toUInt64, 1, 0, false, 0, instructionWords elf text.off count,
    tidyWords (instructionWords elf text.off count)⟩

-- ------------------------------------------------------------------- memory
--
-- Writable memory is one array: the stack, then the heap, then the input
-- region. `locate` turns a virtual address range into an index into that
-- array, or into the program file (marked by `progBase`) for read-only data.

def progBase : Nat := 0x10000000000

def locate (p : Program) (inputLen : Nat) (addr : UInt64) (len : Nat) (write : Bool) : Nat :=
  let region := addr >>> 32
  let off := (addr &&& 0xFFFFFFFF).toNat
  if len > 0x10000000 then Wire.bad
  else if region == 2 then (if off + len <= stackBytes then off else Wire.bad)
  else if region == 3 then (if off + len <= p.heap then stackBytes + off else Wire.bad)
  else if region == 4 then (if off + len <= inputLen then stackBytes + p.heap + off else Wire.bad)
  else if region == p.roRegion && !write then
    (if off >= p.roLow && off + len <= p.roHigh then progBase + (off - p.roLow + p.roFile) else Wire.bad)
  else Wire.bad

def loadAt (p : Program) (mem : ByteArray) (idx size : Nat) : UInt64 :=
  if idx >= progBase then
    let o := idx - progBase
    if size == 1 then Wire.u8 p.elf o else if size == 2 then Wire.u16 p.elf o
    else if size == 4 then Wire.u32 p.elf o else Wire.u64 p.elf o
  else if size == 1 then Wire.u8 mem idx else if size == 2 then Wire.u16 mem idx
  else if size == 4 then Wire.u32 mem idx else Wire.u64 mem idx

/-- The bytes at `[addr, addr + len)`, wherever they live; `none` if any are unmapped. -/
def readBytes (p : Program) (mem : ByteArray) (inputLen : Nat) (addr len : UInt64) : Option ByteArray :=
  if len > 0x10000000 then none
  else if len == 0 then some ByteArray.empty   -- nothing is read, so any address will do (Rust's empty slices point nowhere)
  else
    let idx := locate p inputLen addr len.toNat false
    if !(Wire.ok idx) then none
    else if idx >= progBase then some (p.elf.extract (idx - progBase) (idx - progBase + len.toNat))
    else some (mem.extract idx (idx + len.toNat))

/-- Where `len` writable bytes at `addr` live, or `Wire.bad`. Lengths beyond any region are refused first. -/
def writable (p : Program) (inputLen : Nat) (addr len : UInt64) : Nat :=
  if len > 0x10000000 then Wire.bad
  else if len == 0 then 0   -- nothing is written, so any address will do
  else locate p inputLen addr len.toNat true

-- --------------------------------------------------------------- arithmetic

@[inline] def sext32 (x : UInt64) : UInt64 :=
  if x &&& 0x80000000 != 0 then x ||| 0xFFFFFFFF00000000 else x &&& 0xFFFFFFFF

@[inline] def sext16 (x : UInt64) : UInt64 :=
  if x &&& 0x8000 != 0 then x ||| 0xFFFFFFFFFFFF0000 else x &&& 0xFFFF

/-- Signed "less than" on two's-complement words. -/
@[inline] def slt (a b : UInt64) : Bool := (a ^^^ 0x8000000000000000) < (b ^^^ 0x8000000000000000)

/-- Arithmetic shift right by `n` (0..63). -/
def arsh (a n : UInt64) : UInt64 :=
  if n == 0 then a
  else if a &&& 0x8000000000000000 != 0 then (a >>> n) ||| (0xFFFFFFFFFFFFFFFF <<< (64 - n))
  else a >>> n

def bswap (x : UInt64) (bytes : Nat) : UInt64 := Id.run do
  let mut r : UInt64 := 0
  for i in [0:bytes] do
    r := (r <<< 8) ||| ((x >>> (8 * i).toUInt64) &&& 0xFF)
  return r

/-- The 64-bit operations. `op` is the high nibble of the opcode. Division by zero is the caller's problem. -/
def alu64 (op a b : UInt64) : UInt64 :=
  if op == 0x00 then a + b
  else if op == 0x10 then a - b
  else if op == 0x20 then a * b
  else if op == 0x30 then a / b
  else if op == 0x40 then a ||| b
  else if op == 0x50 then a &&& b
  else if op == 0x60 then a <<< (b &&& 63)
  else if op == 0x70 then a >>> (b &&& 63)
  else if op == 0x80 then 0 - a
  else if op == 0x90 then a % b
  else if op == 0xa0 then a ^^^ b
  else if op == 0xb0 then b
  else arsh a (b &&& 63)

/-- The 32-bit operations of sBPF v0. Add, subtract and multiply sign-extend
their 32-bit result to 64 bits; everything else zero-extends. -/
def alu32 (op a b : UInt64) : UInt64 :=
  let x := a &&& 0xFFFFFFFF
  let y := b &&& 0xFFFFFFFF
  if op == 0x00 then sext32 ((x + y) &&& 0xFFFFFFFF)
  else if op == 0x10 then sext32 ((x - y) &&& 0xFFFFFFFF)
  else if op == 0x20 then sext32 ((x * y) &&& 0xFFFFFFFF)
  else if op == 0x30 then x / y
  else if op == 0x40 then x ||| y
  else if op == 0x50 then x &&& y
  else if op == 0x60 then (x <<< (y &&& 31)) &&& 0xFFFFFFFF
  else if op == 0x70 then x >>> (y &&& 31)
  else if op == 0x80 then (0 - x) &&& 0xFFFFFFFF
  else if op == 0x90 then x % y
  else if op == 0xa0 then x ^^^ y
  else if op == 0xb0 then y
  else arsh (sext32 x) (y &&& 31) &&& 0xFFFFFFFF

/-- The high 64 bits of the unsigned 128-bit product. -/
def umulh (a b : UInt64) : UInt64 :=
  let al := a &&& 0xFFFFFFFF
  let ah := a >>> 32
  let bl := b &&& 0xFFFFFFFF
  let bh := b >>> 32
  let mid := ((al * bl) >>> 32) + ((al * bh) &&& 0xFFFFFFFF) + ((ah * bl) &&& 0xFFFFFFFF)
  ah * bh + ((al * bh) >>> 32) + ((ah * bl) >>> 32) + (mid >>> 32)

def negative (a : UInt64) : Bool := a &&& 0x8000000000000000 != 0

/-- The high 64 bits of the signed 128-bit product. -/
def smulh (a b : UInt64) : UInt64 :=
  umulh a b - (if negative a then b else 0) - (if negative b then a else 0)

/-- Signed division and remainder, rounding toward zero. The caller rules out zero and overflow. -/
def sdiv (a b : UInt64) : UInt64 :=
  let q := (if negative a then 0 - a else a) / (if negative b then 0 - b else b)
  if negative a != negative b then 0 - q else q

def srem (a b : UInt64) : UInt64 :=
  let r := (if negative a then 0 - a else a) % (if negative b then 0 - b else b)
  if negative a then 0 - r else r

/-- Whether a conditional jump is taken. `op` is the high nibble of the opcode. -/
def jumpTaken (op a b : UInt64) : Bool :=
  if op == 0x10 then a == b
  else if op == 0x20 then a > b
  else if op == 0x30 then a >= b
  else if op == 0x40 then a &&& b != 0
  else if op == 0x50 then a != b
  else if op == 0x60 then slt b a
  else if op == 0x70 then !(slt a b)
  else if op == 0xa0 then a < b
  else if op == 0xb0 then a <= b
  else if op == 0xc0 then slt a b
  else !(slt b a)

-- ----------------------------------------------------------------- accounts

/-- An account: an address, the program that owns it, a balance and data. -/
structure Account where
  key : ByteArray
  owner : ByteArray
  lamports : UInt64
  data : ByteArray
  executable : Bool
  deriving Inhabited

def notFound : Nat := 0xFFFFFFFF

-- ----------------------------------------------------- finding things by address
--
-- A table of slots, a power of two of them, each holding 0 or a position + 1 in some array of addresses.
-- An address starts looking at the slot its bytes name and walks on until it finds itself or an empty
-- slot. (The bytes are taken from the middle: chosen addresses share their beginnings or their ends.)

def slotOf (key : ByteArray) (size : Nat) : Nat :=
  ((Wire.u64 key 8 ^^^ (Wire.u64 key 16 * 0x9E3779B97F4A7C15)) >>> 20).toNat % size

/-- The position of `key` among `keys`, by way of the table; `notFound` if it is not there. -/
def keyAt (slots : Array UInt64) (keys : Array ByteArray) (key : ByteArray) : Nat := Id.run do
  if slots.size == 0 then
    return notFound
  let mut at_ := slotOf key slots.size
  for _ in [0:slots.size] do
    let s := slots[at_]!
    if s == 0 then
      return notFound
    if keys[s.toNat - 1]! == key then
      return s.toNat - 1
    at_ := if at_ + 1 == slots.size then 0 else at_ + 1
  return notFound

/-- The table, with `key` now naming `position` (replacing what it named before, if anything). The array
of addresses is the one `position` refers to, with `key` in it or not yet. -/
def keyLink (slots : Array UInt64) (keys : Array ByteArray) (key : ByteArray) (position : Nat) : Array UInt64 := Id.run do
  let mut at_ := slotOf key slots.size
  for _ in [0:slots.size] do
    let s := slots[at_]!
    if s == 0 || (s.toNat - 1 < keys.size && keys[s.toNat - 1]! == key) then
      return slots.set! at_ (position + 1).toUInt64
    at_ := if at_ + 1 == slots.size then 0 else at_ + 1
  return slots

/-- The same for accounts, by their addresses. -/
def accountAt (slots : Array UInt64) (accounts : Array Account) (key : ByteArray) : Nat := Id.run do
  if slots.size == 0 then
    return notFound
  let mut at_ := slotOf key slots.size
  for _ in [0:slots.size] do
    let s := slots[at_]!
    if s == 0 then
      return notFound
    if accounts[s.toNat - 1]!.key == key then
      return s.toNat - 1
    at_ := if at_ + 1 == slots.size then 0 else at_ + 1
  return notFound

def accountLink (slots : Array UInt64) (accounts : Array Account) (key : ByteArray) (position : Nat) : Array UInt64 := Id.run do
  let mut at_ := slotOf key slots.size
  for _ in [0:slots.size] do
    let s := slots[at_]!
    if s == 0 || (s.toNat - 1 < accounts.size && accounts[s.toNat - 1]!.key == key) then
      return slots.set! at_ (position + 1).toUInt64
    at_ := if at_ + 1 == slots.size then 0 else at_ + 1
  return slots

/-- A reference to an account by an instruction: which one, and with what rights. -/
structure Meta where
  index : Nat
  signer : Bool
  writable : Bool
  deriving Inhabited

/-- The `Clock` sysvar a program can ask for. -/
structure Clock where
  slot : UInt64
  epochStartTimestamp : UInt64
  epoch : UInt64
  leaderScheduleEpoch : UInt64
  unixTimestamp : UInt64
  deriving Inhabited

/-- The other sysvars: cluster state a program can ask about, each in its
serialized form, exactly as its sysvar account stores it. -/
structure Sysvars where
  /-- lamports per byte (u64), exemption threshold (f64), burn percentage (u8) -/
  rent : ByteArray
  /-- slots per epoch, leader schedule offset, warmup flag, first normal epoch and slot -/
  epochSchedule : ByteArray
  /-- the state of the current epoch's reward distribution (81 bytes) -/
  epochRewards : ByteArray
  /-- a vector of (slot, hash) for recent slots, newest first -/
  slotHashes : ByteArray
  /-- a vector of (epoch, effective, activating, deactivating) stake -/
  stakeHistory : ByteArray
  lastRestartSlot : UInt64
  deriving Inhabited

/-- One instruction that has been processed, or is being processed: how deep
in the chain of calls it ran (1 = named by the transaction), and what it was. -/
structure Frame where
  depth : Nat
  program : ByteArray
  metas : Array Meta
  data : ByteArray
  deriving Inhabited

/-- The programs that exist, and the world they run in. -/
structure Machine where
  ids : Array ByteArray
  programs : Array Program
  clock : Clock
  budget : UInt64
  sysvars : Sysvars
  /-- bytes of heap each program gets -/
  heap : Nat
  /-- the latest blockhash (32 bytes), or empty if there is none -/
  blockhash : ByteArray
  lamportsPerSignature : UInt64
  /-- for looking into a transaction: stop it after this many compute units, whatever it asked for (0 = no cap) -/
  cap : UInt64
  /-- where each address in `ids` is (see `keyAt`); the latest registration of an address is the one found -/
  index : Array UInt64
  deriving Inhabited

/-- Everything an instruction can change. `status` is `finished` (0) while
all is well; `r0` carries a failing program's error code. `trace` lists
every instruction processed so far in the transaction, calls included. -/
structure State where
  accounts : Array Account
  units : UInt64
  logs : Array String
  returnData : ByteArray
  status : UInt64
  r0 : UInt64
  detail : String
  trace : Array Frame
  deriving Inhabited


def zeros (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := b
  for _ in [0:n] do
    out := out.push 0
  return out

/-- The system program's address: 32 zero bytes. -/
def systemProgram : ByteArray := zeros ByteArray.empty 32

def loaderId : ByteArray := Base58.decode "BPFLoaderUpgradeab1e11111111111111111111111"
def loaderV2 : ByteArray := Base58.decode "BPFLoader2111111111111111111111111111111111"
def loaderV1 : ByteArray := Base58.decode "BPFLoader1111111111111111111111111111111111"
def nativeLoader : ByteArray := Base58.decode "NativeLoader1111111111111111111111111111111"
def computeBudgetProgram : ByteArray := Base58.decode "ComputeBudget111111111111111111111111111111"
def sysvarOwner : ByteArray := Base58.decode "Sysvar1111111111111111111111111111111111111"
def clockSysvar : ByteArray := Base58.decode "SysvarC1ock11111111111111111111111111111111"
def rentSysvar : ByteArray := Base58.decode "SysvarRent111111111111111111111111111111111"
def epochScheduleSysvar : ByteArray := Base58.decode "SysvarEpochSchedu1e111111111111111111111111"
def epochRewardsSysvar : ByteArray := Base58.decode "SysvarEpochRewards1111111111111111111111111"
def slotHashesSysvar : ByteArray := Base58.decode "SysvarS1otHashes111111111111111111111111111"
def stakeHistorySysvar : ByteArray := Base58.decode "SysvarStakeHistory1111111111111111111111111"
def lastRestartSlotSysvar : ByteArray := Base58.decode "SysvarLastRestartS1ot1111111111111111111111"

/-- The sysvars of a quiet cluster. Rent is what Agave serves today: 6,960
lamports per byte with a threshold of 1.0 (older descriptions give 3,480 per
byte-year and 2.0, the same minimum balance; programs can tell the two apart,
so it matters for compute units). The epoch schedule is mainnet's: 432,000
slots per epoch after a warmup that ends at epoch 14, slot 524,256. -/
def Sysvars.standard : Sysvars :=
  let rent := (Wire.putU64 (Wire.putU64 (ByteArray.emptyWithCapacity 17) 6960) 0x3FF0000000000000).push 50
  let schedule := Wire.putU64 (Wire.putU64 ((Wire.putU64 (Wire.putU64 (ByteArray.emptyWithCapacity 33) 432000) 432000).push 1) 14) 524256
  ⟨rent, schedule, zeros ByteArray.empty 81, zeros ByteArray.empty 8, zeros ByteArray.empty 8, 0⟩

def Machine.create (clock : Clock) (budget : UInt64) : Machine :=
  ⟨Array.emptyWithCapacity 4, Array.emptyWithCapacity 4, clock, budget, Sysvars.standard, 32768, ByteArray.empty, 5000, 0,
    Array.replicate 64 0⟩

/-- The smallest balance at which an account with `size` bytes of data is
exempt from rent: (128 + size) bytes at the rate in the Rent sysvar. -/
def Machine.rentMinimum (m : Machine) (size : Nat) : UInt64 :=
  -- lamports per byte, times the threshold (a double: 1.0 today, 2.0 in the older form)
  let factor : UInt64 := if Wire.u64 m.sysvars.rent 8 == 0x4000000000000000 then 2 else 1
  (128 + size).toUInt64 * Wire.u64 m.sysvars.rent 0 * factor

/-- Registers a program under an address. -/
def Machine.add (m : Machine) (id : ByteArray) (p : Program) : Machine := Id.run do
  let ids := m.ids.push id
  -- the table is kept at most half full
  let mut index := m.index
  if ids.size * 2 > index.size then
    index := Array.replicate (index.size * 4) 0
    for i in [0:ids.size] do
      index := keyLink index ids ids[i]! i
  else
    index := keyLink index ids id (ids.size - 1)
  return { m with ids := ids, programs := m.programs.push p, index := index }

/-- Where the program registered under `id` is in `programs`, or `notFound`. -/
def Machine.find (m : Machine) (id : ByteArray) : Nat := keyAt m.index m.ids id

/-- The account that stands for a deployed program when it is passed to another program. -/
def programAccount (id : ByteArray) : Account :=
  ⟨id, loaderId, 1141440, zeros ByteArray.empty 36, true⟩

def findAccount (accounts : Array Account) (key : ByteArray) : Nat := Id.run do
  for i in [0:accounts.size] do
    if accounts[i]!.key == key then
      return i
  return notFound

/-- Rights an instruction holds over account `index`: bit 0 present, bit 1 signer, bit 2 writable. -/
def rights (metas : Array Meta) (index : Nat) : UInt64 := Id.run do
  let mut r : UInt64 := 0
  for mt in metas do
    if mt.index == index then
      r := r ||| 1 ||| (if mt.signer then 2 else 0) ||| (if mt.writable then 4 else 0)
  return r

/-- True when an earlier reference in `metas` names the same account as reference `i`. -/
def isRepeat (metas : Array Meta) (i : Nat) : Bool := Id.run do
  for j in [0:i] do
    if metas[j]!.index == metas[i]!.index then
      return true
  return false

def State.stop (st : State) (status : UInt64) (detail : String) : State :=
  { st with status := status, detail := detail }

def State.charge (st : State) (units : UInt64) : State :=
  { st with units := st.units + units }

def ruleExecutable : String := "an executable account was modified"
def ruleSpend : String := "lamports were taken from an account the program does not own"
def ruleReadOnlyBalance : String := "the balance of an account that was not passed as writable was changed"
def ruleReadOnly : String := "an account that was not passed as writable was modified"
def ruleData : String := "the data of an account the program does not own was modified"
def ruleOwner : String := "the owner of an account was changed by a program that may not reassign it"

/-- Why `program` may not turn `old` into the given balance, owner and data,
or `""` if it may. These are the runtime's ownership rules, checked in the
order Agave checks them: balance, then data, then owner. -/
def changeError (program : ByteArray) (mayWrite : Bool) (old : Account) (lamports : UInt64)
    (owner data : ByteArray) : String :=
  let dataChanged := data != old.data
  let ownerChanged := owner != old.owner
  let owns := old.owner == program
  if lamports == old.lamports && !dataChanged && !ownerChanged then ""
  else if old.executable then ruleExecutable
  else if lamports < old.lamports && !owns then ruleSpend
  else if lamports != old.lamports && !mayWrite then ruleReadOnlyBalance
  else if dataChanged && !mayWrite then ruleReadOnly
  else if dataChanged && !owns then ruleData
  else if ownerChanged && (!owns || !mayWrite) then ruleOwner
  else ""

-- ----------------------------------------------- program-derived addresses

/-- A program address is the hash of seeds, the program's address and a
marker, provided the result is *not* a point on the Ed25519 curve, so that no
private key can exist for it. Only the program itself can sign for it. -/
def createProgramAddress (seeds : Array ByteArray) (programId : ByteArray) : Option ByteArray := Id.run do
  if seeds.size > 16 then
    return none
  let mut message := ByteArray.emptyWithCapacity 128
  for seed in seeds do
    if seed.size > 32 then
      return none
    message := message ++ seed
  message := message ++ programId ++ "ProgramDerivedAddress".toUTF8
  let hash := Sha256.hash message
  if Ed25519.Point.isOnCurve hash then
    return none
  return some hash

/-- Tries bump seeds from 255 downwards until one gives a valid program
address. Returns the address and the bump; the address is empty if none works. -/
def findProgramAddress (seeds : Array ByteArray) (programId : ByteArray) : ByteArray × UInt8 := Id.run do
  for i in [0:256] do
    let bump := (255 - i).toUInt8
    match createProgramAddress (seeds.push (ByteArray.empty.push bump)) programId with
    | some address => return (address, bump)
    | none => pure ()
  return (ByteArray.empty, 0)

-- ---------------------------------------------- reading a call's arguments

/-- A slice of slices: `count` (address, length) pairs at `addr`. -/
def readSlices (p : Program) (mem : ByteArray) (inputLen : Nat) (addr count : UInt64) : Option (Array ByteArray) := Id.run do
  if count > 64 then
    return none
  let mut out : Array ByteArray := Array.emptyWithCapacity count.toNat
  for i in [0:count.toNat] do
    match readBytes p mem inputLen (addr + 16 * i.toUInt64) 16 with
    | none => return none
    | some pair =>
      match readBytes p mem inputLen (Wire.u64 pair 0) (Wire.u64 pair 8) with
      | none => return none
      | some bytes => out := out.push bytes
  return some out

/-- The instruction a program wants to send: callee, account references
(with bit 1 = signer, bit 2 = writable), data. -/
structure Call where
  programId : ByteArray
  keys : Array ByteArray
  flags : Array UInt64
  data : ByteArray

/-- Reads the instruction argument of a call. The two calling conventions
describe the same thing with different layouts:

* C (`SolInstruction`): address of the program id; address and count of 16-byte
  account entries, each the address of a key followed by `is_writable`,
  `is_signer`; address and length of the data.
* Rust (`Instruction`): a vector of 34-byte account entries (the key itself,
  then `is_signer`, `is_writable`), a vector of data bytes, then the program
  id inline. A vector is address, capacity, length. -/
def readCall (p : Program) (mem : ByteArray) (inputLen : Nat) (addr : UInt64) (rust : Bool) : Option Call := Id.run do
  let mut keys : Array ByteArray := Array.emptyWithCapacity 8
  let mut flags : Array UInt64 := Array.emptyWithCapacity 8
  if rust then
    match readBytes p mem inputLen addr 80 with
    | none => return none
    | some head =>
      let count := Wire.u64 head 16
      if count > 255 then
        return none
      match readBytes p mem inputLen (Wire.u64 head 0) (34 * count), readBytes p mem inputLen (Wire.u64 head 24) (Wire.u64 head 40) with
      | some entries, some data =>
        for i in [0:count.toNat] do
          keys := keys.push (entries.extract (34 * i) (34 * i + 32))
          flags := flags.push ((if Wire.u8 entries (34 * i + 32) != 0 then 2 else 0) ||| (if Wire.u8 entries (34 * i + 33) != 0 then 4 else 0))
        return some ⟨head.extract 48 80, keys, flags, data⟩
      | _, _ => return none
  match readBytes p mem inputLen addr 40 with
  | none => return none
  | some head =>
    let count := Wire.u64 head 16
    if count > 255 then
      return none
    match readBytes p mem inputLen (Wire.u64 head 0) 32, readBytes p mem inputLen (Wire.u64 head 24) (Wire.u64 head 32) with
    | some programId, some data =>
      for i in [0:count.toNat] do
        match readBytes p mem inputLen (Wire.u64 head 8 + 16 * i.toUInt64) 16 with
        | none => return none
        | some entry =>
          match readBytes p mem inputLen (Wire.u64 entry 0) 32 with
          | none => return none
          | some key =>
            keys := keys.push key
            flags := flags.push ((if Wire.u8 entry 9 != 0 then 2 else 0) ||| (if Wire.u8 entry 8 != 0 then 4 else 0))
      return some ⟨programId, keys, flags, data⟩
    | _, _ => return none

/-- The caller's view of an account: where in its memory the balance, the
owner and the data live, and where it keeps the data's length. -/
structure Info where
  key : ByteArray
  lamportsAddr : UInt64
  dataLen : UInt64
  dataAddr : UInt64
  ownerAddr : UInt64
  lenAddr : UInt64
  deriving Inhabited

/-- Reads the caller's account views.

* C (`SolAccountInfo`, 56 bytes): addresses of the key and the balance, the
  data's length and address, the address of the owner.
* Rust (`AccountInfo`, 48 bytes): the address of the key, an
  `Rc<RefCell<&mut u64>>` for the balance, an `Rc<RefCell<&mut [u8]>>` for the
  data, the address of the owner. An `Rc` points at two reference counts and
  the cell's borrow flag; what the cell holds starts 24 bytes in. So the
  balance is reached through two pointers, and the data's address and length
  sit in the caller's heap, where a resize has to be written back. -/
def readInfos (p : Program) (mem : ByteArray) (inputLen : Nat) (addr count : UInt64) (rust : Bool) : Option (Array Info) := Id.run do
  if count > 255 then
    return none
  let mut out : Array Info := Array.emptyWithCapacity count.toNat
  for i in [0:count.toNat] do
    if rust then
      match readBytes p mem inputLen (addr + 48 * i.toUInt64) 48 with
      | none => return none
      | some raw =>
        let cell := Wire.u64 raw 16 + 24
        match readBytes p mem inputLen (Wire.u64 raw 0) 32, readBytes p mem inputLen (Wire.u64 raw 8 + 24) 8,
            readBytes p mem inputLen cell 16 with
        | some key, some balance, some slice =>
          out := out.push ⟨key, Wire.u64 balance 0, Wire.u64 slice 8, Wire.u64 slice 0, Wire.u64 raw 24, cell + 8⟩
        | _, _, _ => return none
    else
      let view := addr + 56 * i.toUInt64
      match readBytes p mem inputLen view 56 with
      | none => return none
      | some raw =>
        match readBytes p mem inputLen (Wire.u64 raw 0) 32 with
        | none => return none
        | some key => out := out.push ⟨key, Wire.u64 raw 8, Wire.u64 raw 16, Wire.u64 raw 24, Wire.u64 raw 32, view + 16⟩
  return some out

def findInfo (infos : Array Info) (key : ByteArray) : Nat := Id.run do
  for i in [0:infos.size] do
    if infos[i]!.key == key then
      return i
  return notFound

-- ---------------------------------------------------------------- the input
--
-- A program receives its accounts, instruction data and own address in one
-- buffer, laid out the way Solana's loader does (the "aligned" format).

/-- Zeros for a program's stack and the usual heap, made once: memory that starts as zeros is copied from here rather than pushed a byte at a time. -/
def zeroBlock : ByteArray := zeros (ByteArray.emptyWithCapacity (stackBytes + 262144)) (stackBytes + 262144)

/-- Bytes an account occupies in the input: header, data, room to grow, alignment, rent epoch. -/
def accountSpan (dataLen : Nat) : Nat := (dataLen + 10343) / 8 * 8

/-- The input as the first loader's programs expect it: the same fields in
another order, back to back, with each account's data at its exact size. -/
def serializePacked (accounts : Array Account) (metas : Array Meta) (instruction programId : ByteArray) : ByteArray := Id.run do
  let mut b := Wire.putU64 (ByteArray.emptyWithCapacity 16384) metas.size.toUInt64
  for i in [0:metas.size] do
    let mt := metas[i]!
    let mut first := i
    for j in [0:i] do
      if first == i && metas[j]!.index == mt.index then
        first := j
    if first != i then
      b := b.push first.toUInt8
    else
      let a := accounts[mt.index]!
      b := b.push 0xff
      b := b.push (if mt.signer then 1 else 0)
      b := b.push (if mt.writable then 1 else 0)
      b := b ++ a.key
      b := Wire.putU64 b a.lamports
      b := Wire.putU64 b a.data.size.toUInt64
      b := b ++ a.data
      b := b ++ a.owner
      b := b.push (if a.executable then 1 else 0)
      b := Wire.putU64 b 0xFFFFFFFFFFFFFFFF
  b := Wire.putU64 b instruction.size.toUInt64
  b := b ++ instruction
  return b ++ programId

def serialize (accounts : Array Account) (metas : Array Meta) (instruction programId : ByteArray) : ByteArray := Id.run do
  let mut b := Wire.putU64 (ByteArray.emptyWithCapacity 16384) metas.size.toUInt64
  for i in [0:metas.size] do
    let mt := metas[i]!
    -- an account referenced twice is serialized once; later mentions point at the first
    let mut first := i
    for j in [0:i] do
      if first == i && metas[j]!.index == mt.index then
        first := j
    if first != i then
      b := zeros (b.push first.toUInt8) 7
    else
      let a := accounts[mt.index]!
      b := b.push 0xff
      b := b.push (if mt.signer then 1 else 0)
      b := b.push (if mt.writable then 1 else 0)
      b := b.push (if a.executable then 1 else 0)
      b := zeros b 4
      b := b ++ a.key
      b := b ++ a.owner
      b := Wire.putU64 b a.lamports
      b := Wire.putU64 b a.data.size.toUInt64
      b := b ++ a.data
      -- (room for the account to grow, and alignment: between 10,240 and 10,247 zeros)
      b := zeroBlock.copySlice 0 b b.size (accountSpan a.data.size - 88 - a.data.size - 8)
      b := Wire.putU64 b 0xFFFFFFFFFFFFFFFF
  b := Wire.putU64 b instruction.size.toUInt64
  b := b ++ instruction
  return b ++ programId

end Sbpf
