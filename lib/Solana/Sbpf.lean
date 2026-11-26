import Crypto.Sha256
import Crypto.Ed25519
import Encoding.Base58
import Encoding.Base64
import Solana.Wire

/-!
# An sBPF virtual machine

Solana's on-chain programs are sBPF bytecode. This file loads such programs
from their ELF files and executes instructions against a set of accounts:
the interpreter, the loader with its relocations, the memory map, the
compute-unit meter, the account serialization programs expect, the system
calls, and **cross-program invocation**: a program calling another program,
with the runtime's rules about who may sign for and modify which account.

It targets **sBPF v0**, the version Solana runs today. That covers programs
built by the standard Rust toolchain (the SPL Token programs run here
unmodified) and the default output of
[lean-svm](https://github.com/aeyakovenko/lean-svm), toly's Lean 4 → sBPF
compiler. A program written in Lean and compiled by lean-svm runs here,
inside a virtual machine that is itself written in Lean and compiled by
leanc, and can call the real token programs from it.

Semantics follow the reference implementation (`anza-xyz/sbpf` and Agave's
program runtime) closely enough that compute-unit totals come out the same;
the test suite holds it to the numbers Agave reports for lean-svm's
examples.

Both calling conventions for cross-program calls are provided: the C one
(`sol_invoke_signed_c`, used by lean-svm and Pinocchio programs) and the Rust
one (`sol_invoke_signed_rust`, used by Anchor and `solana-program`).

Not supported: sBPF v3.
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

def storeAt (mem : ByteArray) (idx size : Nat) (v : UInt64) : ByteArray := Id.run do
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
  deriving Inhabited

def Program.failed (elf : ByteArray) (why : String) : Program :=
  ⟨elf, 0, 0, 0, 0, 0, Array.emptyWithCapacity 0, Array.emptyWithCapacity 0, why, 32768⟩

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

/-- Parses and relocates an sBPF v0 ELF file as written by Solana toolchains. -/
def load (image : ByteArray) : Program := Id.run do
  let mut elf := image
  if elf.size < 64 || Wire.u32 elf 0 != 0x464c457f then
    return Program.failed elf "not an ELF file"
  let machine := Wire.u16 elf 18
  if Wire.u8 elf 4 != 2 || (machine != 247 && machine != 263) then
    return Program.failed elf "not a 64-bit sBPF program"
  if Wire.u32 elf 48 != 0 then
    return Program.failed elf "only sBPF v0 programs are supported (this one sets e_flags)"
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
  return ⟨elf, text.off, count, roLow, roHigh, ((entryAddr - text.addr) / 8).toNat, syscalls, calls, "", 32768⟩

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
  else if region == 1 && !write then
    (if off >= p.roLow && off + len <= p.roHigh then progBase + off else Wire.bad)
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

def sext32 (x : UInt64) : UInt64 :=
  if x &&& 0x80000000 != 0 then x ||| 0xFFFFFFFF00000000 else x &&& 0xFFFFFFFF

def sext16 (x : UInt64) : UInt64 :=
  if x &&& 0x8000 != 0 then x ||| 0xFFFFFFFFFFFF0000 else x &&& 0xFFFF

/-- Signed "less than" on two's-complement words. -/
def slt (a b : UInt64) : Bool := (a ^^^ 0x8000000000000000) < (b ^^^ 0x8000000000000000)

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

def notFound : Nat := 0xFFFFFFFF

def zeros (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := b
  for _ in [0:n] do
    out := out.push 0
  return out

/-- The system program's address: 32 zero bytes. -/
def systemProgram : ByteArray := zeros ByteArray.empty 32

def loaderId : ByteArray := Base58.decode "BPFLoaderUpgradeab1e11111111111111111111111"
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
  ⟨Array.emptyWithCapacity 4, Array.emptyWithCapacity 4, clock, budget, Sysvars.standard, 32768⟩

/-- Registers a program under an address. -/
def Machine.add (m : Machine) (id : ByteArray) (p : Program) : Machine :=
  { m with ids := m.ids.push id, programs := m.programs.push p }

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
  if (Ed25519.Point.decode hash).isSome then
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

/-- Bytes an account occupies in the input: header, data, room to grow, alignment, rent epoch. -/
def accountSpan (dataLen : Nat) : Nat := (dataLen + 10343) / 8 * 8

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
      b := zeros b (accountSpan a.data.size - 88 - a.data.size - 8)
      b := Wire.putU64 b 0xFFFFFFFFFFFFFFFF
  b := Wire.putU64 b instruction.size.toUInt64
  b := b ++ instruction
  return b ++ programId

-- ------------------------------------------------------- the system program
--
-- The one program every other program needs is not bytecode: creating
-- accounts and moving lamports between wallets is built into the runtime.

/-- Fails with one of the standard program errors (2 = InvalidArgument, 3 =
InvalidInstructionData, 8 = MissingRequiredSignature, 11 = NotEnoughAccountKeys). -/
def programError (st : State) (code : UInt64) : State :=
  { st with status := programFailed, r0 := code <<< 32 }

/-- Fails with one of the system program's own errors: 0 = account already in
use, 1 = not enough lamports, 3 = data length too large. -/
def systemError (st : State) (code : UInt64) : State :=
  { st with status := programFailed, r0 := if code == 0 then 0x100000000 else code }

/-- The system program's `allocate` followed by `assign`: gives an empty,
system-owned account `space` zero bytes and hands it to `owner`. The account
itself must sign: nobody else can decide what an address becomes. -/
def allocateAndAssign (st : State) (target : Meta) (space : UInt64) (owner : ByteArray) (assign : Bool) : State :=
  let account := st.accounts[target.index]!
  if !target.signer then programError st 8
  else if account.data.size != 0 || account.owner != systemProgram then systemError st 0
  else if space > 10485760 then systemError st 3
  else if !target.writable then st.stop accountRule "the system program was asked to change a read-only account"
  else
    let sized : Account := { account with data := zeros ByteArray.empty space.toNat }
    let owned : Account := if assign then { sized with owner := owner } else sized
    { st with accounts := st.accounts.set! target.index owned }

/-- The system program's `transfer`: lamports from a signing, data-less, system-owned account to any account. -/
def systemTransfer (st : State) (source dest : Meta) (amount : UInt64) : State :=
  let from_ := st.accounts[source.index]!
  if !source.signer then programError st 8
  else if from_.data.size != 0 then programError st 2
  else if amount > from_.lamports then systemError st 1
  else if from_.owner != systemProgram then st.stop accountRule "lamports were taken from an account the system program does not own"
  else if !source.writable || !dest.writable then st.stop accountRule "the system program was asked to change a read-only account"
  else
    let accounts := st.accounts.set! source.index { from_ with lamports := from_.lamports - amount }
    let to := accounts[dest.index]!
    { st with accounts := accounts.set! dest.index { to with lamports := to.lamports + amount } }

def systemInstruction (st : State) (metas : Array Meta) (data : ByteArray) : State := Id.run do
  let st := st.charge 150
  if data.size < 4 then
    return programError st 3
  let tag := Wire.u32 data 0
  if tag == 0 then
    -- CreateAccount { lamports, space, owner }: size and hand over a new account, then fund it
    if data.size < 52 then
      return programError st 3
    if metas.size < 2 then
      return programError st 11
    if st.accounts[metas[1]!.index]!.lamports > 0 then
      return systemError st 0
    let made := allocateAndAssign st metas[1]! (Wire.u64 data 12) (data.extract 20 52) true
    if made.status != finished then
      return made
    return systemTransfer made metas[0]! metas[1]! (Wire.u64 data 4)
  if tag == 1 then
    -- Assign { owner }
    if data.size < 36 then
      return programError st 3
    if metas.size < 1 then
      return programError st 11
    let target := metas[0]!
    let account := st.accounts[target.index]!
    let owner := data.extract 4 36
    if account.owner == owner then
      return st
    if !target.signer then
      return programError st 8
    if account.owner != systemProgram || !target.writable then
      return st.stop accountRule "the system program was asked to reassign an account it may not change"
    return { st with accounts := st.accounts.set! target.index { account with owner := owner } }
  if tag == 2 then
    -- Transfer { lamports }
    if data.size < 12 then
      return programError st 3
    if metas.size < 2 then
      return programError st 11
    return systemTransfer st metas[0]! metas[1]! (Wire.u64 data 4)
  if tag == 8 then
    -- Allocate { space }
    if data.size < 12 then
      return programError st 3
    if metas.size < 1 then
      return programError st 11
    return allocateAndAssign st metas[0]! (Wire.u64 data 4) ByteArray.empty false
  return st.stop unsupportedInstruction s!"system program instruction {tag} is not provided (only create account, assign, transfer and allocate are)"

-- ---------------------------------------------------------------- execution

/-- Replaces bytes that are not printable ASCII, so program output can become a `String`. -/
def printable (b : ByteArray) : String := Id.run do
  let mut out := ByteArray.emptyWithCapacity b.size
  for c in b do
    out := out.push (if c >= 32 && c < 127 then c else 63)
  return String.fromUTF8! out

def hex64 (v : UInt64) : String := Id.run do
  let mut s := "0x"
  let mut started := false
  for i in [0:16] do
    let d := (v >>> (60 - 4 * i).toUInt64) &&& 15
    if d != 0 || started || i == 15 then
      started := true
      s := s.push (Char.ofNat (if d < 10 then 48 + d.toNat else 87 + d.toNat))
  return s

/-- Cost of a memory operation over `n` bytes: Solana charges per 250 bytes, at least 10. -/
def memCost (n : UInt64) : UInt64 := if n / 250 > 10 then n / 250 else 10

def clockBytes (c : Clock) : ByteArray :=
  Wire.putU64 (Wire.putU64 (Wire.putU64 (Wire.putU64 (Wire.putU64 (ByteArray.emptyWithCapacity 40) c.slot)
    c.epochStartTimestamp) c.epoch) c.leaderScheduleEpoch) c.unixTimestamp

/-- A sysvar's serialized form, by its address; empty if it is not one a program can ask for by address. -/
def sysvarBytes (m : Machine) (name : ByteArray) : ByteArray :=
  if name == clockSysvar then clockBytes m.clock
  else if name == rentSysvar then m.sysvars.rent
  else if name == epochScheduleSysvar then m.sysvars.epochSchedule
  else if name == epochRewardsSysvar then m.sysvars.epochRewards
  else if name == slotHashesSysvar then m.sysvars.slotHashes
  else if name == stakeHistorySysvar then m.sysvars.stakeHistory
  else if name == lastRestartSlotSysvar then Wire.putU64 (ByteArray.emptyWithCapacity 8) m.sysvars.lastRestartSlot
  else ByteArray.empty

/-- A sysvar as a Rust program holds it in memory, which is what the
dedicated system calls copy out. It differs from the serialized form only by
alignment padding. -/
def sysvarInMemory (m : Machine) (id : UInt64) : ByteArray :=
  if id == sysClock then clockBytes m.clock
  else if id == sysRent then zeros m.sysvars.rent 7
  else if id == sysEpochSchedule then
    let s := m.sysvars.epochSchedule
    zeros (s.extract 0 17) 7 ++ s.extract 17 33
  else if id == sysEpochRewards then zeros m.sysvars.epochRewards 15
  else Wire.putU64 (ByteArray.emptyWithCapacity 8) m.sysvars.lastRestartSlot

mutual

/-- One program calling another (`sol_invoke_signed_c`, or `sol_invoke_signed_rust`
when `rust` is set: the same call with differently laid out arguments). `st` and `mem` are
the caller's; the result is the state after the callee ran and the caller's
memory with the callee's changes written back.

The steps mirror Agave's: charge for the call; read the instruction, the
caller's account views and its signer seeds; check that every right the
callee is given is one the caller has (or that a seed-derived address
provides); copy the caller's pending changes into the account store; run the
callee; copy what the callee changed back into the caller's memory. -/
partial def invoke (m : Machine) (st0 : State) (callerId : ByteArray) (callerMetas : Array Meta)
    (entry : Array Account) (p : Program) (mem0 : ByteArray) (inputLen : Nat)
    (callAddr infosAddr infosLen seedsAddr seedsLen : UInt64) (depth : Nat) (rust : Bool) : State × ByteArray := Id.run do
  let mut st := st0.charge 946
  let mut mem := mem0
  match readCall p mem inputLen callAddr rust, readInfos p mem inputLen infosAddr infosLen rust with
  | some call, some infos =>
    st := st.charge (call.data.size.toUInt64 / 250 + call.keys.size.toUInt64 * 34 / 250 + infos.size.toUInt64 * 80 / 250)
    -- addresses the caller can sign for because it derived them from seeds
    let mut derived : Array ByteArray := Array.emptyWithCapacity 2
    if seedsLen > 16 then
      return (st.stop invalidSeeds "too many signers", mem)
    for i in [0:seedsLen.toNat] do
      match readBytes p mem inputLen (seedsAddr + 16 * i.toUInt64) 16 with
      | none => return (st.stop accessViolation "signer seeds are not readable", mem)
      | some pair =>
        match readSlices p mem inputLen (Wire.u64 pair 0) (Wire.u64 pair 8) with
        | none => return (st.stop accessViolation "signer seeds are not readable", mem)
        | some seeds =>
          match createProgramAddress seeds callerId with
          | none => return (st.stop invalidSeeds "", mem)
          | some address => derived := derived.push address
    -- the callee's account references, each checked against what the caller holds
    let mut metas : Array Meta := Array.emptyWithCapacity call.keys.size
    for i in [0:call.keys.size] do
      let key := call.keys[i]!
      let index := findAccount st.accounts key
      if index == notFound then
        return (st.stop missingAccount (Base58.encode key), mem)
      let held := rights callerMetas index
      let mut maySign := held &&& 2 != 0
      for d in derived do
        if d == key then
          maySign := true
      let wantSign := call.flags[i]! &&& 2 != 0
      let wantWrite := call.flags[i]! &&& 4 != 0
      if held == 0 then
        return (st.stop missingAccount (Base58.encode key), mem)
      if (wantSign && !maySign) || (wantWrite && held &&& 4 == 0) then
        return (st.stop privilegeEscalation (Base58.encode key), mem)
      metas := metas.push ⟨index, wantSign, wantWrite⟩
    -- a reference repeated with different rights gets the union of them
    for i in [0:metas.size] do
      let r := rights metas metas[i]!.index
      metas := metas.set! i ⟨metas[i]!.index, r &&& 2 != 0, r &&& 4 != 0⟩
    -- the caller may have changed accounts since it started: bring the store up to date
    for i in [0:metas.size] do
      if !(isRepeat metas i) then
        let index := metas[i]!.index
        let account := st.accounts[index]!
        if account.executable then
          st := st.charge (account.data.size.toUInt64 / 250)
        else
          let k := findInfo infos account.key
          if k == notFound then
            return (st.stop missingAccount (Base58.encode account.key), mem)
          let info := infos[k]!
          st := st.charge (info.dataLen / 250)
          match readBytes p mem inputLen info.lamportsAddr 8, readBytes p mem inputLen info.ownerAddr 32,
              readBytes p mem inputLen info.dataAddr info.dataLen with
          | some balance, some owner, some data =>
            let lamports := Wire.u64 balance 0
            let why := changeError callerId (rights callerMetas index &&& 4 != 0) account lamports owner data
            if why != "" then
              return (st.stop accountRule why, mem)
            if data.size > entry[index]!.data.size + maxGrowth then
              return (st.stop invalidRealloc "", mem)
            st := { st with accounts := st.accounts.set! index { account with lamports := lamports, owner := owner, data := data } }
          | _, _, _ => return (st.stop accessViolation "an account view points outside the caller's memory", mem)
    if st.units > m.budget then
      return ({ st with units := m.budget, status := meterExceeded }, mem)
    -- run the callee
    st := execute m st call.programId metas call.data (depth + 1)
    if st.status != finished then
      return (st, mem)
    -- what the callee changed becomes visible in the caller's memory
    for i in [0:metas.size] do
      let index := metas[i]!.index
      let account := st.accounts[index]!
      if !(isRepeat metas i) && metas[i]!.writable && !account.executable then
        let info := infos[findInfo infos account.key]!
        let size := account.data.size.toUInt64
        if account.data.size > entry[index]!.data.size + maxGrowth then
          return (st.stop invalidRealloc "", mem)
        let balanceAt := writable p inputLen info.lamportsAddr 8
        let ownerAt := writable p inputLen info.ownerAddr 32
        let span := if size > info.dataLen then size else info.dataLen
        let dataAt := writable p inputLen info.dataAddr span
        if !(Wire.ok balanceAt) || !(Wire.ok ownerAt) || !(Wire.ok dataAt) then
          return (st.stop accessViolation "an account view points outside the caller's memory", mem)
        mem := storeAt mem balanceAt 8 account.lamports
        mem := account.owner.copySlice 0 mem ownerAt 32
        mem := account.data.copySlice 0 mem dataAt account.data.size
        if size != info.dataLen then
          -- the account was resized: clear what it gave up, and update both places its length is kept
          for k in [account.data.size:info.dataLen.toNat] do
            mem := mem.set! (dataAt + k) 0
          let lenInView := writable p inputLen info.lenAddr 8
          let lenInInput := writable p inputLen (info.dataAddr - 8) 8
          if !(Wire.ok lenInView) || !(Wire.ok lenInInput) then
            return (st.stop accessViolation "an account view points outside the caller's memory", mem)
          mem := storeAt mem lenInView 8 size
          mem := storeAt mem lenInInput 8 size
    return (st, mem)
  | _, _ => return (st.stop accessViolation "the arguments of the call are not readable", mem)

/-- Processes one instruction: `programId` is run on the accounts `metas`
refers to, with `data`. Returns the state afterwards; if `status` is not
`finished` the instruction failed and the caller discards the changes. -/
partial def execute (m : Machine) (st0 : State) (programId : ByteArray) (metas : Array Meta)
    (data : ByteArray) (depth : Nat) : State := Id.run do
  if depth > maxInstructionDepth then
    return st0.stop callDepthExceeded "programs called one another more than 4 levels deep"
  let st0 := { st0 with trace := st0.trace.push ⟨depth, programId, metas, data⟩ }
  let entry := st0.accounts
  let mut entrySum : UInt64 := 0
  for i in [0:metas.size] do
    if !(isRepeat metas i) then
      entrySum := entrySum + entry[metas[i]!.index]!.lamports
  if programId == systemProgram || programId == computeBudgetProgram then
    -- built into the runtime; the compute budget program's work is done before the transaction runs
    let after := if programId == systemProgram then systemInstruction st0 metas data else st0.charge 150
    if after.units > m.budget then
      return { after with units := m.budget, status := meterExceeded }
    return after
  let mut which := notFound
  for i in [0:m.ids.size] do
    if m.ids[i]! == programId then
      which := i
  if which == notFound then
    return st0.stop unknownProgram (Base58.encode programId)
  if m.programs[which]!.error != "" then
    return st0.stop unsupportedInstruction m.programs[which]!.error
  let loaded : Program := m.programs[which]!
  let p : Program := { loaded with heap := m.heap }
  let ⟨accounts0, units0, logs0, returnData0, _, _, _, trace0⟩ := st0
  let mut accounts := accounts0
  -- a heap beyond the first 32 KiB costs 8 units per further 32 KiB
  let mut units := units0 + ((p.heap + 32767) / 32768 - 1).toUInt64 * 8
  let mut logs := logs0
  let mut returnData := returnData0
  let mut trace := trace0
  let budget := m.budget

  let input := serialize accounts metas data programId
  let inputLen := input.size
  let mut mem := ByteArray.emptyWithCapacity (stackBytes + p.heap + inputLen)
  for _ in [0:stackBytes + p.heap] do
    mem := mem.push 0
  mem := mem ++ input
  let mut regs : Array UInt64 := Array.replicate 11 0
  regs := regs.set! 1 inputStart
  regs := regs.set! 10 (stackStart + frameBytes.toUInt64)
  -- saved r6..r9, frame pointer and return address of every active call
  let mut frames : Array UInt64 := Array.replicate (maxDepth * 6) 0
  let mut calls := 0
  let mut pc := p.entry
  let mut status := finished
  let mut r0 : UInt64 := 0
  let mut detail := ""
  repeat
    if units >= budget then
      status := budgetExceeded
      break
    if pc >= p.count then
      status := executionOverrun
      break
    units := units + 1
    let o := p.textOff + pc * 8
    let opc := Wire.u8 p.elf o
    let dst := (Wire.u8 p.elf (o + 1) &&& 15).toNat
    let src := (Wire.u8 p.elf (o + 1) >>> 4).toNat
    let off := sext16 (Wire.u16 p.elf (o + 2))
    let imm32 := Wire.u32 p.elf (o + 4)
    let imm := sext32 imm32
    if dst > 10 || src > 10 then
      status := unsupportedInstruction
      break
    let cls := opc &&& 7
    let op := opc &&& 0xf0
    let mut next := pc + 1
    if cls == 7 || cls == 4 then
      -- arithmetic: 64-bit (class 7) and 32-bit (class 4), operand from a register or the immediate
      let b := if opc &&& 8 != 0 then regs[src]! else imm
      let a := regs[dst]!
      if opc == 0xd4 || opc == 0xdc then
        -- byte order: `le` truncates, `be` also swaps
        let bytes := if imm32 == 16 then 2 else if imm32 == 32 then 4 else if imm32 == 64 then 8 else 0
        if bytes == 0 then
          status := unsupportedInstruction
          break
        let low := if bytes == 8 then a else a &&& (((1 : UInt64) <<< (8 * bytes).toUInt64) - 1)
        regs := regs.set! dst (if opc == 0xdc then bswap low bytes else low)
      else if op > 0xc0 then
        status := unsupportedInstruction
        break
      else if (op == 0x30 || op == 0x90) && (if cls == 7 then b == 0 else b &&& 0xFFFFFFFF == 0) then
        status := divideByZero
        break
      else
        regs := regs.set! dst (if cls == 7 then alu64 op a b else alu32 op a b)
    else if cls == 5 then
      if opc == 0x05 then
        next := (next.toUInt64 + off).toNat
      else if opc == 0x95 then
        if calls == 0 then
          break
        -- return from a call inside the program
        calls := calls - 1
        for k in [0:4] do
          regs := regs.set! (6 + k) frames[calls * 6 + k]!
        regs := regs.set! 10 frames[calls * 6 + 4]!
        next := frames[calls * 6 + 5]!.toNat
      else if opc == 0x8d || (opc == 0x85 && p.syscalls[pc]! == 0) then
        -- call a function of the program: by symbol, by relative offset, or (callx) through a register
        let target := if opc == 0x8d then (regs[(imm32 &&& 15).toNat]! - programStart - p.textOff.toUInt64) / 8
          else if p.calls[pc]! != 0 then p.calls[pc]! - 1
          else next.toUInt64 + imm
        for k in [0:4] do
          frames := frames.set! (calls * 6 + k) regs[6 + k]!
        frames := frames.set! (calls * 6 + 4) regs[10]!
        frames := frames.set! (calls * 6 + 5) next.toUInt64
        calls := calls + 1
        if calls == maxDepth then
          status := callDepthExceeded
          break
        regs := regs.set! 10 (regs[10]! + frameBytes.toUInt64)
        if target >= p.count.toUInt64 then
          status := executionOverrun
          break
        next := target.toNat
      else if opc == 0x85 then
        -- a system call; arguments in r1..r5, result in r0
        let id := p.syscalls[pc]!
        let a1 := regs[1]!
        let a2 := regs[2]!
        let a3 := regs[3]!
        let mut result : UInt64 := 0
        if id == sysLog then
          units := units + (if a2 > 100 then a2 else 100)
          match readBytes p mem inputLen a1 a2 with
          | none => status := accessViolation
          | some text => logs := logs.push (printable text)
        else if id == sysLog64 then
          units := units + 100
          logs := logs.push s!"{hex64 a1}, {hex64 a2}, {hex64 a3}, {hex64 regs[4]!}, {hex64 regs[5]!}"
        else if id == sysLogPubkey then
          units := units + 100
          match readBytes p mem inputLen a1 32 with
          | none => status := accessViolation
          | some key => logs := logs.push (Base58.encode key)
        else if id == sysLogUnits then
          units := units + 100
          logs := logs.push s!"consumption: {budget - units} units remaining"
        else if id == sysMemcpy || id == sysMemmove then
          units := units + memCost a3
          let dest := writable p inputLen a1 a3
          match readBytes p mem inputLen a2 a3 with
          | none => status := accessViolation
          | some bytes =>
            if Wire.ok dest then
              mem := bytes.copySlice 0 mem dest bytes.size
            else
              status := accessViolation
        else if id == sysMemset then
          units := units + memCost a3
          let dest := writable p inputLen a1 a3
          if Wire.ok dest then
            for i in [0:a3.toNat] do
              mem := mem.set! (dest + i) a2.toUInt8
          else
            status := accessViolation
        else if id == sysMemcmp then
          -- compares two ranges and stores the difference of the first unequal bytes as an i32
          units := units + memCost a3
          let dest := writable p inputLen regs[4]! 4
          match readBytes p mem inputLen a1 a3, readBytes p mem inputLen a2 a3 with
          | some x, some y =>
            if Wire.ok dest then
              let mut diff : UInt64 := 0
              for i in [0:x.size] do
                if x[i]! != y[i]! then
                  diff := (x[i]!.toUInt64 - y[i]!.toUInt64) &&& 0xFFFFFFFF
                  break
              mem := storeAt mem dest 4 diff
            else
              status := accessViolation
          | _, _ => status := accessViolation
        else if id == sysSha256 then
          -- hashes a list of byte ranges: a1 points at (address, length) pairs, a2 counts them
          units := units + 85
          if a2 > 20000 then
            status := accessViolation
          else
            let mut message := ByteArray.empty
            for i in [0:a2.toNat] do
              match readBytes p mem inputLen (a1 + 16 * i.toUInt64) 16 with
              | none => status := accessViolation
              | some pair =>
                let len := Wire.u64 pair 8
                units := units + (if len / 2 > 10 then len / 2 else 10)
                match readBytes p mem inputLen (Wire.u64 pair 0) len with
                | none => status := accessViolation
                | some part => message := message ++ part
            let dest := writable p inputLen a3 32
            if status == finished && Wire.ok dest then
              mem := (Sha256.hash message).copySlice 0 mem dest 32
            else
              status := accessViolation
        else if id == sysClock || id == sysRent || id == sysEpochSchedule || id == sysEpochRewards || id == sysLastRestart then
          -- a sysvar, copied out the way a Rust program holds it in memory
          let bytes := sysvarInMemory m id
          units := units + 100 + bytes.size.toUInt64
          let dest := writable p inputLen a1 bytes.size.toUInt64
          if Wire.ok dest then
            mem := bytes.copySlice 0 mem dest bytes.size
          else
            status := accessViolation
        else if id == sysGetSysvar then
          -- part of a sysvar's serialized form: a1 names it, a2 is where to put it, a3 and r4 give offset and length
          let length := regs[4]!
          units := units + 100 + (if length / 250 > 10 then length / 250 else 10)
          let dest := writable p inputLen a2 length
          match readBytes p mem inputLen a1 32 with
          | none => status := accessViolation
          | some name =>
            let whole := sysvarBytes m name
            if !(Wire.ok dest) || a3 + length < a3 then
              status := accessViolation
            else if whole.size == 0 then
              result := 2
            else if a3 + length > whole.size.toUInt64 then
              result := 1
            else
              mem := (whole.extract a3.toNat (a3 + length).toNat).copySlice 0 mem dest length.toNat
        else if id == sysEpochStake then
          -- stake of the whole cluster (a1 = 0) or delegated to one vote account; nothing is staked here
          if a1 == 0 then
            units := units + 100
          else
            units := units + 110
            if (readBytes p mem inputLen a1 32).isNone then
              status := accessViolation
        else if id == sysSetReturn then
          units := units + 100 + a2 / 250
          match readBytes p mem inputLen a1 a2 with
          | none => status := accessViolation
          | some bytes =>
            if bytes.size > 1024 then
              status := accessViolation
            else
              returnData := programId ++ bytes
        else if id == sysGetReturn then
          -- copies up to a2 bytes of the last return data to a1 and its program to a3; returns its length
          units := units + 100
          if returnData.size > 32 then
            let payload := returnData.extract 32 returnData.size
            let n := if a2 < payload.size.toUInt64 then a2 else payload.size.toUInt64
            units := units + (n + 32) / 250
            let dest := writable p inputLen a1 n
            let idDest := writable p inputLen a3 32
            if Wire.ok dest && Wire.ok idDest then
              mem := (payload.extract 0 n.toNat).copySlice 0 mem dest n.toNat
              mem := (returnData.extract 0 32).copySlice 0 mem idDest 32
              result := payload.size.toUInt64
            else
              status := accessViolation
        else if id == sysLogData then
          -- binary data for whoever reads the logs (Anchor's events): a1 points at (address, length) pairs
          units := units + 100 + 100 * a2
          match readSlices p mem inputLen a1 a2 with
          | none => status := accessViolation
          | some fields =>
            let mut line := "data:"
            for field in fields do
              units := units + field.size.toUInt64
              line := line ++ " " ++ Base64.encode field
            logs := logs.push line
        else if id == sysRemaining then
          units := units + 100
          result := budget - units
        else if id == sysStackHeight then
          units := units + 100
          result := depth.toUInt64
        else if id == sysSibling then
          -- an earlier instruction at this depth: a1 = how far back (0 = the one before this). A program
          -- calls this twice: first to learn the sizes (written to the header at a2), then with buffers.
          units := units + 100
          let mut found := notFound
          let mut seen : UInt64 := 0
          let mut k := trace.size
          while k > 0 do
            k := k - 1
            if trace[k]!.depth < depth then
              k := 0
            else if trace[k]!.depth == depth then
              if a1 + 1 == seen then
                found := k
                k := 0
              else
                seen := seen + 1
          if found != notFound then
            let frame := trace[found]!
            let header := writable p inputLen a2 16
            if !(Wire.ok header) then
              status := accessViolation
            else if Wire.u64 mem header == frame.data.size.toUInt64 && Wire.u64 mem (header + 8) == frame.metas.size.toUInt64 then
              let idAt := writable p inputLen a3 32
              let dataAt := writable p inputLen regs[4]! frame.data.size.toUInt64
              let metasAt := writable p inputLen regs[5]! (34 * frame.metas.size).toUInt64
              if Wire.ok idAt && Wire.ok dataAt && Wire.ok metasAt then
                mem := frame.program.copySlice 0 mem idAt 32
                mem := frame.data.copySlice 0 mem dataAt frame.data.size
                for j in [0:frame.metas.size] do
                  let mt := frame.metas[j]!
                  mem := accounts[mt.index]!.key.copySlice 0 mem (metasAt + 34 * j) 32
                  mem := mem.set! (metasAt + 34 * j + 32) (if mt.signer then 1 else 0)
                  mem := mem.set! (metasAt + 34 * j + 33) (if mt.writable then 1 else 0)
              else
                status := accessViolation
            else
              mem := storeAt mem header 8 frame.data.size.toUInt64
              mem := storeAt mem (header + 8) 8 frame.metas.size.toUInt64
            result := 1
        else if id == sysFindAddress || id == sysCreateAddress then
          -- seeds at a1 (a2 of them), program address at a3; results to r4 (and the bump to r5)
          units := units + 1500
          match readSlices p mem inputLen a1 a2, readBytes p mem inputLen a3 32 with
          | some seeds, some owner =>
            let mut address := ByteArray.empty
            let mut bump : UInt64 := 0
            if id == sysCreateAddress then
              match createProgramAddress seeds owner with
              | some found => address := found
              | none => result := 1
            else
              result := 1
              for i in [0:256] do
                if result == 1 then
                  match createProgramAddress (seeds.push (ByteArray.empty.push (255 - i).toUInt8)) owner with
                  | some found =>
                    address := found
                    bump := (255 - i).toUInt64
                    result := 0
                  | none => units := units + 1500
            if result == 0 then
              let dest := writable p inputLen regs[4]! 32
              let bumpDest := if id == sysFindAddress then writable p inputLen regs[5]! 1 else 0
              if Wire.ok dest && Wire.ok bumpDest then
                mem := address.copySlice 0 mem dest 32
                if id == sysFindAddress then
                  mem := mem.set! bumpDest bump.toUInt8
              else
                status := accessViolation
          | _, _ => status := accessViolation
        else if id == sysInvoke || id == sysInvokeRust then
          let (after, memAfter) := invoke m ⟨accounts, units, logs, returnData, finished, 0, "", trace⟩ programId metas entry
            p mem inputLen a1 a2 a3 regs[4]! regs[5]! depth (id == sysInvokeRust)
          mem := memAfter
          let ⟨accounts1, units1, logs1, returnData1, status1, r01, detail1, trace1⟩ := after
          trace := trace1
          accounts := accounts1
          units := units1
          logs := logs1
          returnData := returnData1
          status := status1
          r0 := r01
          detail := detail1
        else if id == sysAbort || id == sysPanic then
          status := aborted
          if id == sysPanic then
            match readBytes p mem inputLen a1 a2 with
            | none => pure ()
            | some file => detail := s!"panicked at {printable file}:{a3}"
        else
          status := unsupportedSyscall
          detail := "the program makes a system call this machine does not provide"
        if status != finished then
          break
        if units > budget then
          -- a system call that the budget cannot pay for uses up whatever was left
          units := budget
          status := meterExceeded
          break
        regs := regs.set! 0 result
      else if op == 0 || op == 0x80 || op == 0x90 || op > 0xd0 then
        status := unsupportedInstruction
        break
      else
        let b := if opc &&& 8 != 0 then regs[src]! else imm
        if jumpTaken op regs[dst]! b then
          next := (next.toUInt64 + off).toNat
    else if opc == 0x18 then
      -- load a 64-bit constant: two instruction slots
      regs := regs.set! dst (imm32 ||| (Wire.u32 p.elf (o + 12) <<< 32))
      next := pc + 2
    else if cls == 1 || cls == 2 || cls == 3 then
      -- memory: load (1), store immediate (2), store register (3); width in bits 3-4
      let width := opc &&& 0x18
      let size := if width == 0x00 then 4 else if width == 0x08 then 2 else if width == 0x10 then 1 else 8
      if opc &&& 0xe0 != 0x60 then
        status := unsupportedInstruction
        break
      let addr := (if cls == 1 then regs[src]! else regs[dst]!) + off
      let idx := locate p inputLen addr size (cls != 1)
      if !(Wire.ok idx) then
        status := accessViolation
        detail := s!"at address {hex64 addr}, instruction {pc}"
        break
      if cls == 1 then
        regs := regs.set! dst (loadAt p mem idx size)
      else
        mem := storeAt mem idx size (if cls == 2 then imm else regs[src]!)
    else
      status := unsupportedInstruction
      break
    pc := next
  if status == unsupportedInstruction && detail == "" then
    detail := s!"at instruction {pc}"
  if status == finished && regs[0]! != 0 then
    status := programFailed
    r0 := regs[0]!
  if status == finished then
    -- the program is done: take its changes to the accounts, if the rules allow them
    let mut o := stackBytes + p.heap + 8
    let mut sum : UInt64 := 0
    for i in [0:metas.size] do
      if status == finished then
        if isRepeat metas i then
          o := o + 8
        else
          let index := metas[i]!.index
          let account := accounts[index]!
          let was := entry[index]!.data.size
          let len := Wire.u64 mem (o + 80)
          if len > (was + maxGrowth).toUInt64 then
            status := invalidRealloc
          else
            let lamports := Wire.u64 mem (o + 72)
            let owner := mem.extract (o + 40) (o + 72)
            let contents := mem.extract (o + 88) (o + 88 + len.toNat)
            let why := changeError programId metas[i]!.writable account lamports owner contents
            if why != "" then
              status := accountRule
              detail := why
            else
              accounts := accounts.set! index { account with lamports := lamports, owner := owner, data := contents }
              sum := sum + lamports
          o := o + accountSpan was
    if status == finished && sum != entrySum then
      status := unbalanced
  return ⟨accounts, units, logs, returnData, status, r0, detail, trace⟩

end

/-- Processes a top-level instruction. A failed instruction leaves the accounts as they were. -/
def process (m : Machine) (accounts : Array Account) (programId : ByteArray) (metas : Array Meta)
    (data : ByteArray) : State :=
  let st := execute m ⟨accounts, 0, Array.emptyWithCapacity 4, ByteArray.empty, finished, 0, "", Array.emptyWithCapacity 4⟩ programId metas data 1
  if st.status == finished then st else { st with accounts := accounts }

/-- Names for the standard program errors a program returns in `r0`. -/
def errorName (r0 : UInt64) : String :=
  let code := r0 >>> 32
  if r0 == 0 then "success"
  else if r0 &&& 0xFFFFFFFF != 0 && code == 0 then s!"custom error {r0}"
  else if code == 1 then "custom error 0"
  else if code == 2 then "InvalidArgument"
  else if code == 3 then "InvalidInstructionData"
  else if code == 4 then "InvalidAccountData"
  else if code == 5 then "AccountDataTooSmall"
  else if code == 6 then "InsufficientFunds"
  else if code == 7 then "IncorrectProgramId"
  else if code == 8 then "MissingRequiredSignature"
  else if code == 9 then "AccountAlreadyInitialized"
  else if code == 10 then "UninitializedAccount"
  else if code == 11 then "NotEnoughAccountKeys"
  else if code == 18 then "IllegalOwner"
  else if code == 24 then "ArithmeticOverflow"
  else s!"program error {hex64 r0}"

/-- One line describing how an instruction ended. -/
def outcome (st : State) : String :=
  if st.status == finished then "success"
  else if st.status == programFailed then errorName st.r0
  else if st.detail == "" then statusName st.status
  else s!"{statusName st.status}: {st.detail}"

end Sbpf
