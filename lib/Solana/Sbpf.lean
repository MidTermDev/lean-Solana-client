import Crypto.Sha256
import Encoding.Base58
import Solana.Wire

/-!
# An sBPF virtual machine

Solana's on-chain programs are sBPF bytecode. This file loads such a program
from its ELF file and executes it: the interpreter, the memory map, the
compute-unit meter, the account serialization programs expect as input, and
the system calls a program can make without calling other programs.

It targets **sBPF v0**, the version Solana runs today and the default output
of [lean-svm](https://github.com/aeyakovenko/lean-svm), toly's Lean 4 → sBPF
compiler. A program written in Lean and compiled by lean-svm runs here,
inside a virtual machine that is itself written in Lean and compiled by
leanc: Lean on both sides of the bytecode.

Semantics follow the reference interpreter (`anza-xyz/sbpf`) instruction by
instruction, including the parts that are easy to get wrong: 32-bit
additions, subtractions and multiplications sign-extend their result in v0,
the other 32-bit operations zero-extend. The test suite runs lean-svm's own
example programs and requires the exact compute-unit counts Agave reports.

Not supported: cross-program invocation (a program calling another
program), and sBPF v3.
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

-- How a run ended.
def finished : UInt64 := 0
def accessViolation : UInt64 := 1
def divideByZero : UInt64 := 2
def unsupportedInstruction : UInt64 := 3
def callDepthExceeded : UInt64 := 4
def budgetExceeded : UInt64 := 5
def unsupportedSyscall : UInt64 := 6
def executionOverrun : UInt64 := 7
def aborted : UInt64 := 8

def statusName (s : UInt64) : String :=
  if s == 0 then "finished"
  else if s == 1 then "access violation"
  else if s == 2 then "divide by zero"
  else if s == 3 then "unsupported instruction"
  else if s == 4 then "call depth exceeded"
  else if s == 5 then "compute budget exceeded"
  else if s == 6 then "unsupported system call"
  else if s == 7 then "execution ran past the end of the program"
  else "program aborted"

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
  else if cstrIs b o "abort" || cstrIs b o "sol_panic_" then sysAbort
  else if cstrIs b o "sol_log_compute_units_" then sysLogUnits
  else sysUnknown

/-- A loaded program. `syscalls[pc]` is the system call made by the `call`
instruction at `pc`, or 0. Program memory is the file itself: the byte at
file offset `x` is readable at address `programStart + x` for `x` in
`[roLow, roHigh)`. -/
structure Program where
  elf : ByteArray
  textOff : Nat
  count : Nat
  roLow : Nat
  roHigh : Nat
  entry : Nat
  syscalls : Array UInt64
  error : String
  deriving Inhabited

def Program.failed (elf : ByteArray) (why : String) : Program :=
  ⟨elf, 0, 0, 0, 0, 0, Array.emptyWithCapacity 0, why⟩

/-- One section header: offset and size of the section named `name`, or (0, 0). -/
def findSection (elf : ByteArray) (shoff shnum strOff : Nat) (name : String) : Nat × Nat := Id.run do
  for i in [0:shnum] do
    let h := shoff + 64 * i
    let nameOff := (Wire.u32 elf h).toNat
    if cstrIs elf (strOff + nameOff) name then
      let off := Wire.u64 elf (h + 24)
      let size := Wire.u64 elf (h + 32)
      -- lengths come from the file: check them before doing arithmetic with them
      if off > elf.size.toUInt64 || size > elf.size.toUInt64 || off.toNat + size.toNat > elf.size then
        return (0, 0)
      return (off.toNat, size.toNat)
  return (0, 0)

/-- Parses an sBPF v0 ELF file as written by Solana toolchains. -/
def load (elf : ByteArray) : Program := Id.run do
  if elf.size < 64 || Wire.u32 elf 0 != 0x464c457f then
    return Program.failed elf "not an ELF file"
  if Wire.u8 elf 4 != 2 || Wire.u16 elf 18 != 247 then
    return Program.failed elf "not a 64-bit sBPF program (expected machine type EM_BPF)"
  if Wire.u32 elf 48 != 0 then
    return Program.failed elf "only sBPF v0 programs are supported (this one sets e_flags)"
  let shoff := Wire.u64 elf 40
  let shnum := (Wire.u16 elf 60).toNat
  let shstrndx := (Wire.u16 elf 62).toNat
  if shoff > elf.size.toUInt64 || shoff.toNat + 64 * shnum > elf.size || shstrndx >= shnum then
    return Program.failed elf "malformed section table"
  let strOff := Wire.u64 elf (shoff.toNat + 64 * shstrndx + 24)
  if strOff > elf.size.toUInt64 then
    return Program.failed elf "malformed section name table"
  let (textOff, textLen) := findSection elf shoff.toNat shnum strOff.toNat ".text"
  if textLen == 0 || textLen % 8 != 0 then
    return Program.failed elf "no .text section"
  let (roOff, roLen) := findSection elf shoff.toNat shnum strOff.toNat ".rodata"
  let roHigh := if roLen != 0 && roOff + roLen > textOff + textLen then roOff + roLen else textOff + textLen
  let roLow := if roLen != 0 && roOff < textOff then roOff else textOff
  let count := textLen / 8
  let entryAddr := Wire.u64 elf 24
  if entryAddr < textOff.toUInt64 || entryAddr >= (textOff + textLen).toUInt64 || (entryAddr - textOff.toUInt64) % 8 != 0 then
    return Program.failed elf "entry point is outside .text"
  -- system calls are `call` instructions whose target a relocation names
  let mut syscalls : Array UInt64 := Array.replicate count 0
  let (relOff, relLen) := findSection elf shoff.toNat shnum strOff.toNat ".rel.dyn"
  let (symOff, symLen) := findSection elf shoff.toNat shnum strOff.toNat ".dynsym"
  let (dynstrOff, dynstrLen) := findSection elf shoff.toNat shnum strOff.toNat ".dynstr"
  for i in [0:relLen / 16] do
    let site := Wire.u64 elf (relOff + 16 * i)
    let info := Wire.u64 elf (relOff + 16 * i + 8)
    let sym := info >>> 32
    -- R_BPF_64_32: the call's immediate is the hash of the symbol's name
    if info &&& 0xFFFFFFFF == 10 && site >= textOff.toUInt64 && site < (textOff + textLen).toUInt64 &&
        sym < (symLen / 24).toUInt64 then
      let nameOff := (Wire.u32 elf (symOff + 24 * sym.toNat)).toNat
      if nameOff < dynstrLen then
        syscalls := syscalls.set! ((site.toNat - textOff) / 8) (syscallId elf (dynstrOff + nameOff))
  return ⟨elf, textOff, count, roLow, roHigh, (entryAddr.toNat - textOff) / 8, syscalls, ""⟩

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
  else if region == 3 then (if off + len <= heapBytes then stackBytes + off else Wire.bad)
  else if region == 4 then (if off + len <= inputLen then stackBytes + heapBytes + off else Wire.bad)
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

def storeAt (mem : ByteArray) (idx size : Nat) (v : UInt64) : ByteArray := Id.run do
  let mut m := mem
  for i in [0:size] do
    m := m.set! (idx + i) (v >>> (8 * i).toUInt64).toUInt8
  return m

/-- The bytes at `[addr, addr + len)`, wherever they live; `none` if any are unmapped. -/
def readBytes (p : Program) (mem : ByteArray) (inputLen : Nat) (addr len : UInt64) : Option ByteArray :=
  if len > 0x10000000 then none
  else
    let idx := locate p inputLen addr len.toNat false
    if !(Wire.ok idx) then none
    else if idx >= progBase then some (p.elf.extract (idx - progBase) (idx - progBase + len.toNat))
    else some (mem.extract idx (idx + len.toNat))

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

-- ---------------------------------------------------------------- execution

/-- The `Clock` sysvar a program can ask for. -/
structure Clock where
  slot : UInt64
  epochStartTimestamp : UInt64
  epoch : UInt64
  leaderScheduleEpoch : UInt64
  unixTimestamp : UInt64

/-- What a run produced. `status` is 0 when the program reached its final
`exit`; `r0` is then its return value (0 for success, a `ProgramError`
otherwise). `input` is the input region afterwards, where the program's
changes to accounts live. -/
structure Outcome where
  status : UInt64
  r0 : UInt64
  units : UInt64
  input : ByteArray
  logs : Array String
  detail : String

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

/-- Runs `p` on a serialized `input` until it exits, faults, or spends `budget` compute units.
Every instruction costs one unit; system calls add their own. -/
def run (p : Program) (input : ByteArray) (clock : Clock) (budget : UInt64) : Outcome := Id.run do
  let inputLen := input.size
  let mut mem := ByteArray.emptyWithCapacity (stackBytes + heapBytes + inputLen)
  for _ in [0:stackBytes + heapBytes] do
    mem := mem.push 0
  mem := mem ++ input
  let mut regs : Array UInt64 := Array.replicate 11 0
  regs := regs.set! 1 inputStart
  regs := regs.set! 10 (stackStart + frameBytes.toUInt64)
  -- saved r6..r9, frame pointer and return address of every active call
  let mut frames : Array UInt64 := Array.replicate (maxDepth * 6) 0
  let mut depth := 0
  let mut pc := p.entry
  let mut units : UInt64 := 0
  let mut status := finished
  let mut detail := ""
  let mut logs : Array String := Array.emptyWithCapacity 4
  let mut running := p.error == ""
  if !running then
    status := unsupportedInstruction
    detail := p.error
  while running do
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
        if depth == 0 then
          break
        -- return from a call inside the program
        depth := depth - 1
        for k in [0:4] do
          regs := regs.set! (6 + k) frames[depth * 6 + k]!
        regs := regs.set! 10 frames[depth * 6 + 4]!
        next := frames[depth * 6 + 5]!.toNat
      else if opc == 0x85 && imm32 != 0xFFFFFFFF || opc == 0x8d then
        -- call a function of the program: relative target, or (callx) an address in a register
        let target := if opc == 0x85 then next.toUInt64 + imm
          else (regs[(imm32 &&& 15).toNat]! - programStart - p.textOff.toUInt64) / 8
        for k in [0:4] do
          frames := frames.set! (depth * 6 + k) regs[6 + k]!
        frames := frames.set! (depth * 6 + 4) regs[10]!
        frames := frames.set! (depth * 6 + 5) next.toUInt64
        depth := depth + 1
        if depth == maxDepth then
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
          let dest := locate p inputLen a1 (if a3 > 0x10000000 then 0x10000001 else a3.toNat) true
          match readBytes p mem inputLen a2 a3 with
          | none => status := accessViolation
          | some bytes =>
            if Wire.ok dest then
              mem := bytes.copySlice 0 mem dest bytes.size
            else
              status := accessViolation
        else if id == sysMemset then
          units := units + memCost a3
          let dest := locate p inputLen a1 (if a3 > 0x10000000 then 0x10000001 else a3.toNat) true
          if Wire.ok dest then
            for i in [0:a3.toNat] do
              mem := mem.set! (dest + i) a2.toUInt8
          else
            status := accessViolation
        else if id == sysMemcmp then
          -- compares two ranges and stores the difference of the first unequal bytes as an i32
          units := units + memCost a3
          let dest := locate p inputLen regs[4]! 4 true
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
            let dest := locate p inputLen a3 32 true
            if status == finished && Wire.ok dest then
              mem := (Sha256.hash message).copySlice 0 mem dest 32
            else
              status := accessViolation
        else if id == sysClock then
          units := units + 140
          let dest := locate p inputLen a1 40 true
          if Wire.ok dest then
            mem := storeAt mem dest 8 clock.slot
            mem := storeAt mem (dest + 8) 8 clock.epochStartTimestamp
            mem := storeAt mem (dest + 16) 8 clock.epoch
            mem := storeAt mem (dest + 24) 8 clock.leaderScheduleEpoch
            mem := storeAt mem (dest + 32) 8 clock.unixTimestamp
          else
            status := accessViolation
        else if id == sysAbort then
          status := aborted
        else
          status := unsupportedSyscall
          detail := "the program makes a system call this machine does not provide (for example calling another program)"
        if status != finished then
          break
        if units > budget then
          status := budgetExceeded
          break
        regs := regs.set! 0 0
      else if op == 0 || op == 0x80 || op == 0x90 || op > 0xd0 || opc &&& 7 != 5 then
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
        detail := s!"at address {hex64 addr}"
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
  return ⟨status, regs[0]!, units, mem.extract (stackBytes + heapBytes) mem.size, logs, detail⟩

-- ------------------------------------------------------------------- input
--
-- A program receives its accounts, instruction data and own address in one
-- buffer, laid out the way Solana's loader does (the "aligned" format).

/-- An account as passed to a program. -/
structure Account where
  key : ByteArray
  owner : ByteArray
  lamports : UInt64
  data : ByteArray
  signer : Bool
  writable : Bool
  deriving Inhabited

def zeros (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := b
  for _ in [0:n] do
    out := out.push 0
  return out

/-- Bytes an account occupies in the input: header, data, room to grow, alignment, rent epoch. -/
def accountSpan (dataLen : Nat) : Nat := (dataLen + 10343) / 8 * 8

def serialize (accounts : Array Account) (instruction programId : ByteArray) : ByteArray := Id.run do
  let mut b := Wire.putU64 (ByteArray.emptyWithCapacity 16384) accounts.size.toUInt64
  for i in [0:accounts.size] do
    let a := accounts[i]!
    -- an account listed twice is serialized once; later mentions point at the first
    let mut first := i
    for j in [0:i] do
      if first == i && accounts[j]!.key == a.key then
        first := j
    if first != i then
      b := zeros (b.push first.toUInt8) 7
    else
      b := b.push 0xff
      b := b.push (if a.signer then 1 else 0)
      b := b.push (if a.writable then 1 else 0)
      b := zeros b 5
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

/-- Reads the accounts back out of the input region after a run. -/
def readBack (accounts : Array Account) (input : ByteArray) : Array Account := Id.run do
  let mut out : Array Account := Array.emptyWithCapacity accounts.size
  let mut o := 8
  for i in [0:accounts.size] do
    let a := accounts[i]!
    let mut first := i
    for j in [0:i] do
      if first == i && accounts[j]!.key == a.key then
        first := j
    if first != i then
      out := out.push out[first]!
      o := o + 8
    else
      let len := Wire.u64 input (o + 80)
      -- a program may grow an account by up to 10240 bytes
      let size := if len > (a.data.size + 10240).toUInt64 then a.data.size else len.toNat
      out := out.push { a with lamports := Wire.u64 input (o + 72), data := input.extract (o + 88) (o + 88 + size) }
      o := o + accountSpan a.data.size
  return out

/-- Names for the standard program errors a program returns in `r0`. -/
def errorName (r0 : UInt64) : String :=
  let code := r0 >>> 32
  if r0 == 0 then "success"
  else if r0 &&& 0xFFFFFFFF != 0 && code == 0 then s!"custom error {r0}"
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

end Sbpf
