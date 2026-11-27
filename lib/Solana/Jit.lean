import Fast

/-!
# sBPF programs as the processor's own instructions

The interpreter (`Solana.Sbpf`) takes about sixty machine instructions to
carry out one instruction of a program: fetch it, find out what it is, find
its registers, do it, count it. This file translates a program once, when
it is loaded, into x86-64 code that does the same thing directly: an sBPF
register is a machine register, an addition is an `add`.

The interpreter stays the definition of what a program does, and the
translation leans on it. The translated code only does what is ordinary:
arithmetic, loads and stores inside the program's memory, jumps, and calls
and returns between the program's own functions. Whenever something else
comes up (a system call, the end of the program, an address outside the
memory, a division by zero, a budget about to run out, an instruction this
file does not translate) it stops and says at which instruction, and the
interpreter carries that instruction out as it always has, errors
included. Nothing has to be right twice.

Under the official Lean toolchain no code is ever run this way (see
`Fast.codeLoad`), so there the interpreter does everything; the tests
compare the two.

## What the translated code is given

The interpreter's registers are an array of 64-bit words, and the
translated code works on that same array, extended (`cpu` below):

    0-10    the registers r0 to r10
    11      the instruction to run next
    12      instructions counted so far
    13      the budget
    14      how many of the program's own calls are in progress
    15      scratch
    16-70   where each of the five 4 GiB regions of the address space is
    72-     the saved registers of each call in progress, six words each

and on the program's memory (stack, heap, input: one byte array) and its
file (the read-only region).

## Registers

    r0-r9   rbx rdi rsi rcx r8 r9 r10 r11 r12 r13
    r10     kept in `cpu`; r14 holds the machine address it stands for
    r15     instructions counted
    rbp     `cpu`
    rax rdx scratch

r10 is the frame pointer, which programs cannot write: it always points one
frame (4096 bytes) above the bottom of the current function's frame. A load
or store at `r10 − 8` therefore needs no check and is one `mov` relative to
r14. Every other access is checked against the tables in `cpu`.

## Counting

Instructions are counted a block at a time. A block is a run of
instructions entered only at its top; before running it the code adds its
length to the count and checks the budget. If the block cannot be finished
within the budget it is not started: the interpreter runs it, one
instruction at a time, to the exact point where the budget ends.
-/

namespace Sbpf

-- The virtual address space of a program.
def programStart : UInt64 := 0x100000000
def stackStart : UInt64 := 0x200000000
def inputStart : UInt64 := 0x400000000
def frameBytes : Nat := 4096
def maxDepth : Nat := 64
def stackBytes : Nat := 262144

end Sbpf

namespace Jit

-- ------------------------------------------------------------ the layout of `cpu`

def cPc : Nat := 11
def cUnits : Nat := 12
def cBudget : Nat := 13
def cCalls : Nat := 14
def cTemp : Nat := 15
/-- For each region 0-4: the first offset inside it that is mapped. -/
def cLow : Nat := 16
/-- For each region: the machine address of that first offset (filled in by the code itself on entry). -/
def cBase : Nat := 21
/-- For each width (1, 2, 4, 8 bytes) and region: how many offsets from `cLow` on can be read at that width. -/
def cRead : Nat := 26
/-- The same for writing. -/
def cWrite : Nat := 46
/-- For each region: where its first mapped byte is inside the array that holds it. -/
def cOffset : Nat := 66
def cFrames : Nat := 72
def cpuWords : Nat := cFrames + 6 * Sbpf.maxDepth

-- ------------------------------------------------------------ x86-64, as much of it as is needed

def rax : UInt64 := 0
def rcx : UInt64 := 1
def rdx : UInt64 := 2
def rbx : UInt64 := 3
def rbp : UInt64 := 5
def rsi : UInt64 := 6
def rdi : UInt64 := 7
def r14 : UInt64 := 14
def r15 : UInt64 := 15

/-- The machine register that holds sBPF register `g` (0-9). -/
def hostOf (g : UInt64) : UInt64 :=
  if g >= 4 then g + 4 else if g == 0 then 3 else if g == 1 then 7 else if g == 2 then 6 else 1

/-- What comes before the opcode: the operand-size prefix and REX. `w` is the width of the operation:
0 = 32 bits, 1 = 64, 2 = 16, 3 = 8 (which always takes a REX, so that registers 4-7 mean their low bytes). -/
def lead (b : ByteArray) (w reg index base : UInt64) : ByteArray :=
  let b := if w == 2 then b.push 0x66 else b
  let wide : UInt64 := if w == 1 then 0x48 else 0x40
  let rex := wide ||| ((reg >>> 3) <<< 2) ||| ((index >>> 3) <<< 1) ||| (base >>> 3)
  if rex != 0x40 || w == 3 then b.push rex.toUInt8 else b

/-- An opcode: one byte, or 0F and a byte if `op` is 0x100 or more. -/
def opcode (b : ByteArray) (op : UInt64) : ByteArray :=
  if op >= 0x100 then (b.push 0x0F).push (op &&& 0xFF).toUInt8 else b.push op.toUInt8

/-- `op reg, rm` on two registers. -/
def rr (b : ByteArray) (w op reg rm : UInt64) : ByteArray :=
  (opcode (lead b w reg 0 rm) op).push (((reg &&& 7) <<< 3) ||| (rm &&& 7) ||| 0xC0).toUInt8

/-- `op reg, [base + disp]`. -/
def rm (b : ByteArray) (w op reg base disp : UInt64) : ByteArray :=
  let b := opcode (lead b w reg 0 base) op
  let r := (reg &&& 7) <<< 3
  let low := base &&& 7
  let mode : UInt64 := if disp == 0 && low != 5 then 0 else if disp + 128 < 256 then 0x40 else 0x80
  let b := b.push (mode ||| r ||| low).toUInt8
  let b := if low == 4 then b.push 0x24 else b
  if mode == 0x40 then b.push disp.toUInt8 else if mode == 0x80 then Fast.push32 b disp else b

/-- `op reg, [base + index * 2^scale + disp]`, the displacement always four bytes. -/
def rx (b : ByteArray) (w op reg base index scale disp : UInt64) : ByteArray :=
  let b := opcode (lead b w reg index base) op
  let b := b.push (((reg &&& 7) <<< 3) ||| 0x84).toUInt8
  let b := b.push ((scale <<< 6) ||| ((index &&& 7) <<< 3) ||| (base &&& 7)).toUInt8
  Fast.push32 b disp

/-- Add (0), or (1), and (4), subtract (5), exclusive or (6), compare (7) a constant to a register. -/
def ri (b : ByteArray) (w ext reg imm : UInt64) : ByteArray :=
  if imm + 128 < 256 then (rr b w 0x83 ext reg).push imm.toUInt8
  else Fast.push32 (rr b w 0x81 ext reg) imm

/-- Loads a 64-bit constant in the shortest way. -/
def loadConstant (b : ByteArray) (reg value : UInt64) : ByteArray :=
  if value < 0x100000000 then
    Fast.push32 ((lead b 0 0 0 reg).push (0xB8 ||| (reg &&& 7)).toUInt8) value
  else if value >= 0xFFFFFFFF80000000 then
    Fast.push32 (rr b 1 0xC7 0 reg) value
  else
    Fast.push64 ((lead b 1 0 0 reg).push (0xB8 ||| (reg &&& 7)).toUInt8) value

/-- A shift by the count in any register (BMI2): 0 = left, 1 = right, 2 = right keeping the sign. -/
def shiftBy (b : ByteArray) (w which dst src count : UInt64) : ByteArray :=
  let pp : UInt64 := if which == 0 then 1 else if which == 1 then 3 else 2
  let b := b.push 0xC4
  let b := b.push ((((dst >>> 3) ^^^ 1) <<< 7) ||| (((src >>> 3) ^^^ 1) <<< 5) ||| 0x42).toUInt8
  let b := b.push ((w <<< 7) ||| ((count ^^^ 15) <<< 3) ||| pp).toUInt8
  (b.push 0xF7).push (((dst &&& 7) <<< 3) ||| (src &&& 7) ||| 0xC0).toUInt8

/-- A jump on condition `cc` whose target is not known yet; the four bytes to fill in are the last four. -/
def jumpIf (b : ByteArray) (cc : UInt64) : ByteArray :=
  Fast.push32 ((b.push 0x0F).push (0x80 ||| cc).toUInt8) 0

def jump (b : ByteArray) : ByteArray := Fast.push32 (b.push 0xE9) 0

/-- Makes the jump whose last four bytes are at `site` go to `target`. -/
def aim (b : ByteArray) (site target : Nat) : ByteArray :=
  Fast.put32 b site (target.toUInt64 - (site.toUInt64 + 4))

def jumpTo (b : ByteArray) (target : Nat) : ByteArray :=
  let b := jump b
  aim b (b.size - 4) target

-- the conditions
def ccB : UInt64 := 2
def ccAE : UInt64 := 3
def ccE : UInt64 := 4
def ccNE : UInt64 := 5
def ccBE : UInt64 := 6
def ccA : UInt64 := 7
def ccL : UInt64 := 12
def ccGE : UInt64 := 13
def ccLE : UInt64 := 14
def ccG : UInt64 := 15

/-- A word of `cpu`, as a displacement from rbp. -/
@[inline] def slot (i : Nat) : UInt64 := (8 * i).toUInt64

-- ------------------------------------------------------------ what can be translated

@[inline] def sext32 (x : UInt64) : UInt64 := ((x &&& 0xFFFFFFFF) ^^^ 0x80000000) - 0x80000000
@[inline] def sext16 (x : UInt64) : UInt64 := ((x &&& 0xFFFF) ^^^ 0x8000) - 0x8000

/-- No instruction writes r10. (The rule that makes a frame access checkable when the program is
translated rather than when it runs. Every program a validator accepts keeps it.) -/
def frameSafe (code : Array UInt64) : Bool := Id.run do
  for word in code do
    let cls := word &&& 7
    if (cls == 7 || cls == 4 || cls == 1 || word &&& 0xFF == 0x18) && (word >>> 8) &&& 15 == 10 then
      return false
  return true

/-- Where the call instruction `word` at `pc` goes, for a call that names its target. -/
def callTarget (word : UInt64) (pc : Nat) (call : UInt64) (v3 : Bool) : UInt64 :=
  if !v3 && call != 0 then call - 1 else (pc + 1).toUInt64 + sext32 (word >>> 32)

/-- How the instruction `word` at `pc` is handled: 0 = translated, 1 = translated, and the last of its
block (a jump, a call, a return), 2 = left to the interpreter. `syscall` and `call` are the program's
notes about a call instruction at `pc`. -/
def classOf (word : UInt64) (pc count : Nat) (syscall call : UInt64) (v3 : Bool) : UInt64 :=
  let opc := word &&& 0xFF
  let cls := opc &&& 7
  let op := opc &&& 0xF0
  let d := (word >>> 8) &&& 15
  let s := (word >>> 12) &&& 15
  let named := word &&& 8 != 0
  let imm32 := word >>> 32
  if cls == 7 || cls == 4 then
    if op == 0xd0 then (if cls == 4 && (imm32 == 16 || imm32 == 32 || imm32 == 64) then 0 else 2)
    else if op > 0xd0 then 2
    else if op == 0x30 || op == 0x90 then (if named then (if s == 10 then 2 else 0) else if imm32 == 0 then 2 else 0)
    else 0
  else if cls == 1 || cls == 2 || cls == 3 then
    if word &&& 0xe0 != 0x60 then 2 else if cls == 3 && s == 10 then 2 else 0
  else if cls == 5 then
    if opc == 0x05 || opc == 0x95 then 1
    else if opc == 0x8d then (if (if v3 then d else imm32 &&& 15) > 9 then 2 else 1)
    else if opc == 0x85 then
      if syscall != 0 || (v3 && s != 1) then 2
      else if callTarget word pc call v3 >= count.toUInt64 then 2
      else 1
    else if op == 0 || op == 0x80 || op == 0x90 || op > 0xd0 then 2
    else if d == 10 then 2
    else 1
  else if opc == 0x18 then (if pc + 1 < count then 0 else 2)
  else 2

/-- Where a jump instruction at `pc` goes when it is taken. -/
@[inline] def jumpTarget (word : UInt64) (pc : Nat) : UInt64 :=
  (pc + 1).toUInt64 + sext16 (word >>> 16)

/-- How each instruction is handled (`classOf`, and 3 for the second half of a two-slot constant), and
which instructions begin a block. -/
def survey (code syscalls calls : Array UInt64) (count entry : Nat) (v3 : Bool) : ByteArray × ByteArray := Id.run do
  let mut kind := Fast.zeroed (count + 1) (count + 1)
  let mut pc := 0
  while pc < count do
    let word := code[pc]!
    let k := classOf word pc count syscalls[pc]! calls[pc]! v3
    kind := kind.set! pc k.toUInt8
    if word &&& 0xFF == 0x18 && k == 0 then
      kind := kind.set! (pc + 1) 3
      pc := pc + 2
    else
      pc := pc + 1
  let mut starts := Fast.zeroed (count + 1) (count + 1)
  starts := starts.set! 0 1
  if entry < count then
    starts := starts.set! entry 1
  for at_ in [0:count] do
    let k := kind[at_]!
    if k == 1 || k == 2 then
      starts := starts.set! (at_ + 1) 1
    if k == 2 then
      starts := starts.set! at_ 1
    if k == 1 then
      let word := code[at_]!
      let opc := word &&& 0xFF
      if opc == 0x85 then
        starts := starts.set! (callTarget word at_ calls[at_]! v3).toNat 1
      else if opc != 0x95 && opc != 0x8d then
        let target := jumpTarget word at_
        if target < count.toUInt64 then
          starts := starts.set! target.toNat 1
  -- nothing begins in the second half of a constant
  for at_ in [0:count] do
    if kind[at_]! == 3 then
      starts := starts.set! at_ 0
  return (kind, starts)

/-- How many instructions the block that begins at `pc` runs. -/
def blockLength (kind starts : ByteArray) (count pc : Nat) : Nat := Id.run do
  let mut n := 0
  let mut q := pc
  while q < count do
    let k := kind[q]!
    if k == 3 then
      q := q + 1
      continue
    if (q != pc && starts[q]! != 0) || k == 2 then
      break
    n := n + 1
    if k == 1 then
      break
    q := q + 1
  return n

-- ------------------------------------------------------------ pieces of code

/-- Leaves in rax the machine address of the bytes at sBPF address `base + off` (`base` a register,
10 included), having checked that `2^width` of them can be read (or written). The two jumps taken when they
cannot are at `faultA` and `faultB` bytes before the end of what is emitted. -/
def address (b : ByteArray) (base off width : UInt64) (write : Bool) : ByteArray :=
  let b := if base == 10 then rm b 1 0x8B rax rbp (slot 10) else b
  let from_ := if base == 10 then rax else hostOf base
  let b := if off == 0 then (if base == 10 then b else rr b 1 0x89 from_ rax) else rm b 1 0x8D rax from_ off
  let b := rr b 1 0x89 rax rdx                                  -- mov rdx, rax
  let b := (rr b 1 0xC1 5 rdx).push 32                          -- shr rdx, 32: the region
  let b := (rr b 1 0x83 7 rdx).push 4                           -- cmp rdx, 4
  let b := jumpIf b ccA
  let b := rr b 0 0x89 rax rax                                  -- mov eax, eax: the offset in the region
  let b := rx b 1 0x2B rax rbp rdx 3 (slot cLow)                -- sub rax, [low]
  let b := rx b 1 0x3B rax rbp rdx 3 (slot ((if write then cWrite else cRead) + 5 * width.toNat))
  let b := jumpIf b ccAE
  rx b 1 0x03 rax rbp rdx 3 (slot cBase)                        -- add rax, [base]

def faultA : Nat := 36
def faultB : Nat := 12

/-- With the number of calls in progress in rax (and room for one more): saves r6-r9, the frame pointer
and the instruction to return to, and moves up one frame. -/
def pushFrame (b : ByteArray) (next : UInt64) : ByteArray := Id.run do
  let mut b := b
  b := (rr b 1 0xFF 0 rax)                                       -- inc rax
  b := rm b 1 0x89 rax rbp (slot cCalls)
  b := (((b.push 0x48).push 0x8D).push 0x14).push 0x40           -- lea rdx, [rax + rax*2]
  b := (rr b 1 0xC1 4 rdx).push 4                                -- shl rdx, 4: 48 bytes a frame
  let at_ := slot cFrames - 48
  for i in [0:4] do
    b := rx b 1 0x89 (hostOf (6 + i.toUInt64)) rbp rdx 0 (at_ + 8 * i.toUInt64)
  b := rm b 1 0x8B rax rbp (slot 10)
  b := rx b 1 0x89 rax rbp rdx 0 (at_ + 32)
  b := Fast.push32 (rx b 1 0xC7 0 rbp rdx 0 (at_ + 40)) next
  b := Fast.push32 (rr b 1 0x81 0 rax) Sbpf.frameBytes.toUInt64  -- add rax, 4096
  b := rm b 1 0x89 rax rbp (slot 10)
  b := Fast.push32 (rr b 1 0x81 0 r14) Sbpf.frameBytes.toUInt64
  return b

-- ------------------------------------------------------------ the translation

/-- Translates a program. Returns the machine code and, for each instruction, whether the code can be
entered there; or two empty arrays if this program is left to the interpreter altogether.

The code is entered at its first byte with rdi = `cpu`, rsi = the memory, rdx = the program's file, and
returns with `cpu[cPc]` naming the instruction the interpreter is to carry out next. -/
def compile (code syscalls calls : Array UInt64) (count entry : Nat) (v3 : Bool) (textAddr roRegion : UInt64)
    : ByteArray × ByteArray := Id.run do
  if count == 0 || count > 0x1000000 || syscalls.size < count || calls.size < count || !(frameSafe code) then
    return (ByteArray.empty, ByteArray.empty)
  let (kind, starts0) := survey code syscalls calls count entry v3
  let mut starts := starts0
  let mut b := ByteArray.emptyWithCapacity (count * 24 + 4096)

  -- Entry: keep the caller's registers, find the regions, load the program's registers.
  b := (b.push 0x53).push 0x55
  for r in [12:16] do
    b := (b.push 0x41).push (0x50 + r - 8).toUInt8
  b := rr b 1 0x89 rdi rbp
  for r in [0:5] do
    b := rm b 1 0x8B rax rbp (slot (cOffset + r))
    b := rr b 1 0x01 (if r.toUInt64 == roRegion then rdx else rsi) rax
    b := rm b 1 0x89 rax rbp (slot (cBase + r))
  b := rm b 1 0x8B r14 rbp (slot 10)
  b := loadConstant b rax Sbpf.stackStart
  b := rr b 1 0x29 rax r14
  b := rm b 1 0x03 r14 rbp (slot (cBase + 2))
  for g in [0:10] do
    b := rm b 1 0x8B (hostOf g.toUInt64) rbp (slot g)
  b := rm b 1 0x8B r15 rbp (slot cUnits)
  b := rm b 1 0x8B rax rbp (slot cPc)
  -- Dispatch: go to the block that begins at the instruction in rax, or back to the interpreter if no
  -- block begins there.
  let dispatch := b.size
  b := rm b 1 0x89 rax rbp (slot cPc)
  b := Fast.push32 (((b.push 0x48).push 0x8D).push 0x15) 0      -- lea rdx, [rip + table]
  let tableSite := b.size - 4
  b := ((b.push 0x8B).push 0x04).push 0x82                      -- mov eax, [rdx + rax*4]
  b := rr b 0 0x85 rax rax
  b := jumpIf b ccE
  let noBlock := b.size - 4
  b := rr b 1 0x01 rdx rax
  b := (b.push 0xFF).push 0xE0                                  -- jmp rax
  -- Leave: put the program's registers back in `cpu`.
  let leave := b.size
  b := aim b noBlock leave
  for g in [0:10] do
    b := rm b 1 0x89 (hostOf g.toUInt64) rbp (slot g)
  b := rm b 1 0x89 r15 rbp (slot cUnits)
  for r in [0:4] do
    b := (b.push 0x41).push (0x5F - r).toUInt8
  b := ((b.push 0x5D).push 0x5B).push 0xC3
  while b.size % 4 != 0 do
    b := b.push 0x90
  -- The table: for each instruction, how far past the table its block begins (0: none begins there).
  let table := b.size
  b := aim b tableSite table
  b := Fast.pushZeros b (4 * (count + 1))

  -- where the code for each instruction that begins a block is (jumps go there)
  let mut placed : Array UInt64 := Array.replicate (count + 1) 0
  -- jumps to fill in when everything is placed: (site, target instruction)
  let mut jumps : Array UInt64 := Array.emptyWithCapacity 1024
  -- ways out for an instruction that cannot be carried out here: (site, site or 0, instruction, how many
  -- instructions of its block were counted and not run)
  let mut faults : Array UInt64 := Array.emptyWithCapacity 1024
  -- jumps to instructions that do not exist: (site, instruction)
  let mut strays : Array UInt64 := Array.emptyWithCapacity 16
  let mut pc := 0
  let mut ran := 0       -- instructions of the current block already translated
  let mut length := 0     -- how many the block has
  let mut open_ := false
  while pc < count do
    let k := kind[pc]!
    if k == 3 then
      pc := pc + 1
      continue
    if starts[pc]! != 0 || !open_ then
      placed := placed.set! pc b.size.toUInt64
      if k == 2 then
        -- the interpreter's: say which instruction and leave
        starts := starts.set! pc 0
        b := Fast.push32 (rm b 1 0xC7 0 rbp (slot cPc)) pc.toUInt64
        b := jumpTo b leave
        open_ := false
        pc := pc + 1
        continue
      starts := starts.set! pc 1
      b := Fast.put32 b (table + 4 * pc) (b.size - table).toUInt64
      length := blockLength kind starts count pc
      ran := 0
      open_ := true
      b := ri b 1 0 r15 length.toUInt64
      b := rm b 1 0x3B r15 rbp (slot cBudget)
      b := jumpIf b ccA
      faults := (((faults.push (b.size - 4).toUInt64).push 0).push pc.toUInt64).push length.toUInt64
    let word := code[pc]!
    let opc := word &&& 0xFF
    let cls := opc &&& 7
    let op := opc &&& 0xF0
    let d := (word >>> 8) &&& 15
    let s := (word >>> 12) &&& 15
    let named := word &&& 8 != 0
    let off := sext16 (word >>> 16)
    let imm32 := word >>> 32
    let imm := sext32 imm32
    let uncounted := (length - ran).toUInt64
    let mut step := 1
    if cls == 7 || cls == 4 then
      let w : UInt64 := if cls == 7 then 1 else 0
      let dh := hostOf d
      -- the second operand, if it is a register: r10 is fetched into rax
      if named && s == 10 then
        b := rm b 1 0x8B rax rbp (slot 10)
      let sh := if s == 10 then rax else hostOf s
      if op == 0x00 || op == 0x10 || op == 0x40 || op == 0x50 || op == 0xa0 then
        let ext : UInt64 := if op == 0x00 then 0 else if op == 0x10 then 5 else if op == 0x40 then 1 else if op == 0x50 then 4 else 6
        b := if named then rr b w (ext * 8 + 1) sh dh else ri b w ext dh imm
        if w == 0 && (op == 0x00 || op == 0x10) then
          b := rr b 1 0x63 dh dh                                -- the 32-bit sum, sign-extended
      else if op == 0x20 then
        b := if named then rr b w 0x1AF dh sh else Fast.push32 (rr b w 0x69 dh dh) imm
        if w == 0 then
          b := rr b 1 0x63 dh dh
      else if op == 0x30 || op == 0x90 then
        if named then
          b := rr b w 0x85 sh sh
          b := jumpIf b ccE
          faults := (((faults.push (b.size - 4).toUInt64).push 0).push pc.toUInt64).push uncounted
        else
          b := Fast.push32 (rm b w 0xC7 0 rbp (slot cTemp)) imm
        b := rr b w 0x89 dh rax
        b := rr b 0 0x31 rdx rdx
        b := if named then rr b w 0xF7 6 sh else rm b w 0xF7 6 rbp (slot cTemp)
        b := rr b w 0x89 (if op == 0x30 then rax else rdx) dh
      else if op == 0x60 || op == 0x70 || op == 0xc0 then
        let which : UInt64 := if op == 0x60 then 0 else if op == 0x70 then 1 else 2
        if named then
          b := shiftBy b w which dh dh sh
        else
          let n := imm &&& (if w == 1 then 63 else 31)
          if n == 0 then
            b := if w == 0 then rr b 0 0x89 dh dh else b
          else
            b := (rr b w 0xC1 (if which == 0 then 4 else if which == 1 then 5 else 7) dh).push n.toUInt8
      else if op == 0x80 then
        b := rr b w 0xF7 3 dh
      else if op == 0xb0 then
        if named then
          b := if s == 10 then rr b w 0x89 rax dh else rr b w 0x89 sh dh
        else
          b := loadConstant b dh (if w == 1 then imm else imm32)
      else
        -- byte order: the low 2, 4 or 8 bytes, reversed if `named`
        if imm32 == 16 then
          if named then
            b := (rr b 2 0xC1 0 dh).push 8                      -- rol r16, 8
          b := rr b 0 0x1B7 dh dh                               -- movzx r32, r16
        else if imm32 == 32 then
          b := if named then ((lead b 0 0 0 dh).push 0x0F).push (0xC8 ||| (dh &&& 7)).toUInt8 else rr b 0 0x89 dh dh
        else if named then
          b := ((lead b 1 0 0 dh).push 0x0F).push (0xC8 ||| (dh &&& 7)).toUInt8
    else if cls == 1 || cls == 2 || cls == 3 then
      let width := word &&& 0x18
      let size : UInt64 := if width == 0x00 then 4 else if width == 0x08 then 2 else if width == 0x10 then 1 else 8
      let log : UInt64 := if size == 1 then 0 else if size == 2 then 1 else if size == 4 then 2 else 3
      let base := if cls == 1 then s else d
      -- inside the current frame: no check needed
      let framed := base == 10 && off + 4096 <= 4096 - size
      let at_ := if framed then r14 else rax
      let disp := if framed then off else 0
      if !framed then
        b := address b base off log (cls != 1)
        faults := (((faults.push (b.size - faultA).toUInt64).push (b.size - faultB).toUInt64).push pc.toUInt64).push uncounted
      if cls == 1 then
        let dh := hostOf d
        b := if size == 8 then rm b 1 0x8B dh at_ disp else if size == 4 then rm b 0 0x8B dh at_ disp
          else if size == 2 then rm b 0 0x1B7 dh at_ disp else rm b 0 0x1B6 dh at_ disp
      else if cls == 3 then
        let sh := hostOf s
        b := if size == 8 then rm b 1 0x89 sh at_ disp else if size == 4 then rm b 0 0x89 sh at_ disp
          else if size == 2 then rm b 2 0x89 sh at_ disp else rm b 3 0x88 sh at_ disp
      else
        b := if size == 8 then Fast.push32 (rm b 1 0xC7 0 at_ disp) imm
          else if size == 4 then Fast.push32 (rm b 0 0xC7 0 at_ disp) imm
          else if size == 2 then Fast.push16 (rm b 2 0xC7 0 at_ disp) imm
          else (rm b 3 0xC6 0 at_ disp).push imm.toUInt8
    else if cls == 5 then
      if opc == 0x05 then
        let target := jumpTarget word pc
        b := jump b
        if target < count.toUInt64 && kind[target.toNat]! != 3 then
          jumps := (jumps.push (b.size - 4).toUInt64).push target
        else
          strays := (strays.push (b.size - 4).toUInt64).push target
      else if opc == 0x95 then
        -- return to the caller inside the program (the end of the program is the interpreter's)
        b := rm b 1 0x8B rax rbp (slot cCalls)
        b := rr b 1 0x85 rax rax
        b := jumpIf b ccE
        faults := (((faults.push (b.size - 4).toUInt64).push 0).push pc.toUInt64).push uncounted
        b := rr b 1 0xFF 1 rax                                  -- dec rax
        b := rm b 1 0x89 rax rbp (slot cCalls)
        b := (((b.push 0x48).push 0x8D).push 0x14).push 0x40    -- lea rdx, [rax + rax*2]
        b := (rr b 1 0xC1 4 rdx).push 4
        for i in [0:4] do
          b := rx b 1 0x8B (hostOf (6 + i.toUInt64)) rbp rdx 0 (slot cFrames + 8 * i.toUInt64)
        b := rx b 1 0x8B rax rbp rdx 0 (slot cFrames + 32)
        b := rm b 1 0x89 rax rbp (slot 10)
        b := Fast.push32 (rr b 1 0x81 5 r14) Sbpf.frameBytes.toUInt64
        b := rx b 1 0x8B rax rbp rdx 0 (slot cFrames + 40)
        b := jumpTo b dispatch
      else if opc == 0x85 || opc == 0x8d then
        if opc == 0x8d then
          -- through a register: the instruction it points at, which must exist
          b := rr b 1 0x89 (hostOf (if v3 then d else imm32 &&& 15)) rax
          b := loadConstant b rdx textAddr
          b := rr b 1 0x29 rdx rax
          b := (rr b 1 0xC1 5 rax).push 3
          b := Fast.push32 (rr b 1 0x81 7 rax) count.toUInt64
          b := jumpIf b ccAE
          faults := (((faults.push (b.size - 4).toUInt64).push 0).push pc.toUInt64).push uncounted
          b := rm b 1 0x89 rax rbp (slot cTemp)
        b := rm b 1 0x8B rax rbp (slot cCalls)
        b := (rr b 1 0x83 7 rax).push (Sbpf.maxDepth - 1).toUInt8
        b := jumpIf b ccAE
        faults := (((faults.push (b.size - 4).toUInt64).push 0).push pc.toUInt64).push uncounted
        b := pushFrame b (pc + 1).toUInt64
        if opc == 0x8d then
          b := rm b 1 0x8B rax rbp (slot cTemp)
          b := jumpTo b dispatch
        else
          let target := callTarget word pc calls[pc]! v3
          b := jump b
          if kind[target.toNat]! != 3 then
            jumps := (jumps.push (b.size - 4).toUInt64).push target
          else
            strays := (strays.push (b.size - 4).toUInt64).push target
      else
        -- a conditional jump
        let dh := hostOf d
        if named && s == 10 then
          b := rm b 1 0x8B rax rbp (slot 10)
        let sh := if s == 10 then rax else hostOf s
        if op == 0x40 then
          b := if named then rr b 1 0x85 sh dh else Fast.push32 (rr b 1 0xF7 0 dh) imm
        else
          b := if named then rr b 1 0x39 sh dh else ri b 1 7 dh imm
        let cc := if op == 0x10 then ccE else if op == 0x20 then ccA else if op == 0x30 then ccAE
          else if op == 0x40 || op == 0x50 then ccNE else if op == 0x60 then ccG else if op == 0x70 then ccGE
          else if op == 0xa0 then ccB else if op == 0xb0 then ccBE else if op == 0xc0 then ccL else ccLE
        let target := jumpTarget word pc
        b := jumpIf b cc
        if target < count.toUInt64 && kind[target.toNat]! != 3 then
          jumps := (jumps.push (b.size - 4).toUInt64).push target
        else
          strays := (strays.push (b.size - 4).toUInt64).push target
    else
      -- a 64-bit constant, in two slots
      b := loadConstant b (hostOf d) (imm32 ||| ((code[pc + 1]! >>> 32) <<< 32))
      step := 2
    ran := ran + 1
    if k == 1 then
      open_ := false
    pc := pc + step
  -- past the last instruction
  placed := placed.set! count b.size.toUInt64
  b := Fast.push32 (rm b 1 0xC7 0 rbp (slot cPc)) count.toUInt64
  b := jumpTo b leave
  for i in [0:jumps.size / 2] do
    b := aim b jumps[2 * i]!.toNat placed[jumps[2 * i + 1]!.toNat]!.toNat
  -- the ways out: uncount what was not run, name the instruction, leave
  for i in [0:faults.size / 4] do
    b := aim b faults[4 * i]!.toNat b.size
    if faults[4 * i + 1]! != 0 then
      b := aim b faults[4 * i + 1]!.toNat b.size
    b := ri b 1 5 r15 faults[4 * i + 3]!
    b := Fast.push32 (rm b 1 0xC7 0 rbp (slot cPc)) faults[4 * i + 2]!
    b := jumpTo b leave
  for i in [0:strays.size / 2] do
    b := aim b strays[2 * i]!.toNat b.size
    b := loadConstant b rax strays[2 * i + 1]!
    b := rm b 1 0x89 rax rbp (slot cPc)
    b := jumpTo b leave
  return (b, starts.set! count 0)

/-- Fills in the parts of `cpu` that say where the program's memory is: the stack (region 2), the heap
(3) and the input (4) in the memory array one after another, and the read-only part of the program's
file. `roLow`, `roHigh`, `roFile` as in `Sbpf.Program`. -/
def prepare (cpu0 : Array UInt64) (budget : UInt64) (heap inputLen : Nat) (roRegion : UInt64)
    (roLow roHigh roFile : Nat) : Array UInt64 := Id.run do
  let mut cpu := cpu0.set! cBudget budget
  let ro := roRegion.toNat
  for r in [0:5] do
    let size := if r == 2 then Sbpf.stackBytes else if r == 3 then heap else if r == 4 then inputLen
      else if r == ro && roHigh > roLow then roHigh - roLow else 0
    let writable := r >= 2
    cpu := cpu.set! (cLow + r) (if r == ro then roLow.toUInt64 else 0)
    cpu := cpu.set! (cOffset + r) (if r == 2 then 0 else if r == 3 then Sbpf.stackBytes.toUInt64
      else if r == 4 then (Sbpf.stackBytes + heap).toUInt64 else if r == ro then roFile.toUInt64 else 0)
    for width in [0:4] do
      let bytes := if width == 0 then 1 else if width == 1 then 2 else if width == 2 then 4 else 8
      let reach := if size >= bytes then (size - bytes + 1).toUInt64 else 0
      cpu := cpu.set! (cRead + 5 * width + r) reach
      cpu := cpu.set! (cWrite + 5 * width + r) (if writable then reach else 0)
  return cpu

end Jit
