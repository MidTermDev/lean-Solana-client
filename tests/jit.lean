import Solana.Sbpf
import Encoding.Hex

/-! Programs as machine code (`Solana.Jit`) against the interpreter.

Compiled by leanc, a program is translated into x86-64 code when it is
loaded and run that way; under the official toolchain nothing is, and the
interpreter does everything. So the expected output of this test, which
the official toolchain wrote, is what the interpreter makes of 1,500 random
programs, and leanc's output is what the machine code makes of them: equal
files mean the two agree. (Each program is also run both ways here, and
compared.)

The programs are random but not shapeless: arithmetic of every kind and
width, loads and stores in the frame, the heap, the account's data, the
program's own file and nowhere at all, jumps forward and (rarely) back,
calls into the middle of things, returns, and now and then an instruction
that does not exist. They end by writing their registers and some memory
into an account, so that what a program computed is seen, not only whether
it finished. -/

def wrap (code : ByteArray) : ByteArray := Id.run do
  let names := Hex.decode "002e74657874002e736873747274616200"   -- "", ".text", ".shstrtab"
  let table := 64 + code.size + 24
  let mut f := Sbpf.zeros ByteArray.empty (table + 192)
  f := (Hex.decode "7f454c46020101").copySlice 0 f 0 7
  f := Sbpf.storeAt f 16 2 3
  f := Sbpf.storeAt f 18 2 247
  f := Sbpf.storeAt f 24 8 64
  f := Sbpf.storeAt f 40 8 table.toUInt64
  f := Sbpf.storeAt f 60 2 3
  f := Sbpf.storeAt f 62 2 2
  f := code.copySlice 0 f 64 code.size
  f := names.copySlice 0 f (64 + code.size) names.size
  f := Sbpf.storeAt f (table + 64) 4 1
  f := Sbpf.storeAt f (table + 64 + 16) 8 64
  f := Sbpf.storeAt f (table + 64 + 24) 8 64
  f := Sbpf.storeAt f (table + 64 + 32) 8 code.size.toUInt64
  f := Sbpf.storeAt f (table + 128) 4 7
  f := Sbpf.storeAt f (table + 128 + 24) 8 (64 + code.size).toUInt64
  f := Sbpf.storeAt f (table + 128 + 32) 8 names.size.toUInt64
  return f

/-- One instruction: opcode, registers, 16-bit offset, 32-bit constant. -/
def ins (b : ByteArray) (opc dst src off imm : UInt64) : ByteArray :=
  Fast.push32 (Fast.push16 ((b.push opc.toUInt8).push ((src <<< 4) ||| dst).toUInt8) off) imm

/-- A 64-bit constant into a register: two slots. -/
def wideConstant (b : ByteArray) (dst v : UInt64) : ByteArray :=
  ins (ins b 0x18 dst 0 0 v) 0 0 0 0 (v >>> 32)

def step (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def aluOps : Array UInt64 := #[0x00, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xa0, 0xb0, 0xc0, 0xd0, 0x00, 0xb0]
def jumpOps : Array UInt64 := #[0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0xa0, 0xb0, 0xc0, 0xd0]
def constants : Array UInt64 := #[0, 1, 2, 7, 31, 32, 63, 64, 0xFFFFFFFF, 0x80000000, 0x7FFFFFFF, 0xFFFF, 1000, 0xFFFFFFF8, 3, 0xDEADBEEF]
def strange : Array UInt64 := #[0x06, 0xe7, 0x8c, 0x0d, 0xd7, 0x9d, 0x00, 0x61]

/-- Where the account's data, the heap and the program's code are. -/
def dataAddress : UInt64 := Sbpf.inputStart + 96
def heapAddress : UInt64 := 0x300000000
def codeAddress : UInt64 := Sbpf.programStart + 64

/-- A program of about `n` random instructions, from `seed`. r8 and r9 point at the heap and at the
account's data and are never changed, r7 points somewhere that can usually be read, r0-r6 are fair game. -/
def randomProgram (seed : UInt64) (n : Nat) : ByteArray := Id.run do
  let mut s := step (seed + 1)
  let mut b := ByteArray.emptyWithCapacity 4096
  b := wideConstant b 9 dataAddress
  b := wideConstant b 8 heapAddress
  for g in [3:7] do
    s := step s
    b := wideConstant b g.toUInt64 (s ^^^ (s >>> 29))
  b := ins b 0xbf 7 9 0 0
  for _ in [0:n] do
    s := step s
    let r := s >>> 11
    let choice := r % 100
    let dst := (r >>> 8) % 7
    let src := (r >>> 12) % 11
    let named := (r >>> 16) &&& 1
    let imm := if (r >>> 17) &&& 1 == 0 then constants[((r >>> 18) % 16).toNat]! else (s >>> 7) &&& 0xFFFFFFFF
    let pick := r >>> 24
    if choice < 40 then
      let op := aluOps[(pick % 16).toNat]!
      if op == 0xd0 then
        b := ins b ((named <<< 3) ||| 0xd4) dst 0 0 (if pick % 9 == 0 then 7 else if (pick >>> 4) % 3 == 0 then 16 else if (pick >>> 4) % 3 == 1 then 32 else 64)
      else
        b := ins b (op ||| (named <<< 3) ||| (if (pick >>> 4) &&& 1 == 0 then 7 else 4)) dst src 0 imm
    else if choice < 62 then
      let cls := 1 + pick % 3
      let width := ((pick >>> 2) % 4) <<< 3
      let wherever := (pick >>> 4) % 16
      -- r7 is a pointer that moves about (see below); once in a long while, the base is any register at all
      let base : UInt64 := if wherever < 6 then 10 else if wherever < 10 then 9 else if wherever < 12 then 8
        else if wherever < 15 || (pick >>> 20) % 6 != 0 then 7 else (pick >>> 8) % 10
      let far := pick >>> 8
      let off : UInt64 := if base == 10 then 0 - 8 * (1 + far % 70) else if base == 7 then far % 64 else far % 1500
      if cls == 1 then
        b := ins b (0x61 ||| width) dst base off 0
      else if cls == 2 then
        b := ins b (0x62 ||| width) base 0 off imm
      else
        b := ins b (0x63 ||| width) base src off 0
    else if choice < 80 then
      let op := jumpOps[(pick % 11).toNat]!
      let far := pick >>> 9
      let off : UInt64 := if (pick >>> 4) % 24 == 0 then 0 - (1 + far % 6) else far % 7
      b := ins b (op ||| (named <<< 3) ||| 5) (if (pick >>> 12) % 40 == 0 then 10 else dst) src off imm
    else if choice < 83 then
      b := wideConstant b dst (s ^^^ (s <<< 13))
    else if choice < 86 then
      b := ins b 0xb7 dst 0 0 imm
    else if choice < 89 then
      b := ins b 0x05 0 0 (pick % 6) 0
    else if choice < 92 then
      let far := pick >>> 3
      b := ins b 0x85 0 0 0 (if pick % 5 == 0 then 0 - (1 + far % 9) else far % 12)
    else if choice < 93 then
      b := ins b 0x95 0 0 0 0
    else if choice < 95 then
      -- a call through a register: nearly always to an instruction that exists
      if pick % 8 != 0 then
        let slot := (pick >>> 4) % (n.toUInt64 + 20)
        b := wideConstant b dst (codeAddress + 8 * slot)
      b := ins b 0x8d 0 0 0 dst
    else if choice < 96 then
      if pick % 6 == 0 then
        b := ins b strange[((pick >>> 2) % 8).toNat]! dst src 0 imm
      else
        b := ins b 0xbf dst (if pick % 2 == 0 then 10 else 9) 0 0
    else
      -- r7: at the frame, the heap, the data or the program's own code, then a little further on
      let some := pick >>> 2
      let region : UInt64 := if some % 16 == 0 then 3 else some % 3
      let far := pick >>> 6
      b := if region == 0 then ins (ins b 0xbf 7 10 0 0) 0x07 7 0 0 (0 - 8 * (8 + far % 400))
        else if region == 3 then wideConstant b 7 (codeAddress + far % 600)
        else ins (ins b 0xbf 7 (if region == 1 then 8 else 9) 0 0) 0x07 7 0 0 (far % 1200)
  -- the registers and a little of the frame and the heap, into the account
  for g in [0:8] do
    b := ins b 0x7b 9 g.toUInt64 (1600 + 8 * g.toUInt64) 0
  for i in [0:6] do
    b := ins b 0x79 0 10 (0 - 8 * (1 + 9 * i.toUInt64)) 0
    b := ins b 0x7b 9 0 (1700 + 8 * i.toUInt64) 0
  for i in [0:4] do
    b := ins b 0x79 0 8 (64 * i.toUInt64) 0
    b := ins b 0x7b 9 0 (1800 + 8 * i.toUInt64) 0
  b := ins b 0xb7 0 0 0 0
  return ins b 0x95 0 0 0 0

def key (name : String) : ByteArray := Sha256.hash name.toUTF8

def le64 (v : UInt64) : ByteArray := Wire.putU64 (ByteArray.emptyWithCapacity 8) v

/-- A cheap checksum (the test runs interpreted too, where SHA-256 of every result would take minutes). -/
def mix (h0 : UInt64) (b : ByteArray) : UInt64 := Id.run do
  let mut h := h0
  for i in [0:(b.size + 7) / 8] do
    h := (h ^^^ Wire.u64 b (8 * i)) * 0x100000001b3
    h := h ^^^ (h >>> 29)
  return h

def main : IO Unit := do
  let programId := key "program"
  let clock : Sbpf.Clock := ⟨1, 0, 0, 0, 0⟩
  let metas : Array Sbpf.Meta := #[⟨0, false, true⟩]
  let mut initial := ByteArray.emptyWithCapacity 2048
  for i in [0:256] do
    initial := initial ++ le64 (step i.toUInt64)
  let accounts : Array Sbpf.Account := #[⟨key "account", programId, 1000000, initial, false⟩]
  let mut digest : UInt64 := 0xcbf29ce484222325
  let mut succeeded := 0
  let mut overBudget := 0
  let mut differ := 0
  let mut translatedAsExpected := true
  for k in [0:1500] do
    let program := Sbpf.load (wrap (randomProgram k.toUInt64 (20 + k % 60)))
    if (program.native != 0) != (Fast.compiled && Fast.anyShift) then
      translatedAsExpected := false
    -- three budgets: one that ends most programs early, in the middle of anything
    let budget : UInt64 := if k % 3 == 0 then 700 else if k % 3 == 1 then 150 else 37 + (k.toUInt64 % 50)
    let m := (Sbpf.Machine.create clock budget).add programId program
    let st := Sbpf.process m accounts programId metas ByteArray.empty
    -- (under the official toolchain the first run was the interpreter's already)
    let reference := if Fast.compiled then Sbpf.process { m with interpret := true } accounts programId metas ByteArray.empty else st
    let outcome := Sbpf.outcome st
    if outcome != Sbpf.outcome reference || st.units != reference.units || st.accounts[0]!.data != reference.accounts[0]!.data then
      differ := differ + 1
      IO.println s!"program {k}: machine code says {outcome} after {st.units} units, the interpreter {Sbpf.outcome reference} after {reference.units}"
    if st.status == Sbpf.finished then
      succeeded := succeeded + 1
    if st.status == Sbpf.budgetExceeded then
      overBudget := overBudget + 1
    let data := mix 0 st.accounts[0]!.data
    digest := mix (mix digest outcome.toUTF8) (le64 st.units ++ le64 data)
    if k < 60 then
      IO.println s!"program {k}: {outcome}, {st.units} units, data {data}"
  IO.println s!"1500 programs: {succeeded} finished, {overBudget} ran out of budget, the rest failed otherwise"
  IO.println s!"all outcomes, units and data together: {digest}"
  IO.println s!"machine code and interpreter differ on {differ}"
  IO.println s!"translated exactly where it should be: {translatedAsExpected}"

  -- The translation itself is plain Lean, so both compilers must write the same bytes.
  let (code, starts) := Jit.compile #[0x00000000000000b7, 0x0000000000000095] #[0, 0] #[0, 0] 2 0 false (Sbpf.programStart + 64) 1
  IO.println s!"mov r0, 0; exit: {code.size} bytes of machine code, entered at {Hex.encode starts}"
  IO.println s!"  its last 64: {Hex.encode (code.extract (code.size - 64) code.size)}"
  let image ← IO.FS.readBinFile "tests/programs/counter.so"
  let p := Sbpf.parse image
  let (code, starts) := Jit.compile p.code p.syscalls p.calls p.count p.entry (p.version == 3) p.textAddr p.roRegion
  IO.println s!"counter.so: {p.count} instructions, {code.size} bytes, {Hex.encode (Sha256.hash code)}, blocks {Hex.encode (Sha256.hash starts)}"
