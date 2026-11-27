import Solana.Native

/-!
# An sBPF virtual machine

Solana's on-chain programs are sBPF bytecode. This file loads such programs
from their ELF files and executes instructions against a set of accounts:
the interpreter, the loader with its relocations, the memory map, the
compute-unit meter, the account serialization programs expect, the system
calls, and **cross-program invocation**: a program calling another program,
with the runtime's rules about who may sign for and modify which account.

It runs **sBPF versions 0 to 3**: v0, which nearly everything deployed today
uses, and the newer encodings up to v3. That covers programs
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

-/


namespace Sbpf

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
  -- these two are lists in a buffer of fixed size, and a program may ask for any part of the buffer
  else if name == slotHashesSysvar then zeros m.sysvars.slotHashes (20488 - m.sysvars.slotHashes.size)
  else if name == stakeHistorySysvar then zeros m.sysvars.stakeHistory (16392 - m.sysvars.stakeHistory.size)
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
  if programId == systemProgram || programId == computeBudgetProgram || programId == loaderId || programId == loaderV1
      || programId == loaderV2 then
    -- built into the runtime. The compute budget program's work is done before the transaction runs, and the
    -- two older loaders no longer accept instructions.
    let after := if programId == systemProgram then systemInstruction m st0 metas data
      else if programId == loaderId then loaderInstruction m st0 metas data
      else if programId == computeBudgetProgram then st0.charge 150
      else refused (st0.charge (if programId == loaderV2 then 570 else 1140)) "UnsupportedProgramId"
    if after.units > m.budget then
      return { after with units := m.budget, status := meterExceeded }
    return after
  let which := m.find programId
  if which == notFound then
    return st0.stop unknownProgram (Base58.encode programId)
  if m.programs[which]!.error != "" then
    return st0.stop unsupportedInstruction m.programs[which]!.error
  if m.clock.slot < m.programs[which]!.since then
    return refused st0 "UnsupportedProgramId"
  let loaded : Program := m.programs[which]!
  let p : Program := { loaded with heap := m.heap }
  let ⟨accounts0, units0, logs0, returnData0, _, _, _, trace0⟩ := st0
  let mut accounts := accounts0
  -- a heap beyond the first 32 KiB costs 8 units per further 32 KiB
  let mut units := Fast.hot (units0 + ((p.heap + 32767) / 32768 - 1).toUInt64 * 8)
  let mut logs := logs0
  let mut returnData := returnData0
  let mut trace := trace0
  let budget := m.budget

  -- The program's memory: stack, heap, then its input. The stack and the heap start as zeros (copied from
  -- a block of zeros made once, not pushed a byte at a time), and the input is written straight after them.
  let packedInput := if p.packed then serializePacked accounts metas data programId else ByteArray.empty
  let mut mem := ByteArray.emptyWithCapacity (stackBytes + p.heap + (if p.packed then packedInput.size else serializedSize accounts metas data) + 64)
  mem := zeroBlock.copySlice 0 mem 0 (if stackBytes + p.heap < zeroBlock.size then stackBytes + p.heap else zeroBlock.size)
  for _ in [mem.size:stackBytes + p.heap] do
    mem := mem.push 0
  mem := if p.packed then mem ++ packedInput else serializeOnto mem accounts metas data programId
  let inputLen := mem.size - (stackBytes + p.heap)
  let mut regs : Array UInt64 := Array.replicate 11 0
  regs := regs.set! 1 inputStart
  -- the second register points at the instruction's data in the input (its length sits just before it)
  regs := regs.set! 2 (inputStart + (inputLen - 32 - data.size).toUInt64)
  -- What the versions of sBPF change. In 1 and 2 a function moves the stack pointer itself. 2 re-encodes
  -- arithmetic and memory instructions. 3 goes back to version 0's instructions and adds 32-bit conditional
  -- jumps, calls that are either relative or name a system call by hash, and the stricter file format.
  let ownStack := p.version == 1 || p.version == 2
  let v2 := p.version == 2
  let v3 := p.version >= 3
  regs := regs.set! 10 (stackStart + (if ownStack then stackBytes else frameBytes).toUInt64)
  -- saved r6..r9, frame pointer and return address of every active call
  -- how much of the heap the old allocation call has handed out
  let mut allocated : UInt64 := 0
  let mut frames : Array UInt64 := Array.replicate (maxDepth * 6) 0
  let mut calls := 0
  let mut pc := Fast.hotNat p.entry
  let code := p.code
  let count := p.count
  let heapSize := p.heap
  let plain := !v2 && p.tidy
  let mut status := finished
  let mut r0 : UInt64 := 0
  let mut detail := ""
  repeat
    if units >= budget then
      status := budgetExceeded
      break
    if pc >= count then
      status := executionOverrun
      break
    units := units + 1
    let word := Fast.hot code[pc]!
    -- The instructions that make up nearly all of a run, first and without the detours: arithmetic, loads
    -- and stores, conditional jumps, in the versions that share version 0's encodings. Each does exactly
    -- what the general code below does for it, reading its fields straight from the word; whatever is
    -- unusual about an instruction is left to that code.
    if plain then
      let cls := word &&& 7
      if cls == 7 then
        let op := word &&& 0xf0
        if op <= 0xc0 && op != 0x30 && op != 0x90 then
          let d := ((word >>> 8) &&& 15).toNat
          let b := if word &&& 8 != 0 then regs[((word >>> 12) &&& 15).toNat]! else sext32 (word >>> 32)
          regs := regs.set! d (if op == 0xb0 then b else if op == 0x00 then regs[d]! + b else alu64 op regs[d]! b)
          pc := pc + 1
          continue
      else if cls == 1 || cls == 2 || cls == 3 then
        if word &&& 0xe0 == 0x60 then
          let width := word &&& 0x18
          let size := if width == 0x00 then 4 else if width == 0x08 then 2 else if width == 0x10 then 1 else 8
          let d := ((word >>> 8) &&& 15).toNat
          let s := ((word >>> 12) &&& 15).toNat
          let addr := (if cls == 1 then regs[s]! else regs[d]!) + sext16 ((word >>> 16) &&& 0xFFFF)
          let region := addr >>> 32
          let within := (addr &&& 0xFFFFFFFF).toNat
          -- the stack and the input are where nearly every access goes
          let idx := if region == 2 && within + size <= stackBytes then within
            else if region == 4 && within + size <= inputLen then stackBytes + heapSize + within
            else locate p inputLen addr size (cls != 1)
          if Wire.ok idx then
            if cls == 1 then
              regs := regs.set! d (if idx >= progBase then loadAt p mem idx size
                else if size == 8 then Fast.le64 mem idx else if size == 4 then Fast.le32 mem idx
                else if size == 2 then Fast.le16 mem idx else Wire.u8 mem idx)
            else
              mem := storeAt mem idx size (if cls == 2 then sext32 (word >>> 32) else regs[s]!)
            pc := pc + 1
            continue
      else if cls == 5 then
        let op := word &&& 0xf0
        if op != 0 && op != 0x80 && op != 0x90 && op <= 0xd0 then
          let b := if word &&& 8 != 0 then regs[((word >>> 12) &&& 15).toNat]! else sext32 (word >>> 32)
          let a := regs[((word >>> 8) &&& 15).toNat]!
          let taken := if op == 0x10 then a == b else if op == 0x50 then a != b else jumpTaken op a b
          pc := if taken then ((pc + 1).toUInt64 + sext16 ((word >>> 16) &&& 0xFFFF)).toNat else pc + 1
          continue
      else if cls == 4 then
        let op := word &&& 0xf0
        if op <= 0xc0 && op != 0x30 && op != 0x90 then
          let d := ((word >>> 8) &&& 15).toNat
          let b := if word &&& 8 != 0 then regs[((word >>> 12) &&& 15).toNat]! else sext32 (word >>> 32)
          regs := regs.set! d (alu32 op regs[d]! b)
          pc := pc + 1
          continue
    -- the instruction: opcode, two registers, a 16-bit offset, a 32-bit constant
    let opc := word &&& 0xFF
    let dst := ((word >>> 8) &&& 15).toNat
    let src := ((word >>> 12) &&& 15).toNat
    let off := sext16 ((word >>> 16) &&& 0xFFFF)
    let imm32 := word >>> 32
    let imm := sext32 imm32
    if dst > 10 || src > 10 then
      status := unsupportedInstruction
      break
    let cls := opc &&& 7
    let op := opc &&& 0xf0
    let mut next := pc + 1
    if v2 && (cls == 4 || cls == 7) && (op == 0x20 || op == 0x30 || op == 0x80 || op == 0x90) then
      -- from v2 the memory instructions use the encodings multiply, divide, negate and modulo had:
      -- loads in the 32-bit class, stores in the 64-bit class, 1, 2, 4 or 8 bytes
      let size := if op == 0x20 then 1 else if op == 0x30 then 2 else if op == 0x80 then 4 else 8
      if cls == 4 && opc &&& 8 == 0 then
        status := unsupportedInstruction
        break
      let addr := (if cls == 4 then regs[src]! else regs[dst]!) + off
      let idx := locate p inputLen addr size (cls == 7)
      if !(Wire.ok idx) then
        status := accessViolation
        detail := s!"at address {hex64 addr}, instruction {pc}"
        break
      if cls == 4 then
        regs := regs.set! dst (loadAt p mem idx size)
      else
        mem := storeAt mem idx size (if opc &&& 8 == 0 then imm else regs[src]!)
    else if v2 && opc == 0xf7 then
      -- sets the upper half of a register: with a 32-bit move, this replaces the two-slot constant load
      regs := regs.set! dst (regs[dst]! ||| (imm32 <<< 32))
    else if v3 && cls == 6 then
      -- conditional jumps comparing the low 32 bits
      let signed := op == 0x60 || op == 0x70 || op == 0xc0 || op == 0xd0
      if op == 0 || op == 0x80 || op == 0x90 || op > 0xd0 then
        status := unsupportedInstruction
        break
      let b := if opc &&& 8 != 0 then regs[src]! else imm
      let x := if signed then sext32 regs[dst]! else regs[dst]! &&& 0xFFFFFFFF
      let y := if signed then sext32 b else b &&& 0xFFFFFFFF
      if jumpTaken op x y then
        next := (next.toUInt64 + off).toNat
    else if v2 && cls == 6 then
      -- products, quotients and remainders, signed and unsigned, 32 and 64 bits
      let wide := opc &&& 0x10 != 0
      let kind := opc &&& 0xe0
      let signed := kind == 0xa0 || kind == 0xc0 || kind == 0xe0
      let a := regs[dst]!
      let b := if opc &&& 8 != 0 then regs[src]! else if signed || kind == 0x80 then imm else imm32
      if kind == 0x00 || ((kind == 0x20 || kind == 0xa0) && !wide) then
        status := unsupportedInstruction
        break
      else if kind == 0x80 then
        regs := regs.set! dst (if wide then a * b else (a * b) &&& 0xFFFFFFFF)
      else if kind == 0x20 then
        regs := regs.set! dst (umulh a b)
      else if kind == 0xa0 then
        regs := regs.set! dst (smulh a b)
      else
        let x := if wide then a else if signed then sext32 a else a &&& 0xFFFFFFFF
        let y := if wide then b else if signed then sext32 b else b &&& 0xFFFFFFFF
        if y == 0 then
          status := divideByZero
          break
        if signed && y == 0xFFFFFFFFFFFFFFFF && x == (if wide then 0x8000000000000000 else 0xFFFFFFFF80000000) then
          status := divideByZero
          detail := "the quotient does not fit"
          break
        let r := if kind == 0x40 then x / y else if kind == 0x60 then x % y else if kind == 0xc0 then sdiv x y else srem x y
        regs := regs.set! dst (if wide then r else r &&& 0xFFFFFFFF)
    else if cls == 7 || cls == 4 then
      -- arithmetic: 64-bit (class 7) and 32-bit (class 4), operand from a register or the immediate
      let b := if opc &&& 8 != 0 then regs[src]! else imm
      let a := regs[dst]!
      if opc == 0xdc || (opc == 0xd4 && !v2) then
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
      else if v2 then
        -- from v2: subtracting from an immediate computes immediate − register; 32-bit add and subtract
        -- zero-extend their result; a 32-bit move between registers sign-extends
        let swap := op == 0x10 && opc &&& 8 == 0
        let r := if cls == 7 then alu64 op (if swap then b else a) (if swap then a else b)
          else alu32 op (if swap then b else a) (if swap then a else b)
        regs := regs.set! dst (if cls == 4 && (op == 0x00 || op == 0x10) then r &&& 0xFFFFFFFF
          else if opc == 0xbc then sext32 r else r)
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
        -- call a function of the program: by symbol, by relative offset, or (callx) through a register,
        -- which the instruction names in a different field in each version
        let through := if v2 then src else if v3 then dst else (imm32 &&& 15).toNat
        if (opc == 0x8d && through > 10) || (v3 && opc == 0x85 && src != 1) then
          status := unsupportedInstruction
          break
        let target := if opc == 0x8d then (regs[through]! - p.textAddr) / 8
          else if !v3 && p.calls[pc]! != 0 then p.calls[pc]! - 1
          else next.toUInt64 + imm
        for k in [0:4] do
          frames := frames.set! (calls * 6 + k) regs[6 + k]!
        frames := frames.set! (calls * 6 + 4) regs[10]!
        frames := frames.set! (calls * 6 + 5) next.toUInt64
        calls := calls + 1
        if calls == maxDepth then
          status := callDepthExceeded
          break
        if !ownStack then
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
        else if id == sysSha256 || id == sysKeccak || id == sysBlake3 then
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
              let digest := if id == sysKeccak then Keccak.hash message else if id == sysBlake3 then Blake3.hash message else Sha256.hash message
              mem := digest.copySlice 0 mem dest 32
            else
              status := accessViolation
        else if id == sysCurveValidate then
          -- is this a point of the curve? (a1 = which curve: 0 Edwards, 1 Ristretto; a2 = the point)
          if a1 == 0 then
            units := units + 159
            match readBytes p mem inputLen a2 32 with
            | none => status := accessViolation
            | some point => result := if (Ed25519.Point.decode point).isSome then 0 else 1
          else
            status := unsupportedSyscall
            detail := s!"curve {a1} of sol_curve_validate_point is not provided"
        else if id == sysCurveOp then
          -- add, subtract or multiply on the Edwards curve: a2 = which, a3 and r4 the operands, r5 where the result goes
          if a1 == 0 && a2 <= 2 then
            units := units + (if a2 == 0 then 473 else if a2 == 1 then 475 else 2177)
            let dest := writable p inputLen regs[5]! 32
            match readBytes p mem inputLen a3 32, readBytes p mem inputLen regs[4]! 32 with
            | some left, some right =>
              if !(Wire.ok dest) then
                status := accessViolation
              else if a2 == 2 then
                -- a scalar (which must be reduced) times a point
                match Ed25519.Point.decode right with
                | none => result := 1
                | some point =>
                  if !(Ed25519.scIsCanonical left) then
                    result := 1
                  else
                    let zero := zeros ByteArray.empty 32
                    let product := Ed25519.doubleScalarMul left (Ed25519.Point.table point) zero (Ed25519.Point.table point)
                    mem := (Ed25519.Point.encode product).copySlice 0 mem dest 32
              else
                match Ed25519.Point.decode left, Ed25519.Point.decode right with
                | some x, some y =>
                  let sum := Ed25519.Point.add x (if a2 == 1 then Ed25519.Point.neg y else y)
                  mem := (Ed25519.Point.encode sum).copySlice 0 mem dest 32
                | _, _ => result := 1
            | _, _ => status := accessViolation
          else
            status := unsupportedSyscall
            detail := s!"curve {a1}, operation {a2} of sol_curve_group_op is not provided"
        else if id == sysCurveMsm then
          -- a sum of scalars times points on the Edwards curve: a2 the scalars, a3 the points, r4 how many, r5 the result
          let count := regs[4]!
          if a1 == 0 && count <= 512 then
            units := units + 2273 + 758 * (if count == 0 then 0 else count - 1)
            let dest := writable p inputLen regs[5]! 32
            match readBytes p mem inputLen a2 (32 * count), readBytes p mem inputLen a3 (32 * count) with
            | some scalars, some points =>
              if !(Wire.ok dest) then
                status := accessViolation
              else
                let zero := zeros ByteArray.empty 32
                let mut sum := Ed25519.Point.identity
                let mut valid := true
                for i in [0:count.toNat] do
                  let scalar := scalars.extract (32 * i) (32 * i + 32)
                  match Ed25519.Point.decode (points.extract (32 * i) (32 * i + 32)) with
                  | none => valid := false
                  | some point =>
                    if !(Ed25519.scIsCanonical scalar) then
                      valid := false
                    else
                      sum := Ed25519.Point.add sum (Ed25519.doubleScalarMul scalar (Ed25519.Point.table point) zero (Ed25519.Point.table point))
                if valid then
                  mem := (Ed25519.Point.encode sum).copySlice 0 mem dest 32
                else
                  result := 1
            | _, _ => status := accessViolation
          else
            status := unsupportedSyscall
            detail := s!"curve {a1} of sol_curve_multiscalar_mul is not provided"
        else if id == sysAllocFree then
          -- the allocator older programs call: hands out the heap from its start, never takes anything back
          if a2 == 0 then
            let aligned := if p.packed then allocated else (allocated + 7) / 8 * 8
            if a1 <= p.heap.toUInt64 && aligned + a1 <= p.heap.toUInt64 then
              result := 0x300000000 + aligned
              allocated := aligned + a1
        else if id == sysBn128 then
          -- the alt_bn128 curve: a1 = add (0), multiply (2) or check pairings (3); a2, a3 the input; r4 the result
          if a1 == 0 || a1 == 2 || a1 == 3 then
            let pairs := a3 / 192
            units := units + (if a1 == 0 then 334 else if a1 == 2 then 3840
              else 36364 + 12121 * (if pairs == 0 then 0 else pairs - 1) + 85 + a3 + 32)
            let outSize : UInt64 := if a1 == 3 then 32 else 64
            let dest := writable p inputLen regs[4]! outSize
            match readBytes p mem inputLen a2 a3 with
            | none => status := accessViolation
            | some raw =>
              if !(Wire.ok dest) then
                status := accessViolation
              else if units > budget then
                -- (nothing is computed that the budget cannot pay for)
                pure ()
              else if a1 == 3 then
                if raw.size % 192 != 0 then
                  result := 1
                else
                  let answer := Bn254.pairingCheck raw true
                  if answer == 2 then
                    result := 1
                  else
                    mem := (zeros ByteArray.empty 31).push answer.toUInt8 |>.copySlice 0 mem dest 32
              else
                let limit := if a1 == 0 then 128 else 96
                if raw.size > limit then
                  result := 1
                else
                  let input := zeros raw (limit - raw.size)
                  match Bn254.g1OfBytes input 0 true with
                  | none => result := 1
                  | some first =>
                    if a1 == 2 then
                      let product := Bn254.g1Scale (Mont.ofBytes input 64 true) first
                      mem := (Bn254.g1ToBytes product true).copySlice 0 mem dest 64
                    else
                      match Bn254.g1OfBytes input 64 true with
                      | none => result := 1
                      | some second => mem := (Bn254.g1ToBytes (Bn254.g1Add first second) true).copySlice 0 mem dest 64
          else
            status := unsupportedSyscall
            detail := s!"operation {a1} of sol_alt_bn128_group_op is not provided"
        else if id == sysBn128Convert then
          -- points of alt_bn128 to half their size and back: a1 = which conversion, a2, a3 the input, r4 the result
          if a1 > 3 then
            status := unsupportedSyscall
            detail := s!"conversion {a1} of sol_alt_bn128_compression is not provided"
          else
            units := units + 100 + (if a1 == 0 then 30 else if a1 == 1 then 398 else if a1 == 2 then 86 else 13610)
            let outSize : UInt64 := if a1 == 0 then 32 else if a1 == 3 then 128 else 64
            let dest := writable p inputLen regs[4]! outSize
            match readBytes p mem inputLen a2 a3 with
            | none => status := accessViolation
            | some raw =>
              if !(Wire.ok dest) then
                status := accessViolation
              else if units > budget then
                pure ()
              else
                let converted := Bn254.convert a1.toNat raw
                if converted.size == 0 then
                  result := 1
                else
                  mem := converted.copySlice 0 mem dest converted.size
        else if id == sysPoseidon then
          -- the Poseidon hash of up to 12 numbers: a1 = which parameters (0), a2 = byte order, a3 the inputs
          -- (address and length pairs), r4 how many, r5 where the 32-byte result goes
          let count := regs[4]!
          if a1 != 0 || a2 > 1 || count > 12 then
            status := runtimeError
            detail := "ProgramFailedToComplete"
          else
            units := units + 61 * count * count + 542
            let dest := writable p inputLen regs[5]! 32
            match readSlices p mem inputLen a3 count with
            | none => status := accessViolation
            | some inputs =>
              if !(Wire.ok dest) then
                status := accessViolation
              else
                let digest := Poseidon.hash inputs (a2 == 0)
                if digest.size != 32 then
                  result := 1
                else
                  mem := digest.copySlice 0 mem dest 32
        else if id == sysSecpRecover then
          -- the public key behind an Ethereum-style signature: a1 the hash, a2 which candidate, a3 the signature, r4 where to put the key
          units := units + 25000
          let dest := writable p inputLen regs[4]! 64
          match readBytes p mem inputLen a1 32, readBytes p mem inputLen a3 64 with
          | some hash, some signature =>
            if !(Wire.ok dest) then
              status := accessViolation
            else if a2 > 3 then
              result := 2
            else
              let key := Secp256k1.recover hash a2.toNat signature
              if key.size != 64 then
                result := 3
              else
                mem := key.copySlice 0 mem dest 64
          | _, _ => status := accessViolation
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
          let mut wanted := if id >= 0x100000000 then s!"with hash {id - 0x100000000}" else "(named in the program's symbols)"
          for name in allSyscallNames do
            if id >= 0x100000000 && murmur3 name.toUTF8 == id - 0x100000000 then
              wanted := name
          detail := s!"the program makes a system call this machine does not provide: {wanted}"
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
    else if opc == 0x18 && !v2 then
      -- load a 64-bit constant: two instruction slots
      let upper := if pc + 1 < p.count then code[pc + 1]! >>> 32 else Wire.u32 p.elf (p.textOff + pc * 8 + 12)
      regs := regs.set! dst (imm32 ||| (upper <<< 32))
      next := pc + 2
    else if !v2 && (cls == 1 || cls == 2 || cls == 3) then
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
          o := o + (if p.packed then 1 else 8)
        else if p.packed then
          -- the first loader's layout: balance and data can change, size and owner cannot
          let index := metas[i]!.index
          let account := accounts[index]!
          let was := entry[index]!.data.size
          if Wire.u64 mem (o + 43) != was.toUInt64 then
            status := invalidRealloc
          else
            let lamports := Wire.u64 mem (o + 35)
            let contents := mem.extract (o + 51) (o + 51 + was)
            let why := changeError programId metas[i]!.writable account lamports account.owner contents
            if why != "" then
              status := accountRule
              detail := why
            else
              accounts := accounts.set! index { account with lamports := lamports, data := contents }
              sum := sum + lamports
          o := o + was + 92
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
