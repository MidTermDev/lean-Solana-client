import Sys
import Fmt
import Solana.Sbpf
import Encoding.Hex

/-!
# leansol run

Executes an on-chain program locally: load an sBPF `.so`, hand it accounts
and instruction data, and report what it returned, what it logged, how many
compute units it used and how it changed the accounts. Nothing is sent to
any network.
-/

namespace RunProgram

def usage : String :=
  "leansol run — execute a Solana program (sBPF v0) locally\n" ++
  "\n" ++
  "usage: leansol run PROGRAM.so [options]\n" ++
  "  --data HEX          instruction data (default: none)\n" ++
  "  --account SPEC      an account, in order; repeatable. SPEC is\n" ++
  "                        KEY:OWNER:LAMPORTS:DATAHEX[:FLAGS]\n" ++
  "                      KEY and OWNER are Base58 addresses, or `program` (the program being run),\n" ++
  "                      `system`, or any other word, which becomes a stand-in address.\n" ++
  "                      FLAGS: s = signer, w = writable.\n" ++
  "                      A SPEC that is only a KEY names a loaded program (or `system`) as an account.\n" ++
  "  --program KEY=FILE  another program this one may call, loaded under address KEY; repeatable\n" ++
  "  --program-id ADDR   the address of the program being run (default: a stand-in)\n" ++
  "  --slot N            the slot the Clock sysvar reports (default 0)\n" ++
  "  --budget N          compute-unit limit (default 200000)\n" ++
  "  --full              print account data in full, so it can be fed to the next run\n" ++
  "\n" ++
  "example: a counter account holding 999, incremented once\n" ++
  "  leansol run counter.so --data 01 --account counter:program:1000000:e703000000000000:w\n"

/-- An address given on the command line. -/
def address (text : String) (programId : ByteArray) : ByteArray :=
  if text == "program" then programId
  else if text == "system" then Sbpf.zeros ByteArray.empty 32
  else
    let b := Base58.decode text
    if b.size == 32 then b else Sha256.hash text.toUTF8

def split (s : String) (sep : UInt8) : Array String := Id.run do
  let b := s.toUTF8
  let mut parts : Array String := Array.emptyWithCapacity 6
  let mut start := 0
  for i in [0:b.size + 1] do
    if i == b.size || b[i]! == sep then
      parts := parts.push (String.fromUTF8! (b.extract start i))
      start := i + 1
  return parts

def isHex (s : String) : Bool := Id.run do
  let b := s.toUTF8
  if b.size % 2 != 0 then
    return false
  for c in b do
    let ok := (c >= 48 && c <= 57) || (c >= 97 && c <= 102) || (c >= 65 && c <= 70)
    if !ok then
      return false
  return true

/-- A decimal number that fits in 64 bits, or `none`. -/
def number (s : String) : Option UInt64 := Id.run do
  let b := s.toUTF8
  if b.size == 0 || b.size > 19 then
    return none
  let mut v : UInt64 := 0
  for c in b do
    if c < 48 || c > 57 then
      return none
    v := v * 10 + (c - 48).toUInt64
  return some v

def fail (msg : String) : IO Unit := do
  IO.eprintln s!"leansol run: {msg}"
  Sys.exit 2

/-- Up to 48 bytes of data as hex, with the total length when there is more. -/
def preview (data : ByteArray) : String :=
  if data.size == 0 then "(no data)"
  else if data.size <= 48 then Hex.encode data
  else s!"{Hex.encode (data.extract 0 48)}… ({data.size} bytes)"

def main : IO Unit := do
  let argc ← Sys.argc
  if argc < 3 then
    IO.print usage
    return
  let path ← Sys.arg 2
  if path == "--help" || path == "-h" then
    IO.print usage
    return
  let mut data := ByteArray.empty
  let mut specs : Array String := Array.emptyWithCapacity 4
  let mut others : Array String := Array.emptyWithCapacity 2
  let mut programName := "program-under-test"
  let mut slot : UInt64 := 0
  let mut budget : UInt64 := 200000
  let mut full := false
  let mut i := 3
  while i < argc do
    let a ← Sys.arg i
    if a == "--full" then
      full := true
      i := i + 1
    else
      if i + 1 >= argc then
        fail s!"{a} needs a value"
      let v ← Sys.arg (i + 1)
      if a == "--data" then
        if !(isHex v) then
          fail "--data expects hexadecimal bytes"
        data := Hex.decode v
      else if a == "--account" then
        specs := specs.push v
      else if a == "--program" then
        others := others.push v
      else if a == "--program-id" then
        programName := v
      else if a == "--slot" || a == "--budget" then
        match number v with
        | none => fail s!"{a} expects a number"
        | some n =>
          if a == "--slot" then
            slot := n
          else
            budget := n
      else
        fail s!"unknown option {a}"
      i := i + 2

  let elf ← Sys.readFile path 0x1000000
  if elf.size == 0 then
    fail s!"cannot read {path}"
  let size := elf.size
  let program := Sbpf.load elf
  if program.error != "" then
    fail s!"{path}: {program.error}"
  let count := program.count
  let programId := address programName ByteArray.empty
  let mut machine := (Sbpf.Machine.create ⟨slot, 0, 0, 0, 0⟩ budget).add programId program
  for spec in others do
    let f := split spec 61
    if f.size != 2 then
      fail s!"--program expects KEY=FILE, got '{spec}'"
    let bytes ← Sys.readFile f[1]! 0x1000000
    if bytes.size == 0 then
      fail s!"cannot read {f[1]!}"
    let other := Sbpf.load bytes
    if other.error != "" then
      fail s!"{f[1]!}: {other.error}"
    machine := machine.add (address f[0]! programId) other

  let mut accounts : Array Sbpf.Account := Array.emptyWithCapacity 4
  let mut metas : Array Sbpf.Meta := Array.emptyWithCapacity 4
  let mut names : Array String := Array.emptyWithCapacity 4
  for spec in specs do
    let f := split spec 58
    let key := address f[0]! programId
    let mut signer := false
    let mut writable := false
    if f.size == 1 then
      -- a program passed as an account
      if key == Sbpf.systemProgram then
        accounts := accounts.push ⟨key, Base58.decode "NativeLoader1111111111111111111111111111111", 1, "system_program".toUTF8, true⟩
      else
        accounts := accounts.push (Sbpf.programAccount key)
    else
      if f.size < 4 || f.size > 5 then
        fail s!"account '{spec}' should be KEY:OWNER:LAMPORTS:DATAHEX[:FLAGS]"
      if !(isHex f[3]!) then
        fail s!"account '{spec}': the data is not hexadecimal"
      let flags := if f.size == 5 then f[4]!.toUTF8 else ByteArray.empty
      for c in flags do
        if c == 115 then
          signer := true
        else if c == 119 then
          writable := true
        else
          fail s!"account '{spec}': flags are s (signer) and w (writable)"
      match number f[2]! with
      | none => fail s!"account '{spec}': lamports is not a number"
      | some lamports => accounts := accounts.push ⟨key, address f[1]! programId, lamports, Hex.decode f[3]!, false⟩
    -- the same account may be listed twice; later mentions refer to the first
    let existing := Sbpf.findAccount accounts key
    if existing + 1 != accounts.size then
      accounts := accounts.pop
    metas := metas.push ⟨existing, signer, writable⟩
    names := names.push f[0]!

  let before := accounts
  let st := Sbpf.process machine accounts programId metas data
  IO.println s!"program   {path} · {Fmt.thousands size.toUInt64} bytes · {Fmt.thousands count.toUInt64} instructions"
  IO.println s!"result    {Sbpf.outcome st}"
  IO.println s!"units     {Fmt.thousands st.units} of {Fmt.thousands budget}"
  for line in st.logs do
    IO.println s!"log       {line}"
  for k in [0:metas.size] do
    if !(Sbpf.isRepeat metas k) then
      let was := before[metas[k]!.index]!
      let now := st.accounts[metas[k]!.index]!
      if !now.executable then
        let changed := now.lamports != was.lamports || now.data != was.data || now.owner != was.owner
        IO.println s!"account   {Fmt.padRight names[k]! 12} lamports {Fmt.padLeft (Fmt.thousands now.lamports) 14}   data {if full then Hex.encode now.data else preview now.data}{if changed then "   (changed)" else ""}"
  if st.status != 0 then
    Sys.exit 1

end RunProgram
