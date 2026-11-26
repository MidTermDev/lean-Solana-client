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
  "                      KEY and OWNER are Base58 addresses, or `program` (this program),\n" ++
  "                      `system`, or any other word, which becomes a stand-in address.\n" ++
  "                      FLAGS: s = signer, w = writable.\n" ++
  "  --program-id ADDR   the program's own address (default: a stand-in)\n" ++
  "  --slot N            the slot the Clock sysvar reports (default 0)\n" ++
  "  --budget N          compute-unit limit (default 200000)\n" ++
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
  let mut programName := "program-under-test"
  let mut slot : UInt64 := 0
  let mut budget : UInt64 := 200000
  let mut i := 3
  while i < argc do
    let a ← Sys.arg i
    if i + 1 >= argc then
      fail s!"{a} needs a value"
    let v ← Sys.arg (i + 1)
    if a == "--data" then
      if !(isHex v) then
        fail "--data expects hexadecimal bytes"
      data := Hex.decode v
    else if a == "--account" then
      specs := specs.push v
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
  let program := Sbpf.load elf
  if program.error != "" then
    fail s!"{path}: {program.error}"
  let programId := address programName ByteArray.empty

  let mut accounts : Array Sbpf.Account := Array.emptyWithCapacity 4
  let mut names : Array String := Array.emptyWithCapacity 4
  for spec in specs do
    let f := split spec 58
    if f.size < 4 || f.size > 5 then
      fail s!"account '{spec}' should be KEY:OWNER:LAMPORTS:DATAHEX[:FLAGS]"
    if !(isHex f[3]!) then
      fail s!"account '{spec}': the data is not hexadecimal"
    let flags := if f.size == 5 then f[4]!.toUTF8 else ByteArray.empty
    let mut signer := false
    let mut writable := false
    for c in flags do
      if c == 115 then
        signer := true
      else if c == 119 then
        writable := true
      else
        fail s!"account '{spec}': flags are s (signer) and w (writable)"
    match number f[2]! with
    | none => fail s!"account '{spec}': lamports is not a number"
    | some lamports =>
      accounts := accounts.push ⟨address f[0]! programId, address f[1]! programId, lamports, Hex.decode f[3]!, signer, writable⟩
      names := names.push f[0]!

  let clock : Sbpf.Clock := ⟨slot, 0, 0, 0, 0⟩
  let o := Sbpf.run program (Sbpf.serialize accounts data programId) clock budget
  let ok := o.status == 0 && o.r0 == 0
  IO.println s!"program   {path} · {Fmt.thousands elf.size.toUInt64} bytes · {Fmt.thousands program.count.toUInt64} instructions"
  if o.status != 0 then
    IO.println s!"result    stopped: {Sbpf.statusName o.status}{if o.detail == "" then "" else " (" ++ o.detail ++ ")"}"
  else
    IO.println s!"result    {Sbpf.errorName o.r0}"
  IO.println s!"units     {Fmt.thousands o.units} of {Fmt.thousands budget}"
  for line in o.logs do
    IO.println s!"log       {line}"
  -- a failed instruction changes nothing, as on chain
  let after := if ok then Sbpf.readBack accounts o.input else accounts
  for k in [0:after.size] do
    let before := accounts[k]!
    let now := after[k]!
    let changed := now.lamports != before.lamports || now.data != before.data
    IO.println s!"account   {Fmt.padRight names[k]! 12} lamports {Fmt.padLeft (Fmt.thousands now.lamports) 14}   data {preview now.data}{if changed then "   (changed)" else ""}"
  if !ok then
    Sys.exit 1

end RunProgram
