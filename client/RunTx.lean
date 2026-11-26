import Sys
import Fmt
import Solana.Bank
import Encoding.Hex
import RunProgram

/-!
`leansol tx`: apply a signed transaction to a set of accounts, locally.

Takes a transaction as wallets and RPC nodes pass it around (Base64), the
accounts it touches as they are before it, and the programs it calls. Checks
the signatures, charges the fee, runs every instruction, and prints what a
block explorer would show: result, fee, compute units, logs, and how each
account changed. Nothing is sent anywhere.
-/

namespace RunTx

def usage : String :=
  "leansol tx — apply a signed transaction to accounts, locally\n" ++
  "\n" ++
  "usage: leansol tx TRANSACTION [options]\n" ++
  "  TRANSACTION         the signed transaction, Base64 (legacy or version 0)\n" ++
  "  --account SPEC      an account as it is before the transaction; repeatable. SPEC is\n" ++
  "                        ADDRESS:OWNER:LAMPORTS:DATAHEX\n" ++
  "                      ADDRESS and OWNER are Base58 addresses; OWNER may be `system`.\n" ++
  "                      Accounts not given are empty. Sysvars and built-in programs are provided.\n" ++
  "  --program ADDR=FILE a program (sBPF v0 .so) deployed at ADDR; repeatable\n" ++
  "  --slot N            the slot the Clock sysvar reports (default 0)\n" ++
  "  --no-verify         do not check the signatures\n" ++
  "  --full              print account data in full\n" ++
  "\n" ++
  "The fee is 5,000 lamports per signature plus any priority fee the transaction sets.\n" ++
  "The blockhash is not checked: any transaction can be replayed against any accounts.\n"

def short (key : ByteArray) : String :=
  let text := Base58.encode key
  Fmt.padRight text 44

def main : IO Unit := do
  let argc ← Sys.argc
  if argc < 3 then
    IO.print usage
    return
  let encoded ← Sys.arg 2
  if encoded == "--help" || encoded == "-h" then
    IO.print usage
    return
  let mut specs : Array String := Array.emptyWithCapacity 4
  let mut programs : Array String := Array.emptyWithCapacity 2
  let mut slot : UInt64 := 0
  let mut verify := true
  let mut full := false
  let mut i := 3
  while i < argc do
    let a ← Sys.arg i
    if a == "--full" || a == "--no-verify" then
      if a == "--full" then
        full := true
      else
        verify := false
      i := i + 1
    else
      if i + 1 >= argc then
        RunProgram.fail s!"{a} needs a value"
      let v ← Sys.arg (i + 1)
      if a == "--account" then
        specs := specs.push v
      else if a == "--program" then
        programs := programs.push v
      else if a == "--slot" then
        match RunProgram.number v with
        | none => RunProgram.fail "--slot expects a number"
        | some n => slot := n
      else
        RunProgram.fail s!"unknown option {a}"
      i := i + 2

  let tx := Tx.parse (Base64.decode encoded)
  if tx.error != "" then
    RunProgram.fail s!"not a transaction: {if (Base64.decode encoded).size == 0 then "it is not Base64" else tx.error}"
  let msg := tx.message
  let mut bank := Bank.create ⟨slot, 0, 0, 0, 0⟩
  for spec in programs do
    let f := RunProgram.split spec 61
    if f.size != 2 || (Base58.decode f[0]!).size != 32 then
      RunProgram.fail s!"--program expects ADDRESS=FILE, got '{spec}'"
    let bytes ← Sys.readFile f[1]! 0x1000000
    if bytes.size == 0 then
      RunProgram.fail s!"cannot read {f[1]!}"
    let program := Sbpf.load bytes
    if program.error != "" then
      RunProgram.fail s!"{f[1]!}: {program.error}"
    bank := bank.addProgram (Base58.decode f[0]!) program
  for spec in specs do
    let f := RunProgram.split spec 58
    if f.size != 4 then
      RunProgram.fail s!"account '{spec}' should be ADDRESS:OWNER:LAMPORTS:DATAHEX"
    let address := Base58.decode f[0]!
    let owner := if f[1]! == "system" then Sbpf.systemProgram else Base58.decode f[1]!
    if address.size != 32 || owner.size != 32 then
      RunProgram.fail s!"account '{spec}': the address and the owner must be Base58 addresses"
    if !(RunProgram.isHex f[3]!) then
      RunProgram.fail s!"account '{spec}': the data is not hexadecimal"
    match RunProgram.number f[2]! with
    | none => RunProgram.fail s!"account '{spec}': lamports is not a number"
    | some lamports => bank := bank.set ⟨address, owner, lamports, Hex.decode f[3]!, false⟩

  IO.println s!"transaction  {Base58.encode tx.signatures[0]!}"
  IO.println s!"             {if msg.versioned then "version 0" else "legacy"} · {tx.signatures.size} signature{if tx.signatures.size == 1 then "" else "s"} · {msg.keys.size} accounts{if msg.lookups.size != 0 then s!" + {msg.lookups.size} address table" else ""}"
  IO.println s!"fee payer    {Base58.encode msg.keys[0]!}"
  for k in [0:msg.instructions.size] do
    let ix := msg.instructions[k]!
    let program := if ix.program < msg.keys.size then Base58.encode msg.keys[ix.program]! else "(from an address table)"
    IO.println s!"instruction  {k}: {program} · {ix.accounts.size} accounts · {ix.data.size} bytes"
  let r := bank.process tx verify
  IO.println s!"result       {if r.error == "" then "success" else r.error}"
  IO.println s!"fee          {Fmt.thousands r.fee} lamports{if r.charged then "" else " (not charged: the transaction was refused before it could run)"}"
  if r.charged then
    IO.println s!"units        {Fmt.thousands r.units} of {Fmt.thousands r.limit}"
  for line in r.logs do
    IO.println s!"log          {line}"
  for key in msg.keys do
    let was := bank.get key
    let now := r.bank.get key
    if was.lamports != now.lamports || was.data != now.data || was.owner != now.owner then
      let change := if was.lamports == 0 then "created" else if now.lamports == 0 then "closed" else "changed"
      IO.println s!"account      {short key} {Fmt.padLeft (Fmt.thousands was.lamports) 14} → {Fmt.padLeft (Fmt.thousands now.lamports) 14} lamports   ({change})"
      if now.data.size != 0 || was.data.size != 0 then
        IO.println s!"             data {if full then Hex.encode now.data else RunProgram.preview now.data}"
      if was.owner != now.owner && now.lamports != 0 then
        IO.println s!"             owner {Base58.encode now.owner}"
  if r.error != "" then
    Sys.exit 1

end RunTx
