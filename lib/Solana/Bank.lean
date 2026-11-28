import Solana.Sbpf
import Solana.Transaction
import Crypto.P256

/-!
# Processing whole transactions

`Sbpf` runs one instruction. A transaction is more than its instructions:
somebody pays a fee for it whether it succeeds or not, it sets its own
compute budget, its instructions share that budget and either all take
effect or none do, and no account may be left holding too little to be
exempt from rent. This file is that layer: a `Bank` holds accounts and
programs, and `Bank.process` applies a transaction to it the way Agave does.

The order of events, each of which can end the transaction with its own error:

1. the transaction is well formed, and its signatures verify;
2. its compute-budget instructions are read: unit limit, unit price, heap size;
3. the fee is computed and taken from the first signer;
4. every instruction runs, in order, on a shared budget;
5. no writable account may have become rent-paying;
6. the changes are kept. If anything failed after step 3, only the fee is.

The bank also provides the accounts that are not anybody's: the sysvars
(clock, rent, epoch schedule, slot hashes, recent blockhashes, the
transaction's own instructions, and so on) and the built-in programs.
-/

namespace Bank

def instructionsSysvar : ByteArray := Base58.decode "Sysvar1nstructions1111111111111111111111111"
def feesSysvar : ByteArray := Base58.decode "SysvarFees111111111111111111111111111111111"
def recentBlockhashesSysvar : ByteArray := Sbpf.recentBlockhashesSysvar
def slotHistorySysvar : ByteArray := Base58.decode "SysvarS1otHistory11111111111111111111111111"
def ed25519Program : ByteArray := Base58.decode "Ed25519SigVerify111111111111111111111111111"
def secp256k1Program : ByteArray := Base58.decode "KeccakSecp256k11111111111111111111111111111"
def secp256r1Program : ByteArray := Base58.decode "Secp256r1SigVerify1111111111111111111111111"
def lookupTableProgram : ByteArray := Base58.decode "AddressLookupTab1e1111111111111111111111111"
def voteProgram : ByteArray := Sbpf.voteProgram
def stakeProgram : ByteArray := Base58.decode "Stake11111111111111111111111111111111111111"
def configProgram : ByteArray := Base58.decode "Config1111111111111111111111111111111111111"
/-- What is sent here is destroyed at the end of the slot. -/
def incinerator : ByteArray := Base58.decode "1nc1nerator11111111111111111111111111111111"
def loaderV2 : ByteArray := Sbpf.loaderV2
def loaderV1 : ByteArray := Sbpf.loaderV1
def loaderV4 : ByteArray := Base58.decode "LoaderV411111111111111111111111111111111111"

/-- Accounts, programs, and the state of the chain around them. -/
structure Bank where
  machine : Sbpf.Machine
  accounts : Array Sbpf.Account
  /-- The latest blockhash. If set (32 bytes), transactions must name it. -/
  blockhash : ByteArray
  lamportsPerSignature : UInt64
  deriving Inhabited

/-- What processing a transaction did. `error` is `""` on success and
otherwise Agave's name for the failure, such as
`InstructionError(1, Custom(6001))`. `charged` says whether the fee was
taken: a transaction that fails before its fee payer is validated costs
nothing and changes nothing. -/
structure Receipt where
  error : String
  charged : Bool
  fee : UInt64
  units : UInt64
  /-- the compute-unit limit the transaction ran under -/
  limit : UInt64
  logs : Array String
  returnData : ByteArray
  bank : Bank
  /-- on a failure inside a program: the machine's own account of it (a diagnostic, not part of the outcome) -/
  why : String
  /-- every instruction that ran, calls between programs included, in order -/
  frames : Array Sbpf.Frame

def u64 (v : UInt64) : ByteArray := Wire.putU64 (ByteArray.emptyWithCapacity 8) v

/-- The `SlotHashes` sysvar when only the current slot is known. -/
def slotHashes (slot : UInt64) (blockhash : ByteArray) : ByteArray :=
  if blockhash.size == 32 then u64 1 ++ u64 slot ++ blockhash else u64 0

def create (clock : Sbpf.Clock) : Bank :=
  ⟨Sbpf.Machine.create clock 200000, Array.emptyWithCapacity 16, ByteArray.empty, 5000⟩

def Bank.withBlockhash (bank : Bank) (blockhash : ByteArray) : Bank :=
  let m := bank.machine
  let sysvars := { m.sysvars with slotHashes := slotHashes m.clock.slot blockhash }
  { bank with blockhash := blockhash, machine := { m with sysvars := sysvars, blockhash := blockhash } }

def Bank.withClock (bank : Bank) (clock : Sbpf.Clock) : Bank :=
  let m := bank.machine
  let sysvars := { m.sysvars with slotHashes := slotHashes clock.slot bank.blockhash }
  { bank with machine := { m with clock := clock, sysvars := sysvars } }

def find (accounts : Array Sbpf.Account) (key : ByteArray) : Nat := Sbpf.findAccount accounts key

/-- Stores an account, replacing any at the same address. An account with no lamports ceases to exist. -/
def Bank.set (bank : Bank) (account : Sbpf.Account) : Bank := Id.run do
  let at_ := find bank.accounts account.key
  if account.lamports == 0 then
    if at_ == Sbpf.notFound then
      return bank
    -- remove: move the last account into its place
    let last := bank.accounts[bank.accounts.size - 1]!
    return { bank with accounts := (bank.accounts.set! at_ last).pop }
  if at_ == Sbpf.notFound then
    return { bank with accounts := bank.accounts.push account }
  return { bank with accounts := bank.accounts.set! at_ account }

/-- Deploys a program: registers its code and stores the account that stands for it. -/
def Bank.addProgram (bank : Bank) (id : ByteArray) (program : Sbpf.Program) : Bank :=
  ({ bank with machine := bank.machine.add id program }).set (Sbpf.programAccount id)

def hasProgram (bank : Bank) (id : ByteArray) : Bool := bank.machine.find id != Sbpf.notFound

/-- Programs live in accounts. For each of `keys` that is a program account
of the loader, the code in its program data account is loaded and registered,
callable from the slot after it was deployed. A program whose data account
was closed stops being callable. With `all` unset, programs that are already
registered are left alone; with it, they are read again where their data
account is among the accounts. -/
def Bank.withPrograms (bank : Bank) (keys : Array ByteArray) (all : Bool) : Bank := Id.run do
  let mut out := bank
  for key in keys do
    let at_ := find out.accounts key
    if at_ != Sbpf.notFound then
      let account := out.accounts[at_]!
      if (account.owner == loaderV2 || account.owner == loaderV1) && account.executable && (all || !(hasProgram out key)) then
        -- the older loaders: the account's data is the program (and the first loader's programs take their input packed)
        let program := Sbpf.parse account.data
        out := { out with machine := out.machine.add key { program with since := (if program.error != "" then 0xFFFFFFFFFFFFFFFF else 0), packed := account.owner == loaderV1 } }
      else if account.owner == Sbpf.loaderId && Sbpf.loaderKind account == 2
          && (!(hasProgram out key) || (all && find out.accounts (account.data.extract 4 36) != Sbpf.notFound)) then
        -- (a registered program is read again only if its code is at hand: whatever changed it had to name it)
        let holder := find out.accounts (account.data.extract 4 36)
        let code := if holder == Sbpf.notFound then ByteArray.empty else out.accounts[holder]!.data
        let program := if code.size > 45 && Wire.u32 code 0 == 3 then Sbpf.parse (code.extract 45 code.size)
          else Sbpf.Program.failed ByteArray.empty "the program was closed"
        if program.error != "" then
          -- cannot run: every call to it is refused
          out := { out with machine := out.machine.add key { program with since := 0xFFFFFFFFFFFFFFFF, holderSize := code.size } }
        else
          out := { out with machine := out.machine.add key { program with since := Wire.u64 code 4 + 1, holderSize := code.size } }
  return out

-- ------------------------------------------------------------------- sysvars

/-- A sysvar account: one lamport, owned by the sysvar address, holding the
value in a buffer of the sysvar's fixed size. -/
def sysvarAccount (key value : ByteArray) (size : Nat) : Sbpf.Account :=
  ⟨key, Sbpf.sysvarOwner, 1, Sbpf.zeros value (size - value.size), false⟩

/-- `SlotHistory`: a bit for each of the last 1,048,576 slots, saying whether
a block was produced in it, and the next slot. Here: only slot 0. -/
def slotHistory : ByteArray := Id.run do
  let mut b := ((ByteArray.emptyWithCapacity 131097).push 1) ++ u64 16384 ++ u64 1
  b := Sbpf.zeros b (16383 * 8)
  return b ++ u64 1048576 ++ u64 1

/-- The account at one of the sysvar addresses, or an account with an empty key if `key` is not one. -/
def sysvar (bank : Bank) (key : ByteArray) : Sbpf.Account :=
  let m := bank.machine
  let cached := Sbpf.sysvarBytes m key
  if cached.size != 0 then sysvarAccount key cached cached.size
  else if key == feesSysvar then sysvarAccount key (u64 0) 8
  else if key == recentBlockhashesSysvar then
    sysvarAccount key (if bank.blockhash.size == 32 then u64 1 ++ bank.blockhash ++ u64 0 else u64 0) 6008
  else if key == slotHistorySysvar then sysvarAccount key slotHistory 131097
  else ⟨ByteArray.empty, ByteArray.empty, 0, ByteArray.empty, false⟩

def builtin (name : String) (key : ByteArray) : Sbpf.Account :=
  ⟨key, Sbpf.nativeLoader, 1, name.toUTF8, true⟩

/-- The account at `key`: one that was stored, a sysvar, a built-in program,
or, for an address nothing was ever sent to, an empty account owned by the
system program. -/
def Bank.get (bank : Bank) (key : ByteArray) : Sbpf.Account :=
  let at_ := find bank.accounts key
  if at_ != Sbpf.notFound then bank.accounts[at_]!
  else if key == Sbpf.systemProgram then builtin "system_program" key
  else if key == Sbpf.computeBudgetProgram then builtin "compute_budget_program" key
  else if key == Sbpf.loaderId then builtin "solana_bpf_loader_upgradeable_program" key
  else if key == loaderV2 then builtin "solana_bpf_loader_program" key
  else if key == loaderV1 then builtin "solana_bpf_loader_deprecated_program" key
  else if key == ed25519Program then builtin "ed25519_program" key
  else
    let s := sysvar bank key
    if s.key.size == 32 then s else ⟨key, Sbpf.systemProgram, 0, ByteArray.empty, false⟩

/-- Addresses a transaction can never write to, whatever it asks for: the sysvars and the built-in programs. -/
def reserved (key : ByteArray) : Bool :=
  key == Sbpf.systemProgram || key == Sbpf.computeBudgetProgram || key == Sbpf.nativeLoader || key == Sbpf.loaderId
  || key == Sbpf.sysvarOwner || key == Sbpf.clockSysvar || key == Sbpf.rentSysvar || key == Sbpf.epochScheduleSysvar
  || key == Sbpf.epochRewardsSysvar || key == Sbpf.slotHashesSysvar || key == Sbpf.stakeHistorySysvar
  || key == Sbpf.lastRestartSlotSysvar || key == instructionsSysvar || key == feesSysvar
  || key == recentBlockhashesSysvar || key == slotHistorySysvar || key == ed25519Program || key == secp256k1Program
  || key == secp256r1Program || key == lookupTableProgram || key == voteProgram || key == stakeProgram
  || key == configProgram || key == loaderV2 || key == loaderV1 || key == loaderV4

/-- The `Instructions` sysvar: the transaction's own instructions, so a
program can check what else is in the transaction it is part of. Offsets of
the instructions, then each one (accounts with their rights, program, data),
then the index of the instruction now running, updated as they run. -/
def instructionsData (keys : Array ByteArray) (signers : Nat) (writable : Array Bool) (ixs : Array Tx.Compiled) : ByteArray := Id.run do
  let mut b := Wire.putU16 (ByteArray.emptyWithCapacity 256) ixs.size.toUInt64
  for _ in ixs do
    b := Wire.putU16 b 0
  for i in [0:ixs.size] do
    let ix := ixs[i]!
    b := Sbpf.storeAt b (2 + 2 * i) 2 b.size.toUInt64
    b := Wire.putU16 b ix.accounts.size.toUInt64
    for index in ix.accounts do
      let k := index.toNat
      b := b.push ((if k < signers then 1 else 0) ||| (if writable[k]! then 2 else 0))
      b := b ++ keys[k]!
    b := b ++ keys[ix.program]!
    b := Wire.putU16 b ix.data.size.toUInt64
    b := b ++ ix.data
  return Wire.putU16 b 0

-- ---------------------------------------------------------------------- rent

/-- The smallest balance at which an account with `size` bytes of data is
exempt from rent. Every account must hold at least this, or nothing. -/
def minimumBalance (bank : Bank) (size : Nat) : UInt64 := bank.machine.rentMinimum size

/-- May an account go from (`lamportsBefore`, `sizeBefore`) to
(`lamports`, `size`)? It may end empty or rent-exempt. It may stay below
the exempt minimum only if it was already there, did not change size and
was not given more. -/
def rentAllowed (bank : Bank) (lamportsBefore : UInt64) (sizeBefore : Nat) (lamports : UInt64) (size : Nat) : Bool :=
  if lamports == 0 || lamports >= minimumBalance bank size then true
  else if lamportsBefore == 0 || lamportsBefore >= minimumBalance bank sizeBefore then false
  else size == sizeBefore && lamports <= lamportsBefore

-- -------------------------------------------------------------------- errors

/-- Agave's name for an error code a program returned. -/
def programError (r0 : UInt64) : String :=
  let names : Array String := #["", "", "InvalidArgument", "InvalidInstructionData", "InvalidAccountData",
    "AccountDataTooSmall", "InsufficientFunds", "IncorrectProgramId", "MissingRequiredSignature",
    "AccountAlreadyInitialized", "UninitializedAccount", "NotEnoughAccountKeys", "AccountBorrowFailed",
    "MaxSeedLengthExceeded", "InvalidSeeds", "BorshIoError", "AccountNotRentExempt", "UnsupportedSysvar",
    "IllegalOwner", "MaxAccountsDataAllocationsExceeded", "InvalidRealloc", "MaxInstructionTraceLengthExceeded",
    "BuiltinProgramsMustConsumeComputeUnits", "InvalidAccountOwner", "ArithmeticOverflow", "Immutable",
    "IncorrectAuthority"]
  let code := (r0 >>> 32).toNat
  if r0 >>> 32 == 0 then s!"Custom({r0})"
  else if r0 &&& 0xFFFFFFFF != 0 || code >= names.size then "InvalidError"
  else if code == 1 then "Custom(0)"
  else names[code]!

/-- Agave's name for the way an instruction failed. -/
def instructionError (st : Sbpf.State) : String :=
  let s := st.status
  if s == Sbpf.programFailed then programError st.r0
  else if s == Sbpf.meterExceeded then "ComputationalBudgetExceeded"
  else if s == Sbpf.runtimeError then st.detail
  else if s == Sbpf.privilegeEscalation then "PrivilegeEscalation"
  else if s == Sbpf.missingAccount || s == Sbpf.unknownProgram then "MissingAccount"
  else if s == Sbpf.unbalanced then "UnbalancedInstruction"
  else if s == Sbpf.invalidRealloc then "InvalidRealloc"
  else if s == Sbpf.callDepthExceeded && st.detail != "" then "CallDepth"
  else if s == Sbpf.accountRule then
    if st.detail == Sbpf.ruleExecutable then "ExecutableDataModified"
    else if st.detail == Sbpf.ruleSpend then "ExternalAccountLamportSpend"
    else if st.detail == Sbpf.ruleReadOnlyBalance then "ReadonlyLamportChange"
    else if st.detail == Sbpf.ruleReadOnly then "ReadonlyDataModified"
    else if st.detail == Sbpf.ruleData then "ExternalAccountDataModified"
    else if st.detail == Sbpf.ruleOwner then "ModifiedProgramId"
    else "ReadonlyLamportChange"
  else "ProgramFailedToComplete"

-- ---------------------------------------------------- signature verification
--
-- The Ed25519 program is not bytecode and does not run in the machine: its
-- instruction data lists signatures to check, each given by where the
-- signature, the public key and the message sit in the data of some
-- instruction of the same transaction. A program can then look at the
-- transaction's instructions and know that a signature it cares about was
-- verified, without paying to verify it itself.

/-- The bytes `[offset, offset + size)` of the data of instruction `index`
(0xFFFF = the instruction itself), or `none` if they are not all there. -/
def precompileSlice (datas : Array ByteArray) (current : Nat) (index offset size : UInt64) : Option ByteArray :=
  let which := if index == 0xFFFF then current else index.toNat
  if which >= datas.size then none
  else if (offset + size).toNat > datas[which]!.size then none
  else some (datas[which]!.extract offset.toNat (offset + size).toNat)

/-- Checks the signatures an Ed25519 program instruction lists. Returns 0 if
all are valid, otherwise 1 + the program's error code (0 = invalid public
key, 2 = invalid signature, 3 = invalid offsets, 4 = invalid data size). -/
def verifyEd25519 (datas : Array ByteArray) (current : Nat) : UInt64 := Id.run do
  let data := datas[current]!
  if data.size < 2 then
    return 5
  let count := data[0]!.toNat
  if (count == 0 && data.size > 2) || data.size < 2 + 14 * count then
    return 5
  for k in [0:count] do
    let o := 2 + 14 * k
    match precompileSlice datas current (Wire.u16 data (o + 2)) (Wire.u16 data o) 64,
        precompileSlice datas current (Wire.u16 data (o + 6)) (Wire.u16 data (o + 4)) 32,
        precompileSlice datas current (Wire.u16 data (o + 12)) (Wire.u16 data (o + 8)) (Wire.u16 data (o + 10)) with
    | some signature, some key, some message =>
      if (Ed25519.Point.decode key).isNone then
        return 1
      if !(Ed25519.verify key signature message) then
        return 3
    | _, _, _ => return 4
  return 0

/-- One P-256 signature: 0 if it is valid, otherwise 1 + the program's error code. -/
def checkSecp256r1 (signature key message : ByteArray) : UInt64 :=
  if !(P256.inRange signature) then 3
  else
    match P256.decode key with
    | none => 1
    | some point => if P256.verify point signature message then 0 else 3

/-- Checks the signatures a secp256r1 program instruction lists (at most
eight; laid out as for Ed25519, with a 33-byte key). Returns 0 if all are
valid, otherwise 1 + the program's error code. -/
def verifySecp256r1 (datas : Array ByteArray) (current : Nat) : UInt64 := Id.run do
  let data := datas[current]!
  if data.size < 2 then
    return 5
  let count := data[0]!.toNat
  if count == 0 || count > 8 || data.size < 2 + 14 * count then
    return 5
  for k in [0:count] do
    let o := 2 + 14 * k
    match precompileSlice datas current (Wire.u16 data (o + 2)) (Wire.u16 data o) 64,
        precompileSlice datas current (Wire.u16 data (o + 6)) (Wire.u16 data (o + 4)) 33,
        precompileSlice datas current (Wire.u16 data (o + 12)) (Wire.u16 data (o + 8)) (Wire.u16 data (o + 10)) with
    | some signature, some key, some message =>
      let result := checkSecp256r1 signature key message
      if result != 0 then
        return result
    | _, _, _ => return 4
  return 0

/-- Checks the signatures a secp256k1 program instruction lists: each names
a 64-byte signature followed by a recovery byte, a 20-byte Ethereum address
and a message, anywhere in the transaction's instructions; the key recovered
from the signature over the message's Keccak hash must hash to the address.
Returns 0 if all hold, otherwise 1 + the program's error code (1 = invalid
recovery byte, 2 = invalid signature, 3 = invalid offsets, 4 = invalid data
size). -/
def verifySecp256k1 (datas : Array ByteArray) (current : Nat) : UInt64 := Id.run do
  let data := datas[current]!
  if data.size == 0 then
    return 5
  let count := data[0]!.toNat
  if (count == 0 && data.size > 1) || data.size < 1 + 11 * count then
    return 5
  for k in [0:count] do
    let o := 1 + 11 * k
    let signatureAt := (Wire.u16 data o).toNat
    let signatureIn := data[o + 2]!.toNat
    if signatureIn >= datas.size then
      return 5
    let holder := datas[signatureIn]!
    if signatureAt + 64 >= holder.size then
      return 3
    let signature := holder.extract signatureAt (signatureAt + 64)
    if Secp256k1.atLeast (Secp256k1.ofBytes signature 0) Secp256k1.n
        || Secp256k1.atLeast (Secp256k1.ofBytes signature 32) Secp256k1.n then
      return 3
    let recovery := holder[signatureAt + 64]!.toNat
    if recovery > 3 then
      return 2
    let addressIn := data[o + 5]!.toNat
    let messageIn := data[o + 10]!.toNat
    if addressIn >= datas.size then
      return 4
    let addressAt := (Wire.u16 data (o + 3)).toNat
    if addressAt + 20 > datas[addressIn]!.size then
      return 3
    if messageIn >= datas.size then
      return 4
    let messageAt := (Wire.u16 data (o + 6)).toNat
    let messageSize := (Wire.u16 data (o + 8)).toNat
    if messageAt + messageSize > datas[messageIn]!.size then
      return 3
    let hash := Keccak.hash (datas[messageIn]!.extract messageAt (messageAt + messageSize))
    let key := Secp256k1.recover hash recovery signature
    if key.size != 64 then
      return 3
    let address := (Keccak.hash key).extract 12 32
    if address != datas[addressIn]!.extract addressAt (addressAt + 20) then
      return 3
  return 0

-- ---------------------------------------------------------------- processing

def refuse (bank : Bank) (why : String) : Receipt :=
  ⟨why, false, 0, 0, 0, Array.emptyWithCapacity 0, ByteArray.empty, bank, "", Array.emptyWithCapacity 0⟩

/-- Is this one of the programs that are part of the runtime? They are given a
smaller default compute budget than programs that run as bytecode. -/
def isBuiltin (key : ByteArray) : Bool :=
  key == Sbpf.systemProgram || key == Sbpf.computeBudgetProgram || key == voteProgram || key == Sbpf.loaderId
  || key == loaderV1 || key == loaderV2 || key == loaderV4 || key == secp256k1Program || key == ed25519Program

/-- Applies a transaction to the bank. With `verify`, the signatures are checked first. -/
def Bank.process (bank : Bank) (tx : Tx.Transaction) (verify : Bool) : Receipt := Id.run do
  let msg := tx.message
  -- 1. is it well formed?
  if tx.error != "" || msg.signers == 0 || tx.signatures.size != msg.signers || msg.signers > msg.keys.size
      || msg.readonlySigned >= msg.signers || msg.readonlyUnsigned + msg.signers > msg.keys.size
      || msg.blockhash.size != 32 then
    return refuse bank "SanitizeFailure"
  if verify && !tx.verify then
    return refuse bank "SignatureFailure"
  -- the accounts of the message: its own keys, then those it takes from address tables
  let mut keys := msg.keys
  let mut writable : Array Bool := Array.emptyWithCapacity (keys.size + 8)
  for i in [0:keys.size] do
    writable := writable.push (if i < msg.signers then i < msg.signers - msg.readonlySigned
      else i < keys.size - msg.readonlyUnsigned)
  for pass in [0:2] do
    for l in msg.lookups do
      let table := bank.get l.table
      if table.lamports == 0 then
        return refuse bank "AddressLookupTableNotFound"
      if table.owner != lookupTableProgram || table.data.size < 56 then
        return refuse bank "InvalidAddressLookupTableOwner"
      -- A table that was deactivated stays usable only while its deactivation slot is still among the recent
      -- slots. Addresses added in the current slot are not usable until the next one.
      let deactivated := Wire.u64 table.data 4
      if deactivated != 0xFFFFFFFFFFFFFFFF && deactivated != bank.machine.clock.slot then
        let recent := bank.machine.sysvars.slotHashes
        let mut found := false
        for k in [0:(Wire.u64 recent 0).toNat] do
          if Wire.u64 recent (8 + 40 * k) == deactivated then
            found := true
        if !found then
          return refuse bank "AddressLookupTableNotFound"
      let entries := if bank.machine.clock.slot > Wire.u64 table.data 12 then (table.data.size - 56) / 32
        else (Wire.u8 table.data 20).toNat
      let wanted := if pass == 0 then l.writable else l.readonly
      for index in wanted do
        let at_ := 56 + 32 * index.toNat
        if index.toNat >= entries || at_ + 32 > table.data.size then
          return refuse bank "InvalidAddressLookupTableIndex"
        keys := keys.push (table.data.extract at_ (at_ + 32))
        writable := writable.push (pass == 0)
  if keys.size > 256 then
    return refuse bank "SanitizeFailure"
  for i in [0:keys.size] do
    for j in [0:i] do
      if keys[i]! == keys[j]! then
        return refuse bank "AccountLoadedTwice"
  let mut loaderPresent := false
  for key in keys do
    if key == Sbpf.loaderId then
      loaderPresent := true
  for ix in msg.instructions do
    if ix.program >= keys.size || ix.program == 0 then
      return refuse bank "SanitizeFailure"
    for index in ix.accounts do
      if index.toNat >= keys.size then
        return refuse bank "SanitizeFailure"
  -- an account is writable only if the message says so and the runtime allows it
  for i in [0:keys.size] do
    if reserved keys[i]! then
      writable := writable.set! i false
  if !loaderPresent then
    for ix in msg.instructions do
      writable := writable.set! ix.program false
  -- The blockhash must be the latest one, or the value held by a nonce account that the first instruction
  -- advances (so that the transaction, signed whenever, works once and only once).
  let mut nonceAt := Sbpf.notFound
  if bank.blockhash.size == 32 && msg.blockhash != bank.blockhash then
    if msg.instructions.size != 0 then
      let first := msg.instructions[0]!
      if keys[first.program]! == Sbpf.systemProgram && first.data.size >= 4 && Wire.u32 first.data 0 == 4
          && first.accounts.size != 0 then
        let at_ := first.accounts[0]!.toNat
        let account := bank.get keys[at_]!
        let mut authorized := false
        for index in first.accounts do
          if index.toNat < msg.signers && keys[index.toNat]! == account.data.extract 8 40 then
            authorized := true
        if writable[at_]! && account.owner == Sbpf.systemProgram && Sbpf.nonceKind account.data == 2
            && account.data.extract 40 72 == msg.blockhash && authorized
            && msg.blockhash != Sbpf.durableNonce bank.blockhash then
          nonceAt := at_
    if nonceAt == Sbpf.notFound then
      return refuse bank "BlockhashNotFound"

  -- 2. the compute budget the transaction asks for
  let mut limit : UInt64 := 0
  let mut limitSet := false
  let mut price : UInt64 := 0
  let mut priceSet := false
  let mut heap : UInt64 := 32768
  let mut heapAt := Sbpf.notFound
  let mut loadedSet := false
  -- how much account data the transaction may load: 64 MiB unless it says otherwise
  let mut loadedLimit : UInt64 := 67108864
  let mut signatures := msg.signers.toUInt64
  for i in [0:msg.instructions.size] do
    let ix := msg.instructions[i]!
    let program := keys[ix.program]!
    if program == Sbpf.computeBudgetProgram then
      let tag := Wire.u8 ix.data 0
      let invalid := s!"InstructionError({i}, InvalidInstructionData)"
      if tag == 1 && ix.data.size >= 5 then
        if heapAt != Sbpf.notFound then
          return refuse bank s!"DuplicateInstruction({i})"
        heap := Wire.u32 ix.data 1
        heapAt := i
      else if tag == 2 && ix.data.size >= 5 then
        if limitSet then
          return refuse bank s!"DuplicateInstruction({i})"
        limit := Wire.u32 ix.data 1
        limitSet := true
      else if tag == 3 && ix.data.size >= 9 then
        if priceSet then
          return refuse bank s!"DuplicateInstruction({i})"
        price := Wire.u64 ix.data 1
        priceSet := true
      else if tag == 4 && ix.data.size >= 5 then
        if loadedSet then
          return refuse bank s!"DuplicateInstruction({i})"
        if Wire.u32 ix.data 1 == 0 then
          return refuse bank "InvalidLoadedAccountsDataSizeLimit"
        loadedSet := true
        loadedLimit := min (Wire.u32 ix.data 1) 67108864
      else
        return refuse bank invalid
    else if program == ed25519Program || program == secp256k1Program || program == secp256r1Program then
      -- signatures these programs verify are paid for like the transaction's own
      signatures := signatures + Wire.u8 ix.data 0
  if heapAt != Sbpf.notFound && (heap < 32768 || heap > 262144 || heap % 1024 != 0) then
    return refuse bank s!"InstructionError({heapAt}, InvalidInstructionData)"
  -- A version-1 message carries its budget itself: a mask saying which settings are present, then the
  -- settings. What is absent is zero (the heap: the usual 32 KiB), and the priority fee is a sum, not a price.
  let mut feeGiven : UInt64 := 0
  if msg.v1 then
    let mask := Wire.u32 msg.config 0
    let mut o := 4
    limit := 0
    limitSet := true
    loadedLimit := 0
    if mask &&& 3 != 0 then
      feeGiven := Wire.u64 msg.config o
      o := o + 8
    if mask &&& 4 != 0 then
      limit := Wire.u32 msg.config o
      o := o + 4
    if mask &&& 8 != 0 then
      loadedLimit := min (Wire.u32 msg.config o) 67108864
      o := o + 4
    if mask &&& 16 != 0 then
      heap := Wire.u32 msg.config o
      if heap < 32768 || heap > 262144 || heap % 1024 != 0 then
        return refuse bank "InvalidTransactionConfig"
  if !limitSet then
    -- by default: 200,000 units per instruction, 3,000 for those of built-in programs
    for ix in msg.instructions do
      limit := limit + (if isBuiltin keys[ix.program]! then 3000 else 200000)
  if limit > 1400000 then
    limit := 1400000

  -- 3. the fee: per signature, plus the price offered for every unit of the limit, in millionths of a lamport
  let priority := if msg.v1 then feeGiven
    else if price > 0xFFFFFFFFFFFFFFFF / 1400000 then 0xFFFFFFFFFFFFFFFF else (price * limit + 999999) / 1000000
  let fee := if priority > 0xFFFFFFFFFFFFFFFF - bank.lamportsPerSignature * signatures then 0xFFFFFFFFFFFFFFFF
    else bank.lamportsPerSignature * signatures + priority
  -- programs deployed through the loader are run from their accounts
  let bank := bank.withPrograms keys false
  let payer := bank.get keys[0]!
  if payer.lamports == 0 then
    return ⟨"AccountNotFound", false, fee, 0, limit, Array.emptyWithCapacity 0, ByteArray.empty, bank, "", Array.emptyWithCapacity 0⟩
  -- the payer is a wallet, or a nonce account, which must keep enough to stay alive
  let payerIsNonce := payer.data.size == 80 && Sbpf.nonceKind payer.data == 2
  if payer.owner != Sbpf.systemProgram || (payer.data.size != 0 && !payerIsNonce) then
    return ⟨"InvalidAccountForFee", false, fee, 0, limit, Array.emptyWithCapacity 0, ByteArray.empty, bank, "", Array.emptyWithCapacity 0⟩
  if payer.lamports < fee || (payerIsNonce && payer.lamports - fee < minimumBalance bank 80) then
    return ⟨"InsufficientFundsForFee", false, fee, 0, limit, Array.emptyWithCapacity 0, ByteArray.empty, bank, "", Array.emptyWithCapacity 0⟩
  if !(rentAllowed bank payer.lamports payer.data.size (payer.lamports - fee) payer.data.size) then
    return ⟨"InsufficientFundsForRent { account_index: 0 }", false, fee, 0, limit, Array.emptyWithCapacity 0, ByteArray.empty, bank, "", Array.emptyWithCapacity 0⟩
  -- From here on the fee is paid, whatever happens. First, what the transaction loads must fit in what it
  -- allowed itself: 8248 bytes for every address table, then for every account that exists 64 bytes and
  -- its data; a program whose code is kept in a second account is charged for that one too (once, and
  -- not if the transaction names it itself).
  let mut loadError := ""
  let mut loaded : UInt64 := 8248 * msg.lookups.size.toUInt64
  let mut holders : Array ByteArray := Array.emptyWithCapacity 4
  for key in keys do
    if loadError == "" && key != instructionsSysvar then
      let account := bank.get key
      if account.lamports != 0 then
        loaded := loaded + 64 + account.data.size.toUInt64
        if account.owner == Sbpf.loaderId && Sbpf.loaderKind account == 2 then
          let holder := account.data.extract 4 36
          let mut counted := false
          for other in keys do
            if other == holder then
              counted := true
          for other in holders do
            if other == holder then
              counted := true
          if !counted then
            holders := holders.push holder
            -- its size: as noted when the program was read, or the account's own if it is at hand
            let mut size := (bank.get holder).data.size
            if find bank.accounts holder == Sbpf.notFound then
              let known := bank.machine.find key
              if known != Sbpf.notFound then
                size := bank.machine.programs[known]!.holderSize
            if size != 0 then
              loaded := loaded + 64 + size.toUInt64
      if loaded > loadedLimit then
        loadError := "MaxLoadedAccountsDataSizeExceeded"
  -- and every program named must exist
  for ix in msg.instructions do
    let program := keys[ix.program]!
    if loadError == "" && !(program == Sbpf.systemProgram || program == Sbpf.computeBudgetProgram || program == ed25519Program
        || program == secp256k1Program || program == secp256r1Program || program == Sbpf.loaderId || program == loaderV1 || program == loaderV2
        || program == voteProgram || hasProgram bank program) then
      loadError := if (bank.get program).lamports == 0 then "ProgramAccountNotFound" else "InvalidProgramForExecution"
  let charged := bank.set { payer with lamports := payer.lamports - fee }

  -- 4. the instructions, in order, on the accounts as the previous one left them
  let mut accounts : Array Sbpf.Account := Array.emptyWithCapacity keys.size
  let mut sysvarAt := Sbpf.notFound
  for i in [0:keys.size] do
    if keys[i]! == instructionsSysvar then
      sysvarAt := i
      accounts := accounts.push ⟨keys[i]!, Sbpf.sysvarOwner, 0, instructionsData keys msg.signers writable msg.instructions, false⟩
    else
      accounts := accounts.push (charged.get keys[i]!)
  let before := accounts
  let mut datas : Array ByteArray := Array.emptyWithCapacity msg.instructions.size
  for ix in msg.instructions do
    datas := datas.push ix.data
  let machine := { bank.machine with budget := (if bank.machine.cap != 0 && bank.machine.cap < limit then bank.machine.cap else limit), heap := heap.toNat }
  let mut st : Sbpf.State := ⟨accounts, 0, Array.emptyWithCapacity 8, ByteArray.empty, Sbpf.finished, 0, "", Array.emptyWithCapacity 8⟩
  let mut error := loadError
  for i in [0:msg.instructions.size] do
    if error == "" then
      let ix := msg.instructions[i]!
      let program := keys[ix.program]!
      let mut metas : Array Sbpf.Meta := Array.emptyWithCapacity ix.accounts.size
      for index in ix.accounts do
        metas := metas.push ⟨index.toNat, index.toNat < msg.signers, writable[index.toNat]!⟩
      if sysvarAt != Sbpf.notFound then
        -- tell the Instructions sysvar which instruction is running
        let account := st.accounts[sysvarAt]!
        let data := Sbpf.storeAt account.data (account.data.size - 2) 2 i.toUInt64
        st := { st with accounts := st.accounts.set! sysvarAt { account with data := data } }
      if program == ed25519Program then
        st := { st with trace := st.trace.push ⟨1, program, metas, ix.data⟩ }
        let result := verifyEd25519 datas i
        if result != 0 then
          error := s!"InstructionError({i}, Custom({result - 1}))"
      else if program == secp256k1Program then
        st := { st with trace := st.trace.push ⟨1, program, metas, ix.data⟩ }
        let result := verifySecp256k1 datas i
        if result != 0 then
          error := s!"InstructionError({i}, Custom({result - 1}))"
      else if program == secp256r1Program then
        st := { st with trace := st.trace.push ⟨1, program, metas, ix.data⟩ }
        let result := verifySecp256r1 datas i
        if result != 0 then
          error := s!"InstructionError({i}, Custom({result - 1}))"
      else
        st := Sbpf.execute machine st program metas ix.data 1
        if st.status != Sbpf.finished then
          error := s!"InstructionError({i}, {instructionError st})"

  -- 5. nobody may be left with too little to be exempt from rent (the incinerator may: it keeps nothing)
  if error == "" then
    for i in [0:keys.size] do
      if error == "" && writable[i]! && keys[i]! != incinerator then
        let was := bank.get keys[i]!
        let now := st.accounts[i]!
        if !(rentAllowed bank was.lamports was.data.size now.lamports now.data.size) then
          error := s!"InsufficientFundsForRent \{ account_index: {i} }"

  -- 6. keep everything, or only the fee (and the advance of the nonce, if one was used)
  let mut after := charged
  if error != "" && nonceAt != Sbpf.notFound then
    let account := charged.get keys[nonceAt]!
    let state := Sbpf.nonceState (account.data.extract 8 40) (Sbpf.durableNonce bank.blockhash) bank.lamportsPerSignature
    after := after.set { account with data := state.copySlice 0 account.data 0 80 }
  let mut loaderTouched := false
  if error == "" then
    for i in [0:keys.size] do
      if writable[i]! && (st.accounts[i]!.lamports != before[i]!.lamports || st.accounts[i]!.data != before[i]!.data
          || st.accounts[i]!.owner != before[i]!.owner) then
        after := after.set st.accounts[i]!
        if st.accounts[i]!.owner == Sbpf.loaderId || before[i]!.owner == Sbpf.loaderId then
          loaderTouched := true
  if error == "" && loaderTouched then
    -- programs this transaction deployed, upgraded or closed
    after := after.withPrograms keys true
  -- 7. the programs that ran have run once more: those that have now run often enough are translated
  -- into machine code (`Sbpf.Program.used`)
  for frame in st.trace do
    let which := after.machine.find frame.program
    if which != Sbpf.notFound then
      let p := after.machine.programs[which]!
      if p.native == 0 && p.uses != Sbpf.settled then
        let m := after.machine
        after := { after with machine := { m with programs := m.programs.set! which p.used } }
  -- for whoever is looking into a failure: how the machine stopped, in its own words
  let why := if error == "" then "" else s!"status {st.status}, r0 {st.r0}: {st.detail}"
  return ⟨error, true, fee, st.units, limit, st.logs, st.returnData, after, why, st.trace⟩

end Bank
