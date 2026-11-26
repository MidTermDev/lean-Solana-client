import Solana.SbpfBase

/-!
# Programs that are part of the runtime

Most programs are bytecode in an account. A few are not: they are built
into the validator and run as native code, because everything else needs
them. This file is those programs, written in Lean. Each takes the state, the
accounts an instruction refers to and its data, and returns the new state,
exactly like a bytecode program run by the interpreter.

* **System**: creates accounts, moves lamports, assigns ownership, and keeps
  nonce accounts, which let a transaction be signed now and sent much later.
-/

namespace Sbpf

/-- Fails with one of the standard program errors (2 = InvalidArgument, 3 =
InvalidInstructionData, 4 = InvalidAccountData, 5 = AccountDataTooSmall, 6 =
InsufficientFunds, 8 = MissingRequiredSignature, 11 = NotEnoughAccountKeys,
23 = InvalidAccountOwner). -/
def programError (st : State) (code : UInt64) : State :=
  { st with status := programFailed, r0 := code <<< 32 }

/-- Fails with a program's own numbered error (`Custom(code)`). -/
def customError (st : State) (code : UInt64) : State :=
  { st with status := programFailed, r0 := if code == 0 then 0x100000000 else code }

/-- The system program's errors: 0 = account already in use, 1 = not enough
lamports, 3 = data length too large, 5 = address does not match its seed,
6 = no recent blockhash, 7 = the nonce is still current. -/
def systemError (st : State) (code : UInt64) : State := customError st code

/-- Did the holder of `key` sign? True if any account the instruction refers to as a signer has that key. -/
def signedBy (st : State) (metas : Array Meta) (key : ByteArray) : Bool := Id.run do
  for mt in metas do
    if mt.signer && st.accounts[mt.index]!.key == key then
      return true
  return false

def keyOf (st : State) (mt : Meta) : ByteArray := st.accounts[mt.index]!.key

-- ------------------------------------------------------- the system program

/-- The system program's `allocate` followed by `assign`: gives an empty,
system-owned account `space` zero bytes and hands it to `owner`. The account
itself must sign: nobody else can decide what an address becomes. -/
def allocateAndAssign (st : State) (target : Meta) (space : UInt64) (owner : ByteArray) (assign : Bool) : State :=
  let account := st.accounts[target.index]!
  if !target.signer then programError st 8
  else if account.data.size != 0 || account.owner != systemProgram then systemError st 0
  else if space > 10485760 then systemError st 3
  else if !target.writable then st.stop accountRule ruleReadOnly
  else
    let sized : Account := { account with data := zeros ByteArray.empty space.toNat }
    let owned : Account := if assign then { sized with owner := owner } else sized
    { st with accounts := st.accounts.set! target.index owned }

/-- The system program's `assign`: hands an account it owns to another program. -/
def assignOwner (st : State) (target : Meta) (owner : ByteArray) : State :=
  let account := st.accounts[target.index]!
  if account.owner == owner then st
  else if !target.signer then programError st 8
  else if account.owner != systemProgram || !target.writable then st.stop accountRule ruleOwner
  else { st with accounts := st.accounts.set! target.index { account with owner := owner } }

/-- The system program's `transfer`: lamports from a signing, data-less, system-owned account to any account. -/
def systemTransfer (st : State) (source dest : Meta) (amount : UInt64) : State :=
  let from_ := st.accounts[source.index]!
  if !source.signer then programError st 8
  else if from_.data.size != 0 then programError st 2
  else if amount > from_.lamports then systemError st 1
  else if from_.owner != systemProgram then st.stop accountRule ruleSpend
  else if !source.writable || !dest.writable then st.stop accountRule ruleReadOnlyBalance
  else
    let accounts := st.accounts.set! source.index { from_ with lamports := from_.lamports - amount }
    let to := accounts[dest.index]!
    { st with accounts := accounts.set! dest.index { to with lamports := to.lamports + amount } }

/-- An address derived from another: the hash of a base address, a seed
string and an owner. Whoever holds the base key controls every address
derived from it, without a key of its own. Returns the 32-byte address, or
one byte holding an error code (0 = seed too long, 2 = owner not allowed). -/
def seedAddress (base seed owner : ByteArray) : ByteArray :=
  let marker := "ProgramDerivedAddress".toUTF8
  if seed.size > 32 then ByteArray.empty.push 0
  else if Wire.eqAt owner (32 - marker.size) marker 0 marker.size then ByteArray.empty.push 2
  else Sha256.hash (base ++ seed ++ owner)

-- Nonce accounts. A transaction normally names a recent blockhash and is
-- only valid for about a minute. A nonce account stores a value that can
-- stand in for the blockhash for as long as it is not advanced: the
-- transaction's first instruction advances it, so it works exactly once.

def recentBlockhashesSysvar : ByteArray := Base58.decode "SysvarRecentB1ockHashes11111111111111111111"

/-- The value a nonce account stores for a blockhash. -/
def durableNonce (blockhash : ByteArray) : ByteArray := Sha256.hash ("DURABLE_NONCE".toUTF8 ++ blockhash)

/-- What a nonce account's data says: 0 = unreadable, 1 = uninitialized, 2 = initialized.
The data is a version (0 or 1), a state (0 or 1) and, if initialized, the
authority, the stored nonce and the fee rate when it was stored: 80 bytes. -/
def nonceKind (data : ByteArray) : Nat :=
  if data.size < 8 || Wire.u32 data 0 > 1 || Wire.u32 data 4 > 1 then 0
  else if Wire.u32 data 4 == 0 then 1
  else if data.size < 80 then 0
  else 2

def nonceState (authority nonce : ByteArray) (fee : UInt64) : ByteArray :=
  Wire.putU64 (Wire.putU32 (Wire.putU32 (ByteArray.emptyWithCapacity 80) 1) 1 ++ authority ++ nonce) fee

/-- Is account `index` of the instruction the sysvar with address `sysvar`?
Returns the program error to fail with, or 0. -/
def sysvarArgument (st : State) (metas : Array Meta) (index : Nat) (sysvar : ByteArray) : UInt64 :=
  if index >= metas.size then 11
  else if keyOf st metas[index]! != sysvar then 2
  else 0

def systemInstruction (m : Machine) (st : State) (metas : Array Meta) (data : ByteArray) : State := Id.run do
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
    return assignOwner st metas[0]! (data.extract 4 36)
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
  if tag == 3 || tag == 9 || tag == 10 then
    -- CreateAccountWithSeed, AllocateWithSeed, AssignWithSeed: the same three operations on an address
    -- derived from a base key and a seed. The base signs instead of the address, which has no key.
    -- Data: base, seed (length, bytes), then lamports and space as the operation needs, then owner.
    if data.size < 44 || Wire.u64 data 36 > data.size.toUInt64 then
      return programError st 3
    let rest := 44 + (Wire.u64 data 36).toNat
    let need := if tag == 3 then 48 else if tag == 9 then 40 else 32
    if data.size < rest + need then
      return programError st 3
    if metas.size < (if tag == 3 then 2 else 1) then
      return programError st 11
    let base := data.extract 4 36
    let owner := data.extract (rest + need - 32) (rest + need)
    let target := metas[if tag == 3 then 1 else 0]!
    let derived := seedAddress base (data.extract 44 rest) owner
    if derived.size != 32 then
      return customError st derived[0]!.toUInt64
    if derived != keyOf st target then
      return systemError st 5
    let asSigner : Meta := { target with signer := signedBy st metas base }
    if tag == 10 then
      return assignOwner st asSigner owner
    if tag == 9 then
      return allocateAndAssign st asSigner (Wire.u64 data rest) owner true
    if st.accounts[target.index]!.lamports > 0 then
      return systemError st 0
    let made := allocateAndAssign st asSigner (Wire.u64 data (rest + 8)) owner true
    if made.status != finished then
      return made
    return systemTransfer made metas[0]! target (Wire.u64 data rest)
  if tag == 11 then
    -- TransferWithSeed { lamports, seed, owner }: from an address derived from the base (account 1), which signs
    if data.size < 20 || Wire.u64 data 12 > data.size.toUInt64 || data.size < 52 + (Wire.u64 data 12).toNat then
      return programError st 3
    if metas.size < 3 then
      return programError st 11
    let rest := 20 + (Wire.u64 data 12).toNat
    if !metas[1]!.signer then
      return programError st 8
    let derived := seedAddress (keyOf st metas[1]!) (data.extract 20 rest) (data.extract rest (rest + 32))
    if derived.size != 32 then
      return customError st derived[0]!.toUInt64
    if derived != keyOf st metas[0]! then
      return systemError st 5
    let asSigner : Meta := { metas[0]! with signer := true }
    return systemTransfer st asSigner metas[2]! (Wire.u64 data 4)
  if tag == 4 || tag == 5 || tag == 6 || tag == 7 || tag == 12 then
    -- the nonce instructions; account 0 is the nonce account
    if metas.size < (if tag == 5 then 2 else 1) then
      return programError st 11
    let target := metas[0]!
    let account := st.accounts[target.index]!
    let kind := nonceKind account.data
    let stored := account.data.extract 40 72
    let current := durableNonce m.blockhash
    -- the sysvars these instructions must be handed, a leftover from before programs could ask for them
    let need := if tag == 4 || tag == 6 then sysvarArgument st metas 1 recentBlockhashesSysvar
      else if tag == 5 then sysvarArgument st metas 2 recentBlockhashesSysvar else 0
    if need != 0 then
      return programError st need
    let needRent := if tag == 5 then sysvarArgument st metas 3 rentSysvar
      else if tag == 6 then sysvarArgument st metas 2 rentSysvar else 0
    if needRent != 0 then
      return programError st needRent
    if (tag == 4 || tag == 6) && m.blockhash.size != 32 then
      return systemError st 6
    if tag == 12 && account.owner != systemProgram then
      return programError st 23
    if !target.writable then
      return programError st 2
    if tag == 5 then
      -- WithdrawNonceAccount(lamports): to account 1. Taking everything closes the nonce account.
      let amount := Wire.u64 data 4
      if data.size < 12 then
        return programError st 3
      if kind == 0 then
        return programError st 4
      let mut after := account.data
      if kind == 1 then
        if amount > account.lamports then
          return programError st 6
      else if amount == account.lamports then
        if stored == current then
          return systemError st 7
        after := (Wire.putU32 (Wire.putU32 (ByteArray.emptyWithCapacity 8) 1) 0).copySlice 0 after 0 8
      else if amount > 0xFFFFFFFFFFFFFFFF - m.rentMinimum account.data.size || amount + m.rentMinimum account.data.size > account.lamports then
        return programError st 6
      if !(signedBy st metas (if kind == 1 then account.key else account.data.extract 8 40)) then
        return programError st 8
      if account.owner != systemProgram then
        return st.stop accountRule (if after != account.data then ruleData else ruleSpend)
      if !metas[1]!.writable then
        return st.stop accountRule ruleReadOnlyBalance
      let accounts := st.accounts.set! target.index { account with lamports := account.lamports - amount, data := after }
      let to := accounts[metas[1]!.index]!
      return { st with accounts := accounts.set! metas[1]!.index { to with lamports := to.lamports + amount } }
    let mut after := account.data
    if tag == 6 then
      -- InitializeNonceAccount(authority): the account must already hold enough to be exempt from rent
      if data.size < 36 then
        return programError st 3
      if kind != 1 then
        return programError st 4
      if account.lamports < m.rentMinimum account.data.size then
        return programError st 6
      if account.data.size < 80 then
        return programError st 5
      after := (nonceState (data.extract 4 36) current m.lamportsPerSignature).copySlice 0 after 0 80
    else if kind != 2 then
      return programError st (if tag == 12 then 2 else 4)
    else if tag == 12 then
      -- UpgradeNonceAccount: from the old format, whose stored value could collide with a blockhash
      if Wire.u32 account.data 0 != 0 then
        return programError st 2
      after := (nonceState (account.data.extract 8 40) (durableNonce stored) (Wire.u64 account.data 72)).copySlice 0 after 0 80
    else if !(signedBy st metas (account.data.extract 8 40)) then
      return programError st 8
    else if tag == 4 then
      -- AdvanceNonceAccount: store the value for the current blockhash; fails if it already holds it
      if stored == current then
        return systemError st 7
      after := (nonceState (account.data.extract 8 40) current m.lamportsPerSignature).copySlice 0 after 0 80
    else
      -- AuthorizeNonceAccount(authority): hand control to another key
      if data.size < 36 then
        return programError st 3
      after := (data.extract 4 36).copySlice 0 after 8 32
    if account.owner != systemProgram then
      return st.stop accountRule ruleData
    return { st with accounts := st.accounts.set! target.index { account with data := after } }
  return programError st 3

end Sbpf
