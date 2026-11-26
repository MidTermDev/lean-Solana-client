import Solana.Sbpf

/-! An Anchor program calling other programs, with the Rust calling convention.

`tests/programs/anchor-vault` is a token vault written in Rust with Anchor.
Creating a vault takes five programs: the vault asks the system program for
its state account (signing with the seeds of a derived address), then calls
the Associated Token Account program, which is itself a Rust program and
calls the token program three times and the system program once.

The scenario below is run here and by `tests/oracle-next` on Agave's own
program runtime, with the vault compiled for sBPF v0 and again for sBPF v3. The two must print the same thing, line for line: results,
compute units, logs, addresses, balances. `make oracle` checks that. -/

def key (name : String) : ByteArray := Sha256.hash name.toUTF8

def le64 (v : UInt64) : ByteArray := Wire.putU64 (ByteArray.emptyWithCapacity 8) v

def zeroBytes (n : Nat) : ByteArray := Sbpf.zeros ByteArray.empty n

/-- Anchor names an instruction by the first 8 bytes of sha256("global:<name>"). -/
def instruction (name : String) : ByteArray := (Sha256.hash s!"global:{name}".toUTF8).extract 0 8

def run (label : String) (m : Sbpf.Machine) (accounts : Array Sbpf.Account) (program : ByteArray)
    (metas : Array Sbpf.Meta) (data : ByteArray) : IO (Array Sbpf.Account) := do
  let st := Sbpf.process m accounts program metas data
  IO.println s!"{label}: {Sbpf.outcome st}, {st.units} units"
  for line in st.logs do
    IO.println s!"  log: {line}"
  return st.accounts

def balances (accounts : Array Sbpf.Account) : IO Unit :=
  IO.println s!"  vault holds {Wire.u64 accounts[3]!.data 64}, owner holds {Wire.u64 accounts[4]!.data 64}, recorded {Wire.u64 accounts[2]!.data 72}"

/-- The whole scenario, with the vault program read from `file`. -/
def scenario (file : String) : IO Unit := do
  let vaultProgram ← IO.FS.readBinFile file
  if vaultProgram[48]! != 0 then
    IO.println s!"the same program compiled for sBPF v{vaultProgram[48]!}:"
  let tokenId := Base58.decode "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"
  let associatedId := Base58.decode "ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL"
  let vaultId := Base58.decode "7Ygt9ghxooFNu4aH8TbsNpvXVTZUxQx45Dm6dvYQHKYJ"
  let system := Sbpf.systemProgram
  let m := (((Sbpf.Machine.create ⟨0, 0, 0, 0, 0⟩ 200000).add vaultId
    (Sbpf.load vaultProgram)).add tokenId
    (Sbpf.load (← IO.FS.readBinFile "tests/programs/pinocchio_token_program.so"))).add associatedId
    (Sbpf.load (← IO.FS.readBinFile "tests/programs/spl_associated_token_account-1.1.1.so"))

  -- wallets are real Ed25519 keys, so both runs derive the same addresses from the same seeds
  let owner := Ed25519.publicKey (key "owner")
  let stranger := Ed25519.publicKey (key "stranger")
  let mint := key "mint"
  -- a mint with 6 decimals and 5,000,000 units in existence, all held by the owner
  let mintData := Sbpf.zeros ((Hex.decode "01000000" ++ owner ++ le64 5000000).push 6 |>.push 1) 36
  let ownerTokens := Sbpf.zeros ((Sbpf.zeros (mint ++ owner ++ le64 5000000) 36).push 1) 56
  let (vault, bump) := Sbpf.findProgramAddress #["vault".toUTF8, mint, owner] vaultId
  let (vaultTokens, _) := Sbpf.findProgramAddress #[vault, tokenId, mint] associatedId
  IO.println s!"owner {Base58.encode owner}"
  IO.println s!"vault {Base58.encode vault} (bump {bump})"
  IO.println s!"vault tokens {Base58.encode vaultTokens}"

  let mut accounts : Array Sbpf.Account := #[
    ⟨owner, system, 10000000000, ByteArray.empty, false⟩,          -- 0
    ⟨mint, tokenId, 10000000, mintData, false⟩,                    -- 1
    ⟨vault, system, 0, ByteArray.empty, false⟩,                    -- 2: does not exist yet
    ⟨vaultTokens, system, 0, ByteArray.empty, false⟩,              -- 3: does not exist yet
    ⟨key "owner tokens", tokenId, 10000000, ownerTokens, false⟩,   -- 4
    Sbpf.programAccount tokenId,                                   -- 5
    Sbpf.programAccount associatedId,                              -- 6
    ⟨system, Base58.decode "NativeLoader1111111111111111111111111111111", 1, "system_program".toUTF8, true⟩,  -- 7
    ⟨stranger, system, 10000000000, ByteArray.empty, false⟩]       -- 8

  -- 1. initialize: the vault's state account and its token account come into being
  let create : Array Sbpf.Meta := #[⟨0, true, true⟩, ⟨1, false, false⟩, ⟨2, false, true⟩, ⟨3, false, true⟩,
    ⟨5, false, false⟩, ⟨6, false, false⟩, ⟨7, false, false⟩]
  accounts ← run "initialize" m accounts vaultId create (instruction "initialize")
  IO.println s!"  vault: {accounts[2]!.data.size} bytes, {accounts[2]!.lamports} lamports, owned by the vault program: {accounts[2]!.owner == vaultId}"
  IO.println s!"  vault tokens: {accounts[3]!.data.size} bytes, {accounts[3]!.lamports} lamports, owned by the token program: {accounts[3]!.owner == tokenId}"
  -- a second time must fail: the accounts already exist
  accounts ← run "initialize again" m accounts vaultId create (instruction "initialize")

  -- (the signer is writable because it pays the transaction fee in the reference run, and programs can see that)
  let move : Array Sbpf.Meta := #[⟨0, true, true⟩, ⟨1, false, false⟩, ⟨2, false, true⟩, ⟨3, false, true⟩,
    ⟨4, false, true⟩, ⟨5, false, false⟩]
  -- 2. deposit: the owner signs the token transfer
  accounts ← run "deposit 1500000" m accounts vaultId move (instruction "deposit" ++ le64 1500000)
  balances accounts
  -- 3. withdraw: the vault signs, with the seeds of its address
  accounts ← run "withdraw 400000" m accounts vaultId move (instruction "withdraw" ++ le64 400000)
  balances accounts
  -- 4. more than the vault holds: the program refuses
  accounts ← run "withdraw 2000000" m accounts vaultId move (instruction "withdraw" ++ le64 2000000)
  balances accounts
  -- 5. somebody else: Anchor's account checks refuse
  accounts ← run "withdraw by a stranger" m accounts vaultId (move.set! 0 ⟨8, true, true⟩) (instruction "withdraw" ++ le64 1)
  balances accounts

def main : IO Unit := do
  scenario "tests/programs/anchor_vault.so"
  -- the same source compiled for sBPF v3: a different encoding of the same program, calling version 0 programs
  scenario "tests/programs/anchor_vault_v3.so"
