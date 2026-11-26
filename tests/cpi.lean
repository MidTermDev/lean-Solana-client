import Solana.Sbpf

/-! Cross-program invocation: lean-svm's constant-product AMM, written in
Lean, moving real tokens by calling the real token programs.

Three programs run in the virtual machine here: the AMM (compiled by
lean-svm), the SPL Token program and the SPL Token-2022 program (the builds
LiteSVM 0.11.0 bundles, unmodified). The scenario is lean-svm's own
`test_amm`: token A lives under the classic token program, token B under
Token-2022, and the pool's vaults are owned by an address derived from
seeds, so every transfer out of them is signed by the AMM itself.

The compute-unit totals are the ones lean-svm reports from Agave:
init 292, add liquidity 4,690, swap 4,690, remove liquidity 4,708. -/

def key (name : String) : ByteArray := Sha256.hash name.toUTF8

def le64 (v : UInt64) : ByteArray := Wire.putU64 (ByteArray.emptyWithCapacity 8) v

def report (label : String) (st : Sbpf.State) : IO Unit := do
  IO.println s!"{label}: {Sbpf.outcome st}, {st.units} units"

def balance (accounts : Array Sbpf.Account) (i : Nat) : UInt64 := Wire.u64 accounts[i]!.data 64

/-- Runs an instruction that must succeed and returns the accounts afterwards. -/
def must (label : String) (st : Sbpf.State) : IO (Array Sbpf.Account) := do
  if st.status != 0 then
    IO.println s!"{label}: FAILED: {Sbpf.outcome st}"
  return st.accounts

def zeroBytes (n : Nat) : ByteArray := Sbpf.zeros ByteArray.empty n

/-- Token instruction `InitializeMint2`: decimals, mint authority, no freeze authority. -/
def initMint (decimals : UInt8) : ByteArray :=
  ((ByteArray.empty.push 20).push decimals) ++ key "payer" ++ (ByteArray.empty.push 0)

/-- Token instruction `InitializeAccount3`: the owner of the new token account. -/
def initAccount (owner : ByteArray) : ByteArray := (ByteArray.empty.push 18) ++ owner

/-- The system program as an account, for programs that are handed it. -/
def systemAccount : Sbpf.Account :=
  ⟨Sbpf.systemProgram, Base58.decode "NativeLoader1111111111111111111111111111111", 1, "system_program".toUTF8, true⟩

/-- A bonding curve that mints Token-2022 tokens under its own derived
authority when bought, and burns them when sold. Agave: 227 / 4,980 / 3,701. -/
def bondingCurve (token2022Id : ByteArray) (token2022 : Sbpf.Program) : IO Unit := do
  let curveId := key "bonding curve"
  let m := ((Sbpf.Machine.create ⟨1, 0, 0, 0, 0⟩ 200000).add curveId
    (Sbpf.load (← IO.FS.readBinFile "tests/programs/bonding_curve.so"))).add token2022Id token2022
  let (authority, bump) := Sbpf.findProgramAddress #["curv".toUTF8, key "curve"] curveId
  let mut accounts : Array Sbpf.Account := #[
    ⟨key "curve", curveId, 10000000, zeroBytes 96, false⟩,                 -- 0
    ⟨key "curve mint", token2022Id, 10000000, zeroBytes 82, false⟩,        -- 1
    ⟨key "trader tokens", token2022Id, 10000000, zeroBytes 165, false⟩,    -- 2
    ⟨key "trader", Sbpf.systemProgram, 5000000000, ByteArray.empty, false⟩,-- 3
    ⟨authority, Sbpf.systemProgram, 0, ByteArray.empty, false⟩,            -- 4
    Sbpf.programAccount token2022Id,                                       -- 5
    systemAccount]                                                         -- 6
  -- the mint's authority is the curve's derived address, so only the curve can mint
  let mintData := ((ByteArray.empty.push 20).push 6) ++ authority ++ (ByteArray.empty.push 0)
  accounts ← must "curve mint" (Sbpf.process m accounts token2022Id #[⟨1, false, true⟩] mintData)
  accounts ← must "trader tokens" (Sbpf.process m accounts token2022Id #[⟨2, false, true⟩, ⟨1, false, false⟩] (initAccount (key "trader")))
  let st := Sbpf.process m accounts curveId #[⟨0, false, true⟩, ⟨1, false, false⟩]
    ((((ByteArray.empty.push 0).push bump).push 6) ++ le64 30000000000 ++ le64 1000000000000 ++ le64 800000000000 ++ le64 100)
  report "curve init" st
  accounts := st.accounts
  let st := Sbpf.process m accounts curveId #[⟨3, true, true⟩, ⟨0, false, true⟩, ⟨4, false, false⟩, ⟨1, false, true⟩,
    ⟨2, false, true⟩, ⟨5, false, false⟩, ⟨6, false, false⟩] ((ByteArray.empty.push 1) ++ le64 1000000000 ++ le64 30000000000)
  report "curve buy" st
  accounts := st.accounts
  let bought := balance accounts 2
  IO.println s!"  bought {bought} tokens for 1 SOL; trader has {accounts[3]!.lamports} lamports"
  let before := accounts[3]!.lamports
  let st := Sbpf.process m accounts curveId #[⟨3, true, true⟩, ⟨0, false, true⟩, ⟨1, false, true⟩, ⟨2, false, true⟩,
    ⟨5, false, false⟩] ((ByteArray.empty.push 2) ++ le64 (bought / 2) ++ le64 400000000)
  report "curve sell" st
  accounts := st.accounts
  IO.println s!"  sold half: {balance accounts 2} tokens left, {accounts[3]!.lamports - before} lamports received"

/-- A Dutch auction for a Token-2022 NFT: the price falls with the slot, the
buyer pays the seller in SOL through the system program, and the escrow
releases the NFT under the auction's derived signature. Agave: 3,296 / 4,672. -/
def dutchAuction (token2022Id : ByteArray) (token2022 : Sbpf.Program) : IO Unit := do
  let auctionId := key "dutch auction"
  let auction := Sbpf.load (← IO.FS.readBinFile "tests/programs/dutch_auction.so")
  let m := ((Sbpf.Machine.create ⟨0, 0, 0, 0, 0⟩ 200000).add auctionId auction).add token2022Id token2022
  let (authority, bump) := Sbpf.findProgramAddress #["auct".toUTF8, key "auction"] auctionId
  let mut accounts : Array Sbpf.Account := #[
    ⟨key "auction", auctionId, 10000000, zeroBytes 144, false⟩,            -- 0
    ⟨key "nft mint", token2022Id, 10000000, zeroBytes 82, false⟩,          -- 1
    ⟨key "seller nft", token2022Id, 10000000, zeroBytes 165, false⟩,       -- 2
    ⟨key "escrow nft", token2022Id, 10000000, zeroBytes 165, false⟩,       -- 3
    ⟨key "buyer nft", token2022Id, 10000000, zeroBytes 165, false⟩,        -- 4
    ⟨key "seller", Sbpf.systemProgram, 1000000000, ByteArray.empty, false⟩,-- 5
    ⟨key "buyer", Sbpf.systemProgram, 5000000000, ByteArray.empty, false⟩, -- 6
    ⟨key "payer", Sbpf.systemProgram, 5000000000, ByteArray.empty, false⟩, -- 7
    ⟨authority, Sbpf.systemProgram, 0, ByteArray.empty, false⟩,            -- 8
    Sbpf.programAccount token2022Id,                                       -- 9
    systemAccount]                                                         -- 10
  accounts ← must "nft mint" (Sbpf.process m accounts token2022Id #[⟨1, false, true⟩] (initMint 0))
  accounts ← must "seller nft" (Sbpf.process m accounts token2022Id #[⟨2, false, true⟩, ⟨1, false, false⟩] (initAccount (key "seller")))
  accounts ← must "escrow nft" (Sbpf.process m accounts token2022Id #[⟨3, false, true⟩, ⟨1, false, false⟩] (initAccount authority))
  accounts ← must "buyer nft" (Sbpf.process m accounts token2022Id #[⟨4, false, true⟩, ⟨1, false, false⟩] (initAccount (key "buyer")))
  accounts ← must "mint nft" (Sbpf.process m accounts token2022Id #[⟨1, false, true⟩, ⟨2, false, true⟩, ⟨7, true, false⟩]
    ((ByteArray.empty.push 7) ++ le64 1))
  -- start at 1 SOL, fall to 0.2 SOL between slots 100 and 500
  let st := Sbpf.process m accounts auctionId #[⟨5, true, false⟩, ⟨0, false, true⟩, ⟨1, false, false⟩, ⟨2, false, true⟩,
    ⟨3, false, true⟩, ⟨9, false, false⟩]
    ((((ByteArray.empty.push 0).push bump).push 0) ++ le64 1000000000 ++ le64 200000000 ++ le64 100 ++ le64 500)
  report "auction create" st
  accounts := st.accounts
  IO.println s!"  escrow holds {balance accounts 3} NFT"
  -- at slot 300, halfway, the price is 0.6 SOL
  let later := ((Sbpf.Machine.create ⟨300, 0, 0, 0, 0⟩ 200000).add auctionId auction).add token2022Id token2022
  let before := accounts[5]!.lamports
  let st := Sbpf.process later accounts auctionId #[⟨6, true, true⟩, ⟨5, false, true⟩, ⟨0, false, true⟩, ⟨8, false, false⟩,
    ⟨1, false, false⟩, ⟨3, false, true⟩, ⟨4, false, true⟩, ⟨9, false, false⟩, ⟨10, false, false⟩]
    ((ByteArray.empty.push 1) ++ le64 650000000)
  report "auction buy" st
  accounts := st.accounts
  IO.println s!"  buyer holds {balance accounts 4} NFT, escrow {balance accounts 3}; seller received {accounts[5]!.lamports - before} lamports"

def main : IO Unit := do
  let tokenId := Base58.decode "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"
  let token2022Id := Base58.decode "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb"
  let ammId := key "amm"
  let system := Sbpf.systemProgram
  let amm := Sbpf.load (← IO.FS.readBinFile "tests/programs/amm.so")
  let token := Sbpf.load (← IO.FS.readBinFile "tests/programs/pinocchio_token_program.so")
  let token2022 := Sbpf.load (← IO.FS.readBinFile "tests/programs/spl_token_2022-10.0.0.so")
  IO.println s!"loaded: amm {amm.count} instructions, token {token.count}, token-2022 {token2022.count}"
  let m := (((Sbpf.Machine.create ⟨1, 0, 0, 0, 0⟩ 200000).add ammId amm).add tokenId token).add token2022Id token2022

  -- the pool's authority is an address only the AMM can sign for
  let (authority, bump) := Sbpf.findProgramAddress #["pool".toUTF8, key "pool"] ammId
  IO.println s!"pool authority found with bump {bump}: on curve {(Ed25519.Point.decode authority).isSome}"

  let mut accounts : Array Sbpf.Account := #[
    ⟨key "pool", ammId, 10000000, zeroBytes 120, false⟩,        -- 0
    ⟨key "mint A", tokenId, 10000000, zeroBytes 82, false⟩,      -- 1
    ⟨key "mint B", token2022Id, 10000000, zeroBytes 82, false⟩,  -- 2
    ⟨key "vault A", tokenId, 10000000, zeroBytes 165, false⟩,    -- 3
    ⟨key "vault B", token2022Id, 10000000, zeroBytes 165, false⟩,-- 4
    ⟨key "user A", tokenId, 10000000, zeroBytes 165, false⟩,     -- 5
    ⟨key "user B", token2022Id, 10000000, zeroBytes 165, false⟩, -- 6
    ⟨key "user", system, 1000000000, ByteArray.empty, false⟩,   -- 7
    ⟨key "payer", system, 5000000000, ByteArray.empty, false⟩,  -- 8
    ⟨authority, system, 0, ByteArray.empty, false⟩,          -- 9
    Sbpf.programAccount tokenId,                             -- 10
    Sbpf.programAccount token2022Id]                         -- 11

  -- set up mints and token accounts with the token programs themselves
  accounts ← must "mint A" (Sbpf.process m accounts tokenId #[⟨1, false, true⟩] (initMint 6))
  accounts ← must "mint B" (Sbpf.process m accounts token2022Id #[⟨2, false, true⟩] (initMint 9))
  accounts ← must "vault A" (Sbpf.process m accounts tokenId #[⟨3, false, true⟩, ⟨1, false, false⟩] (initAccount authority))
  accounts ← must "vault B" (Sbpf.process m accounts token2022Id #[⟨4, false, true⟩, ⟨2, false, false⟩] (initAccount authority))
  accounts ← must "user A" (Sbpf.process m accounts tokenId #[⟨5, false, true⟩, ⟨1, false, false⟩] (initAccount (key "user")))
  accounts ← must "user B" (Sbpf.process m accounts token2022Id #[⟨6, false, true⟩, ⟨2, false, false⟩] (initAccount (key "user")))
  let mintTo := (ByteArray.empty.push 7) ++ le64 2000000
  accounts ← must "mint to A" (Sbpf.process m accounts tokenId #[⟨1, false, true⟩, ⟨5, false, true⟩, ⟨8, true, false⟩] mintTo)
  accounts ← must "mint to B" (Sbpf.process m accounts token2022Id #[⟨2, false, true⟩, ⟨6, false, true⟩, ⟨8, true, false⟩] mintTo)
  IO.println s!"user holds {balance accounts 5} A and {balance accounts 6} B"

  -- 1. create the pool: fee 30 basis points
  let st := Sbpf.process m accounts ammId #[⟨0, false, true⟩, ⟨3, false, false⟩, ⟨4, false, false⟩]
    (((((ByteArray.empty.push 0).push bump).push 6).push 9).push 30 |>.push 0)
  report "init pool" st
  accounts := st.accounts

  -- 2. add 1,000,000 of each token; the AMM calls both token programs
  let add : Array Sbpf.Meta := #[⟨7, true, false⟩, ⟨0, false, true⟩, ⟨1, false, false⟩, ⟨2, false, false⟩,
    ⟨3, false, true⟩, ⟨4, false, true⟩, ⟨5, false, true⟩, ⟨6, false, true⟩, ⟨10, false, false⟩, ⟨11, false, false⟩]
  let st := Sbpf.process m accounts ammId add ((ByteArray.empty.push 1) ++ le64 1000000 ++ le64 1000000 ++ le64 999999)
  report "add liquidity" st
  accounts := st.accounts
  IO.println s!"  vaults hold {balance accounts 3} A and {balance accounts 4} B"

  -- 3. swap 100,000 A for B; the vault pays out under the AMM's derived signature
  let trade : Array Sbpf.Meta := #[⟨7, true, false⟩, ⟨0, false, true⟩, ⟨9, false, false⟩, ⟨1, false, false⟩, ⟨2, false, false⟩,
    ⟨3, false, true⟩, ⟨4, false, true⟩, ⟨5, false, true⟩, ⟨6, false, true⟩, ⟨10, false, false⟩, ⟨11, false, false⟩]
  let st := Sbpf.process m accounts ammId trade (((ByteArray.empty.push 2).push 0) ++ le64 100000 ++ le64 90000)
  report "swap" st
  accounts := st.accounts
  IO.println s!"  vaults hold {balance accounts 3} A and {balance accounts 4} B; user holds {balance accounts 6} B"

  -- 4. withdraw half of the liquidity
  let st := Sbpf.process m accounts ammId trade ((ByteArray.empty.push 3) ++ le64 500000 ++ le64 500000 ++ le64 450000)
  report "remove liquidity" st
  accounts := st.accounts
  IO.println s!"  vaults hold {balance accounts 3} A and {balance accounts 4} B"

  -- the same swap without the user's signature must be refused
  let unsigned : Array Sbpf.Meta := trade.set! 0 ⟨7, false, false⟩
  report "swap, user did not sign" (Sbpf.process m accounts ammId unsigned (((ByteArray.empty.push 2).push 0) ++ le64 100000 ++ le64 90000))
  -- asking for more output than the pool gives must fail in the AMM, before any transfer
  report "swap, slippage too tight" (Sbpf.process m accounts ammId trade (((ByteArray.empty.push 2).push 0) ++ le64 100000 ++ le64 99000))

  -- the vault passed read-only: the AMM asks the token program to write to it, which it may not grant
  let readOnlyVault : Array Sbpf.Meta := trade.set! 5 ⟨3, false, false⟩
  report "swap, vault A read-only" (Sbpf.process m accounts ammId readOnlyVault (((ByteArray.empty.push 2).push 0) ++ le64 100000 ++ le64 60000))
  -- Token-2022 not loaded: the first transfer succeeds, the second cannot run, and nothing is kept
  let half := ((Sbpf.Machine.create ⟨1, 0, 0, 0, 0⟩ 200000).add ammId amm).add tokenId token
  let st := Sbpf.process half accounts ammId trade (((ByteArray.empty.push 2).push 0) ++ le64 100000 ++ le64 60000)
  IO.println s!"swap, Token-2022 missing: {Sbpf.statusName st.status}"
  IO.println s!"  vault A still holds {balance st.accounts 3}"
  -- a budget that runs out inside the token program
  let tight := (((Sbpf.Machine.create ⟨1, 0, 0, 0, 0⟩ 2000).add ammId amm).add tokenId token).add token2022Id token2022
  report "swap, 2,000-unit budget" (Sbpf.process tight accounts ammId trade (((ByteArray.empty.push 2).push 0) ++ le64 100000 ++ le64 60000))

  bondingCurve token2022Id token2022
  dutchAuction token2022Id token2022
