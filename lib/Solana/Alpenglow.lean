import Solana.Snapshot
import Solana.LeaderSchedule
import Crypto.Bls12381
import Crypto.Hkdf
import Crypto.Ed25519

/-!
# What a block's footer does to the vote accounts

Under Alpenglow validators no longer vote with transactions. They sign
votes with BLS keys, the signatures are aggregated, and a block's footer
carries the aggregates: a certificate that an earlier block is final, and a
certificate of who voted on the slot eight back, for rewards. A certificate
names its signers by a bitmap over the validators in *rank* order (most
stake first).

Executing a block applies those certificates to the validators' vote
accounts: the slot each last voted on, its root, its timestamp, and its
credits, which now count the lamports of reward it has earned.

A certificate that a block is final is what lets a node execute that block
without ever having to undo it, so its signature is checked (`finalProven`):
the validators the bitmap names must hold enough of the stake, and the
aggregate must be their signature of the vote.
-/

namespace Alpenglow

/-- The certificates in a footer: for the slot finalised and for the slot rewarded, the bitmaps of who signed. -/
structure Certs where
  error : String
  /-- 0 if the footer finalises nothing -/
  finalSlot : UInt64
  /-- the id of the block finalised -/
  finalBlock : ByteArray
  finalBits : Array ByteArray
  /-- the aggregate signature that goes with each of those bitmaps -/
  finalSignatures : Array ByteArray
  /-- 0 if the footer rewards nothing -/
  rewardSlot : UInt64
  rewardBits : Array ByteArray
  deriving Inhabited

/-- Reads the certificates that follow the producer's name in a footer. -/
def parse (c : ByteArray) : Certs := Id.run do
  let none_ : Array ByteArray := Array.emptyWithCapacity 0
  let bad : Certs := ⟨"the footer's certificates do not parse", 0, ByteArray.empty, none_, none_, 0, none_⟩
  let mut finalSlot : UInt64 := 0
  let mut finalBlock := ByteArray.empty
  let mut finalBits : Array ByteArray := Array.emptyWithCapacity 2
  let mut finalSignatures : Array ByteArray := Array.emptyWithCapacity 2
  let mut rewardSlot : UInt64 := 0
  let mut rewardBits : Array ByteArray := Array.emptyWithCapacity 2
  let mut o := 0
  if c.size == 0 then
    return ⟨"", 0, ByteArray.empty, none_, none_, 0, none_⟩
  -- finality: slot, block, an aggregate (signature, bitmap), optionally a second aggregate
  if c[o]! == 1 then
    if o + 139 > c.size then
      return bad
    finalSlot := Wire.u64 c (o + 1)
    let len := (Wire.u16 c (o + 137)).toNat
    if o + 139 + len + 1 > c.size then
      return bad
    finalBlock := c.extract (o + 9) (o + 41)
    finalSignatures := finalSignatures.push (c.extract (o + 41) (o + 137))
    finalBits := finalBits.push (c.extract (o + 139) (o + 139 + len))
    o := o + 139 + len
    if c[o]! == 1 then
      if o + 99 > c.size then
        return bad
      let more := (Wire.u16 c (o + 97)).toNat
      if o + 99 + more > c.size then
        return bad
      finalSignatures := finalSignatures.push (c.extract (o + 1) (o + 97))
      finalBits := finalBits.push (c.extract (o + 99) (o + 99 + more))
      o := o + 99 + more
    else
      o := o + 1
  else
    o := o + 1
  -- rewards: who voted to skip the slot, and who voted for its block
  for kind in [0:2] do
    if o >= c.size then
      return bad
    if c[o]! == 1 then
      let head := if kind == 0 then 105 else 137
      if o + head + 1 > c.size then
        return bad
      let slot := Wire.u64 c (o + 1)
      if rewardSlot != 0 && slot != rewardSlot then
        return ⟨"the footer's reward certificates are for different slots", 0, ByteArray.empty, none_, none_, 0, none_⟩
      rewardSlot := slot
      let len := (Wire.varint c (o + head)).toNat
      let start := Wire.skipVarint c (o + head)
      if !(Wire.ok start) || start + len > c.size then
        return bad
      rewardBits := rewardBits.push (c.extract start (start + len))
      o := start + len
    else
      o := o + 1
  return ⟨"", finalSlot, finalBlock, finalBits, finalSignatures, rewardSlot, rewardBits⟩

/-- Does a bitmap name the validator of this rank? A bitmap is a kind byte (0: one bit each), the number of bits, and the bits. -/
def named (bitmap : ByteArray) (rank : Nat) : Bool :=
  bitmap.size >= 3 && bitmap[0]! == 0 && rank < (Wire.u16 bitmap 1).toNat && 3 + rank / 8 < bitmap.size
    && (bitmap[3 + rank / 8]! >>> (rank % 8).toUInt8) &&& 1 == 1

def namedByAny (bitmaps : Array ByteArray) (rank : Nat) : Bool := Id.run do
  for b in bitmaps do
    if named b rank then
      return true
  return false

/-- Byte-wise order of two keys of the same length. -/
def keyBefore (a b : ByteArray) : Bool := Id.run do
  for i in [0:a.size] do
    if a[i]! != b[i]! then
      return a[i]! < b[i]!
  return false

/-- The validators of an epoch in rank order: those with stake and a BLS
key, leaving out any whose key or identity another also uses; most stake
first, ties by key. -/
def ranks (voters : Array Snapshot.Voter) : Array Snapshot.Voter := Id.run do
  let mut eligible : Array Snapshot.Voter := Array.emptyWithCapacity voters.size
  for v in voters do
    if v.stake != 0 && v.bls.size == 48 then
      eligible := eligible.push v
  let mut kept : Array Snapshot.Voter := Array.emptyWithCapacity eligible.size
  for i in [0:eligible.size] do
    let mut unique := true
    for j in [0:eligible.size] do
      if i != j && (eligible[i]!.bls == eligible[j]!.bls || eligible[i]!.node == eligible[j]!.node) then
        unique := false
    if unique then
      kept := kept.push eligible[i]!
  -- insertion sort: more stake first, then the smaller key
  let mut out : Array Snapshot.Voter := Array.emptyWithCapacity kept.size
  for v in kept do
    out := out.push v
    let mut j := out.size - 1
    while j > 0 && (out[j]!.stake > out[j - 1]!.stake || (out[j]!.stake == out[j - 1]!.stake && keyBefore out[j]!.bls out[j - 1]!.bls)) do
      let t := out[j]!
      out := out.set! j out[j - 1]!
      out := out.set! (j - 1) t
      j := j - 1
  return out

-- ------------------------------------------------------------- signatures

/-- The purpose validators' signatures of votes are made for. -/
def voteDomain : ByteArray := "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".toUTF8

/-- What a validator signs to vote: the kind of vote (1 for a block, 2 that a slot is final), the slot,
the block's id if the vote is for a block, and the cluster's shred version. -/
def vote (kind : UInt8) (slot : UInt64) (block : ByteArray) (version : UInt64) : ByteArray :=
  Fast.push16 (Wire.putU64 (ByteArray.empty.push kind) slot ++ block) version

/-- The validators of an epoch for checking certificates: their keys and stakes in rank order, the sum
of the keys, and the sum of the stakes. -/
structure Signers where
  epoch : UInt64
  keys : Array Bls12381.Point
  stakes : Array UInt64
  all : Bls12381.Point
  total : UInt64
  deriving Inhabited

def signers (epoch : UInt64) (voters : Array Snapshot.Voter) : Signers := Id.run do
  let mut keys : Array Bls12381.Point := Array.emptyWithCapacity voters.size
  let mut stakes : Array UInt64 := Array.emptyWithCapacity voters.size
  let mut all := Bls12381.Point.infinity
  let mut total : UInt64 := 0
  for v in ranks voters do
    let key := match Bls12381.Point.ofBytes v.bls with
      | some k => k
      | none => Bls12381.Point.infinity
    keys := keys.push key
    stakes := stakes.push v.stake
    all := all.add key
    total := total + v.stake
  return ⟨epoch, keys, stakes, all, total⟩

/-- The stake of the validators a bitmap names, if `signature` is their signatures of `message` added
up; otherwise 0. Their keys are added up too: the named ones, or everyone's less the others, whichever
is fewer. -/
def signedStake (s : Signers) (bitmap signature message : ByteArray) : UInt64 := Id.run do
  let bits := if bitmap.size >= 3 then (Wire.u16 bitmap 1).toNat else 0
  let mut count := 0
  for rank in [0:bits] do
    if named bitmap rank then
      -- (a rank nobody has, or whose key is no point)
      if rank >= s.keys.size || s.keys[rank]!.isInfinity then
        return 0
      count := count + 1
  let most := 2 * count > s.keys.size
  let mut key := Bls12381.Point.infinity
  let mut stake : UInt64 := 0
  for rank in [0:s.keys.size] do
    if named bitmap rank then
      stake := stake + s.stakes[rank]!
    if named bitmap rank != most then
      key := key.add s.keys[rank]!
  if most then
    key := s.all.add key.neg
  match Bls12381.Point.ofBytes signature with
  | none => return 0
  | some point => return if Bls12381.verify key message voteDomain point then stake else 0

/-- How many fifths of the stake (rounded down) signed, by `signedStake`. -/
def fifths (s : Signers) (bitmap signature message : ByteArray) : UInt64 :=
  if s.total == 0 then 0 else 5 * signedStake s bitmap signature message / s.total

/-- Is a footer's claim that a block is final backed by the epoch's validators? Either four fifths of
the stake voted for the block, or three fifths voted for it and three fifths that its slot is final. -/
def finalProven (c : Certs) (s : Signers) (version : UInt64) : Bool :=
  let block := vote 1 c.finalSlot c.finalBlock version
  if c.finalBits.size == 1 then
    fifths s c.finalBits[0]! c.finalSignatures[0]! block >= 4
  else
    c.finalBits.size == 2 && fifths s c.finalBits[0]! c.finalSignatures[0]! (vote 2 c.finalSlot ByteArray.empty version) >= 3
      && fifths s c.finalBits[1]! c.finalSignatures[1]! block >= 3

-- ------------------------------------------------------------ vote accounts

/-- A vote account's state (the current layout, version 4), taken apart as far as a footer changes it. -/
structure VoteState where
  ok : Bool
  /-- everything before the votes: identities, commissions, the BLS key -/
  head : ByteArray
  /-- the votes as stored: a count, then 13 bytes each (latency, slot, confirmations) -/
  votes : ByteArray
  hasRoot : Bool
  root : UInt64
  /-- the authorised voters as stored: a count, then 40 bytes each -/
  voters : ByteArray
  /-- (epoch, credits, credits before the epoch), flattened -/
  credits : Array UInt64
  timestampSlot : UInt64
  timestamp : UInt64
  size : Nat
  deriving Inhabited

def notVoteState : VoteState := ⟨false, ByteArray.empty, ByteArray.empty, false, 0, ByteArray.empty, Array.emptyWithCapacity 0, 0, 0, 0⟩

/-- A vote account's state, read from the present layout (3) or one of the two before it (1 and 2),
which accounts untouched since still have: a shorter head, a list of earlier voters (1,545 bytes) before
the credits, and in layout 1 votes of 12 bytes. Those are read as the validators convert them: the
account itself (`key`) collects the rewards' commission, the node all of the block fees, and there is no
BLS key. -/
def VoteState.read (d key : ByteArray) : VoteState := Id.run do
  let layout := if d.size < 200 then 0 else Wire.u32 d 0
  if layout == 0 || layout > 3 then
    return notVoteState
  let mut o := if layout < 3 then 69 else if d[144]! == 1 then 193 else 145
  let votesAt := o
  let count := Wire.u64 d o
  if count > 64 then
    return notVoteState
  o := o + 8 + (if layout == 1 then 12 else 13) * count.toNat
  if o + 9 > d.size then
    return notVoteState
  let hasRoot := d[o]! == 1
  let root := if hasRoot then Wire.u64 d (o + 1) else 0
  let votesEnd := o
  o := if hasRoot then o + 9 else o + 1
  let votersAt := o
  let voters := Wire.u64 d o
  if voters > 64 then
    return notVoteState
  let votersEnd := o + 8 + 40 * voters.toNat
  o := if layout < 3 then votersEnd + 1545 else votersEnd
  if o + 8 > d.size then
    return notVoteState
  let creditsCount := Wire.u64 d o
  if creditsCount > 128 || o + 8 + 24 * creditsCount.toNat + 16 > d.size then
    return notVoteState
  let mut credits : Array UInt64 := Array.emptyWithCapacity (3 * creditsCount.toNat + 3)
  for i in [0:3 * creditsCount.toNat] do
    credits := credits.push (Wire.u64 d (o + 8 + 8 * i))
  let after := o + 8 + 24 * creditsCount.toNat
  let mut head := d.extract 0 votesAt
  let mut votes := d.extract votesAt votesEnd
  if layout < 3 then
    let node := d.extract 4 36
    head := Wire.putU32 (ByteArray.emptyWithCapacity 145) 3 ++ node ++ d.extract 36 68 ++ key ++ node
    head := (Wire.putU64 (Wire.putU16 (Wire.putU16 head (d[68]!.toUInt64 * 100)) 10000) 0).push 0
  if layout == 1 then
    -- (a vote gains a first byte: how late it landed, unknown)
    votes := d.extract votesAt (votesAt + 8)
    for k in [0:count.toNat] do
      votes := votes.push 0 ++ d.extract (votesAt + 8 + 12 * k) (votesAt + 20 + 12 * k)
  return ⟨true, head, votes, hasRoot, root, d.extract votersAt votersEnd, credits, Wire.u64 d after, Wire.u64 d (after + 8), d.size⟩

/-- The state of a vote account in the present layout. -/
def VoteState.parse (d : ByteArray) : VoteState := if d.size >= 200 && Wire.u32 d 0 == 3 then VoteState.read d ByteArray.empty else notVoteState

/-- The state as it is written into an account, in the present layout. -/
def VoteState.serial (s : VoteState) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 3762
  b := b ++ s.head ++ s.votes
  if s.hasRoot then
    b := Wire.putU64 (b.push 1) s.root
  else
    b := b.push 0
  b := b ++ s.voters
  b := Wire.putU64 b (s.credits.size / 3).toUInt64
  for c in s.credits do
    b := Wire.putU64 b c
  return Wire.putU64 (Wire.putU64 b s.timestampSlot) s.timestamp

/-- The state as account data again, padded to the account's size. Empty if it no longer fits. -/
def VoteState.bytes (s : VoteState) : ByteArray :=
  let b := s.serial
  if b.size > s.size then ByteArray.empty else Fast.pushZeros b (s.size - b.size)

/-- The state of a vote account just set up: no votes, no credits, one voter from `epoch` on; the account
collects the rewards' commission (`commission` percent) and the node all of the block fees. -/
def VoteState.fresh (key node voter withdrawer : ByteArray) (commission : UInt8) (epoch : UInt64) : VoteState :=
  let head := Wire.putU32 (ByteArray.emptyWithCapacity 145) 3 ++ node ++ withdrawer ++ key ++ node
  ⟨true, (Wire.putU64 (Wire.putU16 (Wire.putU16 head (commission.toUInt64 * 100)) 10000) 0).push 0,
    Wire.putU64 ByteArray.empty 0, false, 0, Wire.putU64 (Wire.putU64 ByteArray.empty 1) epoch ++ voter, Array.emptyWithCapacity 0, 0, 0, 3762⟩

/-- Who may vote for an account is a list of (epoch, key), in order: a key holds from its epoch until
the next entry's. This is the entry for `epoch`: its own, or the latest before it; empty if there is none. -/
def voterAt (voters : ByteArray) (epoch : UInt64) : ByteArray := Id.run do
  let mut found := ByteArray.empty
  for k in [0:(Wire.u64 voters 0).toNat] do
    if Wire.u64 voters (8 + 40 * k) <= epoch then
      found := voters.extract (8 + 40 * k) (48 + 40 * k)
  return found

/-- The list with the entries before epoch `low` dropped and, if `key` is one, `key` entered at `epoch`. -/
def votersWith (voters : ByteArray) (low epoch : UInt64) (key : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (voters.size + 40)
  let mut count : UInt64 := 0
  let mut entered := key.size != 32
  for k in [0:(Wire.u64 voters 0).toNat] do
    let e := Wire.u64 voters (8 + 40 * k)
    if !entered && e >= epoch then
      out := Wire.putU64 out epoch ++ key
      count := count + 1
      entered := true
    if e >= low && !(e == epoch && key.size == 32) then
      out := out ++ voters.extract (8 + 40 * k) (48 + 40 * k)
      count := count + 1
  if !entered then
    out := Wire.putU64 out epoch ++ key
    count := count + 1
  return Wire.putU64 (ByteArray.emptyWithCapacity (out.size + 8)) count ++ out

/-- A validator's BLS secret, which it derives from its identity key so that there is one key to keep:
the identity signs a fixed message, and the signature is stretched into a number below the groups'
order the way the BLS standard generates keys (HKDF over a salt hashed until the number is not zero). -/
def blsSecret (seed identity : ByteArray) : Array UInt64 := Id.run do
  let material := (Ed25519.sign seed identity "bls-key-derive-alpenglow".toUTF8).push 0
  let info := (ByteArray.empty.push 0).push 48
  let mut salt := "BLS-SIG-KEYGEN-SALT-".toUTF8
  let mut secret : Array UInt64 := Array.replicate 4 0
  for _ in [0:8] do
    if secret[0]! ||| secret[1]! ||| secret[2]! ||| secret[3]! == 0 then
      salt := Sha256.hash salt
      let key := Hkdf.extract salt material
      let first := Hkdf.hmac key (info.push 1)
      secret := Bls12381.scalarOf (first ++ (Hkdf.hmac key ((first ++ info).push 2)).extract 0 16)
  return secret

def proofDomain : ByteArray := "BLS_POP_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".toUTF8

/-- Does `proof` show that whoever sets the BLS key `key` on the vote account `account` holds its
secret? It is their signature of "ALPENGLOW", the account's address and the key. The key must be a
point of the group, and not nothing. -/
def possessed (account key proof : ByteArray) : Bool :=
  match Bls12381.Point.ofBytes key with
  | none => false
  | some k =>
    match Bls12381.Point.ofBytes proof with
    | none => false
    | some p => key.size == 48 && proof.size == 96 && !k.isInfinity && (k.scale Bls12381.order).isInfinity
        && Bls12381.verify k ("ALPENGLOW".toUTF8 ++ account ++ key) proofDomain p

/-- The slot of the newest vote, or 0. -/
def VoteState.lastVoted (s : VoteState) : UInt64 :=
  let count := (Wire.u64 s.votes 0).toNat
  if count == 0 then 0 else Wire.u64 s.votes (8 + 13 * (count - 1) + 1)

/-- A certificate says the validator voted on `slot`, at about `nanos`: its votes become that one vote, and its timestamp moves if this is later. -/
def VoteState.voted (s : VoteState) (slot nanos : UInt64) : VoteState :=
  let a := if s.lastVoted > slot then s.lastVoted else slot
  let latest := if s.hasRoot && s.root > a then s.root else a
  let votes := Wire.putU32 (Wire.putU64 ((Wire.putU64 (ByteArray.emptyWithCapacity 21) 1).push 0) latest) 1
  let seconds := nanos / 1000000000
  if seconds > s.timestamp && s.timestamp < 0x8000000000000000 then
    { s with votes := votes, timestampSlot := slot, timestamp := seconds }
  else
    { s with votes := votes }

/-- A certificate says `slot` is final: the validator's root is at least that. -/
def VoteState.rooted (s : VoteState) (slot : UInt64) : VoteState :=
  { s with hasRoot := true, root := if s.hasRoot && s.root > slot then s.root else slot }

/-- The entry that marks, in a list of credits, where Alpenglow took over. -/
def marker : UInt64 := 0xFFFFFFFFFFFFFFFF

def saturating (a b : UInt64) : UInt64 := if a + b < a then 0xFFFFFFFFFFFFFFFF else a + b

/-- Adds credits for an epoch, as Agave keeps them: one entry per epoch (epoch, total, total before it), at most 64. -/
def VoteState.credit (s : VoteState) (migrationEpoch epoch new : UInt64) : VoteState := Id.run do
  let mut c := s.credits
  if epoch == migrationEpoch then
    let mut marked := false
    for i in [0:c.size / 3] do
      if c[3 * i]! == marker && c[3 * i + 1]! == marker && c[3 * i + 2]! == marker then
        marked := true
    if !marked then
      c := (c.push marker).push marker
      c := c.push marker
  let n := c.size / 3
  if n == 0 then
    return { s with credits := #[epoch, new, 0] }
  let last := 3 * (n - 1)
  let mut pushed := false
  if c[last]! == marker && c[last + 1]! == marker && c[last + 2]! == marker then
    let before := if n >= 2 then c[last - 2]! else 0
    c := (c.push epoch).push (saturating new before)
    c := c.push before
    pushed := true
  else if c[last]! == epoch then
    c := c.set! (last + 1) (saturating c[last + 1]! new)
  else if c[last + 1]! == c[last + 2]! then
    c := c.set! last epoch
    c := c.set! (last + 1) (saturating c[last + 1]! new)
  else
    let total := c[last + 1]!
    c := (c.push epoch).push (saturating new total)
    c := c.push total
    pushed := true
  if pushed && c.size / 3 > 64 then
    let mut kept : Array UInt64 := Array.emptyWithCapacity 192
    for i in [c.size - 192:c.size] do
      kept := kept.push c[i]!
    c := kept
  return { s with credits := c }

-- ------------------------------------------------------------------ rewards

/-- `a × b / (c × d)` for 64-bit numbers whose products need 128 bits (the quotient must fit 64). -/
def ratio (a b c d : UInt64) : UInt64 := Id.run do
  let (nh, nl) := LeaderSchedule.wide a b
  let (dh, dl) := LeaderSchedule.wide c d
  if dh == 0 && dl == 0 then
    return 0
  -- long division, a bit at a time: the remainder is kept in 128 bits
  let mut rh : UInt64 := 0
  let mut rl : UInt64 := 0
  let mut q : UInt64 := 0
  for i in [0:128] do
    let bit := if i < 64 then (nh >>> (63 - i).toUInt64) &&& 1 else (nl >>> (127 - i).toUInt64) &&& 1
    -- the remainder never reaches 2^127 here: the divisor is far below it
    rh := (rh <<< 1) ||| (rl >>> 63)
    rl := (rl <<< 1) ||| bit
    q := q <<< 1
    if rh > dh || (rh == dh && rl >= dl) then
      let borrow : UInt64 := if rl < dl then 1 else 0
      rl := rl - dl
      rh := rh - dh - borrow
      q := q ||| 1
  return q

end Alpenglow
