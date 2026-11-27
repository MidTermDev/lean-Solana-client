import Crypto.Keccak
import Crypto.Secp256k1
import Solana.Alpenglow
import Encoding.Hex

/-! Pieces that replaying a block needs beyond the virtual machine: two
hashes and a curve that programs reach through system calls, and what a
block's footer does to the vote accounts.

The secp256k1 cases were made with an independent implementation (keys,
nonces and hashes drawn at random; the last with the "high s" form of the
signature); the reward ratios with exact integer arithmetic. -/

def recovered (hash : String) (id : Nat) (signature want : String) : String :=
  let key := Secp256k1.recover (Hex.decode hash) id (Hex.decode signature)
  if Hex.encode key == want then "the signer's key" else if key.size == 0 then "nothing" else "another key"

def ratioLine (a b c d want : UInt64) : String :=
  s!"{a} × {b} / ({c} × {d}) = {Alpenglow.ratio a b c d}{if Alpenglow.ratio a b c d == want then "" else s!" WRONG, should be {want}"}"

def creditsOf (s : Alpenglow.VoteState) : String := Id.run do
  let mut out := ""
  for i in [0:s.credits.size / 3] do
    out := out ++ s!"({s.credits[3 * i]!}, {s.credits[3 * i + 1]!}, {s.credits[3 * i + 2]!}) "
  return out

/-- A vote account as Agave lays it out (version 4): identities, commissions, a BLS key, votes, root, voters, credits, timestamp. -/
def voteAccount (votes : Array UInt64) (root : UInt64) (credits : Array UInt64) (timestamp : UInt64) : ByteArray := Id.run do
  let mut b := Wire.putU32 (ByteArray.emptyWithCapacity 3762) 3
  for i in [0:128] do
    b := b.push (i % 7 + 1).toUInt8
  b := Wire.putU64 (Wire.putU16 (Wire.putU16 b 500) 10000) 77
  b := b.push 1
  for i in [0:48] do
    b := b.push (200 - i).toUInt8
  b := Wire.putU64 b votes.size.toUInt64
  for v in votes do
    b := Wire.putU32 (Wire.putU64 (b.push 3) v) 5
  b := Wire.putU64 (b.push 1) root
  b := Wire.putU64 b 1
  b := Wire.putU64 b 9
  for i in [0:32] do
    b := b.push (i + 40).toUInt8
  b := Wire.putU64 b (credits.size / 3).toUInt64
  for c in credits do
    b := Wire.putU64 b c
  b := Wire.putU64 (Wire.putU64 b 4000) timestamp
  while b.size < 3762 do
    b := b.push 0
  return b

def main : IO Unit := do
  -- Keccak-256: the two values everyone knows, and the block boundary
  IO.println s!"keccak of nothing: {Hex.encode (Keccak.hash ByteArray.empty)}"
  IO.println s!"keccak of abc:     {Hex.encode (Keccak.hash "abc".toUTF8)}"
  let mut long := ByteArray.empty
  for i in [0:300] do
    long := long.push (i % 251).toUInt8
  IO.println s!"135, 136, 137 and 300 bytes: {Hex.encode ((Keccak.hash (long.extract 0 135)).extract 0 8)} {Hex.encode ((Keccak.hash (long.extract 0 136)).extract 0 8)} {Hex.encode ((Keccak.hash (long.extract 0 137)).extract 0 8)} {Hex.encode ((Keccak.hash long).extract 0 8)}"

  -- secp256k1: the key behind a signature
  IO.println s!"signature 1: {recovered "5f2dd97f1cfb10f62827688de6a16a3b0d464138a62332553fc1ea36f17fd374" 1 "9ffa343ed7948d987918baa784a8ce0d517fcfe743f34fda9ee960c8c57c2bb4ca2ec7ff4c7c0c3180e0284931f6f6483713630ac0c75599d41dfc6b79a51253" "e8901aec51f74e698974d4a80ca8b57d4b48c5529fce14b6e7c15e12c005be4b1b8d0cf50b8631a73a5f52da5eea8e9c2bd53ee70989b207046037b08b353cfb"}; with the other candidate: {recovered "5f2dd97f1cfb10f62827688de6a16a3b0d464138a62332553fc1ea36f17fd374" 0 "9ffa343ed7948d987918baa784a8ce0d517fcfe743f34fda9ee960c8c57c2bb4ca2ec7ff4c7c0c3180e0284931f6f6483713630ac0c75599d41dfc6b79a51253" "e8901aec51f74e698974d4a80ca8b57d4b48c5529fce14b6e7c15e12c005be4b1b8d0cf50b8631a73a5f52da5eea8e9c2bd53ee70989b207046037b08b353cfb"}"
  IO.println s!"signature 2: {recovered "9e115e4b9e30691c238642ea126a1e48cc11d357c30d8b7628dbd25e63b229f1" 0 "44a801d263dd0f24df119a0946bf553934f4a2bc12918e5a02af642b08c73c9f9794a888da77e97141ec57d478c01e342c200ce66bdc6ca1573ccc8ef8d7c0cd" "2b3a540e77f62b66777bd6c374bdac09ba000e4323e77227e885f825317f533c8cd7a231968e53ba98662daedaa3eaff21affafc7917fef50f422e75ac5bc440"}; with the other candidate: {recovered "9e115e4b9e30691c238642ea126a1e48cc11d357c30d8b7628dbd25e63b229f1" 1 "44a801d263dd0f24df119a0946bf553934f4a2bc12918e5a02af642b08c73c9f9794a888da77e97141ec57d478c01e342c200ce66bdc6ca1573ccc8ef8d7c0cd" "2b3a540e77f62b66777bd6c374bdac09ba000e4323e77227e885f825317f533c8cd7a231968e53ba98662daedaa3eaff21affafc7917fef50f422e75ac5bc440"}"
  IO.println s!"signature 3: {recovered "4c7d6df0621aef57e4cc4132f7108e96f770c2263266aa3bb0cde917f7f35634" 0 "4a17bd989cf10900fa0ecfacb90e5527369d0f93f19530f147c51702ebd49a253c2797a00c479aaa8d0e384fe394ec33f313ef7ac7eeb8cf54527552004ca826" "f3703c9342af31938546a050bf14fa7adfb31c52c0eb2c794ed1fee3cb4e5975a62b16bb32f23a69d6b8d5c41c79012953bbb52c2f8106dc4e6ec1f7b893dac9"}; with the other candidate: {recovered "4c7d6df0621aef57e4cc4132f7108e96f770c2263266aa3bb0cde917f7f35634" 1 "4a17bd989cf10900fa0ecfacb90e5527369d0f93f19530f147c51702ebd49a253c2797a00c479aaa8d0e384fe394ec33f313ef7ac7eeb8cf54527552004ca826" "f3703c9342af31938546a050bf14fa7adfb31c52c0eb2c794ed1fee3cb4e5975a62b16bb32f23a69d6b8d5c41c79012953bbb52c2f8106dc4e6ec1f7b893dac9"}"
  IO.println s!"signature 4: {recovered "b24891917b121dc54e5a3a26d18a669a5af84e6b4f59672710e6d8e6568068b9" 0 "89f2dade1ab8574fe741362836e7581ce8e441f54af9ff6ae7ba7993d7f6016597cc973686717e9744cec49f106d20dcb187780699c2388fe8f75ea938a15d6c" "d1cd14fa95d996e194f1035b89f4fd09c398fcf3df47a409fd635419a76422b945f44cdf383d97ba08fca7fa6694be3c4b5c5378549b9539db895489eeba6bfb"}; with the other candidate: {recovered "b24891917b121dc54e5a3a26d18a669a5af84e6b4f59672710e6d8e6568068b9" 1 "89f2dade1ab8574fe741362836e7581ce8e441f54af9ff6ae7ba7993d7f6016597cc973686717e9744cec49f106d20dcb187780699c2388fe8f75ea938a15d6c" "d1cd14fa95d996e194f1035b89f4fd09c398fcf3df47a409fd635419a76422b945f44cdf383d97ba08fca7fa6694be3c4b5c5378549b9539db895489eeba6bfb"}"
  IO.println s!"a zero in the signature: {recovered "5f2dd97f1cfb10f62827688de6a16a3b0d464138a62332553fc1ea36f17fd374" 0 "0000000000000000000000000000000000000000000000000000000000000000ca2ec7ff4c7c0c3180e0284931f6f6483713630ac0c75599d41dfc6b79a51253" "e8901aec51f74e698974d4a80ca8b57d4b48c5529fce14b6e7c15e12c005be4b1b8d0cf50b8631a73a5f52da5eea8e9c2bd53ee70989b207046037b08b353cfb"}; s at the group's order: {recovered "5f2dd97f1cfb10f62827688de6a16a3b0d464138a62332553fc1ea36f17fd374" 0 "9ffa343ed7948d987918baa784a8ce0d517fcfe743f34fda9ee960c8c57c2bb4fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141" "e8901aec51f74e698974d4a80ca8b57d4b48c5529fce14b6e7c15e12c005be4b1b8d0cf50b8631a73a5f52da5eea8e9c2bd53ee70989b207046037b08b353cfb"}; a candidate that does not exist: {recovered "5f2dd97f1cfb10f62827688de6a16a3b0d464138a62332553fc1ea36f17fd374" 4 "9ffa343ed7948d987918baa784a8ce0d517fcfe743f34fda9ee960c8c57c2bb4ca2ec7ff4c7c0c3180e0284931f6f6483713630ac0c75599d41dfc6b79a51253" "e8901aec51f74e698974d4a80ca8b57d4b48c5529fce14b6e7c15e12c005be4b1b8d0cf50b8631a73a5f52da5eea8e9c2bd53ee70989b207046037b08b353cfb"}"

  -- rewards: a × b / (c × d) where the products need 128 bits
  IO.println (ratioLine 88373627028219503 4812263350427377 432000 219422777475117211 4486489036)
  IO.println (ratioLine 97514616247484246 6094730419354193 432000 540729259402726871 2544254783)
  IO.println (ratioLine 87146286158371614 6017240938857688 432000 813175631550155728 1492719420)
  IO.println (ratioLine 24415159833816516 7612647962698326 432000 201796881823127036 2132048700)
  IO.println (ratioLine 7398013470137901 2385567046635178 432000 75397286310273156 541835284)
  IO.println (ratioLine 99214770065020779 3692234311116180 432000 262293764287324320 3232911910)
  IO.println (ratioLine 18446744073709551615 18446744073709551615 4294967296 8589934592 9223372036854775807)
  IO.println (ratioLine 5 7 3 0 0)

  -- a certificate's bitmap: kind 0, a count of bits, the bits
  let bitmap : ByteArray := (((ByteArray.empty.push 0).push 11).push 0).push 0b10000101 |>.push 0b00000110
  let mut set := ""
  for rank in [0:14] do
    if Alpenglow.named bitmap rank then
      set := set ++ s!"{rank} "
  IO.println s!"ranks a bitmap names: {set}(of 11)"

  -- a vote account: taken apart and put back unchanged
  let account := voteAccount #[100, 101, 102] 99 #[1097, 500, 400, 1098, 650, 500] 1000
  let state := Alpenglow.VoteState.parse account
  IO.println s!"parsed: {state.ok}; last vote {state.lastVoted}, root {state.root}, timestamp {state.timestamp}; credits {creditsOf state}"
  IO.println s!"put back unchanged: {state.bytes == account}"
  -- a certificate says it voted on slot 120
  let voted := state.voted 120 2000999999999
  IO.println s!"voted on 120: last vote {voted.lastVoted}, timestamp {voted.timestamp} at slot {voted.timestampSlot}; votes take {voted.votes.size} bytes"
  IO.println s!"voted on an older slot, at an earlier time: last vote {(state.voted 50 5).lastVoted}, timestamp {(state.voted 50 5).timestamp}"
  IO.println s!"slot 130 final: root {(state.rooted 130).root}; slot 90 final: root {(state.rooted 90).root}"
  -- credits: the same epoch grows; a new epoch starts a new entry; an untouched entry is taken over
  IO.println s!"credited 25 in epoch 1098: {creditsOf (state.credit 1064 1098 25)}"
  IO.println s!"credited 25 in epoch 1099: {creditsOf (state.credit 1064 1099 25)}"
  let idle := Alpenglow.VoteState.parse (voteAccount #[] 0 #[1090, 500, 500] 0)
  IO.println s!"an entry nothing was added to is reused: {creditsOf (idle.credit 1064 1099 7)}"
  IO.println s!"no credits yet: {creditsOf ((Alpenglow.VoteState.parse (voteAccount #[] 0 #[] 0)).credit 1064 5 9)}"
  IO.println s!"in the epoch Alpenglow took over, a marker goes first: {creditsOf (state.credit 1098 1098 25)}"
  IO.println s!"still the right size: {(voted.credit 1064 1099 25).bytes.size}; not a vote account: {(Alpenglow.VoteState.parse long).ok}"

  -- a footer's certificates: finality for one slot, a reward certificate for another
  let mut footer := (ByteArray.empty.push 1)
  footer := Wire.putU64 footer 4242
  for i in [0:128] do
    footer := footer.push i.toUInt8
  footer := Wire.putU16 footer bitmap.size.toUInt64 ++ bitmap
  footer := (footer.push 0).push 0
  footer := Wire.putU64 (footer.push 1) 4235
  for i in [0:128] do
    footer := footer.push i.toUInt8
  footer := footer.push bitmap.size.toUInt8 ++ bitmap
  let certs := Alpenglow.parse footer
  IO.println s!"footer: {certs.error} final slot {certs.finalSlot} ({certs.finalBits.size} bitmap), reward slot {certs.rewardSlot} ({certs.rewardBits.size} bitmap), rank 2 named {Alpenglow.namedByAny certs.rewardBits 2}, rank 3 named {Alpenglow.namedByAny certs.rewardBits 3}"
  IO.println s!"a footer cut short: {(Alpenglow.parse (footer.extract 0 100)).error}; an empty one: final {(Alpenglow.parse ByteArray.empty).finalSlot}"
