import Fast

/-!
# AES-128 and its use as an authenticated cipher (GCM)

AES turns a block of 16 bytes into another under a key, ten rounds of
substituting, shifting, mixing and adding round keys (FIPS 197). GCM (NIST
SP 800-38D) makes a cipher for messages of any length out of it: the message
is combined with the encryptions of a counter, and a 16-byte tag, a
polynomial in a secret point evaluated over the ciphertext and whatever else
is to be vouched for, shows that nothing was changed.

Only encryption of a block is needed: GCM never decrypts one. This is plain
table-free code, a megabyte or so a second, which is what a node's control
traffic needs; and like the rest of the cryptography here its timing depends
on its inputs.
-/

namespace Aes

/-- Multiplication by `x` in the field of 256 elements AES works in. -/
@[inline] def double (b : UInt8) : UInt8 := (b <<< 1) ^^^ (if b &&& 0x80 != 0 then 0x1b else 0)

/-- The substitution: each byte's inverse in that field, then a fixed shuffle of its bits. -/
def sbox : ByteArray := Id.run do
  let mut table := Fast.zeroed 256 256
  let mut p : UInt8 := 1
  let mut q : UInt8 := 1
  for _ in [0:255] do
    -- p runs through the powers of 3, q through their inverses
    p := p ^^^ double p
    q := q ^^^ (q <<< 1)
    q := q ^^^ (q <<< 2)
    q := q ^^^ (q <<< 4)
    q := q ^^^ (if q &&& 0x80 != 0 then 0x09 else 0)
    let x := q ^^^ ((q <<< 1) ||| (q >>> 7)) ^^^ ((q <<< 2) ||| (q >>> 6)) ^^^ ((q <<< 3) ||| (q >>> 5)) ^^^ ((q <<< 4) ||| (q >>> 4))
    table := table.set! p.toNat (x ^^^ 0x63)
  return table.set! 0 0x63

/-- The eleven round keys of a 16-byte key, 176 bytes. -/
def roundKeys (key : ByteArray) : ByteArray := Id.run do
  let mut w := key.extract 0 16
  let mut constant : UInt8 := 1
  for i in [4:44] do
    let mut a := w[4 * i - 4]!
    let mut b := w[4 * i - 3]!
    let mut c := w[4 * i - 2]!
    let mut d := w[4 * i - 1]!
    if i % 4 == 0 then
      let first := a
      a := sbox[b.toNat]! ^^^ constant
      b := sbox[c.toNat]!
      c := sbox[d.toNat]!
      d := sbox[first.toNat]!
      constant := double constant
    w := (((w.push (w[4 * i - 16]! ^^^ a)).push (w[4 * i - 15]! ^^^ b)).push (w[4 * i - 14]! ^^^ c)).push (w[4 * i - 13]! ^^^ d)
  return w

/-- One block encrypted: the 16 bytes at `from_` in `block`, under round keys `keys`. -/
def encrypt (keys block : ByteArray) (from_ : Nat) : ByteArray := Id.run do
  let mut s := ByteArray.emptyWithCapacity 16
  for i in [0:16] do
    s := s.push (block[from_ + i]! ^^^ keys[i]!)
  for round in [1:11] do
    let mut t := ByteArray.emptyWithCapacity 16
    for column in [0:4] do
      -- substituted, with row r taken from r columns on
      let a := sbox[s[4 * column]!.toNat]!
      let b := sbox[s[(4 * column + 5) % 16]!.toNat]!
      let c := sbox[s[(4 * column + 10) % 16]!.toNat]!
      let d := sbox[s[(4 * column + 15) % 16]!.toNat]!
      if round == 10 then
        t := (((t.push a).push b).push c).push d
      else
        -- each column mixed: every byte twice itself, thrice the next, and the other two
        let all := a ^^^ b ^^^ c ^^^ d
        t := (((t.push (a ^^^ all ^^^ double (a ^^^ b))).push (b ^^^ all ^^^ double (b ^^^ c))).push (c ^^^ all ^^^ double (c ^^^ d))).push (d ^^^ all ^^^ double (d ^^^ a))
    s := ByteArray.emptyWithCapacity 16
    for i in [0:16] do
      s := s.push (t[i]! ^^^ keys[16 * round + i]!)
  return s

-- ------------------------------------------------------------------- GCM

@[inline] def be64 (b : ByteArray) (o : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i in [0:8] do
    v := (v <<< 8) ||| (if o + i < b.size then b[o + i]!.toUInt64 else 0)
  return v

def putBe64 (b : ByteArray) (v : UInt64) : ByteArray := Id.run do
  let mut out := b
  for i in [0:8] do
    out := out.push (v >>> (56 - 8 * i).toUInt64).toUInt8
  return out

/-- The product of two 128-bit values (each two words, the first bit the highest power) as GCM's
field has it: bit by bit, reducing by x¹²⁸ = x⁷ + x² + x + 1. -/
def times (xh xl hh hl : UInt64) : UInt64 × UInt64 := Id.run do
  let mut zh : UInt64 := 0
  let mut zl : UInt64 := 0
  let mut vh := hh
  let mut vl := hl
  for i in [0:128] do
    let bit := if i < 64 then (xh >>> (63 - i).toUInt64) &&& 1 else (xl >>> (127 - i).toUInt64) &&& 1
    if bit == 1 then
      zh := zh ^^^ vh
      zl := zl ^^^ vl
    let carry := vl &&& 1
    vl := (vl >>> 1) ||| (vh <<< 63)
    vh := (vh >>> 1) ^^^ (if carry == 1 then 0xe100000000000000 else 0)
  return (zh, zl)

/-- The tag before it is masked: `extra` and `sealed`, each padded to whole blocks, then their lengths in bits, folded in one block at a time. -/
def digest (hh hl : UInt64) (extra sealed : ByteArray) : UInt64 × UInt64 := Id.run do
  let mut yh : UInt64 := 0
  let mut yl : UInt64 := 0
  for part in [0:2] do
    let data := if part == 0 then extra else sealed
    for block in [0:(data.size + 15) / 16] do
      let (zh, zl) := times (yh ^^^ be64 data (16 * block)) (yl ^^^ be64 data (16 * block + 8)) hh hl
      yh := zh
      yl := zl
  return times (yh ^^^ (8 * extra.size.toUInt64)) (yl ^^^ (8 * sealed.size.toUInt64)) hh hl

/-- `data` combined with the encryptions of the counter blocks that follow `nonce ‖ 1`. -/
def stream (keys nonce data : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (data.size + 16)
  let mut counter := Fast.push32 nonce 0
  for block in [0:(data.size + 15) / 16] do
    let n := block + 2
    counter := (((counter.set! 12 (n >>> 24).toUInt8).set! 13 (n >>> 16).toUInt8).set! 14 (n >>> 8).toUInt8).set! 15 n.toUInt8
    let pad := encrypt keys counter 0
    for i in [0:16] do
      if 16 * block + i < data.size then
        out := out.push (data[16 * block + i]! ^^^ pad[i]!)
  return out

/-- The 16-byte tag over `extra` and the ciphertext `sealed`, for a 12-byte nonce. -/
def tag (keys nonce extra sealed : ByteArray) : ByteArray :=
  let h := encrypt keys (Fast.zeroed 16 16) 0
  let (yh, yl) := digest (be64 h 0) (be64 h 8) extra sealed
  let mask := encrypt keys ((Fast.push32 nonce 0).set! 15 1) 0
  putBe64 (putBe64 (ByteArray.emptyWithCapacity 16) (yh ^^^ be64 mask 0)) (yl ^^^ be64 mask 8)

/-- Seals `plain` under the round keys and a 12-byte nonce, vouching for `extra` too: the ciphertext, then the tag. -/
def shut (keys nonce extra plain : ByteArray) : ByteArray :=
  let sealed := stream keys nonce plain
  sealed ++ tag keys nonce extra sealed

/-- Opens what `shut` made; none if the tag does not fit. -/
def unshut (keys nonce extra sealed : ByteArray) : Option ByteArray :=
  if sealed.size < 16 then none
  else
    let body := sealed.extract 0 (sealed.size - 16)
    if tag keys nonce extra body == sealed.extract (sealed.size - 16) sealed.size then some (stream keys nonce body) else none

end Aes
