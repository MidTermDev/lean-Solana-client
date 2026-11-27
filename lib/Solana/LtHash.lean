import Crypto.Blake3

/-!
# The lattice hash of all accounts

Solana summarises the whole of its state, every account, in one value that
can be updated without rereading the state: each account is hashed to 1024
sixteen-bit numbers, and the state's hash is the element-wise sum of all of
them, each sum wrapping at 65,536. Changing an account subtracts its old
hash and adds its new one.

A snapshot is named after this value (after its 32-byte BLAKE3 *checksum*),
and so is every block, through the bank hash.

The 1024 numbers are held here as 256 words of 64 bits, four numbers to a
word, and added four at a time.
-/

namespace LtHash

def zero : Array UInt64 := Array.replicate 256 0

def high : UInt64 := 0x8000800080008000
def low : UInt64 := 0x7FFF7FFF7FFF7FFF

/-- Four sixteen-bit additions at once: the low 15 bits of each are added
normally (no carry can leave its lane), and the top bits are added without
carry by exclusive-or. -/
@[inline] def add4 (a b : UInt64) : UInt64 := ((a &&& low) + (b &&& low)) ^^^ ((a ^^^ b) &&& high)

/-- Four sixteen-bit subtractions at once, by the same idea. -/
@[inline] def sub4 (a b : UInt64) : UInt64 := ((a ||| high) - (b &&& low)) ^^^ ((a ^^^ ~~~b) &&& high)

/-- What an account is hashed from: lamports, data, executable flag, owner, address. -/
def accountInput (lamports : UInt64) (data : ByteArray) (executable : Bool) (owner pubkey : ByteArray) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (data.size + 73)
  for i in [0:8] do
    b := b.push (lamports >>> (8 * i).toUInt64).toUInt8
  b := b ++ data
  b := b.push (if executable then 1 else 0)
  return b ++ owner ++ pubkey

/-- Adds to `sum` (or removes from it) the lattice hash of the input whose BLAKE3 root is `node`. With
`wide`, the 32 blocks of output are made sixteen at a time. -/
def mixNodeBy (sum : Array UInt64) (node : Blake3.Node) (remove wide : Bool) : Array UInt64 := Id.run do
  let mut out := sum
  if wide then
    let mut f := Blake3.Wide.template
    for half in [0:2] do
      f := Blake3.Wide.output f node (16 * half).toUInt64
      for j in [0:128] do
        let lane := Fast.le64 f (2560 + 8 * j)
        let at_ := 128 * half + j
        out := out.set! at_ (if remove then sub4 out[at_]! lane else add4 out[at_]! lane)
    return out
  for k in [0:32] do
    let w := node.output k.toUInt64
    for j in [0:8] do
      let lane := w[2 * j]!.toUInt64 ||| (w[2 * j + 1]!.toUInt64 <<< 32)
      let at_ := 8 * k + j
      out := out.set! at_ (if remove then sub4 out[at_]! lane else add4 out[at_]! lane)
  return out

def mixNode (sum : Array UInt64) (node : Blake3.Node) (remove : Bool) : Array UInt64 :=
  mixNodeBy sum node remove Fast.quick

/-- What an account adds to the sum: 2048 bytes (1024 sixteen-bit numbers), or nothing at all for an
account with no lamports. Worth keeping: when the account next changes, this is what has to be taken out
again, and it need not be worked out twice. -/
def contribution (lamports : UInt64) (data : ByteArray) (executable : Bool) (owner pubkey : ByteArray) : ByteArray :=
  if lamports == 0 then ByteArray.empty
  else (Blake3.rootNode (accountInput lamports data executable owner pubkey)).bytesBy 2048 Fast.quick

/-- Adds a `contribution` to the sum, or removes it. -/
def addBytes (sum : Array UInt64) (c : ByteArray) (remove : Bool) : Array UInt64 := Id.run do
  if c.size != 2048 then
    return sum
  let mut out := sum
  for i in [0:256] do
    let lane := Fast.le64 c (8 * i)
    out := out.set! i (if remove then sub4 out[i]! lane else add4 out[i]! lane)
  return out

/-- The sum as its 2048 bytes. -/
def bytes (sum : Array UInt64) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 2048
  for v in sum do
    for i in [0:8] do
      b := b.push (v >>> (8 * i).toUInt64).toUInt8
  return b

def ofBytes (b : ByteArray) : Array UInt64 := Id.run do
  let mut sum : Array UInt64 := Array.emptyWithCapacity 256
  for i in [0:256] do
    let mut v : UInt64 := 0
    for j in [0:8] do
      v := v ||| (b[8 * i + j]!.toUInt64 <<< (8 * j).toUInt64)
    sum := sum.push v
  return sum

-- With the vector instructions the sum is kept as bytes, in a file of registers (see `Fast`): the sum in
-- registers 0-31, and what is being added in 32-63. Adding is then 32 instructions.

/-- A sum as such a file. -/
def toFile (sum : Array UInt64) : ByteArray := Id.run do
  let mut f := bytes sum
  for _ in [0:2048] do
    f := f.push 0
  return f

def ofFile (f : ByteArray) : Array UInt64 := ofBytes f

def addFile (f0 : ByteArray) : ByteArray :=
  let f := f0
  let f := Fast.add16 f 0 0 32
  let f := Fast.add16 f 1 1 33
  let f := Fast.add16 f 2 2 34
  let f := Fast.add16 f 3 3 35
  let f := Fast.add16 f 4 4 36
  let f := Fast.add16 f 5 5 37
  let f := Fast.add16 f 6 6 38
  let f := Fast.add16 f 7 7 39
  let f := Fast.add16 f 8 8 40
  let f := Fast.add16 f 9 9 41
  let f := Fast.add16 f 10 10 42
  let f := Fast.add16 f 11 11 43
  let f := Fast.add16 f 12 12 44
  let f := Fast.add16 f 13 13 45
  let f := Fast.add16 f 14 14 46
  let f := Fast.add16 f 15 15 47
  let f := Fast.add16 f 16 16 48
  let f := Fast.add16 f 17 17 49
  let f := Fast.add16 f 18 18 50
  let f := Fast.add16 f 19 19 51
  let f := Fast.add16 f 20 20 52
  let f := Fast.add16 f 21 21 53
  let f := Fast.add16 f 22 22 54
  let f := Fast.add16 f 23 23 55
  let f := Fast.add16 f 24 24 56
  let f := Fast.add16 f 25 25 57
  let f := Fast.add16 f 26 26 58
  let f := Fast.add16 f 27 27 59
  let f := Fast.add16 f 28 28 60
  let f := Fast.add16 f 29 29 61
  let f := Fast.add16 f 30 30 62
  let f := Fast.add16 f 31 31 63
  f

def subFile (f0 : ByteArray) : ByteArray :=
  let f := f0
  let f := Fast.sub16 f 0 0 32
  let f := Fast.sub16 f 1 1 33
  let f := Fast.sub16 f 2 2 34
  let f := Fast.sub16 f 3 3 35
  let f := Fast.sub16 f 4 4 36
  let f := Fast.sub16 f 5 5 37
  let f := Fast.sub16 f 6 6 38
  let f := Fast.sub16 f 7 7 39
  let f := Fast.sub16 f 8 8 40
  let f := Fast.sub16 f 9 9 41
  let f := Fast.sub16 f 10 10 42
  let f := Fast.sub16 f 11 11 43
  let f := Fast.sub16 f 12 12 44
  let f := Fast.sub16 f 13 13 45
  let f := Fast.sub16 f 14 14 46
  let f := Fast.sub16 f 15 15 47
  let f := Fast.sub16 f 16 16 48
  let f := Fast.sub16 f 17 17 49
  let f := Fast.sub16 f 18 18 50
  let f := Fast.sub16 f 19 19 51
  let f := Fast.sub16 f 20 20 52
  let f := Fast.sub16 f 21 21 53
  let f := Fast.sub16 f 22 22 54
  let f := Fast.sub16 f 23 23 55
  let f := Fast.sub16 f 24 24 56
  let f := Fast.sub16 f 25 25 57
  let f := Fast.sub16 f 26 26 58
  let f := Fast.sub16 f 27 27 59
  let f := Fast.sub16 f 28 28 60
  let f := Fast.sub16 f 29 29 61
  let f := Fast.sub16 f 30 30 62
  let f := Fast.sub16 f 31 31 63
  f

/-- Adds a `contribution` to a sum held as a file, or removes it. With `wide` by the vector
instructions; the result is the same either way. -/
def addToFile (f : ByteArray) (c : ByteArray) (remove wide : Bool) : ByteArray :=
  if c.size != 2048 then f
  else if wide then
    let loaded := c.copySlice 0 f 2048 2048
    if remove then subFile loaded else addFile loaded
  else
    let sum := addBytes (ofBytes f) c remove
    (bytes sum).copySlice 0 f 0 2048

/-- Adds an account to the sum, or removes it. An account with no lamports does not exist, and counts for nothing. -/
def mixAccount (sum : Array UInt64) (lamports : UInt64) (data : ByteArray) (executable : Bool) (owner pubkey : ByteArray)
    (remove : Bool) : Array UInt64 :=
  if lamports == 0 then sum
  else mixNode sum (Blake3.rootNode (accountInput lamports data executable owner pubkey)) remove

/-- The same for an account lying in a buffer: `data`, `owner` and `pubkey` are offsets into `b`. -/
def mixStored (sum : Array UInt64) (b : ByteArray) (lamports : UInt64) (data dataLen : Nat) (executable : Bool)
    (owner pubkey : Nat) (remove : Bool) : Array UInt64 := Id.run do
  if lamports == 0 then
    return sum
  let mut input := ByteArray.emptyWithCapacity (dataLen + 73)
  for i in [0:8] do
    input := input.push (lamports >>> (8 * i).toUInt64).toUInt8
  input := b.copySlice data input 8 dataLen
  input := input.push (if executable then 1 else 0)
  input := b.copySlice owner input input.size 32
  input := b.copySlice pubkey input input.size 32
  return mixNode sum (Blake3.rootNode input) remove

/-- Adds one sum to another (or removes it). -/
def combine (a b : Array UInt64) (remove : Bool) : Array UInt64 := Id.run do
  let mut out := a
  for i in [0:256] do
    out := out.set! i (if remove then sub4 a[i]! b[i]! else add4 a[i]! b[i]!)
  return out

/-- The 32 bytes a snapshot is named after. -/
def checksum (sum : Array UInt64) : ByteArray := Blake3.hash (bytes sum)

end LtHash
