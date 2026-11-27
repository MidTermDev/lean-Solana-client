/-!
# BLAKE3

Solana hashes every account with BLAKE3, and not to 32 bytes: to 2048, which
it reads as 1024 sixteen-bit numbers (see `Solana.LtHash`). So this module
gives both the ordinary hash and the *extendable output*.

The design, briefly. Input is cut into chunks of 1024 bytes; each chunk is
hashed block by block (64 bytes) with one compression function; the chunks'
values are then combined pairwise into a binary tree. The last compression,
at the root, can be repeated with a counter to give as much output as is
wanted.
-/

namespace Blake3

def iv : Array UInt32 := #[
  0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

def chunkStart : UInt32 := 1
def chunkEnd : UInt32 := 2
def parent : UInt32 := 4
def root : UInt32 := 8

/-- Which message word each step of each of the seven rounds uses: the
identity for the first round, then the same permutation applied again and
again. -/
def schedule : ByteArray := Id.run do
  let permutation : Array Nat := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
  let mut out := ByteArray.emptyWithCapacity 112
  for i in [0:16] do
    out := out.push i.toUInt8
  for r in [1:7] do
    for i in [0:16] do
      out := out.push out[(r - 1) * 16 + permutation[i]!]!
  return out

@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The compression function. `cv` is the chaining value (8 words), `m` the
block (16 words), `counter` the chunk number or the output block number.
Returns all 16 words of output; the first 8 are the new chaining value. -/
def compress (cv : Array UInt32) (m : Array UInt32) (counter : UInt64) (blockLen flags : UInt32) : Array UInt32 := Id.run do
  let s := schedule
  let mut v0 := cv[0]!
  let mut v1 := cv[1]!
  let mut v2 := cv[2]!
  let mut v3 := cv[3]!
  let mut v4 := cv[4]!
  let mut v5 := cv[5]!
  let mut v6 := cv[6]!
  let mut v7 := cv[7]!
  let mut v8 := iv[0]!
  let mut v9 := iv[1]!
  let mut v10 := iv[2]!
  let mut v11 := iv[3]!
  let mut v12 := counter.toUInt32
  let mut v13 := (counter >>> 32).toUInt32
  let mut v14 := blockLen
  let mut v15 := flags
  for r in [0:7] do
    let at_ := r * 16
    v0 := v0 + v4 + m[s[at_ + 0]!.toNat]!
    v12 := rotr (v12 ^^^ v0) 16
    v8 := v8 + v12
    v4 := rotr (v4 ^^^ v8) 12
    v0 := v0 + v4 + m[s[at_ + 1]!.toNat]!
    v12 := rotr (v12 ^^^ v0) 8
    v8 := v8 + v12
    v4 := rotr (v4 ^^^ v8) 7
    v1 := v1 + v5 + m[s[at_ + 2]!.toNat]!
    v13 := rotr (v13 ^^^ v1) 16
    v9 := v9 + v13
    v5 := rotr (v5 ^^^ v9) 12
    v1 := v1 + v5 + m[s[at_ + 3]!.toNat]!
    v13 := rotr (v13 ^^^ v1) 8
    v9 := v9 + v13
    v5 := rotr (v5 ^^^ v9) 7
    v2 := v2 + v6 + m[s[at_ + 4]!.toNat]!
    v14 := rotr (v14 ^^^ v2) 16
    v10 := v10 + v14
    v6 := rotr (v6 ^^^ v10) 12
    v2 := v2 + v6 + m[s[at_ + 5]!.toNat]!
    v14 := rotr (v14 ^^^ v2) 8
    v10 := v10 + v14
    v6 := rotr (v6 ^^^ v10) 7
    v3 := v3 + v7 + m[s[at_ + 6]!.toNat]!
    v15 := rotr (v15 ^^^ v3) 16
    v11 := v11 + v15
    v7 := rotr (v7 ^^^ v11) 12
    v3 := v3 + v7 + m[s[at_ + 7]!.toNat]!
    v15 := rotr (v15 ^^^ v3) 8
    v11 := v11 + v15
    v7 := rotr (v7 ^^^ v11) 7
    v0 := v0 + v5 + m[s[at_ + 8]!.toNat]!
    v15 := rotr (v15 ^^^ v0) 16
    v10 := v10 + v15
    v5 := rotr (v5 ^^^ v10) 12
    v0 := v0 + v5 + m[s[at_ + 9]!.toNat]!
    v15 := rotr (v15 ^^^ v0) 8
    v10 := v10 + v15
    v5 := rotr (v5 ^^^ v10) 7
    v1 := v1 + v6 + m[s[at_ + 10]!.toNat]!
    v12 := rotr (v12 ^^^ v1) 16
    v11 := v11 + v12
    v6 := rotr (v6 ^^^ v11) 12
    v1 := v1 + v6 + m[s[at_ + 11]!.toNat]!
    v12 := rotr (v12 ^^^ v1) 8
    v11 := v11 + v12
    v6 := rotr (v6 ^^^ v11) 7
    v2 := v2 + v7 + m[s[at_ + 12]!.toNat]!
    v13 := rotr (v13 ^^^ v2) 16
    v8 := v8 + v13
    v7 := rotr (v7 ^^^ v8) 12
    v2 := v2 + v7 + m[s[at_ + 13]!.toNat]!
    v13 := rotr (v13 ^^^ v2) 8
    v8 := v8 + v13
    v7 := rotr (v7 ^^^ v8) 7
    v3 := v3 + v4 + m[s[at_ + 14]!.toNat]!
    v14 := rotr (v14 ^^^ v3) 16
    v9 := v9 + v14
    v4 := rotr (v4 ^^^ v9) 12
    v3 := v3 + v4 + m[s[at_ + 15]!.toNat]!
    v14 := rotr (v14 ^^^ v3) 8
    v9 := v9 + v14
    v4 := rotr (v4 ^^^ v9) 7
  return #[v0 ^^^ v8, v1 ^^^ v9, v2 ^^^ v10, v3 ^^^ v11, v4 ^^^ v12, v5 ^^^ v13, v6 ^^^ v14, v7 ^^^ v15,
    v8 ^^^ cv[0]!, v9 ^^^ cv[1]!, v10 ^^^ cv[2]!, v11 ^^^ cv[3]!, v12 ^^^ cv[4]!, v13 ^^^ cv[5]!, v14 ^^^ cv[6]!, v15 ^^^ cv[7]!]

/-- The 64 bytes at `off` as 16 little-endian words. -/
def block (b : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut m : Array UInt32 := Array.emptyWithCapacity 16
  for i in [0:16] do
    let j := off + 4 * i
    m := m.push (b[j]!.toUInt32 ||| (b[j + 1]!.toUInt32 <<< 8) ||| (b[j + 2]!.toUInt32 <<< 16) ||| (b[j + 3]!.toUInt32 <<< 24))
  return m

/-- Up to 64 bytes `b[off, stop)` as 16 words, padded with zeros. -/
def lastBlock (b : ByteArray) (off stop : Nat) : Array UInt32 := Id.run do
  if stop == off + 64 then
    return block b off
  let mut padded := b.extract off stop
  while padded.size < 64 do
    padded := padded.push 0
  return block padded 0

def first8 (v : Array UInt32) : Array UInt32 :=
  #[v[0]!, v[1]!, v[2]!, v[3]!, v[4]!, v[5]!, v[6]!, v[7]!]

/-- A compression that has not been done yet: the root's can be repeated for more output. -/
structure Node where
  cv : Array UInt32
  block : Array UInt32
  counter : UInt64
  blockLen : UInt32
  flags : UInt32
  deriving Inhabited

def Node.value (n : Node) : Array UInt32 :=
  first8 (compress n.cv n.block n.counter n.blockLen n.flags)

/-- One chunk: `b[start, stop)`, at most 1024 bytes, chunk number `counter`. -/
def chunk (b : ByteArray) (start stop : Nat) (counter : UInt64) : Node := Id.run do
  let mut cv := iv
  let mut o := start
  let mut flags := chunkStart
  -- every block but the last (the last may be full, partial, or empty)
  while o + 64 < stop do
    cv := first8 (compress cv (block b o) counter 64 flags)
    flags := 0
    o := o + 64
  return ⟨cv, lastBlock b o stop, counter, (stop - o).toUInt32, flags ||| chunkEnd⟩

def join (left right : Array UInt32) : Node :=
  ⟨iv, #[left[0]!, left[1]!, left[2]!, left[3]!, left[4]!, left[5]!, left[6]!, left[7]!,
    right[0]!, right[1]!, right[2]!, right[3]!, right[4]!, right[5]!, right[6]!, right[7]!], 0, 64, parent⟩

/-- Hashes `b` down to the root of its tree. -/
def rootNode (b : ByteArray) : Node := Id.run do
  let chunks := if b.size == 0 then 1 else (b.size + 1023) / 1024
  -- values of finished subtrees, largest first: one for each set bit of the number of chunks done
  let mut stack : Array (Array UInt32) := Array.emptyWithCapacity 54
  for i in [0:chunks - 1] do
    let mut value := (chunk b (i * 1024) (i * 1024 + 1024) i.toUInt64).value
    let mut done := i + 1
    while done % 2 == 0 do
      value := (join stack[stack.size - 1]! value).value
      stack := stack.pop
      done := done / 2
    stack := stack.push value
  let mut node := chunk b ((chunks - 1) * 1024) b.size (chunks - 1).toUInt64
  while stack.size > 0 do
    node := join stack[stack.size - 1]! node.value
    stack := stack.pop
  return node

/-- The 16 words of output block number `k` of a root node. -/
@[inline] def Node.output (n : Node) (k : UInt64) : Array UInt32 :=
  compress n.cv n.block k n.blockLen (n.flags ||| root)

/-- `length` bytes of output. -/
def Node.bytes (n : Node) (length : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (length + 64)
  let mut k : UInt64 := 0
  while out.size < length do
    let words := n.output k
    for w in words do
      out := out.push w.toUInt8
      out := out.push (w >>> 8).toUInt8
      out := out.push (w >>> 16).toUInt8
      out := out.push (w >>> 24).toUInt8
    k := k + 1
  return out.extract 0 length

/-- BLAKE3 of `b`: 32 bytes. -/
def hash (b : ByteArray) : ByteArray := (rootNode b).bytes 32

/-- BLAKE3 of `b`, extended to `length` bytes. -/
def xof (b : ByteArray) (length : Nat) : ByteArray := (rootNode b).bytes length

end Blake3
