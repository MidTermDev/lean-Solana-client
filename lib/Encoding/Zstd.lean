import Solana.Wire

/-!
# Zstandard decompression

Solana snapshots are tar archives compressed with Zstandard, over a hundred
gigabytes of them, so this decoder is a stream: feed it input in pieces of
any size, and it returns the output each piece completes.

The format (RFC 8878), in brief. A *frame* is a header and a sequence of
*blocks* of at most 128 KiB. A block is raw bytes, one byte repeated, or
compressed. A compressed block has two parts:

* **literals**: bytes that are simply stored, usually Huffman-coded;
* **sequences**: instructions of the form "copy `l` literals, then copy `m`
  bytes from `o` bytes back in the output". The three numbers are coded with
  three FSE tables (a table-driven form of arithmetic coding), their low
  bits written out plainly.

Huffman and FSE streams are written backwards: the decoder starts at the
last byte, whose highest set bit marks the end, and reads towards the start.

Output is also kept in a ring the size of the frame's window, since a copy
may reach back that far, across blocks.
-/

namespace Zstd

-- ------------------------------------------------------------ bit streams

/-- A stream read backwards from its last byte. `hold` has the next bits at
its top, `count` of them valid; `at_` is the next byte to load, moving down
to `start`. Bits asked for beyond the stream's start read as zero, and are
counted in `over`. -/
structure Back where
  hold : UInt64
  count : Nat
  at_ : Nat
  start : Nat
  over : Nat
  deriving Inhabited

def Back.refill (r : Back) (b : ByteArray) : Back := Id.run do
  let mut hold := r.hold
  let mut count := r.count
  let mut at_ := r.at_
  while count <= 56 && at_ > r.start do
    at_ := at_ - 1
    hold := hold ||| (b[at_]!.toUInt64 <<< (56 - count).toUInt64)
    count := count + 8
  return { r with hold := hold, count := count, at_ := at_ }

/-- Opens the stream `b[start, stop)`: skips the padding and the end mark in its last byte. -/
def Back.init (b : ByteArray) (start stop : Nat) : Back := Id.run do
  if stop <= start || stop > b.size || b[stop - 1]! == 0 then
    return ⟨0, 0, start, start, 1⟩
  let last := b[stop - 1]!
  let mut high := 7
  while (last >>> high.toUInt8) &&& 1 == 0 do
    high := high - 1
  -- the bits below the end mark are the first to be read
  let r : Back := ⟨if high == 0 then 0 else last.toUInt64 <<< (64 - high).toUInt64, high, stop - 1, start, 0⟩
  return r.refill b

/-- The next `n` bits (`n` ≤ 32) without consuming them. -/
@[inline] def Back.peek (r : Back) (n : Nat) : UInt64 :=
  if n == 0 then 0 else r.hold >>> (64 - n).toUInt64

def Back.skip (r : Back) (b : ByteArray) (n : Nat) : Back :=
  if n <= r.count then
    let next := { r with hold := r.hold <<< n.toUInt64, count := r.count - n }
    if next.count <= 32 then next.refill b else next
  else
    { r with hold := 0, count := 0, over := r.over + (n - r.count) }

/-- True when exactly every bit of the stream has been read. -/
def Back.finished (r : Back) : Bool := r.count == 0 && r.at_ == r.start && r.over == 0

/-- `n` bits (at most 56) starting `bit` bits into `b`, least significant first. -/
def bitsAt (b : ByteArray) (bit n : Nat) : UInt64 :=
  if n == 0 then 0
  else (Wire.u64 b (bit / 8) >>> (bit % 8).toUInt64) &&& (((1 : UInt64) <<< n.toUInt64) - 1)

/-- Position of the highest set bit of a non-zero number. -/
def highBit (x : Nat) : Nat := Id.run do
  let mut n := 0
  let mut v := x
  while v > 1 do
    v := v / 2
    n := n + 1
  return n

-- -------------------------------------------------------------------- FSE

/-- An FSE decoding table of `2 ^ log` states: each gives a symbol, a number
of bits to read, and the base those bits are added to for the next state. -/
structure Table where
  log : Nat
  symbol : ByteArray
  bits : ByteArray
  base : Array UInt64
  deriving Inhabited

def noTable : Table := ⟨0, ByteArray.empty, ByteArray.empty, Array.emptyWithCapacity 0⟩

/-- Builds the decoding table from normalised counts (`0xFFFF` stands for
"less than one": such a symbol gets a single state, at the end). -/
def buildTable (counts : Array UInt64) (log : Nat) : Table := Id.run do
  let size := 1 <<< log
  let mut symbol := ByteArray.emptyWithCapacity size
  for _ in [0:size] do
    symbol := symbol.push 0
  let mut next : Array UInt64 := Array.emptyWithCapacity counts.size
  let mut high := size - 1
  for s in [0:counts.size] do
    if counts[s]! == 0xFFFF then
      symbol := symbol.set! high s.toUInt8
      high := high - 1
      next := next.push 1
    else
      next := next.push counts[s]!
  -- spread the symbols over the states with a step that visits every state once
  let step := (size >>> 1) + (size >>> 3) + 3
  let mut position := 0
  for s in [0:counts.size] do
    if counts[s]! != 0xFFFF then
      for _ in [0:counts[s]!.toNat] do
        symbol := symbol.set! position s.toUInt8
        position := (position + step) % size
        while position > high do
          position := (position + step) % size
  let mut bits := ByteArray.emptyWithCapacity size
  let mut base : Array UInt64 := Array.emptyWithCapacity size
  for u in [0:size] do
    let s := symbol[u]!.toNat
    let state := next[s]!.toNat
    next := next.set! s (state + 1).toUInt64
    let n := log - highBit state
    bits := bits.push n.toUInt8
    base := base.push ((state <<< n) - size).toUInt64
  return ⟨log, symbol, bits, base⟩

/-- A table with a single state that always gives `symbol` and reads no bits. -/
def rleTable (symbol : UInt8) : Table :=
  ⟨0, ByteArray.empty.push symbol, ByteArray.empty.push 0, #[0]⟩

/-- Reads the description of an FSE table: its size, then each symbol's
normalised count in a variable number of bits. Returns the table and the
offset just past the description, or `Wire.bad`. -/
def readTable (b : ByteArray) (start stop maxLog maxSymbol : Nat) : Table × Nat := Id.run do
  if start >= stop then
    return (noTable, Wire.bad)
  let log := (b[start]!.toNat &&& 15) + 5
  if log > maxLog then
    return (noTable, Wire.bad)
  let mut bit := start * 8 + 4
  let mut remaining := (1 <<< log) + 1
  let mut threshold := 1 <<< log
  let mut width := log + 1
  let mut counts : Array UInt64 := Array.emptyWithCapacity 64
  let mut previousZero := false
  while remaining > 1 && counts.size <= maxSymbol do
    if previousZero then
      -- after a zero: how many more zeros follow, two bits at a time
      let mut again := true
      while again do
        let n := (bitsAt b bit 2).toNat
        bit := bit + 2
        for _ in [0:n] do
          counts := counts.push 0
        again := n == 3
      previousZero := false
    else
      let max := 2 * threshold - 1 - remaining
      let low := (bitsAt b bit (width - 1)).toNat
      let mut value := 0
      if low < max then
        value := low
        bit := bit + width - 1
      else
        value := (bitsAt b bit width).toNat
        if value >= threshold then
          value := value - max
        bit := bit + width
      -- the value is the count plus one; zero means "less than one"
      if value == 0 then
        counts := counts.push 0xFFFF
        remaining := remaining - 1
      else
        counts := counts.push (value - 1).toUInt64
        if value - 1 > remaining then
          return (noTable, Wire.bad)
        remaining := remaining - (value - 1)
        previousZero := value == 1
      while remaining < threshold && threshold > 1 do
        width := width - 1
        threshold := threshold / 2
    if bit > stop * 8 then
      return (noTable, Wire.bad)
  if remaining != 1 || counts.size > maxSymbol + 1 then
    return (noTable, Wire.bad)
  return (buildTable counts log, (bit + 7) / 8)

def counts (values : Array Nat) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.emptyWithCapacity values.size
  for v in values do
    out := out.push v.toUInt64
  return out

-- The tables used when a block does not bring its own.
def defaultLiteralLengths : Table :=
  buildTable (counts #[4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1,
    0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF]) 6
def defaultMatchLengths : Table :=
  buildTable (counts #[1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF]) 6
def defaultOffsets : Table :=
  buildTable (counts #[1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0xFFFF, 0xFFFF, 0xFFFF,
    0xFFFF, 0xFFFF]) 5

-- What the codes for literal lengths and match lengths stand for: a base value and a number of extra bits.
def literalBase : Array UInt64 := counts #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 28,
  32, 40, 48, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]
def literalBits : ByteArray := Id.run do
  let extra : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8, 9, 10,
    11, 12, 13, 14, 15, 16]
  let mut b := ByteArray.emptyWithCapacity 36
  for e in extra do
    b := b.push e.toUInt8
  return b
def matchBase : Array UInt64 := counts #[3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
  25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 39, 41, 43, 47, 51, 59, 67, 83, 99, 131, 259, 515, 1027, 2051, 4099,
  8195, 16387, 32771, 65539]
def matchBits : ByteArray := Id.run do
  let extra : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  let mut b := ByteArray.emptyWithCapacity 53
  for e in extra do
    b := b.push e.toUInt8
  return b

-- ---------------------------------------------------------------- Huffman

/-- A Huffman decoding table: looking at the next `log` bits gives a symbol and how many of them it used. -/
structure Huffman where
  log : Nat
  symbol : ByteArray
  bits : ByteArray
  deriving Inhabited

def noHuffman : Huffman := ⟨0, ByteArray.empty, ByteArray.empty⟩

/-- Builds the table from the symbols' weights (0 = absent; a larger weight is a shorter code).
The last symbol's weight is not stored: it is whatever completes the code. -/
def buildHuffman (stored : ByteArray) : Huffman := Id.run do
  let mut sum := 0
  for w in stored do
    if w > 11 then
      return noHuffman
    if w != 0 then
      sum := sum + (1 <<< (w.toNat - 1))
  if sum == 0 || stored.size > 255 then
    return noHuffman
  let log := highBit sum + 1
  let rest := (1 <<< log) - sum
  -- what is left must be a power of two: that is the last symbol's share
  if rest == 0 || rest != (1 <<< highBit rest) || log > 11 then
    return noHuffman
  let weights := stored.push (highBit rest + 1).toUInt8
  -- where each weight's codes start: lightest (longest codes) first
  let mut starts : Array Nat := Array.replicate 13 0
  let mut at_ := 0
  for w in [1:log + 1] do
    starts := starts.set! w at_
    for x in weights do
      if x.toNat == w then
        at_ := at_ + (1 <<< (w - 1))
  let size := 1 <<< log
  let mut symbol := ByteArray.emptyWithCapacity size
  let mut bits := ByteArray.emptyWithCapacity size
  for _ in [0:size] do
    symbol := symbol.push 0
    bits := bits.push 0
  for s in [0:weights.size] do
    let w := weights[s]!.toNat
    if w != 0 then
      let length := 1 <<< (w - 1)
      for u in [starts[w]!:starts[w]! + length] do
        symbol := symbol.set! u s.toUInt8
        bits := bits.set! u (log + 1 - w).toUInt8
      starts := starts.set! w (starts[w]! + length)
  return ⟨log, symbol, bits⟩

/-- Reads a Huffman tree description at `start`. Returns the table and the offset past it, or `Wire.bad`. -/
def readHuffman (b : ByteArray) (start stop : Nat) : Huffman × Nat := Id.run do
  if start >= stop then
    return (noHuffman, Wire.bad)
  let header := b[start]!.toNat
  let mut weights := ByteArray.emptyWithCapacity 256
  let mut next := start + 1
  if header >= 128 then
    -- the weights themselves, four bits each
    let n := header - 127
    next := start + 1 + (n + 1) / 2
    if next > stop then
      return (noHuffman, Wire.bad)
    for i in [0:n] do
      let byte := b[start + 1 + i / 2]!
      weights := weights.push (if i % 2 == 0 then byte >>> 4 else byte &&& 15)
  else
    -- the weights FSE-coded: a table, then two states taking turns over one backward stream
    next := start + 1 + header
    if next > stop then
      return (noHuffman, Wire.bad)
    let (table, body) := readTable b (start + 1) next 6 255
    if !(Wire.ok body) || body > next then
      return (noHuffman, Wire.bad)
    let mut r := Back.init b body next
    let mut s1 := (r.peek table.log).toNat
    r := r.skip b table.log
    let mut s2 := (r.peek table.log).toNat
    r := r.skip b table.log
    let mut going := r.over == 0
    while going && weights.size < 255 do
      weights := weights.push table.symbol[s1]!
      let n1 := table.bits[s1]!.toNat
      if n1 > r.count && r.at_ == r.start then
        -- the stream is used up: the other state still holds one symbol
        weights := weights.push table.symbol[s2]!
        going := false
      else
        s1 := table.base[s1]!.toNat + (r.peek n1).toNat
        r := r.skip b n1
        weights := weights.push table.symbol[s2]!
        let n2 := table.bits[s2]!.toNat
        if n2 > r.count && r.at_ == r.start then
          weights := weights.push table.symbol[s1]!
          going := false
        else
          s2 := table.base[s2]!.toNat + (r.peek n2).toNat
          r := r.skip b n2
  let h := buildHuffman weights
  return (h, if h.log == 0 then Wire.bad else next)

/-- Decodes `count` symbols from the backward stream `b[start, stop)`, appending them to `out`.
Returns `none` unless the stream is used up exactly. -/
def huffmanStream (h : Huffman) (b : ByteArray) (start stop count : Nat) (out : ByteArray) : Option ByteArray := Id.run do
  let mut r := Back.init b start stop
  let mut o := out
  for _ in [0:count] do
    let code := (r.peek h.log).toNat
    o := o.push h.symbol[code]!
    r := r.skip b h.bits[code]!.toNat
  if !r.finished then
    return none
  return some o

-- ---------------------------------------------------------------- decoder

structure Decoder where
  /-- input not yet consumed -/
  pending : ByteArray
  /-- the last `mask + 1` bytes of output, as a ring -/
  window : ByteArray
  mask : Nat
  windowSize : Nat
  /-- bytes of output produced in the current frame -/
  produced : Nat
  /-- 0 = between frames, 1 = inside one -/
  inFrame : Bool
  checksum : Bool
  rep1 : Nat
  rep2 : Nat
  rep3 : Nat
  literalLengths : Table
  offsets : Table
  matchLengths : Table
  huffman : Huffman
  /-- total output of all frames -/
  total : Nat
  /-- at least one frame has ended and no further input is pending -/
  atEnd : Bool
  error : String
  deriving Inhabited

def Decoder.create : Decoder :=
  ⟨ByteArray.empty, ByteArray.empty, 0, 0, 0, false, false, 1, 4, 8, noTable, noTable, noTable, noHuffman, 0, false, ""⟩

def Decoder.fail (d : Decoder) (why : String) : Decoder := { d with error := why }

/-- One of the three sequence tables, as the block's mode byte asks for it:
0 = the default, 1 = a single symbol, 2 = described here, 3 = the previous block's. -/
def chooseTable (mode : UInt64) (b : ByteArray) (o stop : Nat) (standard previous : Table) (maxLog maxSymbol : Nat)
    : Table × Nat :=
  if mode == 0 then (standard, o)
  else if mode == 1 then (if o < stop then (rleTable b[o]!, o + 1) else (noTable, Wire.bad))
  else if mode == 2 then readTable b o stop maxLog maxSymbol
  else (previous, if previous.symbol.size == 0 then Wire.bad else o)

/-- Decodes one compressed block `b[start, stop)`, appending its output to
`out`. A copy from earlier output reads this block's own bytes from `out`,
and anything older from `window`, the ring holding the frame's output up to
the start of this block. -/
def Decoder.block (d0 : Decoder) (window : ByteArray) (b : ByteArray) (start stop : Nat) (out0 : ByteArray) : Decoder × ByteArray := Id.run do
  let mut d := d0
  let mut out := out0
  if stop < start + 1 then
    return (d.fail "truncated block", out)
  -- ---- literals
  let first := b[start]!.toNat
  let kind := first &&& 3
  let format := (first >>> 2) &&& 3
  let mut literals := ByteArray.emptyWithCapacity 131072
  let mut o := start
  if kind < 2 then
    -- stored as they are, or one byte repeated
    let mut size := 0
    if format == 0 || format == 2 then
      size := first >>> 3
      o := start + 1
    else if format == 1 then
      size := (Wire.u16 b start).toNat >>> 4
      o := start + 2
    else
      size := (Wire.u32 b start &&& 0xFFFFFF).toNat >>> 4
      o := start + 3
    if kind == 0 then
      if o + size > stop then
        return (d.fail "literals run past the block", out)
      literals := b.extract o (o + size)
      o := o + size
    else
      if o + 1 > stop then
        return (d.fail "literals run past the block", out)
      for _ in [0:size] do
        literals := literals.push b[o]!
      o := o + 1
  else
    -- Huffman-coded, in one stream or four
    let mut regenerated := 0
    let mut compressed := 0
    let mut streams := 4
    if format == 0 || format == 1 then
      let v := (Wire.u32 b start &&& 0xFFFFFF).toNat
      regenerated := (v >>> 4) &&& 0x3FF
      compressed := (v >>> 14) &&& 0x3FF
      streams := if format == 0 then 1 else 4
      o := start + 3
    else if format == 2 then
      let v := (Wire.u32 b start).toNat
      regenerated := (v >>> 4) &&& 0x3FFF
      compressed := (v >>> 18) &&& 0x3FFF
      o := start + 4
    else
      let v := (Wire.u64 b start &&& 0xFFFFFFFFFF).toNat
      regenerated := (v >>> 4) &&& 0x3FFFF
      compressed := (v >>> 22) &&& 0x3FFFF
      o := start + 5
    let finish := o + compressed
    if finish > stop || regenerated > 131072 then
      return (d.fail "literals run past the block", out)
    if kind == 2 then
      let (h, body) := readHuffman b o finish
      if !(Wire.ok body) then
        return (d.fail "invalid Huffman table", out)
      d := { d with huffman := h }
      o := body
    else if d.huffman.log == 0 then
      return (d.fail "a block reuses a Huffman table that was never sent", out)
    if streams == 1 then
      match huffmanStream d.huffman b o finish regenerated literals with
      | none => return (d.fail "corrupt literals", out)
      | some decoded => literals := decoded
    else
      -- three sizes, then four streams each holding a quarter of the literals
      if o + 6 > finish then
        return (d.fail "corrupt literals", out)
      let s1 := (Wire.u16 b o).toNat
      let s2 := (Wire.u16 b (o + 2)).toNat
      let s3 := (Wire.u16 b (o + 4)).toNat
      let a := o + 6
      if a + s1 + s2 + s3 > finish then
        return (d.fail "corrupt literals", out)
      let quarter := (regenerated + 3) / 4
      if 3 * quarter > regenerated then
        return (d.fail "corrupt literals", out)
      let bounds : Array Nat := #[a, a + s1, a + s1 + s2, a + s1 + s2 + s3, finish]
      for k in [0:4] do
        let n := if k == 3 then regenerated - 3 * quarter else quarter
        match huffmanStream d.huffman b bounds[k]! bounds[k + 1]! n literals with
        | none => return (d.fail "corrupt literals", out)
        | some decoded => literals := decoded
    o := finish
  -- ---- sequences
  if o >= stop then
    return (d.fail "block has no sequence section", out)
  let mut count := b[o]!.toNat
  o := o + 1
  if count >= 128 then
    if count == 255 then
      count := (Wire.u16 b o).toNat + 0x7F00
      o := o + 2
    else
      count := ((count - 128) <<< 8) + (Wire.u8 b o).toNat
      o := o + 1
  let mask := d.mask
  -- where this block's output starts, in `out` and in the frame
  let blockStart := out.size
  let before := d.produced
  let mut used := 0
  if count != 0 then
    if o >= stop then
      return (d.fail "truncated sequences", out)
    let modes := b[o]!.toUInt64
    o := o + 1
    let (ll, o1) := chooseTable (modes >>> 6) b o stop defaultLiteralLengths d.literalLengths 9 35
    if !(Wire.ok o1) then
      return (d.fail "invalid literal-length table", out)
    let (off, o2) := chooseTable ((modes >>> 4) &&& 3) b o1 stop defaultOffsets d.offsets 8 31
    if !(Wire.ok o2) then
      return (d.fail "invalid offset table", out)
    let (ml, o3) := chooseTable ((modes >>> 2) &&& 3) b o2 stop defaultMatchLengths d.matchLengths 9 52
    if !(Wire.ok o3) || o3 > stop then
      return (d.fail "invalid match-length table", out)
    d := { d with literalLengths := ll, offsets := off, matchLengths := ml }
    let mut r := Back.init b o3 stop
    let mut sl := (r.peek ll.log).toNat
    r := r.skip b ll.log
    let mut so := (r.peek off.log).toNat
    r := r.skip b off.log
    let mut sm := (r.peek ml.log).toNat
    r := r.skip b ml.log
    let mut rep1 := d.rep1
    let mut rep2 := d.rep2
    let mut rep3 := d.rep3
    for i in [0:count] do
      let lcode := ll.symbol[sl]!.toNat
      let ocode := off.symbol[so]!.toNat
      let mcode := ml.symbol[sm]!.toNat
      if lcode > 35 || mcode > 52 || ocode > 31 then
        return (d.fail "corrupt sequences", out)
      -- the extra bits come in this order: offset, match length, literal length
      let mut value := ((1 : UInt64) <<< ocode.toUInt64).toNat
      if ocode > 24 then
        -- too many bits for one read
        value := value + ((r.peek (ocode - 24)).toNat <<< 24)
        r := r.skip b (ocode - 24)
        value := value + (r.peek 24).toNat
        r := r.skip b 24
      else
        value := value + (r.peek ocode).toNat
        r := r.skip b ocode
      let mbits := matchBits[mcode]!.toNat
      let length := matchBase[mcode]!.toNat + (r.peek mbits).toNat
      r := r.skip b mbits
      let lbits := literalBits[lcode]!.toNat
      let run := literalBase[lcode]!.toNat + (r.peek lbits).toNat
      r := r.skip b lbits
      -- an offset code of 1 to 3 means one of the last three offsets used
      let mut offset := 0
      if value > 3 then
        offset := value - 3
        rep3 := rep2
        rep2 := rep1
        rep1 := offset
      else
        let which := if run == 0 then value + 1 else value
        if which == 1 then
          offset := rep1
        else
          offset := if which == 2 then rep2 else if which == 3 then rep3 else rep1 - 1
          if which != 2 then
            rep3 := rep2
          rep2 := rep1
          rep1 := offset
      -- the states move on, except after the last sequence
      if i + 1 < count then
        let nl := ll.bits[sl]!.toNat
        sl := ll.base[sl]!.toNat + (r.peek nl).toNat
        r := r.skip b nl
        let nm := ml.bits[sm]!.toNat
        sm := ml.base[sm]!.toNat + (r.peek nm).toNat
        r := r.skip b nm
        let no := off.bits[so]!.toNat
        so := off.base[so]!.toNat + (r.peek no).toNat
        r := r.skip b no
      if r.over != 0 then
        return (d.fail "corrupt sequences", out)
      -- execute: some literals, then a copy from earlier output
      if used + run > literals.size then
        return (d.fail "sequences use more literals than the block has", out)
      out := literals.copySlice used out out.size run
      used := used + run
      let here := out.size - blockStart
      if offset == 0 || offset > before + here || offset > d.windowSize then
        return (d.fail "a copy reaches before the start of the window", out)
      -- byte by byte: a copy may overlap what it is writing
      let mut k := 0
      if offset > here then
        -- it starts before this block
        let old := if offset - here < length then offset - here else length
        let from_ := before + here - offset
        while k < old do
          out := out.push window[(from_ + k) &&& mask]!
          k := k + 1
      while k < length do
        out := out.push out[out.size - offset]!
        k := k + 1
    if !r.finished then
      return (d.fail "corrupt sequences", out)
    d := { d with rep1 := rep1, rep2 := rep2, rep3 := rep3 }
  -- the literals no sequence used come last
  out := literals.copySlice used out out.size (literals.size - used)
  return (d, out)

/-- Gives the decoder more input. Returns it with whatever output that
input completes. Check `error` afterwards; once it is set, nothing more is
produced. -/
def Decoder.feed (d0 : Decoder) (chunk : ByteArray) : Decoder × ByteArray := Id.run do
  let mut d := d0
  if d.error != "" then
    return (d, ByteArray.empty)
  let b := if d.pending.size == 0 then chunk else d.pending ++ chunk
  let mut out := ByteArray.emptyWithCapacity (4 * chunk.size + 65536)
  -- the ring of recent output is held here, apart from the decoder, while it is being written to
  let mut window := d.window
  d := { d with window := ByteArray.empty, pending := ByteArray.empty }
  let mut o := 0
  let mut waiting := false
  while !waiting && d.error == "" do
    if !d.inFrame then
      -- a frame header, or a frame to skip
      if o + 4 > b.size then
        waiting := true
      else
        let magic := Wire.u32 b o
        if magic &&& 0xFFFFFFF0 == 0x184D2A50 then
          if o + 8 > b.size || o + 8 + (Wire.u32 b (o + 4)).toNat > b.size then
            waiting := true
          else
            o := o + 8 + (Wire.u32 b (o + 4)).toNat
        else if magic != 0xFD2FB528 then
          d := d.fail "not a Zstandard stream"
        else if o + 18 > b.size && o + 6 > b.size then
          waiting := true
        else
          let descriptor := b[o + 4]!.toNat
          let single := (descriptor >>> 5) &&& 1 == 1
          let sizeFlag := descriptor >>> 6
          let dictionary := descriptor &&& 3
          let dictionaryBytes := if dictionary == 3 then 4 else dictionary
          let sizeBytes := if sizeFlag == 0 then (if single then 1 else 0) else if sizeFlag == 1 then 2 else if sizeFlag == 2 then 4 else 8
          let headerSize := 5 + (if single then 0 else 1) + dictionaryBytes + sizeBytes
          if o + headerSize > b.size then
            waiting := true
          else if descriptor &&& 8 != 0 then
            d := d.fail "reserved bit set in the frame header"
          else if dictionary != 0 && Wire.u32 b (o + 5 + (if single then 0 else 1)) &&& ((1 <<< (8 * dictionaryBytes).toUInt64) - 1) != 0 then
            d := d.fail "the stream needs a dictionary"
          else
            let mut windowSize := 0
            if single then
              let at_ := o + 5 + dictionaryBytes
              let content := if sizeBytes == 1 then Wire.u8 b at_ else if sizeBytes == 2 then Wire.u16 b at_ + 256
                else if sizeBytes == 4 then Wire.u32 b at_ else Wire.u64 b at_
              windowSize := if content > 0x8000000 then 0x8000001 else content.toNat
            else
              let w := b[o + 5]!.toNat
              let base := 1 <<< (10 + (w >>> 3))
              windowSize := base + (base / 8) * (w &&& 7)
            if windowSize > 0x8000000 then
              d := d.fail "the window is larger than 128 MiB"
            else
              -- a ring of a power-of-two size at least as large as the window
              let mut ring := 1024
              while ring < windowSize do
                ring := ring * 2
              if window.size != ring then
                window := ByteArray.emptyWithCapacity ring
                for _ in [0:ring] do
                  window := window.push 0
              let reach := if windowSize == 0 then 1 else windowSize
              let checked := descriptor &&& 4 != 0
              d := { d with mask := ring - 1, windowSize := reach, produced := 0, inFrame := true, checksum := checked }
              d := { d with rep1 := 1, rep2 := 4, rep3 := 8, atEnd := false }
              d := { d with literalLengths := noTable, offsets := noTable, matchLengths := noTable, huffman := noHuffman }
              o := o + headerSize
    else
      -- a block: three bytes of header, then its content
      if o + 3 > b.size then
        waiting := true
      else
        let header := (Wire.u32 b o &&& 0xFFFFFF).toNat
        let last := header &&& 1 == 1
        let kind := (header >>> 1) &&& 3
        let size := header >>> 3
        let stored := if kind == 1 then 1 else size
        let trailer := if last && d.checksum then 4 else 0
        if size > 131072 || kind == 3 then
          d := d.fail "invalid block header"
        else if o + 3 + stored + trailer > b.size then
          waiting := true
        else
          let before := out.size
          if kind == 0 then
            out := b.copySlice (o + 3) out out.size size
          else if kind == 1 then
            for _ in [0:size] do
              out := out.push b[o + 3]!
          else
            let (next, grown) := d.block window b (o + 3) (o + 3 + size) out
            d := next
            out := grown
          -- the block's output goes into the ring (only its last part, if it is larger than the ring)
          let made := out.size - before
          let ring := d.mask + 1
          let skipped := if made > ring then made - ring else 0
          let at_ := (d.produced + skipped) &&& d.mask
          let first := if made - skipped < ring - at_ then made - skipped else ring - at_
          window := out.copySlice (before + skipped) window at_ first
          if first < made - skipped then
            window := out.copySlice (before + skipped + first) window 0 (made - skipped - first)
          d := { d with total := d.total + made, produced := d.produced + made }
          o := o + 3 + stored + trailer
          if last then
            d := { d with inFrame := false, atEnd := true }
  return ({ d with window := window, pending := b.extract o b.size, atEnd := d.atEnd && o == b.size && !d.inFrame }, out)

/-- Decompresses a whole stream held in memory. Returns an empty array and the reason if it is not valid. -/
def decompress (b : ByteArray) : ByteArray × String :=
  let (d, out) := Decoder.create.feed b
  if d.error != "" then (ByteArray.empty, d.error)
  else if !d.atEnd then (ByteArray.empty, "the stream ends early")
  else (out, "")

end Zstd
