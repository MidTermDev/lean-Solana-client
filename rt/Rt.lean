/-!
# The leanc runtime

Everything a compiled program needs at run time lives in this file, written
in Lean and compiled by leanc together with the program: the memory
allocator, growable arrays, strings, printing, panics.

There is no libc underneath. The only primitives are a handful of
*intrinsics* that leanc turns directly into machine instructions: raw memory
loads and stores, `rep movsb`, a few atomics, and `syscall`.

This file is also valid input for the official Lean toolchain (the
intrinsics are plain `opaque` constants there), so it can be type-checked
independently of leanc.

Heap object layouts (must match `leanc/gen.c`):

    constructor object   [0] refcount  [8] tag    [16 + 8*i] field i
    Array                [0] refcount  [8] size   [16] capacity  [24 + 8*i] element i
    ByteArray / String   [0] refcount  [8] size   [16] capacity  [24 + i]   byte i
-/

namespace Mem

@[extern "leanc_load8"] opaque load8 (addr : UInt64) : IO UInt64
@[extern "leanc_load16"] opaque load16 (addr : UInt64) : IO UInt64
@[extern "leanc_load32"] opaque load32 (addr : UInt64) : IO UInt64
@[extern "leanc_load64"] opaque load64 (addr : UInt64) : IO UInt64
@[extern "leanc_store8"] opaque store8 (addr val : UInt64) : IO Unit
@[extern "leanc_store16"] opaque store16 (addr val : UInt64) : IO Unit
@[extern "leanc_store32"] opaque store32 (addr val : UInt64) : IO Unit
@[extern "leanc_store64"] opaque store64 (addr val : UInt64) : IO Unit
/-- `rep movsb`: copies `n` bytes from `src` to `dst`. -/
@[extern "leanc_copy"] opaque copy (dst src n : UInt64) : IO Unit
/-- `rep stosb`: fills `n` bytes at `dst` with `byte`. -/
@[extern "leanc_fill"] opaque fill (dst byte n : UInt64) : IO Unit
/-- `repe cmpsb`: true when the two `n`-byte regions are equal. -/
@[extern "leanc_memeq"] opaque eq (a b n : UInt64) : IO Bool
/-- `lock cmpxchg` on a 32-bit word. Returns the previous value. -/
@[extern "leanc_cas32"] opaque cas32 (addr expected new : UInt64) : IO UInt64
/-- `lock cmpxchg` on a 64-bit word. Returns the previous value. -/
@[extern "leanc_cas64"] opaque cas64 (addr expected new : UInt64) : IO UInt64
/-- `lock xadd` on a 64-bit word. Returns the previous value. -/
@[extern "leanc_xadd64"] opaque xadd64 (addr delta : UInt64) : IO UInt64
/-- `xchg` on a 32-bit word. Returns the previous value. -/
@[extern "leanc_xchg32"] opaque xchg32 (addr val : UInt64) : IO UInt64
/-- The `pause` spin-loop hint. -/
@[extern "leanc_pause"] opaque pause : IO Unit
@[extern "leanc_rdtsc"] opaque rdtsc : IO UInt64

end Mem

namespace Sys

/-- The raw `syscall` instruction: number in rax, arguments in rdi, rsi, rdx, r10, r8, r9. -/
@[extern "leanc_syscall"] opaque syscall (n a b c d e f : UInt64) : IO UInt64

end Sys

namespace Rt

/-- Address of a string object (borrowed). -/
@[extern "leanc_ptr"] opaque strAddr (s : @& String) : UInt64

-- Fixed addresses inside the zero-initialised runtime page (BSS_BASE in leanc.h).
def bss : UInt64 := 0x20000000
def heapCur : UInt64 := 0x20000008
def heapEnd : UInt64 := 0x20000010
def scratch : UInt64 := 0x20000040
def freeLists : UInt64 := 0x20000100
def chunkSize : UInt64 := 0x400000
def bigThreshold : UInt64 := 0x100000
def errorFloor : UInt64 := 0xFFFFFFFFFFFFF000

def exit (code : UInt64) : IO Unit := do
  let _ ← Sys.syscall 231 code 0 0 0 0 0
  pure ()

def writeAll (fd p len : UInt64) : IO Unit := do
  let mut off : UInt64 := 0
  while off < len do
    let r ← Sys.syscall 1 fd (p + off) (len - off) 0 0 0
    if r > errorFloor then
      return
    off := off + r

def errStr (s : String) : IO Unit := do
  let p := strAddr s
  let n ← Mem.load64 (p + 8)
  writeAll 2 (p + 24) n

/-- Formats `n` in decimal, right-aligned so that it ends at `scratch + 32`.
Returns the address of the first digit. -/
def fmtNat (n : UInt64) : IO UInt64 := do
  let mut v := n
  let mut p := scratch + 32
  if v == 0 then
    p := p - 1
    Mem.store8 p 48
  while v != 0 do
    p := p - 1
    Mem.store8 p (48 + v % 10)
    v := v / 10
  return p

def errNat (n : UInt64) : IO Unit := do
  let p ← fmtNat n
  writeAll 2 p (scratch + 32 - p)

def panic (kind line : UInt64) : IO Unit := do
  errStr "leanc panic: "
  if kind == 1 then
    errStr "index out of bounds"
  else if kind == 2 then
    errStr "Nat overflow (leanc represents Nat as an unsigned 64-bit word)"
  else if kind == 3 then
    errStr "non-exhaustive match"
  else if kind == 4 then
    errStr "Option.get! on none"
  else if kind == 6 then
    errStr "String.toNat! on a non-numeric string"
  else if kind == 7 then
    errStr "out of memory"
  else
    errStr "internal error"
  errStr " (line "
  errNat line
  errStr ")\n"
  exit 101

def panicMsg (msg line : UInt64) : IO Unit := do
  errStr "leanc panic: "
  let n ← Mem.load64 (msg + 8)
  writeAll 2 (msg + 24) n
  errStr " (line "
  errNat line
  errStr ")\n"
  exit 101

-- ---------------------------------------------------------------- allocator
--
-- Segregated free lists. Requests up to 1 KiB use exact 16-byte classes,
-- larger ones power-of-two classes, and anything from 1 MiB up goes straight
-- to mmap/munmap. `free` is always told the size that was requested, so
-- objects carry no allocator header.

def mmapAnon (len : UInt64) : IO UInt64 := do
  let p ← Sys.syscall 9 0 len 3 0x22 0xFFFFFFFFFFFFFFFF 0
  if p > errorFloor then
    panic 7 0
  return p

def largeClass (sz : UInt64) : UInt64 := Id.run do
  let mut c : UInt64 := 2048
  while c < sz do
    c := c <<< 1
  return c

def largeSlot (cls : UInt64) : UInt64 := Id.run do
  let mut i : UInt64 := 65
  let mut c : UInt64 := 2048
  while c < cls do
    c := c <<< 1
    i := i + 1
  return freeLists + i * 8

/-- Carves `cls` bytes off the current chunk, starting a new chunk if needed. -/
def bump (cls : UInt64) : IO UInt64 := do
  let cur ← Mem.load64 heapCur
  let endp ← Mem.load64 heapEnd
  if cur != 0 && cur + cls <= endp then
    Mem.store64 heapCur (cur + cls)
    return cur
  let chunk ← mmapAnon chunkSize
  Mem.store64 heapCur (chunk + cls)
  Mem.store64 heapEnd (chunk + chunkSize)
  return chunk

def alloc (size : UInt64) : IO UInt64 := do
  let sz := (size + 15) &&& 0xFFFFFFFFFFFFFFF0
  if sz <= 1024 then
    let slot := freeLists + (sz >>> 1)
    let head ← Mem.load64 slot
    if head != 0 then
      let next ← Mem.load64 head
      Mem.store64 slot next
      return head
    let p ← bump sz
    return p
  if sz >= bigThreshold then
    let p ← mmapAnon ((sz + 4095) &&& errorFloor)
    return p
  let cls := largeClass sz
  let slot := largeSlot cls
  let head ← Mem.load64 slot
  if head != 0 then
    let next ← Mem.load64 head
    Mem.store64 slot next
    return head
  let p ← bump cls
  return p

def free (p size : UInt64) : IO Unit := do
  let sz := (size + 15) &&& 0xFFFFFFFFFFFFFFF0
  if sz <= 1024 then
    let slot := freeLists + (sz >>> 1)
    let head ← Mem.load64 slot
    Mem.store64 p head
    Mem.store64 slot p
    return
  if sz >= bigThreshold then
    let _ ← Sys.syscall 11 p ((sz + 4095) &&& errorFloor) 0 0 0 0
    return
  let slot := largeSlot (largeClass sz)
  let head ← Mem.load64 slot
  Mem.store64 p head
  Mem.store64 slot p

-- ------------------------------------------------------- ByteArray / String

def baNew (cap : UInt64) : IO UInt64 := do
  let p ← alloc (24 + cap)
  Mem.store64 p 1
  Mem.store64 (p + 8) 0
  Mem.store64 (p + 16) cap
  return p

def baEmpty : IO UInt64 := baNew 0

/-- Gives up one reference to a byte array. -/
def baRelease (p : UInt64) : IO Unit := do
  let rc ← Mem.load64 p
  if rc == 1 then
    let cap ← Mem.load64 (p + 16)
    free p (24 + cap)
  else
    Mem.store64 p (rc - 1)

def baPush (p v : UInt64) : IO UInt64 := do
  let rc ← Mem.load64 p
  let size ← Mem.load64 (p + 8)
  let cap ← Mem.load64 (p + 16)
  if rc == 1 && size < cap then
    Mem.store8 (p + 24 + size) v
    Mem.store64 (p + 8) (size + 1)
    return p
  let ncap : UInt64 := if cap < 16 then 32 else cap * 2
  let q ← baNew ncap
  Mem.copy (q + 24) (p + 24) size
  Mem.store8 (q + 24 + size) v
  Mem.store64 (q + 8) (size + 1)
  baRelease p
  return q

/-- `a ++ b`: consumes `a`, borrows `b`. Appends in place when `a` is unique. -/
def baAppend (a b : UInt64) : IO UInt64 := do
  let rc ← Mem.load64 a
  let sa ← Mem.load64 (a + 8)
  let cap ← Mem.load64 (a + 16)
  let sb ← Mem.load64 (b + 8)
  if rc == 1 && sa + sb <= cap then
    Mem.copy (a + 24 + sa) (b + 24) sb
    Mem.store64 (a + 8) (sa + sb)
    return a
  let need := sa + sb
  let ncap : UInt64 := if rc == 1 && cap * 2 > need then cap * 2 else need
  let q ← baNew ncap
  Mem.copy (q + 24) (a + 24) sa
  Mem.copy (q + 24 + sa) (b + 24) sb
  Mem.store64 (q + 8) need
  baRelease a
  return q

def baExtract (b start stop : UInt64) : IO UInt64 := do
  let size ← Mem.load64 (b + 8)
  let e : UInt64 := if stop < size then stop else size
  if start >= e then
    let q ← baNew 0
    return q
  let n := e - start
  let q ← baNew n
  Mem.copy (q + 24) (b + 24 + start) n
  Mem.store64 (q + 8) n
  return q

def baEq (a b : UInt64) : IO Bool := do
  let sa ← Mem.load64 (a + 8)
  let sb ← Mem.load64 (b + 8)
  if sa != sb then
    return false
  Mem.eq (a + 24) (b + 24) sa

def baIsEmpty (b : UInt64) : IO Bool := do
  let size ← Mem.load64 (b + 8)
  return size == 0

/-- Returns an array equal to `p` that nobody else references. -/
def baUnique (p : UInt64) : IO UInt64 := do
  let rc ← Mem.load64 p
  if rc == 1 then
    return p
  let size ← Mem.load64 (p + 8)
  let q ← baNew size
  Mem.copy (q + 24) (p + 24) size
  Mem.store64 (q + 8) size
  Mem.store64 p (rc - 1)
  return q

/-- `ByteArray.copySlice src srcOff dest destOff len`, same result as Lean's:
`dest[0:destOff] ++ src[srcOff:srcOff+len] ++ dest[destOff + min len (src.size - srcOff):]`. -/
def baCopySlice (src srcOff dest destOff len : UInt64) : IO UInt64 := do
  let ssz ← Mem.load64 (src + 8)
  let dsz ← Mem.load64 (dest + 8)
  let s0 : UInt64 := if srcOff < ssz then srcOff else ssz
  let avail := ssz - s0
  let n : UInt64 := if len < avail then len else avail
  let d0 : UInt64 := if destOff < dsz then destOff else dsz
  let tailStart := destOff + n
  let tailLen : UInt64 := if tailStart < dsz then dsz - tailStart else 0
  let total := d0 + n + tailLen
  let rc ← Mem.load64 dest
  if rc == 1 && total == dsz && d0 == destOff then
    Mem.copy (dest + 24 + d0) (src + 24 + s0) n
    return dest
  let q ← baNew total
  Mem.copy (q + 24) (dest + 24) d0
  Mem.copy (q + 24 + d0) (src + 24 + s0) n
  Mem.copy (q + 24 + d0 + n) (dest + 24 + tailStart) tailLen
  Mem.store64 (q + 8) total
  baRelease dest
  return q

-- -------------------------------------------------------------------- Array

def arrNew (cap : UInt64) : IO UInt64 := do
  let p ← alloc (24 + cap * 8)
  Mem.store64 p 1
  Mem.store64 (p + 8) 0
  Mem.store64 (p + 16) cap
  return p

/-- Adds one reference to each of the first `n` elements (they are pointers). -/
def incElems (p n : UInt64) : IO Unit := do
  let mut i : UInt64 := 0
  while i < n do
    let e ← Mem.load64 (p + 24 + i * 8)
    let rc ← Mem.load64 e
    Mem.store64 e (rc + 1)
    i := i + 1

def arrUnique (p isPtr : UInt64) : IO UInt64 := do
  let rc ← Mem.load64 p
  if rc == 1 then
    return p
  let size ← Mem.load64 (p + 8)
  let q ← arrNew size
  Mem.copy (q + 24) (p + 24) (size * 8)
  Mem.store64 (q + 8) size
  if isPtr != 0 then
    incElems q size
  Mem.store64 p (rc - 1)
  return q

def arrPush (p v isPtr : UInt64) : IO UInt64 := do
  let rc ← Mem.load64 p
  let size ← Mem.load64 (p + 8)
  let cap ← Mem.load64 (p + 16)
  if rc == 1 && size < cap then
    Mem.store64 (p + 24 + size * 8) v
    Mem.store64 (p + 8) (size + 1)
    return p
  let ncap : UInt64 := if cap < 4 then 8 else cap * 2
  let q ← arrNew ncap
  Mem.copy (q + 24) (p + 24) (size * 8)
  Mem.store64 (q + 24 + size * 8) v
  Mem.store64 (q + 8) (size + 1)
  if rc == 1 then
    -- the elements moved to the new array; only the old shell goes away
    free p (24 + cap * 8)
  else
    if isPtr != 0 then
      incElems q size
    Mem.store64 p (rc - 1)
  return q

/-- `Array.replicate n v`. Borrows `v`; adds `n` references to it if it is a pointer. -/
def arrReplicate (n v isPtr : UInt64) : IO UInt64 := do
  let q ← arrNew n
  let mut i : UInt64 := 0
  while i < n do
    Mem.store64 (q + 24 + i * 8) v
    i := i + 1
  Mem.store64 (q + 8) n
  if isPtr != 0 then
    let rc ← Mem.load64 v
    Mem.store64 v (rc + n)
  return q

/-- Copy of a constructor object for a functional update on a shared value.
`mask` has bit `i` set when field `i` holds a pointer. -/
def objUnique (p nfields mask : UInt64) : IO UInt64 := do
  let rc ← Mem.load64 p
  if rc == 1 then
    return p
  let q ← alloc (16 + nfields * 8)
  Mem.copy q p (16 + nfields * 8)
  Mem.store64 q 1
  let mut i : UInt64 := 0
  while i < nfields do
    if (mask >>> i) &&& 1 != 0 then
      let f ← Mem.load64 (q + 16 + i * 8)
      let frc ← Mem.load64 f
      Mem.store64 f (frc + 1)
    i := i + 1
  Mem.store64 p (rc - 1)
  return q

-- ------------------------------------------------------------------ strings

def natToString (n : UInt64) : IO UInt64 := do
  let p ← fmtNat n
  let len := scratch + 32 - p
  let s ← baNew len
  Mem.copy (s + 24) p len
  Mem.store64 (s + 8) len
  return s

def boolToString (b : UInt64) : IO UInt64 := do
  let s ← baNew 8
  if b != 0 then
    Mem.store32 (s + 24) 0x65757274
    Mem.store64 (s + 8) 4
  else
    Mem.store32 (s + 24) 0x736c6166
    Mem.store8 (s + 28) 0x65
    Mem.store64 (s + 8) 5
  return s

/-- Appends the UTF-8 encoding of code point `c`. -/
def strPush (s c : UInt64) : IO UInt64 := do
  if c < 0x80 then
    let r ← baPush s c
    return r
  let b0 := c &&& 0x3F
  let b1 := (c >>> 6) &&& 0x3F
  let b2 := (c >>> 12) &&& 0x3F
  if c < 0x800 then
    let r ← baPush s (0xC0 ||| b1)
    let r ← baPush r (0x80 ||| b0)
    return r
  if c < 0x10000 then
    let r ← baPush s (0xE0 ||| b2)
    let r ← baPush r (0x80 ||| b1)
    let r ← baPush r (0x80 ||| b0)
    return r
  let b3 := c >>> 18
  let r ← baPush s (0xF0 ||| b3)
  let r ← baPush r (0x80 ||| b2)
  let r ← baPush r (0x80 ||| b1)
  let r ← baPush r (0x80 ||| b0)
  return r

def strSingleton (c : UInt64) : IO UInt64 := do
  let s ← baNew 8
  strPush s c

/-- Number of code points: bytes that are not UTF-8 continuation bytes. -/
def strLength (s : UInt64) : IO UInt64 := do
  let size ← Mem.load64 (s + 8)
  let mut n : UInt64 := 0
  let mut i : UInt64 := 0
  while i < size do
    let b ← Mem.load8 (s + 24 + i)
    if b &&& 0xC0 != 0x80 then
      n := n + 1
    i := i + 1
  return n

def strToNat (s : UInt64) : IO UInt64 := do
  let size ← Mem.load64 (s + 8)
  if size == 0 then
    panic 6 0
  let mut n : UInt64 := 0
  let mut i : UInt64 := 0
  while i < size do
    let b ← Mem.load8 (s + 24 + i)
    if b < 48 || b > 57 then
      panic 6 0
    n := n * 10 + (b - 48)
    i := i + 1
  return n

-- ----------------------------------------------------------------------- IO

def print (s : UInt64) : IO Unit := do
  let n ← Mem.load64 (s + 8)
  writeAll 1 (s + 24) n

def eprint (s : UInt64) : IO Unit := do
  let n ← Mem.load64 (s + 8)
  writeAll 2 (s + 24) n

/-- Writes the string and a newline with a single `write`, so lines from
different processes never interleave. -/
def putLine (fd s : UInt64) : IO Unit := do
  let n ← Mem.load64 (s + 8)
  let buf ← alloc (n + 1)
  Mem.copy buf (s + 24) n
  Mem.store8 (buf + n) 10
  writeAll fd buf (n + 1)
  free buf (n + 1)

def println (s : UInt64) : IO Unit := putLine 1 s

def eprintln (s : UInt64) : IO Unit := putLine 2 s

def monoNs : IO UInt64 := do
  let ts := scratch + 64
  let _ ← Sys.syscall 228 1 ts 0 0 0 0
  let sec ← Mem.load64 ts
  let nsec ← Mem.load64 (ts + 8)
  return sec * 1000000000 + nsec

def monoMs : IO UInt64 := do
  let ns ← monoNs
  return ns / 1000000

def sleepMs (ms : UInt64) : IO Unit := do
  let ts := scratch + 64
  Mem.store64 ts (ms / 1000)
  Mem.store64 (ts + 8) ((ms % 1000) * 1000000)
  let _ ← Sys.syscall 35 ts 0 0 0 0 0
  pure ()

def randomBytes (n : UInt64) : IO UInt64 := do
  let b ← baNew n
  let mut got : UInt64 := 0
  while got < n do
    let r ← Sys.syscall 318 (b + 24 + got) (n - got) 0 0 0 0
    if r > errorFloor then
      panic 0 0
    got := got + r
  Mem.store64 (b + 8) n
  return b

def argc : IO UInt64 := do
  let sp ← Mem.load64 bss
  Mem.load64 sp

/-- Command-line argument `i` as a fresh string object. -/
def argv (i : UInt64) : IO UInt64 := do
  let sp ← Mem.load64 bss
  let cstr ← Mem.load64 (sp + 8 + i * 8)
  let mut len : UInt64 := 0
  repeat
    let c ← Mem.load8 (cstr + len)
    if c == 0 then
      break
    len := len + 1
  let s ← baNew len
  Mem.copy (s + 24) cstr len
  Mem.store64 (s + 8) len
  return s

end Rt
