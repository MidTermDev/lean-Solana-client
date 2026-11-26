/-! # Text formatting for the dashboard -/

namespace Fmt

def spaces (n : Nat) : String := Id.run do
  let mut s := ""
  for _ in [0:n] do
    s := s.push ' '
  return s

def padLeft (s : String) (width : Nat) : String :=
  spaces (width - s.length) ++ s

def padRight (s : String) (width : Nat) : String :=
  s ++ spaces (width - s.length)

/-- `1234567` as `1,234,567`. -/
def thousands (n : UInt64) : String := Id.run do
  let digits := (toString n).toUTF8
  let mut out := ByteArray.emptyWithCapacity (digits.size + digits.size / 3)
  for i in [0:digits.size] do
    if i > 0 && (digits.size - i) % 3 == 0 then
      out := out.push 44
    out := out.push digits[i]!
  return String.fromUTF8! out

def two (n : UInt64) : String :=
  if n < 10 then s!"0{n}" else toString n

/-- Seconds as `hh:mm:ss`. -/
def clock (secs : UInt64) : String :=
  s!"{two (secs / 3600)}:{two (secs / 60 % 60)}:{two (secs % 60)}"

/-- One decimal place: `tenths = 123` renders as `12.3`. -/
def tenths (v : UInt64) : String := s!"{v / 10}.{v % 10}"

/-- A byte rate with a unit. -/
def rate (bytesPerSec : UInt64) : String :=
  if bytesPerSec >= 1000000 then s!"{tenths (bytesPerSec / 100000)} MB/s"
  else if bytesPerSec >= 1000 then s!"{tenths (bytesPerSec / 100)} kB/s"
  else s!"{bytesPerSec} B/s"

/-- A horizontal bar of `width` cells filled in proportion to `value / max`. -/
def bar (value max : UInt64) (width : Nat) : String := Id.run do
  let cells : Nat := if max == 0 then 0 else (value * width.toUInt64 * 8 / max).toNat
  let mut s := ""
  for i in [0:width] do
    let fill := if cells >= (i + 1) * 8 then 8 else if cells > i * 8 then cells - i * 8 else 0
    -- U+2588 is the full block; U+2589..U+258F get progressively narrower
    if fill == 0 then
      s := s.push ' '
    else
      s := s.push (Char.ofNat (0x2590 - fill))
  return s

end Fmt
