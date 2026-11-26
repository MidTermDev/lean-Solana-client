/-! # JSON string escaping -/

namespace Json

def hexDigit (n : UInt8) : UInt8 := if n < 10 then 48 + n else 87 + n

/-- `s` as a JSON string literal, quotes included. Quotes, backslashes and
control characters are escaped; everything else passes through as UTF-8. -/
def quote (s : String) : String := Id.run do
  let mut out := ByteArray.emptyWithCapacity (s.utf8ByteSize + 2)
  out := out.push 34
  for c in s.toUTF8 do
    if c == 34 || c == 92 then
      out := out.push 92
      out := out.push c
    else if c < 32 then
      out := out ++ "\\u00".toUTF8
      out := out.push (hexDigit (c >>> 4))
      out := out.push (hexDigit (c &&& 15))
    else
      out := out.push c
  out := out.push 34
  return String.fromUTF8! out

end Json
