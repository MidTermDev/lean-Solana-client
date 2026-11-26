/-! # IPv4 addresses as `UInt32` in host byte order (`a.b.c.d` = `a<<24 | b<<16 | c<<8 | d`) -/

namespace Ip

def toString (ip : UInt32) : String :=
  s!"{ip >>> 24}.{(ip >>> 16) &&& 255}.{(ip >>> 8) &&& 255}.{ip &&& 255}"

/-- Parses dotted-quad text in `b[start .. stop)`. Returns 0 if it is not an IPv4 address. -/
def parseAt (b : ByteArray) (start stop : Nat) : UInt32 := Id.run do
  let mut ip : UInt32 := 0
  let mut part : UInt32 := 0
  let mut digits := 0
  let mut dots := 0
  for i in [start:stop] do
    let c := b[i]!
    if c >= 48 && c <= 57 then
      part := part * 10 + (c - 48).toUInt32
      digits := digits + 1
      if part > 255 || digits > 3 then
        return 0
    else if c == 46 && digits > 0 && dots < 3 then
      ip := (ip <<< 8) ||| part
      part := 0
      digits := 0
      dots := dots + 1
    else
      return 0
  if dots != 3 || digits == 0 then
    return 0
  return (ip <<< 8) ||| part

def parse (s : String) : UInt32 :=
  let b := s.toUTF8
  parseAt b 0 b.size

/-- Addresses a public node should never be told to talk to. -/
def isPublic (ip : UInt32) : Bool :=
  let a := ip >>> 24
  let b := (ip >>> 16) &&& 255
  !(a == 0 || a == 10 || a == 127 || a >= 224 || (a == 172 && b >= 16 && b <= 31) || (a == 192 && b == 168) ||
    (a == 169 && b == 254) || (a == 100 && b >= 64 && b <= 127))

end Ip
