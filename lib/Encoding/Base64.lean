/-! Base64 (RFC 4648, with padding). Solana prints the binary data programs log this way. -/

namespace Base64

def alphabet : ByteArray := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toUTF8

def encode (b : ByteArray) : String := Id.run do
  let mut out := ByteArray.emptyWithCapacity ((b.size + 2) / 3 * 4)
  let mut i := 0
  while i < b.size do
    let have_ := b.size - i
    let x := b[i]!.toNat
    let y := if have_ > 1 then b[i + 1]!.toNat else 0
    let z := if have_ > 2 then b[i + 2]!.toNat else 0
    out := out.push alphabet[x / 4]!
    out := out.push alphabet[(x % 4) * 16 + y / 16]!
    out := out.push (if have_ > 1 then alphabet[(y % 16) * 4 + z / 64]! else 61)
    out := out.push (if have_ > 2 then alphabet[z % 64]! else 61)
    i := i + 3
  return String.fromUTF8! out

def value (c : UInt8) : Nat :=
  if c >= 65 && c <= 90 then c.toNat - 65
  else if c >= 97 && c <= 122 then c.toNat - 71
  else if c >= 48 && c <= 57 then c.toNat + 4
  else if c == 43 || c == 45 then 62
  else if c == 47 || c == 95 then 63
  else 64

/-- Decodes Base64 (either alphabet, padding optional, whitespace ignored).
Returns an empty array if the text contains anything else. -/
def decode (text : String) : ByteArray := Id.run do
  let raw := text.toUTF8
  let mut out := ByteArray.emptyWithCapacity (raw.size / 4 * 3 + 3)
  let mut acc := 0
  let mut bits := 0
  for c in raw do
    if !(c == 61 || c == 10 || c == 13 || c == 32) then
      let v := value c
      if v == 64 then
        return ByteArray.empty
      acc := (acc * 64 + v) % 16777216
      bits := bits + 6
      if bits >= 8 then
        bits := bits - 8
        out := out.push ((acc / (if bits == 0 then 1 else if bits == 2 then 4 else 16)) % 256).toUInt8
  return out

end Base64
