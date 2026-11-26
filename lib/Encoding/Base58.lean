/-! # Base58 (Bitcoin alphabet), the encoding Solana uses for public keys -/

namespace Base58

def alphabet : ByteArray := "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz".toUTF8

def encode (data : ByteArray) : String := Id.run do
  let mut zeros := 0
  while zeros < data.size && data[zeros]! == 0 do
    zeros := zeros + 1
  -- repeated multiply-by-256-and-add over little-endian base-58 digits
  let mut digits : Array UInt64 := Array.emptyWithCapacity 48
  for byte in data do
    let mut carry := byte.toUInt64
    for j in [0:digits.size] do
      let v := digits[j]! * 256 + carry
      digits := digits.set! j (v % 58)
      carry := v / 58
    while carry > 0 do
      digits := digits.push (carry % 58)
      carry := carry / 58
  let mut out := ByteArray.emptyWithCapacity (zeros + digits.size)
  for _ in [0:zeros] do
    out := out.push 49
  for i in [0:digits.size] do
    out := out.push alphabet[digits[digits.size - 1 - i]!.toNat]!
  return String.fromUTF8! out

/-- Decodes Base58 text. Returns an empty array if a character is not in the alphabet. -/
def decode (text : String) : ByteArray := Id.run do
  let chars := text.toUTF8
  let mut zeros := 0
  while zeros < chars.size && chars[zeros]! == 49 do
    zeros := zeros + 1
  -- repeated multiply-by-58-and-add over little-endian bytes
  let mut bytes : Array UInt64 := Array.emptyWithCapacity 40
  for c in chars do
    let mut carry : UInt64 := 58
    for k in [0:58] do
      if alphabet[k]! == c then
        carry := k.toUInt64
    if carry == 58 then
      return ByteArray.empty
    for j in [0:bytes.size] do
      let v := bytes[j]! * 58 + carry
      bytes := bytes.set! j (v &&& 0xFF)
      carry := v >>> 8
    while carry > 0 do
      bytes := bytes.push (carry &&& 0xFF)
      carry := carry >>> 8
  let mut out := ByteArray.emptyWithCapacity (zeros + bytes.size)
  for _ in [0:zeros] do
    out := out.push 0
  for i in [0:bytes.size] do
    out := out.push bytes[bytes.size - 1 - i]!.toUInt8
  return out

end Base58
