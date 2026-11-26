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

end Base58
