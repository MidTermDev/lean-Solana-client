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

end Base64
