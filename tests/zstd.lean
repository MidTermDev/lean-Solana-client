import Encoding.Zstd
import Encoding.Hex
import Crypto.Sha256

/-! Zstandard decompression, against the reference implementation.

The files in `tests/zstd/` were compressed by `zstd` 1.5.5 at settings
chosen to reach every part of the format: stored, repeated and compressed
blocks; literals stored, repeated, Huffman-coded in one stream and in four,
with tables sent as weights or FSE-coded, and reused; sequence tables
default, single-symbol, sent and reused; windows from 1 KiB to 128 MiB;
several frames in one file; a frame to be skipped.

The hash of each original is written here, so a pass means this decoder
gave back, byte for byte, what the reference compressor was given. -/

def names : Array String := #["text-1", "text-19", "code-3", "code-22", "binary-9", "skewed-3", "skewed-long", "zeros",
  "random", "empty", "one-byte", "fast", "no-checksum", "two-frames", "skippable"]

/-- SHA-256 of each original, from `sha256sum`. -/
def originals : Array String := #[
  "5afe9a3d030f170bc0f0538fbda261abd7711d5cc3f56d2d71d4ddb3c2d311b2",
  "5afe9a3d030f170bc0f0538fbda261abd7711d5cc3f56d2d71d4ddb3c2d311b2",
  "84479cc1b1fceecf7236d1cd55701fcb6cb0774332f6406e3738da69b5a46763",
  "84479cc1b1fceecf7236d1cd55701fcb6cb0774332f6406e3738da69b5a46763",
  "352381c9f85c81cba498f2560e55c42e59bcdb6a5e55c409c33968e8277af7f6",
  "15a830bbeea4eab6f25ff4d945f83571ea534c02b9c07aaa3ffde192c0c585ea",
  "15a830bbeea4eab6f25ff4d945f83571ea534c02b9c07aaa3ffde192c0c585ea",
  "886715e4051e827f4fe215df3053af3f85ad0d352db2c829c7487af6d78efe30",
  "0638d17deb73fabede7c2ddea3eed433835713f7522bb4b75f03f1f82181e829",
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881",
  "8cda048058eb1b5e1b68b2ea4b4a1950def975309e639ad7d3ed2f86eb2c4a62",
  "84479cc1b1fceecf7236d1cd55701fcb6cb0774332f6406e3738da69b5a46763",
  "8cda048058eb1b5e1b68b2ea4b4a1950def975309e639ad7d3ed2f86eb2c4a62",
  "5afe9a3d030f170bc0f0538fbda261abd7711d5cc3f56d2d71d4ddb3c2d311b2"]

/-- Decompresses `b` fed `piece` bytes at a time. -/
def inPieces (b : ByteArray) (piece : Nat) : ByteArray × Bool := Id.run do
  let mut d := Zstd.Decoder.create
  let mut all := ByteArray.empty
  let mut o := 0
  while o < b.size do
    let stop := if o + piece > b.size then b.size else o + piece
    let (next, out) := d.feed (b.extract o stop)
    d := next
    all := all ++ out
    o := stop
  return (all, d.error == "" && d.atEnd)

def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def main : IO Unit := do
  let mut whole := 0
  let mut pieces := 0
  for i in [0:names.size] do
    let b ← IO.FS.readBinFile s!"tests/zstd/{names[i]!}.zst"
    let (out, why) := Zstd.decompress b
    let same := why == "" && Hex.encode (Sha256.hash out) == originals[i]!
    -- the same stream arriving in pieces of 61 bytes, and one byte at a time for the small ones
    let (again, complete) := inPieces b (if b.size < 2000 then 1 else 61)
    let samePieces := complete && Hex.encode (Sha256.hash again) == originals[i]!
    if same then
      whole := whole + 1
    if samePieces then
      pieces := pieces + 1
    IO.println s!"{names[i]!}: {b.size} bytes to {out.size}: {if same then "the original" else s!"WRONG ({why})"}{if samePieces then "" else ", WRONG in pieces"}"
  IO.println s!"{whole} of {names.size} give back the original; {pieces} also when fed in pieces"

  -- a stream cut short is not mistaken for a whole one
  let text ← IO.FS.readBinFile "tests/zstd/text-19.zst"
  let mut early := 0
  for cut in [0:40] do
    let (_, why) := Zstd.decompress (text.extract 0 (text.size * cut / 40))
    if why != "" then
      early := early + 1
  IO.println s!"cut short at 40 places: {early} refused"
  IO.println s!"not Zstandard at all: {(Zstd.decompress "plain text, not compressed".toUTF8).2}"

  -- damaged streams must be refused or decoded to something, never crash the decoder
  let mut r : UInt64 := 0x9E3779B97F4A7C15
  let mut refused := 0
  let mut decoded := 0
  let mut digest : UInt64 := 0
  for round in [0:400] do
    let source ← IO.FS.readBinFile s!"tests/zstd/{names[round % 5]!}.zst"
    let mut b := source
    r := xorshift r
    for _ in [0:(r % 3).toNat + 1] do
      r := xorshift r
      let at_ := (r % b.size.toUInt64).toNat
      r := xorshift r
      b := b.set! at_ (r >>> 20).toUInt8
    let (out, why) := Zstd.decompress b
    if why == "" then
      decoded := decoded + 1
      digest := digest * 31 + out.size.toUInt64
    else
      refused := refused + 1
  IO.println s!"400 damaged streams: {refused} refused, {decoded} decoded, digest {digest}"
