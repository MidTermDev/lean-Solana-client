import Crypto.Ed25519

def check (name : String) (ok : Bool) : IO Unit :=
  IO.println (name ++ (if ok then ": ok" else ": FAIL"))

def main : IO Unit := do
  let seed := Hex.decode "28554ffdaccebd7ecb9f313a72e272e27fe3f2c7b1d15b1c6a7df5a361769dd8"
  let pk := Hex.decode "8f80338eef733ec67c601349c4a8251393b28deb722cfd0a91907744a26d3dab"
  let msg := Hex.decode ""
  let sig := Hex.decode "dad88d9f735434282a6cc50924f71eb03f10acd0f4ea598f0c7f0842c74327ed62c52f2408c0ce65212c7153739ba3957eefbd11f63cc2968c04700bdb33370c"
  check "pubkey 0" (Ed25519.publicKey seed == pk)
  check "sign 0" (Ed25519.sign seed pk msg == sig)
  check "verify 0" (Ed25519.verify pk sig msg)
  check "reject tampered msg 0" (!(Ed25519.verify pk sig (msg.push 1)))
  check "reject tampered sig 0" (!(Ed25519.verify pk (sig.set! 5 (sig[5]! ^^^ 1)) msg))
  let seed := Hex.decode "df9ecf4c79e5ad77701cfc88c196632b353149d85810a381f469f8fc05dc1b92"
  let pk := Hex.decode "cc1983469486418cd66dcdc8664677c263487b736840cfd1532e144386fa7610"
  let msg := Hex.decode "5a"
  let sig := Hex.decode "cca09d4dad0dfb5a30e8ba7d1497ba44eff91cd22838943031d215967c51ebbc54e05325b5b8d240729f695aa02666301bc9e98a5953f5fe507de54696602800"
  check "pubkey 1" (Ed25519.publicKey seed == pk)
  check "sign 1" (Ed25519.sign seed pk msg == sig)
  check "verify 1" (Ed25519.verify pk sig msg)
  check "reject tampered msg 1" (!(Ed25519.verify pk sig (msg.push 1)))
  check "reject tampered sig 1" (!(Ed25519.verify pk (sig.set! 5 (sig[5]! ^^^ 1)) msg))
  let seed := Hex.decode "35b0fad16758b58124f39f00d26061704514be4e39c1e03b7b23534afd6081e3"
  let pk := Hex.decode "88166617f91bc145b243c2ae6e1088f1208bf17311cca74dbf032fee25b219e0"
  let msg := Hex.decode "331ba04fd5052a4415794fe87c86bb8b8eca6abfd89d75702c2b7767298a927088"
  let sig := Hex.decode "e6a44c15baedd1b70a957389451ad553cf43fca03c793ed58bb508717a6b6d358a065130ad1654085fdce5e64ff27f47c2d6b330a0f3c9cab8ef9b5d1c088e01"
  check "pubkey 2" (Ed25519.publicKey seed == pk)
  check "sign 2" (Ed25519.sign seed pk msg == sig)
  check "verify 2" (Ed25519.verify pk sig msg)
  check "reject tampered msg 2" (!(Ed25519.verify pk sig (msg.push 1)))
  check "reject tampered sig 2" (!(Ed25519.verify pk (sig.set! 5 (sig[5]! ^^^ 1)) msg))
  let seed := Hex.decode "b9e1e9b068c94af0129d20f775a395e4e0ab28cd2026f45eea0821b72bf58d93"
  let pk := Hex.decode "6f97404947a00311785785217b1759b002cbae16da26e0801f0dcbe4e00d5f45"
  let msg := Hex.decode "5339531a19c97e8534d0f021f5bb43d9c20b031e06f611382d51c14887d49c875bc5b79a92849fbf999463ebddb5acb42d255545734e4da7fddd051142e11616"
  let sig := Hex.decode "a8cdb904b8398a5670b9cd7bd91fb1bc032e7f59769911d3a99f9cbf9c47d59f560271e85e53fd592ecf932cbce0b2b7ca277f1b5d50d343f451e8332a9cf000"
  check "pubkey 3" (Ed25519.publicKey seed == pk)
  check "sign 3" (Ed25519.sign seed pk msg == sig)
  check "verify 3" (Ed25519.verify pk sig msg)
  check "reject tampered msg 3" (!(Ed25519.verify pk sig (msg.push 1)))
  check "reject tampered sig 3" (!(Ed25519.verify pk (sig.set! 5 (sig[5]! ^^^ 1)) msg))
  let pk := Hex.decode "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
  let sig := Hex.decode "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
  check "rfc8032 test 1" (Ed25519.verify pk sig ByteArray.empty)
  IO.println (Hex.encode (Ed25519.Point.encode Ed25519.basePoint))
  IO.println (Hex.encode (Ed25519.Fe.toBytes (Ed25519.Fe.invert (Ed25519.Fe.add Ed25519.Fe.one Ed25519.Fe.one))))
