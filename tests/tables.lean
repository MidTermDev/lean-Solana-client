import Solana.Table
import Fmt
import Crypto.Sha256

def main : IO Unit := do
  let mut s := Set64.create (1 <<< 12)
  for i in [0:1500] do
    s := s.insert (i.toUInt64 * 0x9E3779B97F4A7C15 + 1)
  let mut hits := 0
  for i in [0:3000] do
    if s.contains (i.toUInt64 * 0x9E3779B97F4A7C15 + 1) then
      hits := hits + 1
  IO.println s!"set: count {s.count}, hits {hits}"
  -- Nodes: insert 5000 keys, update fields, look them up again
  let mut nodes := Nodes.create 1024
  for i in [0:600] do
    let key := Sha256.hash (toString i).toUTF8
    if nodes.find key 0 == Nodes.notFound then
      nodes := nodes.append key 0
    let row := nodes.find key 0
    nodes := nodes.set row Nodes.fVersion (i.toUInt64 * 3)
  let mut sum : UInt64 := 0
  let mut missing := 0
  for i in [0:600] do
    let key := Sha256.hash (toString i).toUTF8
    let row := nodes.find key 0
    if row == Nodes.notFound then
      missing := missing + 1
    else
      sum := sum + nodes.get row Nodes.fVersion
  IO.println s!"nodes: count {nodes.count}, missing {missing}, sum {sum}"
  IO.println s!"[{Fmt.padLeft (Fmt.thousands 474241109) 14}] [{Fmt.padRight "abc" 6}] {Fmt.clock 3725} {Fmt.rate 1234567} {Fmt.rate 999} [{Fmt.bar 5 8 8}] [{Fmt.bar 8 8 4}] {Fmt.thousands 12} {Fmt.thousands 1234}"
