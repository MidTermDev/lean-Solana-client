/-! Language semantics that a compiler with in-place updates can easily get
wrong: value semantics under aliasing, pattern matching, control flow,
integer edge cases. Expected output comes from the official toolchain. -/

inductive Color where
  | red
  | green
  | blue
  deriving Inhabited

inductive Shape where
  | circle (r : Nat)
  | rect (w : Nat) (h : Nat)
  | empty
  deriving Inhabited

structure Account where
  owner : String
  balance : Nat
  history : Array Nat
  deriving Inhabited

def Color.name (c : Color) : String :=
  match c with
  | .red => "red"
  | .green => "green"
  | .blue => "blue"

def area (s : Shape) : Nat :=
  match s with
  | .circle r => 3 * r * r
  | .rect w h => w * h
  | .empty => 0

def describe (s : Shape) (c : Color) : String :=
  match s, c with
  | .empty, _ => "nothing"
  | .circle 0, _ => "a point"
  | .circle r, .red => s!"a red circle of radius {r}"
  | _, col => s!"a {col.name} shape of area {area s}"

def deposit (a : Account) (n : Nat) : Account :=
  { a with balance := a.balance + n, history := a.history.push n }

def sumTo (xs : Array Nat) (limit : Nat) : Nat := Id.run do
  let mut total := 0
  for x in xs do
    if x == 0 then
      continue
    if total + x > limit then
      break
    total := total + x
  return total

def firstNegative (xs : Array UInt64) : Option Nat := Id.run do
  for i in [0:xs.size] do
    if xs[i]! > 0x7fffffffffffffff then
      return some i
  return none

def collatz (n : Nat) : Nat := Id.run do
  let mut x := n
  let mut steps := 0
  while x != 1 do
    if x % 2 == 0 then
      x := x / 2
    else
      x := 3 * x + 1
    steps := steps + 1
  return steps

partial def fib (n : Nat) : Nat := if n < 2 then n else fib (n - 1) + fib (n - 2)

def swap (p : Nat × String) : String × Nat := (p.2, p.1)

def classify (n : Nat) : String :=
  match n with
  | 0 | 1 => "tiny"
  | 2 => "two"
  | _ => if n < 100 then "small" else "large"

def nested (o : Option (Option Nat)) : Nat :=
  match o with
  | none => 0
  | some none => 1
  | some (some n) => n + 2

def main : IO Unit := do
  -- value semantics: an alias must not observe a later update
  let a : Array Nat := #[1, 2, 3]
  let b := a
  let a2 := a.set! 0 99
  IO.println s!"alias: {b[0]!} {a2[0]!} {a[0]!}"
  let s1 := "abc"
  let s2 := s1 ++ "def"
  IO.println s!"strings: {s1} {s2} {s1.length} {s2.length}"
  let bytes := ByteArray.empty.push 1 |>.push 2
  let bytes2 := bytes.push 3
  let bytes3 := bytes.push 4
  IO.println s!"bytes: {bytes.size} {bytes2.size} {bytes2[2]!} {bytes3[2]!}"
  -- nested arrays
  let mut grid : Array (Array Nat) := #[]
  for i in [0:3] do
    let mut row : Array Nat := #[]
    for j in [0:3] do
      row := row.push (i * 3 + j)
    grid := grid.push row
  let saved := grid
  grid := grid.set! 1 (grid[1]!.set! 1 100)
  IO.println s!"grid: {grid[1]![1]!} {saved[1]![1]!} {grid[2]![2]!} {grid.size}"
  -- structures and functional update
  let acct : Account := { owner := "ada", balance := 10, history := #[] }
  let acct2 := deposit (deposit acct 5) 7
  IO.println s!"account: {acct.balance} {acct.history.size} {acct2.balance} {acct2.history.size} {acct2.history[1]!} {acct2.owner}"
  -- inductive types and matching
  IO.println s!"{describe Shape.empty Color.red} / {describe (Shape.circle 0) Color.blue} / {describe (Shape.circle 2) Color.red} / {describe (Shape.rect 3 4) Color.green}"
  IO.println s!"{classify 0} {classify 1} {classify 2} {classify 50} {classify 500} {nested none} {nested (some none)} {nested (some (some 40))}"
  -- control flow
  IO.println s!"{sumTo #[5, 0, 6, 7, 100, 1] 20} {collatz 27} {fib 20}"
  match firstNegative #[1, 2, 0xffffffffffffffff, 4] with
  | some i => IO.println s!"negative at {i}"
  | none => IO.println "no negative"
  IO.println s!"{(firstNegative #[1, 2]).isNone} {(swap (7, "seven")).1} {(swap (7, "seven")).2}"
  -- integer semantics
  let big : UInt64 := 0xffffffffffffffff
  let small : UInt8 := 200
  IO.println s!"{big + 2} {small + 100} {small * 2} {(0 : UInt32) - 1} {(5 : Nat) - 9} {(17 : Nat) / 0} {(17 : Nat) % 0} {(17 : UInt8) % 5}"
  IO.println s!"{(1 : UInt32) <<< 33} {(0x80 : UInt8) >>> 9} {(1 : UInt64) <<< 63} {~~~(0 : UInt16)} {(300 : Nat).toUInt8} {(0xdeadbeef : UInt64).toUInt16} {(250 : UInt8).toNat + 10}"
  IO.println s!"{min 3 7} {max 3 7} {(3 : Nat) == 3} {(3 : Nat) != 3} {3 < 2 || 2 < 3} {3 < 2 && 2 < 3} {!(3 < 2)}"
  -- characters and strings
  let greeting := "héllo wörld"
  IO.println s!"{greeting.length} {greeting.toUTF8.size} {String.singleton 'λ'} {"".isEmpty} {"x".isEmpty} {"42".toNat! + 1} {toString true}"
  let mut word := ""
  for c in #['L', 'e', 'a', 'n'] do
    word := word.push c
  IO.println s!"{word} {word == "Lean"} {word != "lean"}"
  -- tuples and options
  let (q, r) := (17 / 5, 17 % 5)
  let pair : Nat × Nat × Nat := (1, 2, 3)
  IO.println s!"{q} {r} {pair.1} {pair.2.1} {pair.2.2}"
  let opt : Option String := some "x"
  IO.println s!"{opt.isSome} {opt.get!}"
