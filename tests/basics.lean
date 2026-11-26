def sum (b : ByteArray) : Nat := Id.run do
  let mut s := 0
  for i in [0:b.size] do
    s := s + b[i]!.toNat
  return s

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

structure P where
  a : Nat
  b : Array UInt64
  deriving Inhabited

def upd (p : P) : P := { p with a := p.a + 1 }

def bump (a : Array UInt64) (i : Nat) : Array UInt64 := a.set! i (a[i]! + 1)

def t (x : UInt64) : UInt8 := (x >>> 8).toUInt8

def classify (n : Nat) : String :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | _ => s!"many {n}"

def beq (a b : ByteArray) : Bool := a == b
def app (a b : ByteArray) : ByteArray := a ++ b
def mk : ByteArray := ByteArray.emptyWithCapacity 10
def rep : Array UInt64 := Array.replicate 4 0
def ex (a : ByteArray) : ByteArray := a.extract 1 3
def w : Nat := Id.run do
  let mut i := 0
  while i < 10 do
    i := i + 1
  return i
def opt (o : Option Nat) : Nat := match o with
  | some x => x
  | none => 0
def tup (p : Nat × UInt8) : Nat := p.1 + p.2.toNat
def strs (s : String) : Nat := s.length + s.toUTF8.size + (String.fromUTF8! s.toUTF8).length
def ch : String := (String.singleton 'a').push (Char.ofNat 66)
def sh (x : UInt8) : UInt8 := x <<< 9
def nsh (x : Nat) : Nat := (x <<< 3) ^^^ (x >>> 1) &&& 0xff ||| 7

def main : IO Unit := do
  IO.println s!"{sum (ByteArray.empty.push 3 |>.push 4)} {rotr 1 1} {(upd ⟨1, #[]⟩).a} {classify 5} {w} {ch} {sh 1} {nsh 5} {(255 : UInt8) + 1} {(3 : Nat) - 5} {(7 : UInt64) / 0} {beq mk mk}"
  IO.eprintln "err"
  let x ← pure 5
  IO.println (toString x ++ " " ++ toString (rotr 0x80000000 31))
  IO.println s!"{classify 0} {classify 1} {opt (some 9)} {opt none} {tup (4, 5)} {strs "héllo"} {t 0x1234}"
  let a := bump (bump rep 2) 2
  IO.println s!"{a[2]!} {a[0]!} {rep[2]!} {a.size} {(ex (app (ByteArray.empty.push 1 |>.push 2) (ByteArray.empty.push 3 |>.push 4))).size}"
