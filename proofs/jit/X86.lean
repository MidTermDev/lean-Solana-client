import Std

namespace X86

/-- Register numbers use the Intel ModRM numbering, including the REX high bit. -/
abbrev Regs := Fin 16 → UInt64
def reg (r : UInt64) : Fin 16 := ⟨r.toNat % 16, Nat.mod_lt _ (by decide)⟩

inductive Bin where
  | add | sub | mul | bor | band | xor | mov
  deriving DecidableEq, Repr
inductive Shift where
  | shl | shr | sar
  deriving DecidableEq, Repr

/-- Header semantics. The immediate, if present, follows the header, little endian.
The two memory operands refer to mapped words at rbp+80 and rbp+120. -/
inductive Form where
  | rr (wide : Bool) (op : Bin) (dst src : UInt64)
  | grp (wide short : Bool) (op : Bin) (dst : UInt64)
  | imulI (wide : Bool) (dst src : UInt64)
  | neg (wide : Bool) (dst : UInt64)
  | shiftI (wide : Bool) (op : Shift) (dst : UInt64)
  | bmi (wide : Bool) (op : Shift) (dst src count : UInt64)
  | movI (dst : UInt64) | movS (dst : UInt64)
  | sxd (dst src : UInt64) | zx (dst src : UInt64)
  | rol16 (dst : UInt64) | swap (wide : Bool) (dst : UInt64)
  | frameLoad | tempStore (wide : Bool)
  | test (wide : Bool) (a b : UInt64) | jz
  | divR (wide : Bool) (src : UInt64) | divM (wide : Bool)
  deriving DecidableEq, Repr

def Form.size : Form → Nat
  | .grp _ short .. => if short then 1 else 4
  | .shiftI .. | .rol16 .. => 1
  | .imulI .. | .movI .. | .movS .. | .tempStore .. | .jz => 4
  | .rr .. | .neg .. | .bmi .. | .sxd .. | .zx .. | .swap ..
  | .frameLoad | .test .. | .divR .. | .divM .. => 0

/-- A byte reader carries the property needed to compose independent instruction decodes. -/
structure Reader (α : Type) where
  read : List UInt8 → Option (α × List UInt8)
  append_ok : ∀ {bs a rest}, read bs = some (a, rest) → ∀ tail,
    read (bs ++ tail) = some (a, rest ++ tail)

namespace Reader
def byte : Reader UInt8 where
  read := fun | [] => none | x :: xs => some (x,xs)
  append_ok := by rintro (_|⟨x,xs⟩) a rest h tail <;> cases h <;> rfl

def pureR (a : α) : Reader α where
  read := fun bs => some (a, bs)
  append_ok := by intros; simp_all

def failR : Reader α where
  read := fun _ => none
  append_ok := by simp

def bindR (p : Reader α) (f : α → Reader β) : Reader β where
  read := fun bs => do
    let (a, xs) ← p.read bs
    (f a).read xs
  append_ok := by
    intro bs b rest h tail
    cases hp : p.read bs with
    | none => simp [hp] at h
    | some pair =>
      obtain ⟨a,xs⟩ := pair
      simpa [p.append_ok hp tail] using (f a).append_ok (by simpa [hp] using h) tail

instance : Monad Reader where
  pure := pureR
  bind := bindR

def fromOption : Option α → Reader α
  | some a => pure a
  | none => failR

def expect (n : UInt8) : Reader Unit := do
  if (← byte) == n then pure () else failR
end Reader

open Reader

private def groupBin : UInt8 → Option Bin
  | 0 => some .add | 1 => some .bor | 4 => some .band | 5 => some .sub | 6 => some .xor
  | _ => none
private def shiftExt : UInt8 → Option Shift
  | 4 => some .shl | 5 => some .shr | 7 => some .sar | _ => none

private def legacy (word16 : Bool) (rex op : UInt8) : Reader Form := do
  let w := rex &&& 8 != 0
  let hiR := ((rex &&& 4) <<< 1).toUInt64
  let hiB := ((rex &&& 1) <<< 3).toUInt64
  if !word16 && op >= 0xb8 && op <= 0xbf && !w then
    return .movI (hiB + (op - 0xb8).toUInt64)
  let two := op == 0x0f
  let code ← if two then byte else pure op
  if two && !word16 then
    if code == 0x84 && rex == 0 then return .jz
    if code >= 0xc8 && code <= 0xcf then return .swap w (hiB + (code - 0xc8).toUInt64)
  let m ← byte
  let ext := (m >>> 3) &&& 7
  let a := hiR + ext.toUInt64
  let b := hiB + (m &&& 7).toUInt64
  if m >>> 6 == 1 && !word16 && !two && b == 5 then
    let disp ← byte
    if w && code == 0x8b && a == 0 && disp == 80 then return .frameLoad
    if code == 0xc7 && a == 0 && disp == 120 then return .tempStore w
    if code == 0xf7 && a == 6 && disp == 120 then return .divM w
    failR
  else if m >>> 6 != 3 then failR
  else if word16 then
    if !w && !two && code == 0xc1 && a == 0 then return .rol16 b
    failR
  else if two then
    if code == 0xaf then return .rr w .mul a b
    if code == 0xb7 && !w then return .zx a b
    failR
  else
    match code with
    | 0x01 => return .rr w .add b a
    | 0x09 => return .rr w .bor b a
    | 0x21 => return .rr w .band b a
    | 0x29 => return .rr w .sub b a
    | 0x31 => return .rr w .xor b a
    | 0x89 => return .rr w .mov b a
    | 0x69 => return .imulI w a b
    | 0x85 => return .test w b a
    | 0x63 => if w then pure (.sxd a b) else failR
    | 0x81 | 0x83 => return .grp w (code == 0x83) (← fromOption (groupBin ext)) b
    | 0xc7 => if w && ext == 0 then pure (.movS b) else failR
    | 0xf7 => if ext == 3 then pure (.neg w b) else if ext == 6 then pure (.divR w b) else failR
    | 0xc1 => return .shiftI w (← fromOption (shiftExt ext)) b
    | _ => failR

def header : Reader Form := do
  let first ← byte
  if first == 0xc4 then
    let rx ← byte
    let wc ← byte
    expect 0xf7
    let m ← byte
    if rx &&& 0x5f != 0x42 || wc &&& 4 != 0 || m >>> 6 != 3 then failR
    else
      let k ← fromOption (match wc &&& 3 with
        | 1 => some Shift.shl | 3 => some .shr | 2 => some .sar | _ => none)
      return .bmi (wc &&& 128 != 0) k
        (((~~~rx >>> 7) <<< 3) + ((m >>> 3) &&& 7)).toUInt64
        ((((~~~rx >>> 5) &&& 1) <<< 3) + (m &&& 7)).toUInt64 ((~~~wc >>> 3) &&& 15).toUInt64
  else
    let word16 := first == 0x66
    let lead ← if word16 then byte else pure first
    if lead >= 0x40 && lead <= 0x4f then legacy word16 lead (← byte)
    else legacy word16 0 lead

def payload : Nat → Reader UInt64
  | 0 => pure 0
  | n+1 => do
    let lo ← byte
    let hi ← payload n
    return lo.toUInt64 ||| (hi <<< 8)

structure Ins where
  form : Form
  imm : UInt64 := 0
  deriving DecidableEq, Repr

def decode : Reader Ins := do
  let f ← header
  return ⟨f, ← payload f.size⟩

def narrow (w : Bool) (x : UInt64) := if w then x else x.toUInt32.toUInt64
def sx8 (x : UInt64) := UInt64.ofBitVec (x.toBitVec.truncate 8 |>.signExtend 64)
def sx32 (x : UInt64) := UInt64.ofBitVec (x.toBitVec.truncate 32 |>.signExtend 64)

structure State where
  regs : Regs
  frame : UInt64              -- memory[rbp+80], guest r10
  temp : UInt64               -- memory[rbp+120], scratch
  zf : Bool

def State.write (m : State) (dst v : UInt64) : State :=
  { m with regs := fun i => if i == reg dst then v else m.regs i }

def bin : Bin → UInt64 → UInt64 → UInt64
  | .add, a,b => a+b | .sub,a,b => a-b | .mul,a,b => a*b
  | .bor,a,b => a ||| b | .band,a,b => a &&& b | .xor,a,b => a ^^^ b | .mov,_,b => b

def shift (w : Bool) (k : Shift) (a b : UInt64) : UInt64 :=
  let n := b &&& (if w then 63 else 31)
  let x := narrow w a
  narrow w (match k with
  | .shl => x <<< n | .shr => x >>> n
  | .sar =>
    let signed := if w then a else sx32 x
    let fill := if n != 0 && signed &&& 0x8000000000000000 != 0
      then 0xffffffffffffffff <<< (64-n) else 0
    (signed >>> n) ||| fill)

def reverseBytes (bytes : Nat) (x : UInt64) : UInt64 :=
  match bytes with
  | 0 => 0
  | n+1 => ((x &&& 255) <<< (8*n).toUInt64) ||| reverseBytes n (x >>> 8)

inductive Outcome where
  | next (state : State)
  | taken (rel32 : UInt32) (state : State)  -- relative to first byte after jz
  | divideError
  | invalid

/-- Hardware divides RDX:RAX by the operand, trapping on zero or quotient overflow. -/
def divide (m : State) (w : Bool) (source : UInt64) : Outcome :=
  let lo := narrow w (m.regs 0)
  let hi := narrow w (m.regs 2)
  let den := narrow w source
  if den == 0 || hi >= den then .divideError
  else if hi == 0 then .next ((m.write 0 (lo / den)).write 2 (lo % den))
  else
    let bits := if w then 64 else 32
    let num := (hi.toBitVec.zeroExtend 128 <<< bits) ||| lo.toBitVec.zeroExtend 128
    let divisor := den.toBitVec.zeroExtend 128
    .next ((m.write 0 (narrow w (UInt64.ofBitVec ((num / divisor).truncate 64)))).write 2 (narrow w (UInt64.ofBitVec ((num % divisor).truncate 64))))

def exec (i : Ins) (m : State) : Outcome :=
  let get := fun r => m.regs (reg r)
  let put := fun w d x => Outcome.next (m.write d (narrow w x))
  let v := i.imm
  match i.form with
  | .rr w op d s => put w d (bin op (get d) (get s))
  | .grp w short op d => put w d (bin op (get d) (if short then sx8 v else sx32 v))
  | .imulI w d s => put w d (get s * sx32 v)
  | .neg w d => put w d (0 - get d)
  | .shiftI w k d => put w d (shift w k (get d) v)
  | .bmi w k d s c => put w d (shift w k (get s) (get c))
  | .movI d => put false d v
  | .movS d => put true d (sx32 v)
  | .sxd d s => put true d (sx32 (get s))
  | .zx d s => put false d (get s).toUInt16.toUInt64
  | .rol16 d =>
    let x := (get d).toBitVec.truncate 16
    .next (m.write d ((get d &&& 0xffffffffffff0000) ||| (UInt64.ofBitVec ((x.rotateLeft v.toNat).zeroExtend 64))))
  | .swap w d => put w d (reverseBytes (if w then 8 else 4) (get d))
  | .frameLoad => .next (m.write 0 m.frame)
  | .tempStore w =>
    .next {m with temp := if w then sx32 v else (m.temp &&& 0xffffffff00000000) ||| v.toUInt32.toUInt64}
  | .test w a b => .next {m with zf := narrow w (get a &&& get b) == 0 }
  | .jz => if m.zf then .taken v.toUInt32 m else .next m
  | .divR w s => divide m w (get s)
  | .divM w => divide m w m.temp

/-- Stop at the first taken branch. A caller supplies relocation and dispatch.
Fuel bounds decoding work; zero bytes succeed even at zero fuel. -/
def run : Nat → List UInt8 → State → Outcome
  | _, [], m => .next m
  | 0, _ :: _, _ => .invalid
  | n+1, b :: bs, m =>
    match decode.read (b :: bs) with
    | none => .invalid
    | some (i, rest) =>
      match exec i m with
      | .next m' => run n rest m'
      | other => other

end X86
