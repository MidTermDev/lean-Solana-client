import Encoding

namespace Certificate
open X86

inductive Op where
  | add | sub | mul | udiv | bor | band | shl | shr | neg | umod | xor | mov | sar | endian
  deriving DecidableEq, Repr

def Op.nibble : Op → UInt64
  | .add => 0x00 | .sub => 0x10 | .mul => 0x20 | .udiv => 0x30 | .bor => 0x40
  | .band => 0x50 | .shl => 0x60 | .shr => 0x70 | .neg => 0x80 | .umod => 0x90
  | .xor => 0xa0 | .mov => 0xb0 | .sar => 0xc0 | .endian => 0xd0

def cls (w : Bool) : UInt64 := if w then 7 else 4
def host (g : Fin 10) := Jit.hostOf g.val.toUInt64
def source (s : Fin 11) : UInt64 := if s.val.toUInt64 == 10 then 0 else Jit.hostOf s.val.toUInt64

def ins (f : Form) (v : UInt64 := 0) : Ins := ⟨f,v⟩

def arith (w named : Bool) (k : Bin) (d s v : UInt64) : Ins :=
  if named then ins (.rr w k d s) else ins (.grp w (v+128 < 256) k d) v

def signTail (w : Bool) (d : UInt64) : List Ins := if w then [] else [ins (.sxd d d)]

def shifts (w named : Bool) (k : Shift) (d s v : UInt64) : List Ins :=
  if named then [ins (.bmi w k d d s)] else
    let n := v &&& (if w then 63 else 31)
    if n == 0 then (if w then [] else [ins (.rr false .mov d d)])
    else [ins (.shiftI w k d) n]

def division (w named rem : Bool) (d s v : UInt64) (rel : UInt32 := 0) : List Ins :=
  (if named then [ins (.test w s s), ins .jz rel.toUInt64] else [ins (.tempStore w) v]) ++
  [ins (.rr w .mov 0 d), ins (.rr false .xor 2 2),
   ins (if named then .divR w s else .divM w), ins (.rr w .mov d (if rem then 2 else 0))]

def body (op : Op) (w named : Bool) (d s : UInt64) (i : UInt32) : List Ins :=
  let v := Sbpf.sext32 i.toUInt64
  match op with
  | .add => arith w named .add d s v :: signTail w d
  | .sub => arith w named .sub d s v :: signTail w d
  | .bor => [arith w named .bor d s v]
  | .band => [arith w named .band d s v]
  | .xor => [arith w named .xor d s v]
  | .mul => (if named then ins (.rr w .mul d s) else ins (.imulI w d d) v) :: signTail w d
  | .shl => shifts w named .shl d s v
  | .shr => shifts w named .shr d s v
  | .sar => shifts w named .sar d s v
  | .neg => [ins (.neg w d)]
  | .mov =>
    if named then [ins (.rr w .mov d s)]
    else if w && v >= 0x100000000 then [ins (.movS d) v]
    else [ins (.movI d) (if w then v else i.toUInt64)]
  | .udiv => division w named false d s v
  | .umod => division w named true d s v
  | .endian =>
    if i.toUInt64 == 16 then (if named then [ins (.rol16 d) 8] else []) ++ [ins (.zx d d)]
    else if i.toUInt64 == 32 then [ins (if named then .swap false d else .rr false .mov d d)]
    else if named then [ins (.swap true d)] else []

def plan (op : Op) (w named : Bool) (d : Fin 10) (s : Fin 11) (i : UInt32) : List Ins :=
  (if named && s.val.toUInt64 == 10 then [ins .frameLoad] else []) ++
  body op w named (host d) (source s) i

def code (op : Op) (w named : Bool) (d : Fin 10) (s : Fin 11) (i : UInt32) :=
  Jit.aluCode .empty #[] 0 0 (cls w) op.nibble d.val.toUInt64 s.val.toUInt64 named i.toUInt64

end Certificate
