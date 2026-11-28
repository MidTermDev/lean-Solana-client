-- Interpreter arithmetic adapted from lib/Solana/Sbpf.lean at b9fa957 (MIT, see LICENSE).
import Plan
import Execution

namespace Certificate
open X86

/-- The post-decode arithmetic arm of Sbpf.lean for the versions admitted by Program.translated.
The two high-nibble DIV/MOD guards use the interpreter's width test. -/
def reference (op : Op) (wide named : Bool) (i : UInt32) (dst src : UInt64) : Option UInt64 :=
  let a := dst
  let b := if named then src else Sbpf.sext32 i.toUInt64
  if op == .endian then
    let bytes := if i == 16 then 2 else if i == 32 then 4 else if i == 64 then 8 else 0
    if bytes == 0 then none else
      let low := if bytes == 8 then a else a &&& (((1 : UInt64) <<< (8 * bytes).toUInt64) - 1)
      some (if named then Sbpf.bswap low bytes else low)
  else if (op == .udiv || op == .umod) && (if wide then b == 0 else b &&& 0xffffffff == 0)
    then none
  else some (if wide then Sbpf.alu64 op.nibble a b else Sbpf.alu32 op.nibble a b)

def admitted (op : Op) (w named : Bool) (s : Fin 11) (i : UInt32) : Bool :=
  match op with
  | .endian => !w && (i == 16 || i == 32 || i == 64)
  | .udiv | .umod => if named then s.val != 10 else i != 0
  | _ => true

/-- Observe one of the ten mapped registers and the virtual frame pointer. -/
def observation (g : UInt64) : Outcome → Option (Option UInt32 × UInt64 × UInt64)
  | .next m => some (none, m.regs (reg g), m.frame)
  | .taken rel m => some (some rel, m.regs (reg g), m.frame)
  | _ => none

def expected (hit : Bool) (old frame : UInt64) (result : Option UInt64) (rel : UInt32 := 0) :
    Option (Option UInt32 × UInt64 × UInt64) :=
  match result with
  | some v => some (none, if hit then v else old, frame)
  | none => some (some rel, old, frame)

end Certificate
