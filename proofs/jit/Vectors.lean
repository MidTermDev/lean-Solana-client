import Semantics
open Certificate X86

-- Runtime driver. The proof library has no input/output entry points.
def hexN (n : Nat) (v : UInt64) : String := Id.run do
  let alphabet := "0123456789abcdef".toList.toArray
  let mut result := ""
  for j in [0:n] do
    result := result.push alphabet[((v >>> (4 * (n-1-j)).toUInt64) &&& 15).toNat]!
  return result

def hexCode (b : ByteArray) := String.join (b.data.toList.map (fun x => hexN 2 x.toUInt64))
def ops := [Op.add,.sub,.mul,.udiv,.bor,.band,.shl,.shr,.neg,.umod,.xor,.mov,.sar,.endian]
def constants : List UInt32 := [0,1,7,16,31,32,63,64,127,128,255,256,0x7fffffff,0x80000000,0xffffff7f,0xffffff80,0xffffffff]

-- SplitMix64, fixed before selecting inputs. The original words are also stored in the TSV.
def randomWord (index : Nat) : UInt64 :=
  let a := 0xb9fa957 + 0x9e3779b97f4a7c15 * (index+1).toUInt64
  let b := (a ^^^ (a >>> 30)) * 0xbf58476d1ce4e5b9
  let c := (b ^^^ (b >>> 27)) * 0x94d049bb133111eb
  c ^^^ (c >>> 31)

def input (row : Nat) : State :=
  let word := fun j => randomWord (row * 19 + j)
  -- Files 64 and 65 exercise register-divide exits at each width.
  let regs := fun (r : Fin 16) => if row == 64 then 0 else if row == 65 then word r.val &&& 0xffffffff00000000 else word r.val
  ⟨regs, word 16, word 17, word 18 &&& 1 == 1⟩

def effects (before after : State) : String := Id.run do
  let mut delta := #[]
  for r in List.finRange 16 do
    if before.regs r != after.regs r then
      delta := delta.push s!"r{r.val}={hexN 16 (after.regs r)}"
  if before.temp != after.temp then delta := delta.push s!"t={hexN 16 after.temp}"
  if before.frame != after.frame then delta := delta.push s!"f={hexN 16 after.frame}"
  return if delta.isEmpty then "-" else ",".intercalate delta.toList

def selected (op : Op) (w named : Bool) (d : Fin 10) (s : Fin 11) (i : UInt32) : Bool :=
  let pair := if named then
    (d.val == 0 || d.val == 4) && (s.val == 0 || s.val == 1 || s.val == 4 || s.val == 5 || s.val == 10)
    else (d.val == 0 || d.val == 4) && s.val == 0
  pair && (if op == .endian then true else if named then i == 0 else
    match op with
    | .shl | .shr | .sar => i == 0 || i == 1 || i == (if w then 63 else 31)
    | .neg => i == 0
    | _ => i == 1 || i == 128 || i == 0x80000000 || i == 0xffffff80)

def main (args : List String) : IO Unit := do
  let vectors := args == ["vectors"]
  if !vectors && args != ["controls"] then throw (IO.userError "specify vectors or controls")
  if vectors then
    IO.println "kind\tid\tdata"
    for row in [0:66] do
      let m := input row
      let vals := (List.finRange 16).map (fun r => hexN 16 (m.regs r))
      IO.println s!"input\t{row}\t{",".intercalate (vals ++ [hexN 16 m.frame, hexN 16 m.temp, if m.zf then "1" else "0"])}"
  let mut id := 0
  for op in ops do
    for w in [false,true] do
      for named in [false,true] do
        let opc := op.nibble + cls w + (if named then 8 else 0)
        for d in List.finRange 10 do
          for s in List.finRange 11 do
            for i in constants do
              if !(admitted op w named s i) then continue
              if vectors && !(selected op w named d s i) then continue
              let (bytes, sites) := code op w named d s i
              let site := if sites.isEmpty then "-" else toString sites[0]!
              let desc := s!"{hexN 2 opc},{d.val},{s.val},{hexN 8 i.toUInt64},{hexCode bytes},{site}"
              if vectors then
                IO.println s!"code\t{id}\t{desc}"
                let guard := (op == .udiv || op == .umod) && named
                for row in [0:(if guard then 66 else 64)] do
                  let m := input row
                  let (status, after) ← match run bytes.size (wire bytes) m with
                    | .next f => pure ("ok", f)
                    | .taken rel f => pure (s!"j{hexN 8 rel.toUInt64}", f)
                    | _ => throw (IO.userError s!"model rejected {desc} on file {row}")
                  IO.println s!"out\t{id}.{row}\t{status},{effects m after}"
              else IO.println desc
              id := id+1
