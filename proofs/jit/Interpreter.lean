-- MIT, Copyright (c) 2026 MidTermDev. Source: lean-Solana-client b9fa957. See LICENSE.
-- ALU arm of lib/Solana/Sbpf.lean; status constants from lib/Solana/SbpfBase.lean.
import Alu

namespace Sbpf
def finished : UInt64 := 0
def divideByZero : UInt64 := 2
def unsupportedInstruction : UInt64 := 3

/-- Execute the pinned post-decode ALU arm for one iteration of the interpreter loop. -/
def aluStep (registers : Array UInt64) (opc : UInt64) (dst src : Nat) (imm32 : UInt64)
    (v2 : Bool) : UInt64 × Array UInt64 := Id.run do
  let mut regs := registers
  let mut status := finished
  let cls := opc &&& 7
  let op := opc &&& 0xf0
  let imm := sext32 imm32
  for _ in [()] do
    -- arithmetic: 64-bit (class 7) and 32-bit (class 4), operand from a register or the immediate
    let b := if opc &&& 8 != 0 then regs[src]! else imm
    let a := regs[dst]!
    if opc == 0xdc || (opc == 0xd4 && !v2) then
      -- byte order: `le` truncates, `be` also swaps
      let bytes := if imm32 == 16 then 2 else if imm32 == 32 then 4 else if imm32 == 64 then 8 else 0
      if bytes == 0 then
        status := unsupportedInstruction
        break
      let low := if bytes == 8 then a else a &&& (((1 : UInt64) <<< (8 * bytes).toUInt64) - 1)
      regs := regs.set! dst (if opc == 0xdc then bswap low bytes else low)
    else if op > 0xc0 then
      status := unsupportedInstruction
      break
    else if (op == 0x30 || op == 0x90) && (if cls == 7 then b == 0 else b &&& 0xFFFFFFFF == 0) then
      status := divideByZero
      break
    else if v2 then
      -- from v2: subtracting from an immediate computes immediate − register; 32-bit add and subtract
      -- zero-extend their result; a 32-bit move between registers sign-extends
      let swap := op == 0x10 && opc &&& 8 == 0
      let r := if cls == 7 then alu64 op (if swap then b else a) (if swap then a else b)
        else alu32 op (if swap then b else a) (if swap then a else b)
      regs := regs.set! dst (if cls == 4 && (op == 0x00 || op == 0x10) then r &&& 0xFFFFFFFF
        else if opc == 0xbc then sext32 r else r)
    else
      regs := regs.set! dst (if cls == 7 then alu64 op a b else alu32 op a b)
  return (status, regs)
end Sbpf
