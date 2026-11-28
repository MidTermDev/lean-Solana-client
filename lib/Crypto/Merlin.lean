import Fast
import Crypto.Keccak

/-!
# Merlin transcripts

A proof that needs no conversation replaces the verifier's random questions
by a hash of everything said so far. Merlin is that hash, kept as a running
state: messages go in under labels, and challenges come out that depend on
all of them. It is STROBE-128 over Keccak's permutation: bytes are mixed
into the first 166 of the state's 200, and the state is permuted when those
are used up and before any bytes are taken out.
-/

namespace Merlin

/-- Keccak's state as 25 words, where in its first 166 bytes the next byte goes, and one past where the operation under way began. -/
structure Transcript where
  state : Array UInt64
  pos : Nat
  began : Nat

def rate : Nat := 166

def mix (s : Array UInt64) (i : Nat) (b : UInt8) : Array UInt64 :=
  s.set! (i / 8) (s[i / 8]! ^^^ (b.toUInt64 <<< (8 * (i % 8)).toUInt64))

def Transcript.permute (t : Transcript) : Transcript :=
  ⟨Keccak.permute (mix (mix (mix t.state t.pos t.began.toUInt8) (t.pos + 1) 4) (rate + 1) 0x80), 0, 0⟩

def Transcript.absorb (t0 : Transcript) (data : ByteArray) : Transcript := Id.run do
  let mut t := t0
  for i in [0:data.size] do
    t := ⟨mix t.state t.pos data[i]!, t.pos + 1, t.began⟩
    if t.pos == rate then
      t := t.permute
  return t

/-- Starts an operation: 0x12 a label, 2 a message, 7 taking bytes out. -/
def Transcript.operation (t : Transcript) (flags : UInt8) : Transcript :=
  let u := (⟨t.state, t.pos, t.pos + 1⟩ : Transcript).absorb ((ByteArray.empty.push t.began.toUInt8).push flags)
  if flags &&& 4 != 0 && u.pos != 0 then u.permute else u

/-- Adds a message under a label. -/
def Transcript.append (t : Transcript) (label : String) (message : ByteArray) : Transcript :=
  (((t.operation 0x12).absorb (Fast.push32 label.toUTF8 message.size.toUInt64)).operation 2).absorb message

def Transcript.append64 (t : Transcript) (label : String) (x : UInt64) : Transcript :=
  t.append label (Fast.push64 ByteArray.empty x)

/-- Takes `count` bytes that depend on everything added so far. -/
def Transcript.challenge (t0 : Transcript) (label : String) (count : Nat) : Transcript × ByteArray := Id.run do
  let mut t := ((t0.operation 0x12).absorb (Fast.push32 label.toUTF8 count.toUInt64)).operation 7
  let mut out := ByteArray.emptyWithCapacity count
  for _ in [0:count] do
    let b := (t.state[t.pos / 8]! >>> (8 * (t.pos % 8)).toUInt64).toUInt8
    out := out.push b
    t := ⟨mix t.state t.pos b, t.pos + 1, t.began⟩
    if t.pos == rate then
      t := t.permute
  return (t, out)

/-- A transcript for the protocol named. -/
def Transcript.new (label : String) : Transcript := Id.run do
  let mut s : Array UInt64 := Array.replicate 25 0
  let head := (ByteArray.empty.push 1).push 168 ++ ((ByteArray.empty.push 1).push 0).push 1 ++ (ByteArray.empty.push 96) ++ "STROBEv1.0.2".toUTF8
  for i in [0:head.size] do
    s := mix s i head[i]!
  return (((⟨Keccak.permute s, 0, 0⟩ : Transcript).operation 0x12).absorb "Merlin v1.0".toUTF8).append "dom-sep" label.toUTF8

end Merlin
