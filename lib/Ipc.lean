import Sys

/-!
# Inter-process communication on a raw futex

Tiles (processes) talk through single-producer/single-consumer rings that
live in `MAP_SHARED` memory created before `fork`. Passing a message is a
`rep movsb` into the ring and one atomic add; no syscall is made unless the
consumer is actually asleep, in which case the producer issues one
`FUTEX_WAKE`.

There are no locks and no kernel objects other than the futex word itself:
no pipes, no eventfds, no sockets, no semaphores.

## The wake-up protocol

A consumer that finds its rings empty must not go to sleep if a producer is
publishing at the same moment. Both sides follow a Dekker-style handshake
whose two stores are *locked* instructions (full memory barriers), so at
least one side always sees the other:

    consumer                           producer
    --------                           --------
    xchg  sleeping := 1                lock xadd  head += 1
    seq := load futexWord              if load sleeping != 0:
    if rings still empty:                  lock xadd  futexWord += 1
        futex_wait(futexWord, seq)         futex_wake(futexWord)
    sleeping := 0

If the producer's publish lands after the consumer's emptiness check, the
producer is guaranteed to observe `sleeping = 1`, bump the futex word and
wake; the kernel then refuses to sleep on a stale `seq` (or wakes the
sleeper). If it lands before, the consumer's check sees the message.
-/

namespace Ipc

/-- A futex-backed event counter in shared memory.
Layout: `+0` futex word (bumped on every notify), `+8` "consumer is sleeping" flag. -/
structure Waiter where
  addr : UInt64
  deriving Inhabited

namespace Waiter

def create : IO Waiter := do
  let addr ← Sys.mmapShared 4096
  return ⟨addr⟩

/-- Producer side: call after publishing. Costs one load when the consumer is awake. -/
def notify (w : Waiter) : IO Unit := do
  let sleeping ← Mem.load32 (w.addr + 8)
  if sleeping != 0 then
    let _ ← Mem.xadd64 w.addr 1
    Sys.futexWake w.addr 1

/-- Consumer side, step 1: announce the intent to sleep and sample the futex word. -/
def prepare (w : Waiter) : IO UInt64 := do
  let _ ← Mem.xchg32 (w.addr + 8) 1
  Mem.load32 w.addr

/-- Consumer side, step 2 (the rings were still empty): sleep until notified. -/
def commit (w : Waiter) (seq timeoutMs : UInt64) : IO Unit := do
  Sys.futexWait w.addr seq timeoutMs
  Mem.store32 (w.addr + 8) 0

/-- Consumer side, step 2 (a message showed up after all): stay awake. -/
def cancel (w : Waiter) : IO Unit := Mem.store32 (w.addr + 8) 0

end Waiter

/-- A message as it comes out of a ring: a small tag word plus the payload. -/
structure Msg where
  tag : UInt64
  data : ByteArray
  deriving Inhabited

/-- A single-producer/single-consumer ring of fixed-size slots in shared memory.

Layout of the mapping: `+0` head (messages published), `+64` tail (messages
consumed), `+128` count of messages dropped because the ring was full; slots
start at `+4096`. Head and tail sit on separate cache lines. Each slot holds
`[length : u64][tag : u64][payload]`. -/
structure Ring where
  base : UInt64
  mask : UInt64
  slotSize : UInt64
  waiter : Waiter
  deriving Inhabited

namespace Ring

/-- Creates a ring with `slots` slots (a power of two) that wakes `w` on publish. -/
def create (slots slotSize : UInt64) (w : Waiter) : IO Ring := do
  let base ← Sys.mmapShared (4096 + slots * slotSize)
  return ⟨base, slots - 1, slotSize, w⟩

/-- Publishes a message. Returns false (and counts a drop) when the ring is full. -/
def push (r : Ring) (tag : UInt64) (data : ByteArray) : IO Bool := do
  let h ← Mem.load64 r.base
  let t ← Mem.load64 (r.base + 64)
  let n := data.size.toUInt64
  if h - t > r.mask || n + 16 > r.slotSize then
    let _ ← Mem.xadd64 (r.base + 128) 1
    return false
  let slot := r.base + 4096 + (h &&& r.mask) * r.slotSize
  Mem.store64 slot n
  Mem.store64 (slot + 8) tag
  let p := Unsafe.addr data
  Mem.copy (slot + 16) (p + 24) n
  -- the locked add is both the publication and the memory barrier of the handshake
  let _ ← Mem.xadd64 r.base 1
  r.waiter.notify
  return true

/-- Takes the next message, if any. Never blocks. -/
def pop (r : Ring) : IO (Option Msg) := do
  let t ← Mem.load64 (r.base + 64)
  let h ← Mem.load64 r.base
  if t == h then
    return none
  let slot := r.base + 4096 + (t &&& r.mask) * r.slotSize
  let n ← Mem.load64 slot
  let tag ← Mem.load64 (slot + 8)
  let buf := Sys.scratch n.toNat
  let p := Unsafe.addr buf
  Mem.copy (p + 24) (slot + 16) n
  let buf ← Sys.setSize buf n
  Mem.store64 (r.base + 64) (t + 1)
  return some ⟨tag, buf⟩

def isEmpty (r : Ring) : IO Bool := do
  let t ← Mem.load64 (r.base + 64)
  let h ← Mem.load64 r.base
  return t == h

/-- Messages currently queued. -/
def depth (r : Ring) : IO UInt64 := do
  let t ← Mem.load64 (r.base + 64)
  let h ← Mem.load64 r.base
  return h - t

def dropped (r : Ring) : IO UInt64 := Mem.load64 (r.base + 128)

/-- Blocking receive on a single ring, with a timeout. -/
def recv (r : Ring) (timeoutMs : UInt64) : IO (Option Msg) := do
  let m ← r.pop
  if m.isSome then
    return m
  let seq ← r.waiter.prepare
  if (← r.isEmpty) then
    r.waiter.commit seq timeoutMs
  else
    r.waiter.cancel
  r.pop

end Ring

/-- A page of 64-bit counters in shared memory, updated atomically by the
tiles and read by the supervisor for the dashboard. -/
structure Metrics where
  base : UInt64
  deriving Inhabited

namespace Metrics

def create : IO Metrics := do
  let base ← Sys.mmapShared 65536
  return ⟨base⟩

def add (m : Metrics) (i : Nat) (v : UInt64) : IO Unit := do
  let _ ← Mem.xadd64 (m.base + i.toUInt64 * 8) v
  pure ()

def set (m : Metrics) (i : Nat) (v : UInt64) : IO Unit := Mem.store64 (m.base + i.toUInt64 * 8) v

def get (m : Metrics) (i : Nat) : IO UInt64 := Mem.load64 (m.base + i.toUInt64 * 8)

end Metrics

end Ipc
