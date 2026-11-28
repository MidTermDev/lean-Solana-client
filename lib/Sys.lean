import Rt

/-!
# Linux, directly

Typed wrappers around the raw `syscall` instruction: files, sockets,
processes, shared memory, futexes, clocks. There is no libc between this
file and the kernel; the numbers below are the x86-64 Linux syscall table.

Buffers handed to the kernel are ordinary `ByteArray`s. `Unsafe.addr` gives
the address of the array object; its bytes start 24 bytes in (after the
reference count, size and capacity words).
-/

namespace Unsafe

/-- Address of the heap object behind `b`. Valid while `b` is alive. -/
@[extern "leanc_ptr"] opaque addr (b : @& ByteArray) : UInt64

/-- Address of the heap object behind an array of words; its elements start 24 bytes in. -/
@[extern "leanc_ptr"] opaque arrayAddr (a : @& Array UInt64) : UInt64

/-- Reinterprets a runtime string object (as returned by `Rt.argv`) as a `String`. -/
@[extern "leanc_ofptr"] opaque stringOfAddr (p : UInt64) : String

end Unsafe

namespace Sys

/-- Linux reports errors as `-errno`, i.e. the top 4095 values of the word. -/
def isErr (r : UInt64) : Bool := r > 0xFFFFFFFFFFFFF000

def errno (r : UInt64) : UInt64 := 0 - r

/-- A zero-filled scratch buffer with `n` bytes of capacity for the kernel to write into. -/
def scratch (n : Nat) : ByteArray := ByteArray.emptyWithCapacity n

/-- Sets the length of a buffer after the kernel filled `n` bytes of it. -/
def setSize (buf : ByteArray) (n : UInt64) : IO ByteArray := do
  let p := Unsafe.addr buf
  Mem.store64 (p + 8) n
  return buf

-- -------------------------------------------------------------------- files

def close (fd : UInt64) : IO Unit := do
  let _ ← syscall 3 fd 0 0 0 0 0
  pure ()

def write (fd : UInt64) (data : ByteArray) : IO UInt64 := do
  let p := Unsafe.addr data
  syscall 1 fd (p + 24) data.size.toUInt64 0 0 0

/-- Reads up to `max` bytes. Returns an empty array on error or end of file. -/
def read (fd : UInt64) (max : Nat) : IO ByteArray := do
  let buf := scratch max
  let p := Unsafe.addr buf
  let r ← syscall 0 fd (p + 24) max.toUInt64 0 0 0
  if isErr r then
    return ByteArray.empty
  setSize buf r

/-- Reads a whole (small) file. Returns an empty array if it cannot be opened. -/
def readFile (path : String) (max : Nat) : IO ByteArray := do
  let cpath := path.toUTF8.push 0
  let p := Unsafe.addr cpath
  let fd ← syscall 2 (p + 24) 0 0 0 0 0
  if isErr fd then
    return ByteArray.empty
  let data ← read fd max
  close fd
  return data

/-- Replaces the file at `path` with `data`, atomically: the bytes go to a
temporary file next to it, which is then renamed over the target. Readers
see either the old contents or the new, never a partial write. -/
def writeFileMode (path : String) (data : ByteArray) (mode : UInt64) : IO Bool := do
  let tmp := (path ++ ".tmp").toUTF8.push 0
  let tp := Unsafe.addr tmp
  -- O_WRONLY | O_CREAT | O_TRUNC
  let fd ← syscall 2 (tp + 24) 0x241 mode 0 0 0
  if isErr fd then
    return false
  let p := Unsafe.addr data
  let total := data.size.toUInt64
  let mut off : UInt64 := 0
  while off < total do
    let r ← syscall 1 fd (p + 24 + off) (total - off) 0 0 0
    if isErr r || r == 0 then
      close fd
      return false
    off := off + r
  close fd
  let dst := path.toUTF8.push 0
  let dp := Unsafe.addr dst
  let r ← syscall 82 (tp + 24) (dp + 24) 0 0 0 0
  return !(isErr r)

/-- `writeFileMode` with the usual permissions for a public file (0644). -/
def writeFileAtomic (path : String) (data : ByteArray) : IO Bool := writeFileMode path data 0x1a4

/-- True when `fd` is a terminal (TCGETS succeeds). -/
def isTty (fd : UInt64) : IO Bool := do
  let buf := scratch 64
  let p := Unsafe.addr buf
  let r ← syscall 16 fd 0x5401 (p + 24) 0 0 0
  return !(isErr r)

-- ------------------------------------------------------------------- clocks

/-- Wall-clock time in milliseconds since the Unix epoch. -/
def nowMs : IO UInt64 := do
  let ts := scratch 16
  let p := Unsafe.addr ts
  let _ ← syscall 228 0 (p + 24) 0 0 0 0
  let sec ← Mem.load64 (p + 24)
  let nsec ← Mem.load64 (p + 32)
  return sec * 1000 + nsec / 1000000

/-- Microseconds on a clock that only moves forward (for measuring how long something took). -/
def nowUs : IO UInt64 := do
  let ts := scratch 16
  let p := Unsafe.addr ts
  let _ ← syscall 228 1 (p + 24) 0 0 0 0
  let sec ← Mem.load64 (p + 24)
  let nsec ← Mem.load64 (p + 32)
  return sec * 1000000 + nsec / 1000

-- ---------------------------------------------------------------- processes

/-- `fork()`: returns 0 in the child and the child's pid in the parent. -/
def fork : IO UInt64 := syscall 57 0 0 0 0 0 0

def getpid : IO UInt64 := syscall 39 0 0 0 0 0 0

def kill (pid sig : UInt64) : IO Unit := do
  let _ ← syscall 62 pid sig 0 0 0 0
  pure ()

/-- Reaps one exited child without blocking. Returns its pid, or 0 if none has exited. -/
def reapChild : IO UInt64 := do
  let r ← syscall 61 0xFFFFFFFFFFFFFFFF 0 1 0 0 0
  if isErr r then
    return 0
  return r

/-- Asks the kernel to SIGKILL this process when its parent dies. -/
def dieWithParent : IO Unit := do
  let _ ← syscall 157 1 9 0 0 0 0
  pure ()

def exit (code : UInt64) : IO Unit := do
  let _ ← syscall 231 code 0 0 0 0 0
  pure ()

def argc : IO Nat := do
  let n ← Rt.argc
  return n.toNat

/-- Command-line argument `i` (0 is the program name). -/
def arg (i : Nat) : IO String := do
  let p ← Rt.argv i.toUInt64
  return Unsafe.stringOfAddr p

-- ------------------------------------------------------------ shared memory

/-- Anonymous memory that stays shared across `fork`: the substrate for IPC. -/
def mmapShared (len : UInt64) : IO UInt64 := do
  let p ← syscall 9 0 len 3 0x21 0xFFFFFFFFFFFFFFFF 0
  if isErr p then
    IO.eprintln "mmap(MAP_SHARED) failed"
    exit 1
  return p

-- ------------------------------------------------------------------ futexes
--
-- The futex syscall is the only kernel service the IPC layer uses. The
-- operations are deliberately the cross-process ones (no FUTEX_PRIVATE_FLAG):
-- the word lives in shared memory and the waiter and waker are different
-- processes.

/-- Sleeps while the 32-bit word at `addr` still equals `expected`, for at
most `timeoutMs` milliseconds. Returns immediately if the word differs. -/
def futexWait (addr expected timeoutMs : UInt64) : IO Unit := do
  let ts := scratch 16
  let p := Unsafe.addr ts
  Mem.store64 (p + 24) (timeoutMs / 1000)
  Mem.store64 (p + 32) ((timeoutMs % 1000) * 1000000)
  let _ ← syscall 202 addr 0 expected (p + 24) 0 0
  pure ()

/-- Wakes up to `n` processes sleeping on the word at `addr`. -/
def futexWake (addr n : UInt64) : IO Unit := do
  let _ ← syscall 202 addr 1 n 0 0 0
  pure ()

-- ------------------------------------------------------------------ sockets

/-- A `struct sockaddr_in` for an IPv4 address (host byte order) and port. -/
def sockaddr (ip : UInt32) (port : UInt16) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 16
  b := b.push 2
  b := b.push 0
  b := b.push (port >>> 8).toUInt8
  b := b.push port.toUInt8
  b := b.push (ip >>> 24).toUInt8
  b := b.push (ip >>> 16).toUInt8
  b := b.push (ip >>> 8).toUInt8
  b := b.push ip.toUInt8
  for _ in [0:8] do
    b := b.push 0
  return b

/-- A 32-bit little-endian integer in memory (socket options, lengths). -/
def int32 (v : UInt32) : ByteArray :=
  (((ByteArray.emptyWithCapacity 8).push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8 |>.push
    (v >>> 24).toUInt8

def udpSocket : IO UInt64 := syscall 41 2 2 0 0 0 0

def tcpSocket : IO UInt64 := syscall 41 2 1 0 0 0 0

def bind (fd : UInt64) (ip : UInt32) (port : UInt16) : IO UInt64 := do
  let sa := sockaddr ip port
  let p := Unsafe.addr sa
  syscall 49 fd (p + 24) 16 0 0 0

def connect (fd : UInt64) (ip : UInt32) (port : UInt16) : IO UInt64 := do
  let sa := sockaddr ip port
  let p := Unsafe.addr sa
  syscall 42 fd (p + 24) 16 0 0 0

/-- Sets a send or receive timeout (`SO_RCVTIMEO` = 20, `SO_SNDTIMEO` = 21). -/
def setTimeout (fd opt ms : UInt64) : IO Unit := do
  let tv := scratch 16
  let p := Unsafe.addr tv
  Mem.store64 (p + 24) (ms / 1000)
  Mem.store64 (p + 32) ((ms % 1000) * 1000)
  let _ ← syscall 54 fd 1 opt (p + 24) 16 0
  pure ()

/-- Sets an integer `SOL_SOCKET` option. -/
def setSockOpt (fd opt : UInt64) (value : UInt32) : IO Unit := do
  let v := int32 value
  let p := Unsafe.addr v
  let _ ← syscall 54 fd 1 opt (p + 24) 4 0
  pure ()

/-- Asks for a larger kernel receive buffer (`SO_RCVBUF`). -/
def setRecvBuffer (fd : UInt64) (bytes : UInt32) : IO Unit := setSockOpt fd 8 bytes

/-- A listening TCP socket on `ip:port` (`SO_REUSEADDR` set). Returns the
descriptor, or an error value (`isErr`). -/
def listenTcp (ip : UInt32) (port : UInt16) : IO UInt64 := do
  let fd ← tcpSocket
  if isErr fd then
    return fd
  setSockOpt fd 2 1
  let r ← bind fd ip port
  if isErr r then
    close fd
    return r
  let r ← syscall 50 fd 64 0 0 0 0
  if isErr r then
    close fd
    return r
  return fd

/-- Waits for the next connection on a listening socket. -/
def accept (fd : UInt64) : IO UInt64 := syscall 43 fd 0 0 0 0 0

/-- Sends all of `data` on a connected socket. Uses `MSG_NOSIGNAL`, so a
peer that hangs up early yields an error instead of a fatal SIGPIPE. -/
def sendAll (fd : UInt64) (data : ByteArray) : IO Bool := do
  let p := Unsafe.addr data
  let total := data.size.toUInt64
  let mut off : UInt64 := 0
  while off < total do
    let r ← syscall 44 fd (p + 24 + off) (total - off) 0x4000 0 0
    if isErr r || r == 0 then
      return false
    off := off + r
  return true

/-- The local port a socket is bound to. -/
def localPort (fd : UInt64) : IO UInt16 := do
  let sa := sockaddr 0 0
  let p := Unsafe.addr sa
  let len := int32 16
  let lp := Unsafe.addr len
  let _ ← syscall 51 fd (p + 24) (lp + 24) 0 0 0
  let hi ← Mem.load8 (p + 26)
  let lo ← Mem.load8 (p + 27)
  return ((hi <<< 8) ||| lo).toUInt16

def sendTo (fd : UInt64) (ip : UInt32) (port : UInt16) (data : ByteArray) : IO UInt64 := do
  let sa := sockaddr ip port
  let sp := Unsafe.addr sa
  let p := Unsafe.addr data
  syscall 44 fd (p + 24) data.size.toUInt64 0 (sp + 24) 16

/-- A received UDP datagram and where it came from. -/
structure Datagram where
  data : ByteArray
  ip : UInt32
  port : UInt16

/-- Receives one datagram of at most `max` bytes. On timeout or error the
returned datagram is empty. -/
def recvFrom (fd : UInt64) (max : Nat) : IO Datagram := do
  let buf := scratch max
  let p := Unsafe.addr buf
  let sa := sockaddr 0 0
  let sp := Unsafe.addr sa
  let len := int32 16
  let lp := Unsafe.addr len
  let r ← syscall 45 fd (p + 24) max.toUInt64 0 (sp + 24) (lp + 24)
  if isErr r then
    return ⟨ByteArray.empty, 0, 0⟩
  let buf ← setSize buf r
  let p0 ← Mem.load8 (sp + 26)
  let p1 ← Mem.load8 (sp + 27)
  let a0 ← Mem.load8 (sp + 28)
  let a1 ← Mem.load8 (sp + 29)
  let a2 ← Mem.load8 (sp + 30)
  let a3 ← Mem.load8 (sp + 31)
  let ip := (a0 <<< 24) ||| (a1 <<< 16) ||| (a2 <<< 8) ||| a3
  return ⟨buf, ip.toUInt32, ((p0 <<< 8) ||| p1).toUInt16⟩

-- ---------------------------------------------------- large files and pipes

/-- Opens a file. `flags`: 0 read, 0x42 read and write, creating it, 0x241 write, creating and emptying it, 0x242 the same and readable,
0x441 write at the end, creating it. Returns the descriptor, or an error (`isErr`). -/
def openFile (path : String) (flags : UInt64) : IO UInt64 := do
  let cpath := path.toUTF8.push 0
  let p := Unsafe.addr cpath
  syscall 2 (p + 24) flags 0x1a4 0 0 0

/-- Writes `len` bytes starting at address `addr`, all of them. -/
def writeFrom (fd addr len : UInt64) : IO Bool := do
  let mut off : UInt64 := 0
  while off < len do
    let r ← syscall 1 fd (addr + off) (len - off) 0 0 0
    if isErr r || r == 0 then
      -- (an interrupted call is simply made again)
      if errno r != 4 then
        return false
    else
      off := off + r
  return true

/-- Writes all of `data`. -/
def writeFully (fd : UInt64) (data : ByteArray) : IO Bool :=
  writeFrom fd (Unsafe.addr data + 24) data.size.toUInt64

/-- Reads exactly `len` bytes at offset `off` of a file. Returns fewer only at the end of the file or on error. -/
def readAt (fd off : UInt64) (len : Nat) : IO ByteArray := do
  let buf := scratch len
  let p := Unsafe.addr buf
  let mut got : UInt64 := 0
  while got < len.toUInt64 do
    let r ← syscall 17 fd (p + 24 + got) (len.toUInt64 - got) (off + got) 0 0
    if isErr r || r == 0 then
      break
    got := got + r
  setSize buf got

/-- The size of an open file. -/
def fileSize (fd : UInt64) : IO UInt64 := do
  let st := scratch 144
  let p := Unsafe.addr st
  let r ← syscall 5 fd (p + 24) 0 0 0 0
  if isErr r then
    return 0
  Mem.load64 (p + 24 + 48)

/-- A pipe: what is written to the second descriptor is read from the first. -/
def pipe : IO (UInt64 × UInt64) := do
  let fds := scratch 8
  let p := Unsafe.addr fds
  let r ← syscall 22 (p + 24) 0 0 0 0 0
  if isErr r then
    IO.eprintln "pipe failed"
    exit 1
  let reading ← Mem.load32 (p + 24)
  let writing ← Mem.load32 (p + 28)
  return (reading, writing)

/-- Asks for a pipe that holds `bytes` before a writer has to wait. -/
def setPipeSize (fd bytes : UInt64) : IO Unit := do
  let _ ← syscall 72 fd 1031 bytes 0 0 0
  pure ()

/-- Writing to a pipe nobody reads then fails with an error instead of ending the process. -/
def ignoreBrokenPipes : IO Unit := do
  let act := scratch 32
  let p := Unsafe.addr act
  Mem.fill (p + 24) 0 32
  Mem.store64 (p + 24) 1
  let _ ← syscall 13 13 (p + 24) 0 8 0 0
  pure ()

/-- Creates a directory; it is no error if it exists. -/
def mkdir (path : String) : IO Unit := do
  let cpath := path.toUTF8.push 0
  let p := Unsafe.addr cpath
  let _ ← syscall 83 (p + 24) 0x1ed 0 0 0 0
  pure ()

def unlink (path : String) : IO Unit := do
  let cpath := path.toUTF8.push 0
  let p := Unsafe.addr cpath
  let _ ← syscall 87 (p + 24) 0 0 0 0 0
  pure ()

/-- Waits until what was written to a file is on the disk. -/
def sync (fd : UInt64) : IO Unit := do
  let _ ← syscall 74 fd 0 0 0 0 0
  pure ()

/-- Cuts a file to `length` bytes. -/
def truncate (fd length : UInt64) : IO Unit := do
  let _ ← syscall 77 fd length 0 0 0 0
  pure ()

/-- Bytes free for an ordinary user on the filesystem holding `path`; 0 if that cannot be told. -/
def freeSpace (path : String) : IO UInt64 := do
  let cpath := path.toUTF8.push 0
  let p := Unsafe.addr cpath
  let st := scratch 120
  let q := Unsafe.addr st
  let r ← syscall 137 (p + 24) (q + 24) 0 0 0 0
  if isErr r then
    return 0
  let blockSize ← Mem.load64 (q + 24 + 8)
  let available ← Mem.load64 (q + 24 + 32)
  return blockSize * available

/-- Private zeroed memory, straight from the kernel: for tables too large for the heap. Returns 0 on failure. -/
def mapMemory (len : UInt64) : IO UInt64 := do
  let p ← syscall 9 0 len 3 0x22 0xFFFFFFFFFFFFFFFF 0
  return if isErr p then 0 else p

/-- Maps a whole file for reading. Returns 0 on failure. -/
def mapFile (fd len : UInt64) : IO UInt64 := do
  let p ← syscall 9 0 len 1 2 fd 0
  return if isErr p then 0 else p

def unmap (addr len : UInt64) : IO Unit := do
  let _ ← syscall 11 addr len 0 0 0 0
  pure ()

/-- Waits for a child to exit. Returns its pid and how it ended (0 = normally, with success), or pid 0 if there are no children. -/
def waitChild : IO (UInt64 × UInt64) := do
  let st := scratch 8
  let p := Unsafe.addr st
  Mem.store64 (p + 24) 0
  let r ← syscall 61 0xFFFFFFFFFFFFFFFF (p + 24) 0 0 0 0
  if isErr r then
    return (0, 0)
  let status ← Mem.load32 (p + 24)
  return (r, status)

end Sys
