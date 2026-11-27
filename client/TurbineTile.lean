import Layout
import Solana.Shred

/-!
# The turbine tile

Validators relay each block's shreds to one another in a tree ("turbine"):
the leader sends each shred to one node, which sends it to 200 more, and so
on. Because this node names a socket for shreds in its gossip contact info,
it is in everyone's tree, and shreds arrive here unasked.

This tile receives them, discards what is not a shred of the kind in use,
and hands the rest to the block tile.
-/

def turbineTile (sh : Shared) : IO Unit := do
  Sys.dieWithParent
  Sys.setTimeout sh.tvuSock 20 200
  repeat
    let d ← Sys.recvFrom sh.tvuSock 1500
    if d.data.size != 0 then
      routeShred sh d.data
