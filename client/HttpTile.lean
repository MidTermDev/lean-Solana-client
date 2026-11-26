import Layout
import Export
import Net.Http

/-!
# http

An optional tile that answers HTTP on a socket the supervisor opened:

    GET /metrics      Prometheus text format
    GET /nodes.json   the full JSON document
    GET /             a short index

One connection at a time, one request per connection. It reads the shared
pages like the dashboard does; the gossip and verify tiles never know it
exists.
-/

def httpIndex : String :=
  "lean-solana-client\n\n  /metrics      Prometheus metrics\n  /nodes.json   every node seen in gossip, as JSON\n"

def httpTile (sh : Shared) (cfg : Config) : IO Unit := do
  repeat
    let conn ← Sys.accept sh.httpFd
    if Sys.isErr conn then
      IO.sleep 10
      continue
    -- never let one slow client hold the endpoint
    Sys.setTimeout conn 20 2000
    Sys.setTimeout conn 21 5000
    let path := Http.requestPath (← Sys.read conn 4096)
    let mut resp := Http.response "404 Not Found" "text/plain; charset=utf-8" "not found\n".toUTF8
    if Http.isPath path "/metrics" then
      resp := Http.response "200 OK" "text/plain; version=0.0.4; charset=utf-8" (← Export.prometheus sh cfg).toUTF8
    else if Http.isPath path "/nodes.json" then
      resp := Http.response "200 OK" "application/json" (← Export.json sh cfg).toUTF8
    else if Http.isPath path "/" then
      resp := Http.response "200 OK" "text/plain; charset=utf-8" httpIndex.toUTF8
    else if path.size == 0 then
      resp := Http.response "400 Bad Request" "text/plain; charset=utf-8" "only GET is supported\n".toUTF8
    let _ ← Sys.sendAll conn resp
    Sys.close conn
