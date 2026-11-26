import Encoding.Json
import Net.Http
import Tally

/-! The pure helpers behind the JSON and metrics export. -/

def main : IO Unit := do
  IO.println (Json.quote "plain")
  IO.println (Json.quote "quote \" backslash \\ tab \t newline \n unicode λ")
  IO.println (Json.quote "")
  let get := "GET /metrics?x=1 HTTP/1.1\r\nHost: localhost\r\n\r\n".toUTF8
  IO.println s!"{Http.isPath (Http.requestPath get) "/metrics"} {(Http.requestPath get).size}"
  IO.println s!"{(Http.requestPath "POST /metrics HTTP/1.1\r\n".toUTF8).size} {(Http.requestPath "GET".toUTF8).size} {(Http.requestPath "GET /".toUTF8).size} {(Http.requestPath ByteArray.empty).size}"
  let resp := Http.response "200 OK" "text/plain" "hello".toUTF8
  IO.println s!"{resp.size} {String.fromUTF8! (resp.extract 0 15)}"
  let mut t := Tally.create 8
  for k in #[(5 : UInt64), 7, 5, 9, 7, 5, 11] do
    t := t.add k
  let mut line := ""
  for i in t.order do
    line := line ++ s!"{t.keys[i]!}x{t.counts[i]!} "
  IO.println line
  IO.println s!"braces: \{ and } survive, {1 + 1}"
