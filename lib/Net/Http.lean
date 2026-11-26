/-!
# Just enough HTTP to be scraped

A request is read once, only its request line is looked at, and every
response closes the connection. That is all a metrics endpoint needs.
-/

namespace Http

/-- The path of a `GET` request, without any query string, as raw bytes.
Empty when the request is not a well-formed `GET`. The bytes come from the
network, so they are never turned into a `String`. -/
def requestPath (req : ByteArray) : ByteArray := Id.run do
  if req.size < 5 || req[0]! != 71 || req[1]! != 69 || req[2]! != 84 || req[3]! != 32 then
    return ByteArray.empty
  let mut stop := 4
  while stop < req.size && req[stop]! != 32 && req[stop]! != 63 && req[stop]! != 13 && req[stop]! != 10 do
    stop := stop + 1
  return req.extract 4 stop

def isPath (path : ByteArray) (want : String) : Bool := path == want.toUTF8

/-- A complete response: status line, headers, body. `maxAge` (seconds)
lets a cache or CDN in front absorb repeated requests; the data is public,
so any origin may read it. -/
def response (status contentType : String) (maxAge : Nat) (body : ByteArray) : ByteArray :=
  (s!"HTTP/1.1 {status}\r\nContent-Type: {contentType}\r\nContent-Length: {body.size}\r\n" ++
    s!"Cache-Control: public, max-age={maxAge}, s-maxage={maxAge}\r\n" ++
    "Access-Control-Allow-Origin: *\r\nConnection: close\r\n\r\n").toUTF8 ++ body

end Http
