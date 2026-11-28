# The figures tests/double.lean must print, from the processor's doubles; powers from 60-digit
# arithmetic, rounded once. (The C library's pow, which the chain's nodes use, differs from that in one
# of these 2,000 cases, by one unit in the last place, where the true value is 0.4965 of a unit from
# one double and 0.5035 from the next. For the rate itself, the last line, it is the C library's.)
import struct, math
from decimal import Decimal, getcontext
getcontext().prec = 60
def power(x, y): return float((Decimal(y) * Decimal(x).ln()).exp())
M = (1 << 64) - 1
def draw(s):
    a = s ^ ((s << 13) & M)
    b = a ^ (a >> 7)
    return b ^ ((b << 17) & M)
def number(r, low, span): return ((low + (r >> 52) % span) << 52) | (r & 0xFFFFFFFFFFFFF)
def f(bits): return struct.unpack('<d', struct.pack('<Q', bits))[0]
def b(x): return struct.unpack('<Q', struct.pack('<d', x))[0]
s = 0x9E3779B97F4A7C15
sums = [0] * 7
for _ in range(2000):
    s = draw(s); x = number(s, 1003, 41)
    s = draw(s); y = number(s, 1003, 41)
    big, small = max(x, y), min(x, y)
    whole = f(number(s, 1020, 70))
    results = [b(f(x) * f(y)), b(f(x) / f(y)), b(f(x) + f(y)), b(f(big) - f(small)),
               b(float(s >> (x % 64))), min(int(whole), M),
               b(power(f(number(s, 1022, 1)), f(number(x, 1016, 12))))]
    sums = [(sums[k] * 31 + results[k]) & M for k in range(7)]
for name, v in zip(["mul", "div", "add", "sub", "ofU64", "toU64", "pow"], sums):
    print(f"{name}: {v}")
print("rate:", b(0.08 * math.pow(1.0 - 0.15, 5.022694543573436)))
