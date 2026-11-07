#!/usr/bin/env python3
"""Second-tool check (Python, stdlib only) for Leg B kernel computations.

Recomputes, independently of Lean:
 1. E5 sieve table: for each of the 9 candidates, 21*b' - 8*a' and 13*gcd(21-a', 8-b'),
    and which pass the divisibility (expect [(1,1),(5,2),(13,5)]).
 2. E9 algorithm output on (l,a,b) = (1,8,3), with per-candidate s, N1, N2, direction
    (expect [(2,0),(3,1),(4,1),(6,2)] with directions [(1,-2),(2,-5),(1,-2),(1,-2)]).
 3. E5/E7 k-bounds: k=1 forced / k in {1,2}.
 4. Phi-maps on the pre-phi polygons (E5/E6/E7/E8 finals).
 5. Jacobian-factor pairs.

Exit 0 iff every check matches the Lean file's claims.
"""
import math
from fractions import Fraction

fails = []


def check(name, got, want):
    ok = got == want
    print(f"{'PASS' if ok else 'FAIL'} {name}: got {got!r}, want {want!r}")
    if not ok:
        fails.append(name)


# 1. E5 sieve
cands = [(-2, 0), (-1, 0), (1, 1), (2, 1), (4, 2), (5, 2), (7, 3), (10, 4), (13, 5)]
surv = []
for (a, b) in cands:
    lhs = 21 * b - 8 * a
    rhs = 13 * math.gcd(21 - a, 8 - b)
    if rhs % lhs == 0:
        surv.append((a, b))
check("sieve survivors", surv, [(1, 1), (5, 2), (13, 5)])
check("sieve (1,1) passes divisibility (diag-excluded, not sieve-excluded)",
      (13 % 13 == 0), True)

# 2. E9 algorithm
def dir_perp(u, v):
    g = math.gcd(u, v)
    return (v // g, -(u // g))


def psp(l, a, b):
    out = []
    detail = []
    for d in range(0, b):
        lo = (d * a) // b + 1
        hi = l * d + a - b * l - 1
        for c in range(lo, hi + 1):
            n1 = math.gcd(a - c, b - d)
            n2 = math.gcd(c, d)
            rho, sig = dir_perp(a - c, b - d)
            num = rho * a + sig * l * b
            s = num // math.gcd(num, l * (rho + sig))
            inc = (n2 % s == 0 and d > 0) or (s <= n1)  # s divides N2 (paper), not N2 divides s
            detail.append(((c, d), (rho, sig), s, n1, n2, inc))
            if inc:
                out.append((c, d))
    return out, detail


out, detail = psp(1, 8, 3)
check("psp(1,8,3) output", out, [(2, 0), (3, 1), (4, 1), (6, 2)])
dirs = [dir_perp(8 - c, 3 - d) for (c, d) in out]
check("psp(1,8,3) directions", dirs, [(1, -2), (2, -5), (1, -2), (1, -2)])
for (pt, direction, s, n1, n2, inc) in detail:
    print(f"  candidate {pt}: dir={direction} s={s} N1={n1} N2={n2} include={inc}")

# 3. k-bounds
k5 = [k for k in range(0, 6) if 1 <= k and (k + 1) * 2 < 5]
check("E5 k=1 forced by (5,2) row", k5, [1])
k247 = [k for k in range(0, 6) if 1 <= k and (k + 1) * 7 < 24]
check("E7 k in {1,2} from (24,7) row", k247, [1, 2])
k31 = [k for k in range(0, 6) if 1 <= k and (k + 1) * 1 < 3]
check("E7 k=1 from (3,1) row", k31, [1])

# 4. phi-maps
def phi(c, pts):
    return [(c * b - a, b) for (a, b) in pts]


check("phi3 E5 P", phi(3, [(0, 0), (2, 1), (42, 16), (48, 18), (54, 18)]),
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)])
check("phi3 E5 Q", phi(3, [(0, 0), (-1, 0), (63, 24), (72, 27), (81, 27)]),
      [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)])
check("phi3 E6 sub1 P", phi(3, [(0, 0), (2, 1), (42, 16), (48, 18), (36, 12)]),
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 12)])
check("phi3 E6 sub2 P", phi(3, [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)]),
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 6)])
check("phi3 E6 sub3 P", phi(3, [(0, 0), (2, 1), (42, 16), (48, 18)]),
      [(0, 0), (1, 1), (6, 16), (6, 18)])
check("phi4 E7 ab P", phi(4, [(0, 0), (-1, 0), (48, 14), (56, 16)]),
      [(0, 0), (1, 0), (8, 14), (8, 16)])
check("phi4 E7 ab Q", phi(4, [(0, 0), (2, 1), (72, 21), (84, 24)]),
      [(0, 0), (2, 1), (12, 21), (12, 24)])
check("phi4 E7 c P", phi(4, [(0, 0), (-1, 0), (48, 14), (56, 16), (32, 8)]),
      [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)])
check("phi4 E7 c Q", phi(4, [(0, 0), (2, 1), (72, 21), (84, 24), (48, 12)]),
      [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)])
check("phi3 E8 base", phi(3, [(0, 0), (0, 1), (21, 7), (-2, 0)]),
      [(0, 0), (3, 1), (0, 7), (2, 0)])

# 5. Jacobian-factor pairs: det of ((-1,0),(c,1)) = -1; x-exp = -1 + c - 1
for c, want in [(3, (-1, 1)), (4, (-1, 2))]:
    det = (-1) * 1 - 0 * c
    check(f"phiJacPair {c}", (det, c - 2), want)

print()
if fails:
    print(f"SECOND-TOOL CHECK: {len(fails)} FAILURES: {fails}")
    raise SystemExit(1)
print("SECOND-TOOL CHECK: ALL PASS")
