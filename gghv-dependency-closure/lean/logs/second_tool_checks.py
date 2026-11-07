#!/usr/bin/env python3
"""Second-tool checks for Leg E (run on lean-build-3, NOT locally).
Pure Python (stdlib only) — no sympy dependency.
Checks:
  R11: ((z^7-a)^2 (z^7-b)) expands to z^21 -(2a+b)z^14 + (a^2+2ab)z^7 - a^2*b,
       with a,b symbolic (coeffs in Q[a,b]); also the m=1 coefficients and
       the degree-21m / factor-count arithmetic.
  R8:  the b'-case direction determinations by brute force over the integers,
       and the phi-argument impossibilities by exhaustive search.
  R16: the slot fractions (2/3)(24,9)=(16,6), (3/4)(28,8)=(21,6).
Exit 0 iff every check passes; prints one line per check.
"""
from fractions import Fraction as Q

# ---------- tiny polynomial arithmetic over Q[a,b], variable z ----------
# poly in z: dict exp -> dict (ia,ib) -> Fraction coeff
def padd(p, q):
    r = {e: dict(c) for e, c in p.items()}
    for e, c in q.items():
        r.setdefault(e, {})
        for k, v in c.items():
            r[e][k] = r[e].get(k, Q(0)) + v
            if r[e][k] == 0:
                del r[e][k]
        if not r[e]:
            del r[e]
    return r

def pmul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = e1 + e2
            r.setdefault(e, {})
            for (i1, j1), v1 in c1.items():
                for (i2, j2), v2 in c2.items():
                    k = (i1 + i2, j1 + j2)
                    r[e][k] = r[e].get(k, Q(0)) + v1 * v2
    return {e: c for e, c in r.items() if c}

def pscale(p, s):
    return {e: {k: v * s for k, v in c.items()} for e, c in p.items()}

def zpow(n):
    return {n: {(0, 0): Q(1)}}

def const_ab(ia, ib, s=1):
    return {0: {(ia, ib): Q(s)}}

z7 = zpow(7)
A = padd(z7, pscale(const_ab(1, 0), Q(-1)))   # z^7 - a
B = padd(z7, pscale(const_ab(0, 1), Q(-1)))   # z^7 - b
lhs = pmul(pmul(A, A), B)
# rhs = z^21 -(2a+b)z^14 + (a^2+2ab)z^7 - a^2*b, built term by term:
rhs = {}
for e, c in zpow(21).items():
    rhs[e] = dict(c)
for e, c in {14: {(1, 0): Q(-2), (0, 1): Q(-1)}}.items():
    rhs[e] = dict(c)
for e, c in {7: {(2, 0): Q(1), (1, 1): Q(2)}}.items():
    rhs[e] = dict(c)
for e, c in {0: {(2, 1): Q(-1)}}.items():
    rhs[e] = dict(c)
ok = True

def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    ok = ok and cond

check("R11 base identity ((z^7-a)^2 (z^7-b)) expansion", lhs == rhs)
check("R11 coeff z^21 = 1", lhs.get(21) == {(0, 0): Q(1)})
check("R11 coeff z^14 = -(2a+b)", lhs.get(14) == {(1, 0): Q(-2), (0, 1): Q(-1)})
check("R11 coeff z^7 = a^2+2ab", lhs.get(7) == {(2, 0): Q(1), (1, 1): Q(2)})
check("R11 coeff z^0 = -a^2 b", lhs.get(0) == {(2, 1): Q(-1)})
check("R11 factor count 7+7=14, 7*(2m)+7*m=21m (m=3)",
      7 + 7 == 14 and 7 * (2 * 3) + 7 * 3 == 21 * 3)

# ---------- R8: b' cases by brute force ----------
from math import gcd
def dir_of(a, b):
    g = gcd(a, b)
    return (-b // g, a // g)
sols = []
for bp in range(3):
    for ap in range(-4, 17):
        if 8 * bp - 3 * ap > 0 and 4 > 4 * bp - ap:
            if (ap, bp) == (1, 1):
                continue  # central(4) exclusion
            if bp == 0 and ap in (-2, -3):
                continue  # discards
            sols.append((ap, bp))
check("R8 b' cases: exactly {(5,2),(2,1),(-1,0)} survive",
      set(sols) == {(5, 2), (2, 1), (-1, 0)})
check("R8 dir in all surviving cases = (-1,3)",
      all(dir_of(8 - ap, 3 - bp) == (-1, 3) for ap, bp in sols))
check("R8 phi aligned: no (a'',b'') with 0<=b''<5, 3b''-a''<1, 2b''-a''>0",
      not any(3 * b - a < 1 and 2 * b - a > 0
              for b in range(5) for a in range(-10, 11)))
check("R8 phi nonaligned: no k>=1 with k+1<2",
      not any(k + 1 < 2 for k in range(1, 10)))
check("R8 v(-1,3)(8,3)=1", -1 * 8 + 3 * 3 == 1)
check("R8 lform term val: -(-m+3j)+3j=m for m=5,j=0..15",
      all(-(-5 + 3 * j) + 3 * j == 5 for j in range(16)))

# ---------- R16 slot fractions ----------
check("R16 (2/3)(24,9)=(16,6)",
      Q(2, 3) * 24 == 16 and Q(2, 3) * 9 == 6)
check("R16 (3/4)(28,8)=(21,6)",
      Q(3, 4) * 28 == 21 and Q(3, 4) * 8 == 6)
check("R16 slot orderings 9<24, 8<28, 27>9, 21>7",
      9 < 24 and 8 < 28 and 27 > 9 and 21 > 7)

# ---------- R15 / R17 arithmetic ----------
check("R15 GGHV uses (2,3),(3,2) have m,n>1", 1 < 2 and 1 < 3)
check("R15 mb>1, nb>1 at (m,n,b)=(2,3,21)", 1 < 2 * 21 and 1 < 3 * 21)
check("R17 descent: d(j)=d0-j hits <0 at j=d0+1 (d0=5)",
      5 - 6 < 0)
check("R17 counting: (t+1)^2 > d*t+1 for t>=d, t>=1 (d=4,t=4..20)",
      all((t + 1) ** 2 > 4 * t + 1 for t in range(4, 21)))

print("ALL PASS" if ok else "SOME FAILED")
raise SystemExit(0 if ok else 1)
