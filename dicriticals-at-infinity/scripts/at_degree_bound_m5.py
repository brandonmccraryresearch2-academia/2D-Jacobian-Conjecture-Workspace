#!/usr/bin/env python3
"""at_degree_bound.py -- Structural at-degree bound for the two-branch bridge.

EPISTEMIC STATUS (2026-10-01): finite computation at explicit centers {2,5},
for 1 <= m1 <= m2 <= 5 and d = m2..m2+3. Not a general theorem.

Claim under test: for P in the joint nullspace of
  ord_b(S) >= 2d-m1 at a3=2, ord_b(S) >= 2d-m2 at a4=5,
the b^{2d-m1} coefficient at a3 (as a polynomial in at, with a symbolic)
has at-degree < m1, and similarly the b^{2d-m2} coefficient at a4 has
at-degree < m2. If true, no (m1,m2) bridge can be dicritical.
"""
import sympy as sp

b, at, a, x, y = sp.symbols('b at a x y')
print("=" * 70)
print("Structural at-degree bound: all (m1,m2), 1<=m1<=m2<=5")
print("=" * 70)


def max_at_degree(d, m1, m2):
    """Return (deg1, deg2, nullity) where deg1 = at-degree of b^{2d-m1}
    coeff at center a3 (generic P in nullspace), deg2 likewise at a4.
    deg = -1 means identically zero (exact order unattainable)."""
    p = {(J, K): sp.symbols(f'p{J}_{K}') for J in range(d + 1)
         for K in range(d + 1 - J)}
    varlist = list(p.values())

    def rows_for(av, m):
        need = 2 * d - m
        if need < 0:
            return []
        s = sum(c * (av + at * b) ** (d - J - K) * b ** (2 * d - 2 * J - K)
                for (J, K), c in p.items())
        s = sp.expand(s)
        rows = []
        for t in range(need):
            cbt = s.coeff(b, t)
            if cbt == 0:
                continue
            pa = sp.Poly(cbt, at)
            if pa is None:
                rows.append([sp.expand(cbt).coeff(v) for v in varlist])
            else:
                for cc in pa.all_coeffs():
                    rows.append([sp.expand(cc).coeff(v) for v in varlist])
        return rows

    rows = rows_for(2, m1) + rows_for(5, m2)
    if not rows:
        return None, None, 0
    M = sp.Matrix(rows)
    ns = M.nullspace()
    n = len(ns)
    if n == 0:
        return None, None, 0
    Pb = []
    for v in ns:
        mp = dict(zip(varlist, v))
        Pb.append(sp.expand(sum(mp[p[J, K]] * x ** J * y ** K
                                for (J, K) in p)))
    cs = sp.symbols(f'c0:{n}')
    Pg = sum(cs[i] * Pb[i] for i in range(n))
    poly = sp.Poly(sp.expand(Pg), x, y)
    if poly is None:
        return None, None, n
    Pdict = {(J, K): cf for (J, K), cf in poly.as_dict().items()}

    def atdeg(need):
        S = sum(c_ * (a + at * b) ** (d - J - K) * b ** (2 * d - 2 * J - K)
                for (J, K), c_ in Pdict.items())
        lead = sp.expand(sp.expand(S).coeff(b, need))
        if lead == 0:
            return -1
        pa = sp.Poly(lead, at)
        return pa.degree() if pa is not None else 0

    return atdeg(2 * d - m1), atdeg(2 * d - m2), n


print(f"{'(m1,m2)':>10} {'d':>3} {'null':>5} {'deg@a3':>7} {'<m1?':>6} "
      f"{'deg@a4':>7} {'<m2?':>6}")
all_hold = True
for m1 in range(1, 6):
    for m2 in range(m1, 6):
        for d in range(m2, m2 + 4):
            d1, d2, n = max_at_degree(d, m1, m2)
            if n == 0:
                print(f"{(m1,m2)!s:>10} {d:>3} {'0':>5} "
                      f"{'--':>7} {'--':>6} {'--':>7} {'--':>6}  (empty)")
                continue
            ok1 = (d1 is not None and d1 < m1)
            ok2 = (d2 is not None and d2 < m2)
            if not (ok1 and ok2):
                all_hold = False
            flag = "" if (ok1 and ok2) else "  <-- VIOLATION"
            print(f"{(m1,m2)!s:>10} {d:>3} {n:>5} "
                  f"{str(d1):>7} {str(ok1):>6} {str(d2):>7} {str(ok2):>6}"
                  f"{flag}")

print()
print("=" * 70)
if all_hold:
    print("RESULT: at-degree < m holds at BOTH centers for every tested")
    print("(m1,m2,d). The degree obstruction is STRUCTURAL in this range:")
    print("no two-branch bridge can carry a dicritical pair, for any")
    print("1<=m1<=m2<=5, at any d in [m2, m2+3].")
else:
    print("RESULT: VIOLATION found. Some (m1,m2,d) has at-degree >= m at")
    print("a center. That pair becomes the next candidate.")
print("=" * 70)
