"""check_bridgeEq.py -- the definition `bridgeEq` of TwoDicritical/BridgeCollapse.lean against the paper's pullback.

For d = 2..6 it expands S_a(b) = sum_{J+K<=d} p_JK (a + at*b)^(d-J-K) b^(2d-2J-K) (paper, eq:bridge-pullback) with
sympy, and checks that the coefficient of at^i b^t equals bridgeEq(d, W = 2d - t + i, i, a, p) for every t <= 2d-2
and every i (with Lean's natural subtraction mirrored by max(e - i, 0); the binomial is 0 when i > e). It then
computes the rank of the full system at the centers 2 and 5: the nullity must be 2 (span{1, y}), as the Lean theorem
`bridge_collapse` and the paper's scripts say.
Usage: python3 check_bridgeEq.py   (exit status 0 iff every check passes)
"""
import sys
import sympy as sp
from math import comb
a, at, b = sp.symbols("a at b")
ok = True
for d in range(2, 7):
    P = {(J, K): sp.Symbol(f"p_{J}_{K}") for J in range(d + 1) for K in range(d + 1) if J + K <= d}
    S = sp.expand(sum(v * (a + at * b) ** (d - J - K) * b ** (2 * d - 2 * J - K) for (J, K), v in P.items()))
    poly = sp.Poly(S, at, b)
    for t in range(0, 2 * d - 1):
        for i in range(0, 2 * d + 1):
            W = 2 * d - t + i
            lhs = poly.coeff_monomial(at**i * b**t)
            rhs = 0
            for J in range(max(0, W - d), W // 2 + 1):
                e = d + J - W
                key = (J, W - 2 * J)
                if key in P:
                    rhs += P[key] * comb(e, i) * a ** max(e - i, 0)
            if sp.expand(lhs - rhs) != 0:
                ok = False; print("MISMATCH", d, t, i, lhs, rhs)
    # the conditions t <= 2d-2 give exactly i <= W-2 (W = 2d - t + i)
print("bridgeEq matches the pullback coefficients for d = 2..6:", ok)
all_ok = ok
# nullity of the full system at random centers, d = 2..6 (expect 2: span{1, y})
for d in range(2, 7):
    P = [(J, K) for J in range(d + 1) for K in range(d + 1) if J + K <= d]
    rows = []
    for a0 in (sp.Rational(2), sp.Rational(5)):
        for W in range(2, 2 * d + 1):
            for i in range(0, W - 1):
                row = []
                for (J, K) in P:
                    if 2 * J + K == W:
                        e = d + J - W
                        row.append(comb(e, i) * a0 ** max(e - i, 0))
                    else:
                        row.append(0)
                rows.append(row)
    M = sp.Matrix(rows)
    r = M.rank()
    print(f"d={d}: variables {len(P)}, rank {r}, nullity {len(P) - r}")
    all_ok = all_ok and (len(P) - r == 2)
print("PASS" if all_ok else "FAIL")
sys.exit(0 if all_ok else 1)
