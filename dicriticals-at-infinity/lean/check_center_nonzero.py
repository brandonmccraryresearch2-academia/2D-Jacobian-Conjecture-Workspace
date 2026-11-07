"""Is the hypothesis "both centers nonzero" needed in the bridge collapse, read as a theorem about these equations?

Read geometrically (2026-10-13): at a = 0 these equations are not the m = 1 condition. The point a = 0 of E2 is a
satellite point (E2 meets the line at infinity), where the threshold 2d - 1 means nu >= -(d+1), not nu >= -1
(check_satellite.py). So a nonzero nullspace at a3 = 0 shows that the formal theorem needs a3 != 0; it is not a
geometric bridge with a center at 0.

Computed directly from the paper's pullback formula (eq:bridge-pullback), independently of `bridgeEq`:

    S_a(b) = sum_{J+K<=d} p_JK (a + at*b)^(d-J-K) * b^(2d-2J-K),

conditions: for each center a in {a3, a4}, every coefficient of at^i * b^t with t <= 2d-2 vanishes
(at is treated as an indeterminate, as in eq:block).

Reports the nullspace of the linear system in the p_JK and the Jacobian [P, y] of each basis element.
Controls: (a3, a4) = (2, 5) must give span{1, y} (the paper's theorem); (a3, a4) = (5, 5) (one center) must not.
"""
import sympy as sp

x, y, b, at = sp.symbols('x y b at')


def nullspace(d, a3, a4):
    idx = [(J, K) for J in range(d + 1) for K in range(d + 1) if J + K <= d]
    p = {jk: sp.Symbol(f'p{jk[0]}{jk[1]}') for jk in idx}
    eqs = []
    for a in (a3, a4):
        S = sum(p[(J, K)] * (a + at * b) ** (d - J - K) * b ** (2 * d - 2 * J - K) for (J, K) in idx)
        S = sp.Poly(sp.expand(S), b, at)
        for (t, i), c in S.terms():
            if t <= 2 * d - 2:
                eqs.append(c)
    unknowns = [p[jk] for jk in idx]
    A = sp.Matrix([[sp.diff(e, u) for u in unknowns] for e in eqs]) if eqs else sp.zeros(0, len(unknowns))
    ns = A.nullspace()
    basis = []
    for v in ns:
        P = sum(v[k] * x ** idx[k][0] * y ** idx[k][1] for k in range(len(idx)))
        basis.append(sp.factor(sp.expand(P)))
    return basis


def jac(P, Q):
    return sp.simplify(sp.diff(P, x) * sp.diff(Q, y) - sp.diff(P, y) * sp.diff(Q, x))


a4s = sp.Symbol('a4', nonzero=True)
cases = [((2, 5), 'control: distinct nonzero centers (paper)'),
         ((5, 5), 'control: one center only (a3 = a4)'),
         ((0, 5), 'attack: a3 = 0, a4 = 5'),
         ((0, a4s), 'attack: a3 = 0, a4 symbolic nonzero')]
for d in range(2, 7):
    for (a3, a4), label in cases:
        B = nullspace(d, a3, a4)
        jacs = sorted({str(jac(P, y)) for P in B})
        xdep = [P for P in B if sp.diff(P, x) != 0]
        print(f'd={d} {label}: nullity={len(B)} basis={B} x-dependent={xdep} [P,y] over basis={jacs}')
