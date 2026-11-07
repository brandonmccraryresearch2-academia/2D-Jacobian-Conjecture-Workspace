"""restatement_checks.py -- the explicit examples of RESTATEMENT.md, executed (sympy).

Phi = (P - c1)/(Q - c2) is the rational function whose fibres are the members of the pencil Lambda_c. A divisor E,
reached by point blow-ups, is dicritical iff the residue of Phi on E is non-constant (review section 9.3).

  1. (x + y^3, y), c = 0: the base points of the pencil at infinity; over [1:0:0] the chain of five blow-ups along
     which the members stay together, through the satellite point E2 ∩ E1 at the third step; the residue of Phi on
     E1 .. E4 is constant and on E5 it is a function of degree 1. A non-constant residue on E5 certifies that every
     center of the chain was a base point. So the dicritical at infinity (unique by Corollary 2.2 of RESTATEMENT.md)
     has degree 1 and depth 5, over the satellite point a = infinity of E2.
  2. (x, x*y), c = (1, 1): not Keller ([P,Q] = x). Its pencil has two base points at infinity, [1:0:0] and [0:1:0],
     and a dicritical of degree 1 over each: two dicriticals at infinity. The second lies over the line u = 0 of
     non-proper values (F(eps, v/eps) = (eps, v)). So the Keller condition cannot be left out of a proof of Theorem R.
Each check prints PASS or FAIL; exit status 1 on any FAIL.
"""
import sys

import sympy as sp

x, y, X, Y, Z = sp.symbols('x y X Y Z')
s, t, w1, sg, ta, rh, ka, p_, q_, r_, s2 = sp.symbols('s t w1 sigma tau rho kappa p q r s2')
FAILS = []


def check(name, ok, detail=''):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f": {detail}" if detail else ''))
    if not ok:
        FAILS.append(name)


def jac(P, Q):
    return sp.expand(sp.diff(P, x) * sp.diff(Q, y) - sp.diff(P, y) * sp.diff(Q, x))


def residue(Phi, var):
    """Phi on {var = 0}: N(0)/D(0) for the reduced fraction N/D; oo if D(0) = 0 != N(0)."""
    num, den = sp.fraction(sp.cancel(sp.together(Phi)))
    n0, d0 = sp.expand(num.subs(var, 0)), sp.expand(den.subs(var, 0))
    if d0 == 0:
        assert n0 != 0
        return sp.oo
    return sp.simplify(n0 / d0)


def base_points_at_infinity(Pc, Qc, d):
    Ph = sp.expand(Z ** d * Pc.subs({x: X / Z, y: Y / Z}, simultaneous=True))
    Qh = sp.expand(Z ** d * Qc.subs({x: X / Z, y: Y / Z}, simultaneous=True))
    pts = set()
    for chart, other in (({X: 1}, Y), ({Y: 1}, X)):
        a, b = sp.expand(Ph.subs(chart).subs(Z, 0)), sp.expand(Qh.subs(chart).subs(Z, 0))
        g = sp.gcd(a, b) if (a != 0 and b != 0) else (a if b == 0 else b)
        if a == 0 and b == 0:
            raise ValueError('line at infinity in the base locus')
        for root in sp.roots(sp.Poly(g, other)).keys():
            pts.add(('[1:%s:0]' % root) if chart == {X: 1} else ('[%s:1:0]' % root))
    return sorted(pts)


print('1. (x + y^3, y), c = 0')
P, Q = x + y ** 3, y
check('[P, Q] = 1', jac(P, Q) == 1)
bp = base_points_at_infinity(P, Q, 3)
check('the only base point at infinity is [1:0:0]', bp == ['[1:0:0]'], f'{bp}')
# chart at [1:0:0]: s = y/x, t = 1/x, so x = 1/t, y = s/t
Phi = (P / Q).subs({x: 1 / t, y: s / t}, simultaneous=True)
steps = [
    ('E1: s = s, t = s*w1', {t: s * w1}, s, w1),
    ('E2: s = w1*sigma (the members met E1 at w1 = 0 = E1 ∩ L, a satellite point)', {s: w1 * sg}, w1, sg),
    ('E3: sigma = w1*tau (the members met E2 at sigma = 0 = E2 ∩ E1, a satellite point: a = infinity)', {sg: w1 * ta}, w1, ta),
    ('E4: tau = -1 + w1*rho (the members met E3 at tau = -1, a free point)', {ta: -1 + w1 * rh}, w1, rh),
    ('E5: rho = w1*kappa (the members met E4 at rho = 0, a free point)', {rh: w1 * ka}, w1, ka),
]
cur = Phi
res = []
for label, sub, var, coord in steps:
    cur = sp.cancel(sp.together(cur.subs(sub, simultaneous=True)))
    r = residue(cur, var)
    res.append(r)
    print(f'  {label}: residue of Phi = {r}')
check('the residue is constant on E1 .. E4', all(r == sp.oo or sp.diff(r, c) == 0
                                                for r, (_, _, _, c) in zip(res[:4], steps[:4])), f'{res[:4]}')
check('on E5 the residue is a function of degree 1 (E5 is the dicritical)',
      res[4] != sp.oo and sp.degree(sp.numer(sp.together(res[4])), ka) <= 1
      and sp.degree(sp.denom(sp.together(res[4])), ka) <= 1 and sp.diff(res[4], ka) != 0, f'{res[4]}')

print('2. (x, x*y), c = (1, 1)')
P, Q = x, x * y
check('[P, Q] = x: not a Keller map', jac(P, Q) == x)
eps, v = sp.symbols('eps v')
check('non-proper along u = 0: F(eps, v/eps) = (eps, v)',
      [sp.simplify(e) for e in (P.subs({x: eps, y: v / eps}), Q.subs({x: eps, y: v / eps}))] == [eps, v])
Pc, Qc = P - 1, Q - 1
bp = base_points_at_infinity(Pc, Qc, 2)
check('base points at infinity: [0:1:0] and [1:0:0]', bp == ['[0:1:0]', '[1:0:0]'], f'{bp}')
Phi = Pc / Qc
# over [1:0:0]: s = y/x, t = 1/x; one blow-up s = t*w
Phi1 = sp.cancel(sp.together(Phi.subs({x: 1 / t, y: s / t}, simultaneous=True).subs(s, t * w1)))
r1 = residue(Phi1, t)
check('over [1:0:0]: after one blow-up the residue is non-constant (degree 1)', sp.diff(r1, w1) != 0, f'{r1}')
# over [0:1:0]: p = x/y, q = 1/y; blow-ups p = q*r, then r = q*s2
Phi2 = Phi.subs({x: p_ / q_, y: 1 / q_}, simultaneous=True)
Phi2a = sp.cancel(sp.together(Phi2.subs(p_, q_ * r_)))
ra = residue(Phi2a, q_)
Phi2b = sp.cancel(sp.together(Phi2a.subs(r_, q_ * s2)))
rb = residue(Phi2b, q_)
check('over [0:1:0]: constant residue after one blow-up, degree 1 after the second',
      (ra == sp.oo or sp.diff(ra, r_) == 0) and sp.diff(rb, s2) != 0, f'{ra}, then {rb}')

print('RESULT:', 'PASS' if not FAILS else f'FAIL {FAILS}')
sys.exit(1 if FAILS else 0)
