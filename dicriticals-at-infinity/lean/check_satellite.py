"""The bridge pullback is a chart at a point of E2; what the conditions mean at a free point and at a = 0.

Conventions (paper section 3.1): x = X/Z, y = Y/Z, S^h(X, Y, Z) = Z^d S(X/Z, Y/Z). Over [1:0:0] take s = y/x, t = 1/x.
E1 is the blow-up of (s, t) = (0, 0); E2 the blow-up of E1 ∩ L (L the line at infinity), with coordinate
w2 = t/s^2 = x/y^2 on E2: w2 = 0 is the point E2 ∩ L, w2 = infinity is E2 ∩ E1 (both satellite points), every other
value is a free point. E(a) is the blow-up of the point w2 = a: s = b, w2 = a + at*b, i.e. t = b^2 (a + at*b), with
E(a) = {b = 0} and coordinate at.

Checks (each prints PASS or FAIL; exit 1 on any FAIL):
  1. eq:bridge-pullback equals S^h(1, b, b^2 (a + at*b)), and raising d multiplies it by b^2 (a + at*b) (d = 2..5);
  2. nu(x), nu(y) at a free point (-2, -1) and at a = 0 (-3, -2); ord_b S_a = 2d + nu_E(a)(S) at a free point and
     3d + nu_E(0)(S) at a = 0 (60 random S): the threshold 2d - 1 means nu >= -1 at a free point, nu >= -(d+1) at 0;
  3. the witness (x - a4 y^2, y): nu = -4 over a = 0, where P/Q has a pole (constant); P/Q = at/a4 on E(a4) (m = 1);
  4. with nu >= -1 at a = 0 (ord_b S_0 >= 3d - 1), the conditions at the centers (0, 5) leave span{1}, d = 2..6;
     one center 5 alone leaves span{1, y, x - 5y^2};
  5. nu_E(a)(S) = -(degree of S in x - a y^2, y) for a != 0: the exact image of (x - a y^2)^j y^k along E(a), and
     240 random S;
  6. (x + y^3, y): every member of its pencil passes through w2 = infinity, the satellite point E2 ∩ E1;
  7. a restriction of degree 1 does not force nu >= -1: for P = (x - a4 y^2) y + 1, Q = y^2 + 1, nu = -2 on E(a4)
     for both, and P/Q restricts to at/a4 there.
"""
import random
import sys

import sympy as sp

x, y, b, at, lam = sp.symbols('x y b at lam')
X, Y, Z = sp.symbols('X Y Z')
a = sp.Symbol('a')
a4 = sp.Symbol('a4', nonzero=True)
FAILS = []


def check(name, ok, detail=''):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f": {detail}" if detail else ''))
    if not ok:
        FAILS.append(name)


def homog(S, d):
    return sp.expand(Z ** d * S.subs({x: X / Z, y: Y / Z}, simultaneous=True))


def lowest_order(expr, var):
    num, den = sp.fraction(sp.together(sp.expand(expr)))
    return min(m[0] for m in sp.Poly(sp.expand(num), var).monoms()) - min(m[0] for m in sp.Poly(sp.expand(den), var).monoms())


def arc(S, aval):
    return S.subs({x: 1 / (b ** 2 * (aval + at * b)), y: 1 / (b * (aval + at * b))}, simultaneous=True)


def nu(S, aval):
    return lowest_order(arc(S, aval), b)


def lead(S, aval):
    return sp.cancel(sp.together(arc(S, aval) * b ** (-nu(S, aval)))).subs(b, 0)


def generic_S(d):
    cs = {(J, K): sp.Symbol(f'p{J}_{K}') for J in range(d + 1) for K in range(d + 1 - J)}
    return cs, sum(c * x ** J * y ** K for (J, K), c in cs.items())


def pullback(S, d, aval):
    return sp.expand(homog(S, d).subs({X: 1, Y: b, Z: b ** 2 * (aval + at * b)}, simultaneous=True))


print('1. The pullback formula is a chart')
ok = True
for d in range(2, 6):
    cs, S = generic_S(d)
    paper = sum(c * (a + at * b) ** (d - J - K) * b ** (2 * d - 2 * J - K) for (J, K), c in cs.items())
    ok &= sp.expand(paper - pullback(S, d, a)) == 0
    ok &= sp.expand(pullback(S, d + 1, a) - b ** 2 * (a + at * b) * pullback(S, d, a)) == 0
check('eq:bridge-pullback = S^h(1, b, b^2 (a + at b)); raising d multiplies it by b^2 (a + at b); d = 2..5', ok)

print('2. Valuations at a free point and at a = 0')
check('free point: nu(x) = -2, nu(y) = -1', nu(x, a4) == -2 and nu(y, a4) == -1)
check('a = 0: nu(x) = -3, nu(y) = -2', nu(x, 0) == -3 and nu(y, 0) == -2)
random.seed(7)
ok = True
for trial in range(60):
    d = random.randint(1, 5)
    S = sum(random.randint(-2, 2) * x ** J * y ** K for J in range(d + 1) for K in range(d + 1 - J))
    if S == 0:
        continue
    aval = sp.Rational(random.choice([-3, -1, 2, 5]), random.choice([1, 2, 3]))
    for av, shift in ((aval, 2 * d), (0, 3 * d)):
        ordb = min(m[0] for m in sp.Poly(pullback(S, d, av), b).monoms())
        ok &= ordb == shift + nu(S, av)
check('ord_b S_a = 2d + nu_E(a)(S) at a free point, 3d + nu_E(0)(S) at a = 0 (60 random S)', ok)

print('3. The witness (x - a4 y^2, y)')
W = x - a4 * y ** 2
check('nu(x - a4 y^2) = -4 over a = 0 (= -(d+1) at d = 3) and -1 over a = a4', nu(W, 0) == -4 and nu(W, a4) == -1)
check('over a = 0, nu(P/Q) = -2: P/Q is the constant infinity on E(0), not dicritical', nu(W, 0) - nu(y, 0) == -2)
r = sp.simplify(lead(W, a4) / lead(y, a4))
check('over a = a4, P/Q restricts to at/a4: E(a4) is its dicritical, of degree 1', sp.simplify(r - at / a4) == 0, f'{r}')


def nullspace(d, conds):
    cs, S = generic_S(d)
    unknowns = list(cs.values())
    eqs = []
    for aval, T in conds:
        Sa = sp.Poly(pullback(S, d, aval), b, at)
        eqs += [c for (t, i), c in Sa.terms() if t < T]
    A = sp.Matrix([[sp.diff(e, u) for u in unknowns] for e in eqs])
    return [sp.factor(sp.expand(sum(v[k] * sp.diff(S, unknowns[k]) for k in range(len(unknowns)))))
            for v in A.nullspace()]


print('4. The conditions at a = 0, read as nu >= -1')
for d in range(2, 7):
    right0 = nullspace(d, [(0, 3 * d - 1), (5, 2 * d - 1)])
    one = nullspace(d, [(5, 2 * d - 1)])
    check(f'd = {d}: centers (0, 5) with ord_b S_0 >= 3d - 1 leave span{{1}}', len(right0) == 1 and right0[0].is_number,
          f'{right0}')
    check(f'd = {d}: the center 5 alone leaves span{{1, y, x - 5y^2}}', len(one) == 3 and sp.Matrix(
        [[sp.Poly(Pb, x, y).coeff_monomial(m) for m in (1, y, x, y ** 2)] for Pb in one]).rank() == 3 and all(
        sp.Poly(Pb, x, y).coeff_monomial(y ** 2) == -5 * sp.Poly(Pb, x, y).coeff_monomial(x)
        and sp.Poly(Pb, x, y).total_degree() <= 2 for Pb in one), f'{one}')

print('5. The valuation over a free point')
ok = True
for j in range(5):
    for k in range(5):
        ok &= sp.simplify(arc((x - a4 * y ** 2) ** j * y ** k, a4)
                          - at ** j * b ** (-(j + k)) * (a4 + at * b) ** (-2 * j - k)) == 0
check('(x - a y^2)^j y^k = at^j b^-(j+k) (a + at b)^(-2j-k) along E(a), j, k <= 4', ok)
xp, yp = sp.symbols('xp yp')
random.seed(240)
ok = True
count = 0
while count < 240:
    d = random.randint(1, 5)
    S = sum(random.randint(-3, 3) * x ** J * y ** K for J in range(d + 1) for K in range(d + 1 - J))
    if S == 0:
        continue
    aval = sp.Rational(random.choice([-5, -3, -2, -1, 1, 2, 3, 7]), random.choice([1, 2, 3, 5]))
    Snew = sp.Poly(sp.expand(S.subs({x: xp + aval * yp ** 2, y: yp}, simultaneous=True)), xp, yp)
    ok &= nu(S, aval) == -Snew.total_degree()
    count += 1
check('nu_E(a)(S) = -(degree of S in x - a y^2, y) on 240 random S of degree <= 5, random a != 0', ok)

print('6. A dicritical over a satellite point')
check('(x + y^3, y): on every member x = lam y - y^3, w2 = x/y^2 -> -infinity as y -> infinity',
      sp.limit((lam * y - y ** 3) / y ** 2, y, sp.oo) == -sp.oo)

print('7. Degree 1 on E(a) with pole order 2')
P7, Q7 = (x - a4 * y ** 2) * y + 1, y ** 2 + 1
r7 = sp.simplify(lead(P7, a4) / lead(Q7, a4))
check('P = (x - a4 y^2) y + 1, Q = y^2 + 1: nu = -2 for both on E(a4), and P/Q restricts to at/a4 (degree 1)',
      nu(P7, a4) == -2 and nu(Q7, a4) == -2 and sp.simplify(r7 - at / a4) == 0, f'{r7}')

print('RESULT:', 'PASS' if not FAILS else f'FAIL {FAILS}')
sys.exit(1 if FAILS else 0)
