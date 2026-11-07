"""The order condition on E1, the two monomial sets, the counterexample to Theorem thm:e1, and the corrected step.

Conventions (paper section 3.1 and e1_solitary.py): the affine plane is {Z != 0}, x = X/Z, y = Y/Z, and
S^h(X, Y, Z) = Z^d S(X/Z, Y/Z). E1 is the blow-up of [1:0:0]; e1_solitary.py uses the chart s = Y/X = y/x,
t = Z/X = 1/x, then s = s1, t = s1*t1 with E1 = {s1 = 0}, and the normalized section S^h(1, s1, s1*t1) / s1^d, whose
s1^(-2) coefficient is the pencil restriction C(t1). Its unknowns p[J,K] multiply X^(d-J-K) Y^J Z^K, that is, the
affine monomial x^(d-J-K) y^J.

Checks (each prints PASS or FAIL; exit 1 on any FAIL):
  1. nu_E1(x^i y^j) = -i, so nu_E1 >= -2 means x-degree <= 2;
  2. e1_solitary.py's condition (i) in affine terms is that set; read as x^J y^K (e1_keller_search.py, noLowTerms in
     E1Obstruction.lean) it is "total degree >= 2"; both have 12 elements at d = 4 and they differ;
  3. P = (x + y^2)^2 + y, Q = P + x + y^2: degree 4, nu_E1 = -2, C_P = C_Q = t1^2, all of e1_solitary.py's
     conditions hold, and [P, Q] = -1; P/Q is constant (1) on E1; P contains y;
  4. the x^(2n-1)-coefficient of [P, Q] is n (A D' - A' D) for x-degree <= n (n = 1..4, generic coefficients);
  5. on 40 random S, nu_E1(S) = -deg_x S and the restriction is t1^(d-n) A(1/t1) with A the x^n-coefficient;
  6. e1_global.py's pair (y^2, y^2 + xy), labelled in the chart coordinates, is (x^2, x^2 (1 + y)) in affine terms:
     C_P = t1^2, C_Q = t1^2 + t1, and P/Q restricts to t1/(t1 + 1), of degree 1, not 2.
"""
import random
import sys

import sympy as sp

x, y, s1, t1 = sp.symbols('x y s1 t1')
X, Y, Z = sp.symbols('X Y Z')
FAILS = []


def check(name, ok, detail=''):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f": {detail}" if detail else ''))
    if not ok:
        FAILS.append(name)


def jac(P, Q):
    return sp.expand(sp.diff(P, x) * sp.diff(Q, y) - sp.diff(P, y) * sp.diff(Q, x))


def homog(S, d):
    return sp.expand(Z ** d * S.subs({x: X / Z, y: Y / Z}, simultaneous=True))


def lowest_order(expr, var):
    num, den = sp.fraction(sp.together(sp.expand(expr)))
    return min(m[0] for m in sp.Poly(sp.expand(num), var).monoms()) - min(m[0] for m in sp.Poly(sp.expand(den), var).monoms())


def nu_E1(S):
    return lowest_order(S.subs({x: 1 / (s1 * t1), y: 1 / t1}, simultaneous=True), s1)


def e1_section(S, d):
    return sp.expand(homog(S, d).subs({X: 1, Y: s1, Z: s1 * t1}, simultaneous=True) / s1 ** d)


def C_of(S, d):
    return sp.expand(sp.expand(e1_section(S, d) * s1 ** 2).subs(s1, 0))


print('1. The order condition')
nus = {(i, j): nu_E1(x ** i * y ** j) for i in range(5) for j in range(5)}
check('nu_E1(x^i y^j) = -i for 0 <= i, j <= 4', all(v == -i for (i, j), v in nus.items()))

print('2. The two monomial sets at d = 4')
d = 4
monos = [(i, j) for i in range(d + 1) for j in range(d + 1) if i + j <= d]
true_set = {m for m in monos if nus[m] >= -2}
idx = [(J, K) for J in range(d + 1) for K in range(d + 1 - J)]
kept = [(J, K) for (J, K) in idx if J + K >= d - 2]
as_affine = {(d - J - K, J) for (J, K) in kept}
as_read = set(kept)
check("e1_solitary.py's condition (i), in affine terms, is x-degree <= 2", as_affine == true_set,
      f'{sorted(true_set)}')
check('read as x^J y^K it is total degree >= 2', as_read == {m for m in monos if sum(m) >= 2}, f'{sorted(as_read)}')
check('both sets have 12 elements', len(true_set) == 12 and len(as_read) == 12)
check('the sets differ', true_set != as_read,
      f'only in the true set: {sorted(true_set - as_read)}; only in the other: {sorted(as_read - true_set)}')

print('3. The counterexample')
P = sp.expand((x + y ** 2) ** 2 + y)
Q = sp.expand(P + x + y ** 2)
print(f'  P = {P}')
print(f'  Q = {Q}')
check('[P, Q] = -1', jac(P, Q) == -1)
check('deg P = deg Q = 4', sp.Poly(P, x, y).total_degree() == 4 and sp.Poly(Q, x, y).total_degree() == 4)
check('nu_E1(P) = nu_E1(Q) = -2', nu_E1(P) == -2 and nu_E1(Q) == -2)
CP, CQ = C_of(P, 4), C_of(Q, 4)
check('C_P = C_Q = t1^2: each of exact degree 2', CP == t1 ** 2 and CQ == t1 ** 2, f'C_P = {CP}, C_Q = {CQ}')
for name, S in (('P', P), ('Q', Q)):
    pS = sp.Poly(S, x, y)
    pJK = {(J, K): pS.coeff_monomial(x ** (d - J - K) * y ** J) for (J, K) in idx}
    ok = (all(pJK[(J, K)] == 0 for (J, K) in idx if J + K < d - 2)
          and all(pJK[(J, K)] == 0 for (J, K) in idx if J + K == d - 2 and K > 2) and pJK[(d - 4, 2)] != 0)
    check(f"{name} satisfies e1_solitary.py's conditions (i), (ii) and its open condition p[d-4,2] != 0", ok)
check('P/Q restricted to E1 is constant: C_P/C_Q = 1, so E1 is not dicritical for this pair', sp.simplify(CP / CQ) == 1)
check('P contains y (total degree 1), so it violates noLowTerms', (0, 1) in sp.Poly(P, x, y).monoms())

print('4. The top x-coefficient of the Jacobian')
ok = True
for n in range(1, 5):
    A = [sp.Function(f'A{i}')(y) for i in range(n + 1)]
    D = [sp.Function(f'D{i}')(y) for i in range(n + 1)]
    Pg = sum(A[i] * x ** i for i in range(n + 1))
    Qg = sum(D[i] * x ** i for i in range(n + 1))
    J = sp.expand(sp.diff(Pg, x) * sp.diff(Qg, y) - sp.diff(Pg, y) * sp.diff(Qg, x))
    top = sp.expand(J.coeff(x, 2 * n - 1) - n * (A[n] * sp.diff(D[n], y) - sp.diff(A[n], y) * D[n]))
    ok &= top == 0 and all(sp.expand(J.coeff(x, k)) == 0 for k in range(2 * n, 2 * n + 3))
check("x^(2n-1)-coefficient of [P, Q] = n (A D' - A' D), nothing above it, n = 1..4", ok)

print('5. The restriction to E1')
random.seed(20261013)
ok = True
for trial in range(40):
    n = random.randint(1, 3)
    dd = random.randint(n, 5)
    S = sum(random.randint(-3, 3) * x ** i * y ** j for i in range(n + 1) for j in range(dd - i + 1))
    A = sum(random.randint(1, 3) * y ** j for j in range(dd - n + 1))
    S = sp.expand(S - sp.Poly(S, x).coeff_monomial(x ** n) * x ** n + A * x ** n)
    lead = sp.expand(sp.expand(e1_section(S, dd) * s1 ** n).subs(s1, 0))
    ok &= nu_E1(S) == -n and sp.expand(lead - t1 ** (dd - n) * A.subs(y, 1 / t1)) == 0
check('nu_E1(S) = -deg_x S and the restriction is t1^(d-n) A(1/t1), 40 random S', ok)

print("6. e1_global.py's pair, in affine terms")
P6, Q6 = x ** 2, x ** 2 * (1 + y)
C6P, C6Q = C_of(P6, 4), C_of(Q6, 4)
r6 = sp.cancel(C6P / C6Q)
num6, den6 = sp.fraction(r6)
check('C_P = t1^2, C_Q = t1^2 + t1, and C_P/C_Q = t1/(t1 + 1) has degree 1',
      C6P == t1 ** 2 and sp.expand(C6Q - t1 ** 2 - t1) == 0
      and max(sp.degree(num6, t1), sp.degree(den6, t1)) == 1, f'{r6}')

print('RESULT:', 'PASS' if not FAILS else f'FAIL {FAILS}')
sys.exit(1 if FAILS else 0)
