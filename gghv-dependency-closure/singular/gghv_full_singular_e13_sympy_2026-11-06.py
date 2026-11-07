"""Leg G, Phase 4 — E13 ODE second-tool cross-check (SymPy 1.14.0).

Independent of the Singular script gghv_full_singular_e13_ode_2026-11-06.sing:
same claims, different tool. Checks:
  (1) C3' = (9y+8) y^7;
  (2) f1 satisfies the ODE y^9 (y+1)^2 = 6y(y+1) f1' - 10(9y+8) f1 (both forms);
  (3) f = f1/C3 has deg 6, f = y(y+1) g(y), g(0)!=0, g(-1)!=0;
  (4) f separable: gcd(f, f') = 1; g has 4 distinct roots (discriminant != 0);
  (5) bracket identities of TeX 1568-1586;
  (6) ODE uniqueness among polynomials: dsolve general solution is
      f1 + C1 * y^(40/3) (y+1)^(5/3); the homogeneous part is not a polynomial
      unless C1 = 0, so the given f1 is the UNIQUE polynomial solution.
Status: I1 only, never a proof / kernel verification.
"""
import sys
import sympy as sp

y, x = sp.symbols('y x')
ok = True

def check(name, got, want):
    global ok
    status = "PASS" if got == want else "FAIL"
    if got != want:
        ok = False
    print(f"[{status}] {name}: got {got!r}, want {want!r}")

C3 = y**8 * (y + 1)
check("C3' == (9y+8) y^7", sp.expand(sp.diff(C3, y) - (9*y + 8)*y**7), 0)

f1 = sp.Rational(-1, 910) * y**9 * (y + 1)**2 * (35 - 42*y + 54*y**2 - 81*y**3 + 243*y**4)
f1p = sp.diff(f1, y)
check("ODE form 1 (TeX 1590)",
      sp.expand(y**9*(y + 1)**2 - (6*y*(y + 1)*f1p - 10*(9*y + 8)*f1)), 0)
check("ODE form 2 (TeX 1588)",
      sp.expand(y**16*(y + 1)**2 - (6*y**8*(y + 1)*f1p - 10*(9*y + 8)*y**7*f1)), 0)
check("deg f1", sp.Poly(f1, y).degree(), 15)
check("deg C3", sp.Poly(C3, y).degree(), 9)

f = sp.simplify(f1 / C3)
fpoly = sp.Poly(f, y)
check("f1 - C3*f", sp.expand(f1 - C3*f), 0)
check("deg f", fpoly.degree(), 6)
g = sp.Rational(-1, 910) * (35 - 42*y + 54*y**2 - 81*y**3 + 243*y**4)
check("f - y(y+1) g", sp.expand(f - y*(y + 1)*g), 0)
check("deg g", sp.Poly(g, y).degree(), 4)
check("g(0) != 0", g.subs(y, 0) != 0, True)
check("g(-1) != 0", g.subs(y, -1) != 0, True)
print("g(0) =", g.subs(y, 0), "; g(-1) =", g.subs(y, -1))

fp = sp.diff(f, y)
check("gcd(f, f') == 1 (f separable)", sp.gcd(sp.Poly(f, y), sp.Poly(fp, y)), sp.Poly(1, y))
gp = sp.diff(g, y)
check("gcd(g, g') == 1 (g 4 distinct roots)", sp.gcd(sp.Poly(g, y), sp.Poly(gp, y)), sp.Poly(1, y))
disc = sp.discriminant(sp.Poly(g, y), y)
print("discriminant(g) =", disc)
check("discriminant(g) != 0", disc != 0, True)
roots = sp.nroots(sp.Poly(g, y), n=30, maxsteps=200)
print("g roots (numeric):", [complex(r) for r in roots])
check("g has 4 pairwise-distinct roots",
      len({round(complex(r).real, 8) + 1j*round(complex(r).imag, 8) for r in roots}), 4)
froots = sp.nroots(fpoly, n=30, maxsteps=200)
print("f roots (numeric):", [complex(r) for r in froots])
check("f has 6 pairwise-distinct roots",
      len({round(complex(r).real, 8) + 1j*round(complex(r).imag, 8) for r in froots}), 6)

# Bracket identities (TeX 1568-1586), [P,Q] = P_x Q_y - P_y Q_x.
def bracket(P, Q):
    return sp.expand(sp.diff(P, x)*sp.diff(Q, y) - sp.diff(P, y)*sp.diff(Q, x))

br = bracket(x**3 * C3, x**5 * f1)
check("[x^3 C3, x^5 f1] == x^7 (6 C3 f1' - 10 C3' f1)",
      sp.expand(br - x**7*(6*C3*sp.diff(f1, y) - 10*sp.diff(C3, y)*f1)), 0)
br2 = bracket(x**6 * C3**2, 2*x**5 * f1)
check("[x^6 C3^2, 2 x^5 f1] == 2 x^10 C3^3 (ODE-dependent)",
      sp.expand(br2 - 2*x**10*C3**3), 0)
check("x^7 C3^2 == 2 [x^3 C3, x^5 f1] (ODE-dependent)",
      sp.expand(x**7*C3**2 - 2*br), 0)

# ODE uniqueness among polynomials via dsolve.
F = sp.Function('F')
ode = sp.Eq(6*y*(y + 1)*F(y).diff(y) - 10*(9*y + 8)*F(y), y**9*(y + 1)**2)
sol = sp.dsolve(ode, F(y))
print("dsolve general solution:", sol)
particular = sol.rhs.subs(sp.Symbol('C1'), 0)
check("dsolve particular (C1=0) == f1", sp.expand(particular - f1), 0)
homog = sp.simplify(sol.rhs - particular)
print("homogeneous part (C1 * ...):", homog)
check("homogeneous part is C1*y^(40/3)*(y+1)^(5/3) (non-polynomial unless C1=0)",
      sp.simplify(homog / (sp.Symbol('C1') * y**sp.Rational(40, 3) * (y + 1)**sp.Rational(5, 3))), 1)

print("OVERALL:", "ALL PASS" if ok else "FAILURES PRESENT")
sys.exit(0 if ok else 1)
