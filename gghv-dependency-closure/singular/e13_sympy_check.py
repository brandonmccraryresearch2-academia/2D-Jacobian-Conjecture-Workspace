"""E13 second-tool check (tool 1 of 2): SymPy 1.14.0.
Paper §5: f1 = -(1/910) y^9 (y+1)^2 (35 - 42y + 54y^2 - 81y^3 + 243y^4)
is the claimed solution of  y^9 (y+1)^2 = 6 y (y+1) f1' - 10 (9y+8) f1,
f := f1 / C3 with C3 = y^8 (y+1) is separable, y(y+1) | f, deg f = 6.
Also outputs Bezout coefficients u, v (polys over QQ) with u*f + v*f' = 1,
for the Lean separability proof.
"""
import sympy as sp

y = sp.symbols('y')
C3 = y**8 * (y + 1)
C3p = sp.diff(C3, y)
print("C3' =", sp.expand(C3p), " == (9y+8)y^7 ?", sp.expand(C3p - (9*y + 8)*y**7) == 0)

g_inner = 35 - 42*y + 54*y**2 - 81*y**3 + 243*y**4
f1 = sp.Rational(-1, 910) * y**9 * (y + 1)**2 * g_inner
f1 = sp.expand(f1)
print("deg f1 =", sp.Poly(f1, y).degree())

# ODE check, both forms
lhs = y**9 * (y + 1)**2
rhs = 6*y*(y + 1)*sp.diff(f1, y) - 10*(9*y + 8)*f1
print("ODE_DIFF =", sp.expand(lhs - rhs))
print("ODE_OK =", sp.expand(lhs - rhs) == 0)
lhs2 = y**16 * (y + 1)**2
rhs2 = 6*y**8*(y + 1)*sp.diff(f1, y) - 10*(9*y + 8)*y**7*f1
print("ODE_PREDIV_DIFF =", sp.expand(lhs2 - rhs2))

# f = f1 / C3
q, r = sp.div(sp.Poly(f1, y), sp.Poly(C3, y), domain='QQ')
print("DIV_REM =", r, " (must be 0)")
f = q.as_expr()
print("f =", sp.expand(f))
print("deg f =", sp.Poly(f, y).degree())
print("f / (y(y+1)) =", sp.expand(f / (y*(y + 1))))
g = sp.Rational(-1, 910) * g_inner
print("g(0) =", g.subs(y, 0), " g(-1) =", g.subs(y, -1))
print("f == y(y+1)g ?", sp.expand(f - y*(y + 1)*g) == 0)

fp = sp.diff(f, y)
print("gcd(f, f') =", sp.gcd(sp.Poly(f, y, domain='QQ'), sp.Poly(fp, y, domain='QQ')))
print("disc(f) nonzero ?", sp.discriminant(sp.Poly(f, y, domain='QQ')) != 0)
print("disc(f) =", sp.discriminant(sp.Poly(f, y, domain='QQ')))
print("factor f over QQ:", sp.factor(f, domain='QQ'))
print("roots of g (numeric, distinct?):", sorted([complex(z) for z in sp.nroots(g_inner)], key=lambda z: (z.real, z.imag)))
# Bezout for f and f'
s, t, d = sp.gcdex(sp.Poly(f, y, domain='QQ'), sp.Poly(fp, y, domain='QQ'))
print("BEZOUT_DEG =", d)
print("BEZOUT_U =", s.as_expr())
print("BEZOUT_V =", t.as_expr())
print("BEZOUT_CHECK =", sp.expand(s.as_expr()*f + t.as_expr()*fp))
print("ALL_PASS =", (sp.expand(lhs - rhs) == 0 and r == 0
                     and sp.Poly(f, y).degree() == 6
                     and sp.gcd(sp.Poly(f, y, domain='QQ'), sp.Poly(fp, y, domain='QQ')) == 1))
