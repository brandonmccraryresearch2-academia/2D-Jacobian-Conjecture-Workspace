"""Leg G phi-shift hypothesis check (tool-checked, SymPy).

Paper (GGHV v1, TeX line 1663): automorphism phi of K[y]((x^-1)) with
phi(y)=y, phi(x)=x-D_2. Line 1668 asserts the shifted D has d_2 = 0.
Leg G hand arithmetic (UNVERIFIED, to be tool-checked here): the x^2-coefficient
of phi(D) = D(x-t) is D_2 - 3*t, so t = D_2 gives d_2 = -2*D_2 (not 0),
while t = D_2/3 gives d_2 = 0.

D is monic of degree 3 in x (TeX line 1617: D_3 = 1, D_2 = C_2*C_3 = P_5/2),
so D = x^3 + D_2*x^2 + D_1*x + D_0 + (negative powers of x).
Negative powers cannot contribute to the x^2 coefficient: phi(x^-1) expands
only in negative powers of x (verified below against the paper's expansion).
"""
import sympy as sp

x, D2, D1, D0, t = sp.symbols('x D2 D1 D0 t')
D = x**3 + D2*x**2 + D1*x + D0

# (A) x^2-coefficient of D(x - t)
Dshift = sp.expand(D.subs(x, x - t))
c2 = sp.expand(Dshift).coeff(x, 2)
print("A: coeff of x^2 in D(x-t) =", c2)
print("A: equals D2 - 3*t ?", sp.simplify(c2 - (D2 - 3*t)) == 0)

# (B) evaluate at the paper's shift t = D_2, and at t = D_2/3
print("B: at t = D2   : d2 =", sp.simplify(c2.subs(t, D2)))
print("B: at t = D2/3 : d2 =", sp.simplify(c2.subs(t, D2/3)))

# (C) paper's phi(x^-1) expansion (line 1663): 1/(x-D2) = x^-1 + D2*x^-2 + D2^2*x^-3 + D2^3*x^-4 + ...
# Check by series expansion at infinity (4 terms) and by multiplying out.
s = sp.series(1/(x - D2), x, sp.oo, 5).removeO()
print("C: series of 1/(x-D2) at oo =", s)
print("C: matches paper expansion ?",
      sp.simplify(s - (1/x + D2/x**2 + D2**2/x**3 + D2**3/x**4)) == 0)
# multiply-out check: (x - D2) * (x^-1 + D2*x^-2 + D2^2*x^-3 + D2^3*x^-4) = 1 - D2^4*x^-4
prod = sp.expand((x - D2)*(1/x + D2/x**2 + D2**2/x**3 + D2**3/x**4))
print("C: (x-D2)*partial_sum =", prod, " (expect 1 - D2^4/x^4)")

# (D) full verdict
ok_A = sp.simplify(c2 - (D2 - 3*t)) == 0
ok_B1 = sp.simplify(c2.subs(t, D2) + 2*D2) == 0
ok_B2 = sp.simplify(c2.subs(t, D2/3)) == 0
ok_C = sp.simplify(s - (1/x + D2/x**2 + D2**2/x**3 + D2**3/x**4)) == 0
print("VERDICT: A(D2-3t)=%s  B(t=D2 -> -2D2)=%s  B(t=D2/3 -> 0)=%s  C(phi(x^-1))=%s"
      % (ok_A, ok_B1, ok_B2, ok_C))
print("ALL_PASS =", ok_A and ok_B1 and ok_B2 and ok_C)
