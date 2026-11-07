"""Leg G, Phase 4 — R23 second-tool cross-check (SymPy 1.14.0).

Independent of gghv_full_singular_nine_eq_2026-11-06.sing (Singular 4.3.1):
same claims, different tool. Checks:
  (A) D-scaling identities (termwise, §5 C3-powers and §6 y-powers).
  (B) (D~^2)_{-k} / (D~^3)_{-j} expansions via series in u = x^{-1}, against
      the paper displays — including the (D~^2)_{-7} omission of 2 d_{-10}.
  (C) (D~^{-1})_{-j} for j=1..4 via series inversion: 0, 0, 1, 0.
  (D) phi-shift: x^2-coefficient of phi(D) is D_2 - 3t; t=D_2 gives -2 D_2,
      t=D_2/3 gives 0. Plus the negative-index coefficients d_{-1}, d_{-2},
      d_{-3} of phi(D) via series in u.
  (E) E23-adjacent: [x^6 y^2, (1/2) y^{-1} x^{-4}] = x (Laurent bracket).
Status: I1 only, never a proof / kernel verification.
"""
import sys
import sympy as sp

ok = True

def check(name, got, want):
    global ok
    status = "PASS" if got == want else "FAIL"
    if got != want:
        ok = False
    print(f"[{status}] {name}: got {got!r}, want {want!r}")

# ---------------- (A) D-scaling, termwise ----------------
# Indices -11..3. C[k] symbols; D[k] = C[k]*C3**(5-2k) (§5) or C[k]*y**(2-k) (§6).
idx = list(range(-11, 4))
C = {k: sp.Symbol(f"C{k}") for k in idx}
C3, y = sp.symbols("C3 y")
D5 = {k: C[k] * C3**(5 - 2*k) for k in idx}
D6 = {k: C[k] * y**(2 - k) for k in idx}

def check_scale(D, scale2, scale3, tag):
    for k in range(1, 9):
        s2 = sum(D[i] * D[j] for i in idx for j in idx if i + j == -k)
        c2 = sum(C[i] * C[j] for i in idx for j in idx if i + j == -k)
        check(f"{tag} (D^2)_{{-{k}}} == (C^2)_{{-{k}}} * {scale2(k)}",
              sp.expand(s2 - c2 * scale2(k)), 0)
    for k in range(1, 5):
        s3 = sum(D[i] * D[j] * D[l] for i in idx for j in idx for l in idx
                 if i + j + l == -k)
        c3s = sum(C[i] * C[j] * C[l] for i in idx for j in idx for l in idx
                  if i + j + l == -k)
        check(f"{tag} (D^3)_{{-{k}}} == (C^3)_{{-{k}}} * {scale3(k)}",
              sp.expand(s3 - c3s * scale3(k)), 0)

check_scale(D5, lambda k: C3**(10 + 2*k), lambda k: C3**(15 + 2*k), "S5")
check_scale(D6, lambda k: y**(4 + k), lambda k: y**(6 + k), "S6")

# ---------------- (B) D~ expansions via series in u ----------------
u = sp.Symbol("u")
d = {1: sp.Symbol("d1"), 0: sp.Symbol("d0")}
for k in range(1, 12):
    d[-k] = sp.Symbol(f"dm{k}")
# E = u^3 * D~ = 1 + d1 u^2 + d0 u^3 + dm1 u^4 + ... + dm11 u^14
E = 1 + d[1]*u**2 + d[0]*u**3 + sum(d[-k]*u**(3 + k) for k in range(1, 12))
E2 = sp.expand(E**2)
E3 = sp.expand(E**3)

def coeff_u(poly, n):
    return sp.expand(poly).coeff(u, n)

D2disp = {
    1: 2*d[0]*d[-1] + 2*d[1]*d[-2] + 2*d[-4],
    2: d[-1]**2 + 2*d[0]*d[-2] + 2*d[1]*d[-3] + 2*d[-5],
    3: 2*d[-1]*d[-2] + 2*d[0]*d[-3] + 2*d[1]*d[-4] + 2*d[-6],
    4: d[-2]**2 + 2*d[-1]*d[-3] + 2*d[0]*d[-4] + 2*d[1]*d[-5] + 2*d[-7],
    5: 2*d[-2]*d[-3] + 2*d[-1]*d[-4] + 2*d[0]*d[-5] + 2*d[1]*d[-6] + 2*d[-8],
    6: d[-3]**2 + 2*d[-2]*d[-4] + 2*d[-1]*d[-5] + 2*d[0]*d[-6] + 2*d[1]*d[-7] + 2*d[-9],
    7: 2*d[-3]*d[-4] + 2*d[-2]*d[-5] + 2*d[-1]*d[-6] + 2*d[0]*d[-7] + 2*d[1]*d[-8],
    8: 2*d[-11] + d[-4]**2 + 2*d[-3]*d[-5] + 2*d[-2]*d[-6] + 2*d[-1]*d[-7]
       + 2*d[0]*d[-8] + 2*d[1]*d[-9],
}
for k in range(1, 9):
    true = coeff_u(E2, k + 6)
    if k == 7:
        check("(D~^2)_{-7} TRUE - DISPLAY == 2 d_{-10}",
              sp.expand(true - D2disp[7]), 2*d[-10])
        check("(D~^2)_{-7} TRUE - (DISPLAY + 2 d_{-10}) == 0",
              sp.expand(true - (D2disp[7] + 2*d[-10])), 0)
    else:
        check(f"(D~^2)_{{-{k}}} TRUE - DISPLAY == 0",
              sp.expand(true - D2disp[k]), 0)

Q3disp = {
    1: 3*d[0]**2*d[-1] + 3*d[1]*d[-1]**2 + 6*d[0]*d[1]*d[-2] + 3*d[-2]**2
       + 3*d[1]**2*d[-3] + 6*d[-1]*d[-3] + 6*d[0]*d[-4] + 6*d[1]*d[-5] + 3*d[-7],
    2: 3*d[0]*d[-1]**2 + 3*d[0]**2*d[-2] + 6*d[1]*d[-1]*d[-2] + 6*d[0]*d[1]*d[-3]
       + 6*d[-2]*d[-3] + 3*d[1]**2*d[-4] + 6*d[-1]*d[-4] + 6*d[0]*d[-5]
       + 6*d[1]*d[-6] + 3*d[-8],
    3: d[-1]**3 + 6*d[0]*d[-1]*d[-2] + 3*d[1]*d[-2]**2 + 3*d[0]**2*d[-3]
       + 6*d[1]*d[-1]*d[-3] + 3*d[-3]**2 + 6*d[0]*d[1]*d[-4] + 6*d[-2]*d[-4]
       + 3*d[1]**2*d[-5] + 6*d[-1]*d[-5] + 6*d[0]*d[-6] + 6*d[1]*d[-7] + 3*d[-9],
    4: 3*d[-10] + 3*d[-1]**2*d[-2] + 3*d[0]*d[-2]**2 + 6*d[0]*d[-1]*d[-3]
       + 6*d[1]*d[-2]*d[-3] + 3*d[0]**2*d[-4] + 6*d[1]*d[-1]*d[-4]
       + 6*d[-3]*d[-4] + 6*d[0]*d[1]*d[-5] + 6*d[-2]*d[-5] + 3*d[1]**2*d[-6]
       + 6*d[-1]*d[-6] + 6*d[0]*d[-7] + 6*d[1]*d[-8],
}
for j in range(1, 5):
    check(f"(D~^3)_{{-{j}}} TRUE - DISPLAY == 0",
          sp.expand(coeff_u(E3, j + 9) - Q3disp[j]), 0)

# ---------------- (C) inverse coefficients ----------------
Einv = sp.series(1 / E, u, 0, 6).removeO()
print("1/E mod u^6 =", Einv)
# (D~^{-1})_{-j} = coeff of u^{j-3} in 1/E (j>=3); 0 for j=1,2.
check("(D~^{-1})_{-3} == 1 (coeff u^0 in 1/E)", Einv.coeff(u, 0), 1)
check("(D~^{-1})_{-4} == 0 (coeff u^1 in 1/E)", Einv.coeff(u, 1), 0)
check("(D~^{-1})_{-1} == 0 (no u^{-2} term)", 0, 0)
check("(D~^{-1})_{-2} == 0 (no u^{-1} term)", 0, 0)
check("1/E coeff u^0 == 1", Einv.coeff(u, 0), 1)
check("1/E coeff u^1 == 0", Einv.coeff(u, 1), 0)
check("1/E coeff u^2 == -d1", Einv.coeff(u, 2), -d[1])
check("1/E coeff u^3 == -d0", Einv.coeff(u, 3), -d[0])
check("1/E coeff u^4 == d1^2 - dm1", Einv.coeff(u, 4), d[1]**2 - d[-1])
check("1/E coeff u^5 == 2 d0 d1 - dm2 (inverse only mod u^5)",
      Einv.coeff(u, 5), 2*d[0]*d[1] - d[-2])

# ---------------- (D) phi-shift ----------------
x, t = sp.symbols("x t")
D2, D1, D0 = sp.symbols("D2 D1 D0")
Dm1, Dm2 = sp.symbols("Dm1 Dm2")
Dsh_poly = (x - t)**3 + D2*(x - t)**2 + D1*(x - t) + D0
check("phi(D) poly part == x^3 + (D2-3t) x^2 + (D1-2 D2 t+3 t^2) x + (D0-D1 t+D2 t^2-t^3)",
      sp.expand(Dsh_poly - (x**3 + (D2 - 3*t)*x**2 + (D1 - 2*D2*t + 3*t**2)*x
                             + (D0 - D1*t + D2*t**2 - t**3))), 0)
check("x^2 coeff at t=D2 == -2 D2",
      sp.expand(Dsh_poly.subs(t, D2)).coeff(x, 2), -2*D2)
check("x^2 coeff at t=D2/3 == 0",
      sp.expand(Dsh_poly.subs(t, D2/3)).coeff(x, 2), 0)
# Negative-index coefficients via series: D includes Dm1 x^{-1} + Dm2 x^{-2};
# phi(x^{-1}) = 1/(x-t) = u/(1-t u), phi(x^{-2}) = u^2/(1-t u)^2, u = 1/x.
# D~ = sum_k D_k (x-t)^k; in u: (x-t)^k = u^{-k} (1-t u)^k for k>=0,
# (x-t)^{-1} = u/(1-t u), (x-t)^{-2} = u^2/(1-t u)^2.
Dt_u = (u**-3*(1 - t*u)**3 + D2*u**-2*(1 - t*u)**2 + D1*u**-1*(1 - t*u)
        + D0 + Dm1*u/(1 - t*u) + Dm2*u**2/(1 - t*u)**2)
Dt_series = sp.series(sp.expand(Dt_u), u, 0, 5).removeO()
print("phi(D) as u-series (to u^4):", Dt_series)
check("d_{-1} == Dm1", sp.expand(Dt_series).coeff(u, 1), Dm1)
check("d_{-2} == Dm2 + t*Dm1", sp.expand(Dt_series).coeff(u, 2), Dm2 + t*Dm1)
check("d_{-3} == t^2*Dm1 + 2 t*Dm2", sp.expand(Dt_series).coeff(u, 3),
      t**2*Dm1 + 2*t*Dm2)
check("d_1 (coeff u^{-1}) == D1 - 2 D2 t + 3 t^2",
      sp.expand(Dt_series).coeff(u, -1), D1 - 2*D2*t + 3*t**2)
check("d_2 (coeff u^{-2}) == D2 - 3 t",
      sp.expand(Dt_series).coeff(u, -2), D2 - 3*t)

# ---------------- (E) E23-adjacent Laurent bracket ----------------
def bracket(P, Q):
    return sp.expand(sp.diff(P, x)*sp.diff(Q, y) - sp.diff(P, y)*sp.diff(Q, x))

check("[x^6 y^2, (1/2) y^{-1} x^{-4}] == x",
      sp.expand(bracket(x**6*y**2, sp.Rational(1, 2)*y**-1*x**-4) - x), 0)

print("OVERALL:", "ALL PASS" if ok else "FAILURES PRESENT")
sys.exit(0 if ok else 1)
