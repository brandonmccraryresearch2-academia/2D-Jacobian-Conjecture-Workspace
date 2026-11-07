# Second-tool check (Python/Fractions) of the §4 square-root recursion:
# given q 0..5 and u0 = 1, build u by the recursion
#   u (n+1) = (1/(2*u0)) * (q (n+1) - sum_{j=0}^{n-1} u (j+1) * u (n-j))
# and verify (u*u)_n = q n for n <= 5 (the convolution identity that
# `powser_sq` / `exists_sqrt_series` prove in Lean).
from fractions import Fraction as Q

q = [Q(1), Q(2), Q(3), Q(5), Q(7), Q(11)]
u = [Q(1)]  # u 0 = u0
inv2 = Q(1, 2)
for n in range(5):
    s = sum(u[j + 1] * u[n - j] for j in range(n))
    u.append(inv2 * (q[n + 1] - s))
print("u =", u)
ok = True
for n in range(6):
    conv = sum(u[i] * u[n - i] for i in range(n + 1))
    status = "OK " if conv == q[n] else "FAIL"
    if conv != q[n]:
        ok = False
    print(f"n={n}: (u*u)_n = {conv}, q_n = {q[n]}  {status}")
print("CONVOLUTION IDENTITY:", "PASS" if ok else "FAIL")
