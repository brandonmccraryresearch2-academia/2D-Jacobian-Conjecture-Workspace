"""Leg G, Phase 4 — R22 second-tool cross-check (Python exact ints + flint).

Independent implementation of [GGV5] Algorithm GetmnFamilies and of the
family-to-row attribution, to be compared with
gghv_full_singular_ggv5_families_2026-11-06.sing (Singular 4.3.1).
Status: I1 only, never a proof / kernel verification.
"""
import sys
from math import gcd

ok = True

def check(name, got, want):
    global ok
    status = "PASS" if got == want else "FAIL"
    if got != want:
        ok = False
    print(f"[{status}] {name}: got {got!r}, want {want!r}")

def bezout_coeff(x, y):
    """Smallest positive N with (1 + N*y) % x == 0; return (M, N), M*x - N*y = 1."""
    for N in range(1, 5001):
        if (1 + N * y) % x == 0:
            M = (1 + N * y) // x
            if M > 0:
                return (M, N)
    return (0, 0)

def getmn_families(a, l, b):
    """Final corner (a/l, b) -> list of ((k,i),(m,n),(D1,D2))."""
    out = []
    bl = b * l - a
    kmax = -(-bl // b) - 1  # ceil(bl/b) - 1 == ceil(l - a/b) - 1
    for k in range(1, kmax + 1):
        e = gcd(k, bl)
        q = bl // e
        if gcd(b, q) == 1:
            M, N = bezout_coeff(b, q)
            n = N * k // e
            m = M - n
            D1 = (bl - b * k) // e
            D2 = b * k // e
            if m == 1 or n == 1:
                m, n = m + D1, n + D2
            kbar = k // e
            if kbar == 1:
                out.append(((k, 0), (m, n), (D1, D2)))
            else:
                for i in range(kbar):
                    mi, ni = m + i * D1, n + i * D2
                    if gcd(mi, ni) == 1:
                        out.append(((k, i), (mi, ni), (kbar * D1, kbar * D2)))
    return out

# Expected families from the [GGV5] §5 table (family -> ((k,i),(m0,n0),(D1,D2))).
expected = {
    "F1":  [((1, 0), (3, 4), (2, 3))],
    "F2":  [((1, 0), (2, 3), (1, 2))],
    "F3":  [((1, 0), (3, 2), (4, 3))],
    "F4":  [((2, 1), (3, 16), (2, 12))],
    "F9":  [((1, 0), (2, 3), (1, 2))],
    "F10": [((1, 0), (7, 4), (5, 3))],
    "F11": [((2, 0), (2, 5), (1, 3))],
    "F17": [((1, 0), (2, 3), (5, 8))],
    "F22": [((1, 0), (2, 3), (1, 2))],
}
corners = {
    "F1": (7, 4, 3), "F2": (7, 5, 2), "F3": (8, 5, 3), "F4": (8, 5, 3),
    "F9": (11, 7, 2), "F10": (13, 7, 3), "F11": (13, 7, 3),
    "F17": (11, 3, 8), "F22": (5, 4, 2),
}
for fam, (a, l, b) in corners.items():
    got = getmn_families(a, l, b)
    print(f"{fam} corner ({a}/{l},{b}) -> {got}")
    for want in expected[fam]:
        check(f"{fam} contains {want}", want in got, True)
check("F3/F4 corner yields exactly 2 families",
      len(getmn_families(8, 5, 3)), 2)
check("F10/F11 corner yields exactly 2 families",
      len(getmn_families(13, 7, 3)), 2)
check("F1 corner yields exactly 1 family", len(getmn_families(7, 4, 3)), 1)

# Family-to-row attribution: (row, family, j, A0, stated (m,n), stated max).
rows = [
    (1, "F1", 0, (4, 12), (3, 4), 64),
    (2, "F1", 1, (4, 12), (5, 7), 112),
    (3, "F2", 0, (5, 20), (2, 3), 75),
    (4, "F3", 0, (5, 20), (3, 2), 75),
    (5, "F9", 0, (7, 21), (2, 3), 84),
    (6, "F22", 0, (8, 24), (2, 3), 96),
    (9, "F17", 0, (9, 24), (2, 3), 99),
]
base = {"F1": (3, 4, 2, 3), "F2": (2, 3, 1, 2), "F3": (3, 2, 4, 3),
        "F9": (2, 3, 1, 2), "F22": (2, 3, 1, 2), "F17": (2, 3, 5, 8)}
for row, fam, j, (a0, b0), (m, n), mx in rows:
    m0, n0, D1, D2 = base[fam]
    check(f"row {row} ({fam}, j={j}) (m,n)",
          (m0 + j * D1, n0 + j * D2), (m, n))
    check(f"row {row} gcd(m,n) == 1", gcd(m, n), 1)
    check(f"row {row} max degree", max(m, n) * (a0 + b0), mx)

# §6 chain-table rows (arithmetic only).
for row, (a0, b0), (m, n), mx in [
        (7, (8, 28), (3, 2), 108), (8, (8, 32), (3, 2), 120),
        (10, (9, 27), (2, 3), 108)]:
    check(f"row {row} max degree", max(m, n) * (a0 + b0), mx)
    check(f"row {row} gcd(m,n) == 1", gcd(m, n), 1)

# Second tool within Python: python-flint fmpz spot checks.
from flint import fmpz
f = lambda n: fmpz(n)
check("flint: gcd(3,16)", int(f(3).gcd(f(16))), 1)
check("flint: F4 j=1 (m,n)=(5,28) gcd", int(f(5).gcd(f(28))), 1)
check("flint: F11 step gcd", int(f(2 + 1).gcd(f(5 + 3))), 1)
check("flint: 3*(8+28)", int(f(3) * f(36)), 108)
check("flint: 3*(9+27)", int(f(3) * f(36)), 108)

print("OVERALL:", "ALL PASS" if ok else "FAILURES PRESENT")
sys.exit(0 if ok else 1)
