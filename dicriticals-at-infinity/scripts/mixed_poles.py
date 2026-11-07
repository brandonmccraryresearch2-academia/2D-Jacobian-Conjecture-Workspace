#!/usr/bin/env python3
"""mixed_poles.py -- Two-branch bridge with UNEQUAL pole orders.

EPISTEMIC STATUS (2026-10-01): finite computation at explicit centers {2,5},
in the two-branch bridge chart. Not a general theorem.

Center a3=2 carries m=2 (ord_b >= 2d-2); center a4=5 carries m=3
(ord_b >= 2d-3). Joint linear system. Report nullity, J-vanishing.
If nontrivial with J not identically zero, extract:
  - b^{2d-2} coeff at a3: at-degree must be 2 for m=2 dicritical.
  - b^{2d-3} coeff at a4: at-degree must be 3 for m=3 dicritical.
If either at-degree < required m, that center's dicritical is impossible.
"""
import sympy as sp
import random

b, at, a, x, y = sp.symbols('b at a x y')
a3, a4 = 2, 5
m3, m4 = 2, 3  # pole orders at the two centers

print("=" * 70)
print("Mixed poles: m=2 at a=2, m=3 at a=5")
print("=" * 70)


def analyze(d):
    p = {(J, K): sp.symbols(f'p{J}_{K}') for J in range(d + 1)
         for K in range(d + 1 - J)}
    varlist = list(p.values())

    def rows_for(av, m):
        need = 2 * d - m
        s = sum(c * (av + at * b) ** (d - J - K) * b ** (2 * d - 2 * J - K)
                for (J, K), c in p.items())
        s = sp.expand(s)
        rows = []
        for t in range(need):
            cbt = s.coeff(b, t)
            if cbt == 0:
                continue
            pa = sp.Poly(cbt, at)
            if pa is None:
                rows.append([sp.expand(cbt).coeff(v) for v in varlist])
            else:
                for cc in pa.all_coeffs():
                    rows.append([sp.expand(cc).coeff(v) for v in varlist])
        return rows

    rows = rows_for(a3, m3) + rows_for(a4, m4)
    M = sp.Matrix(rows)
    ns = M.nullspace()
    Pb = []
    for v in ns:
        mp = dict(zip(varlist, v))
        Pb.append(sp.expand(sum(mp[p[J, K]] * x ** J * y ** K
                                for (J, K) in p)))
    Jvan = True
    Jex = None
    for i in range(len(Pb)):
        for j in range(i + 1, len(Pb)):
            Jij = sp.expand(sp.diff(Pb[i], x) * sp.diff(Pb[j], y)
                            - sp.diff(Pb[i], y) * sp.diff(Pb[j], x))
            if Jij != 0:
                Jvan = False
                if Jex is None:
                    Jex = (Pb[i], Pb[j], Jij)
                break
        if not Jvan:
            break
    random.seed(7)
    Pg = sp.expand(sum(random.randint(1, 9) * q for q in Pb))
    supp = set()
    poly = sp.Poly(Pg, x, y)
    if poly is not None:
        for mon, cf in poly.as_dict().items():
            if cf != 0:
                supp.add(mon)
    return {'d': d, 'nvars': len(varlist), 'rank': M.rank(),
            'nullity': len(ns), 'Jvanishes': Jvan, 'Jexample': Jex,
            'support': sorted(supp), 'Pbasis': Pb}


print("\n--- Linear joint vanishing ---")
res = {}
for d in range(2, 8):
    r = analyze(d)
    res[d] = r
    print(f"  d={d}: nvars={r['nvars']} rank={r['rank']} "
          f"nullity={r['nullity']} J_identically_0={r['Jvanishes']}")
    if r['nullity'] > 0:
        print(f"       support: {r['support']}")
        if not r['Jvanishes'] and r['Jexample'] is not None:
            Pi, Pj, Jij = r['Jexample']
            print(f"       J({Pi},{Pj})={Jij}")

d0 = min((d for d in res if res[d]['nullity'] > 0), default=None)
print(f"\nLowest d with nontrivial joint span: {d0}")

print()
print("=" * 70)
print("Nonlinear: leading at-degrees at each center")
print("=" * 70)
if d0 is None:
    print("Empty linear span; stop.")
else:
    r = res[d0]
    if r['Jvanishes']:
        print("J vanishes identically; no Keller pair; stop.")
    else:
        n = r['nullity']
        cs = sp.symbols(f'c0:{n}')
        Pg = sum(cs[i] * r['Pbasis'][i] for i in range(n))
        poly = sp.Poly(sp.expand(Pg), x, y)
        Pdict = {(J, K): cf for (J, K), cf in poly.as_dict().items()}
        # center a3, m=2: b^{2d-2} coeff
        need3 = 2 * d0 - m3
        S3 = sum(c_ * (a + at * b) ** (d0 - J - K) * b ** (2 * d0 - 2 * J - K)
                 for (J, K), c_ in Pdict.items())
        lead3 = sp.expand(sp.expand(S3).coeff(b, need3))
        p3 = sp.Poly(lead3, at)
        deg3 = p3.degree() if p3 is not None else 0
        print(f"center a3 (m=2): b^{need3} coeff = {lead3}")
        print(f"  at-degree = {deg3} (need 2). "
              f"{'OK' if deg3 == 2 else 'FAIL: deg != 2'}")
        # center a4, m=3: b^{2d-3} coeff
        need4 = 2 * d0 - m4
        S4 = sum(c_ * (a + at * b) ** (d0 - J - K) * b ** (2 * d0 - 2 * J - K)
                 for (J, K), c_ in Pdict.items())
        lead4 = sp.expand(sp.expand(S4).coeff(b, need4))
        p4 = sp.Poly(lead4, at)
        deg4 = p4.degree() if p4 is not None else 0
        print(f"center a4 (m=3): b^{need4} coeff = {lead4}")
        print(f"  at-degree = {deg4} (need 3). "
              f"{'OK' if deg4 == 3 else 'FAIL: deg != 3'}")
        print()
        if deg3 != 2 or deg4 != 3:
            print("CONCLUSION: at least one center fails the degree test.")
            print("The mixed (m=2,m=3) bridge is INCONSISTENT at "
                  f"d={d0}.")
            print("Unequal poles do NOT evade the degree obstruction.")
        else:
            print("Both degree tests pass at the linear level; the mixed")
            print("candidate survives this test.")
