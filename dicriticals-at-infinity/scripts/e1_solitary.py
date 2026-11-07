#!/usr/bin/env python3
"""e1_solitary.py -- Solitary m=2 dicritical on FIRST exceptional E1.

EPISTEMIC STATUS (2026-10-01): finite computation in the explicit E1
chart U1, at d=4,5,6. Not a general theorem.

E1: blow up p1=[1:0:0]. Affine x=1: (s,t). Blow up (0,0).
Chart U1: s = s1, t = s1*t1. E1 = {s1=0}, transverse t1.

For P = sum p[J,K] X^{d-J-K} Y^J Z^K, affine: sum p[J,K] s^J t^K.
Pullback: sum p[J,K] s1^{J+K} t1^K.

Normalized section (divide by s1^d for O(0)):
  S(t1,s1) = sum p[J,K] s1^{J+K-d} t1^K.

s1-order: J+K-d. For nu = -2: need min(J+K-d) = -2, i.e., min(J+K)=d-2.

s1^{-2} coefficient:
  C(t1) = sum_{J+K=d-2} p[J,K] t1^K.
Degree in t1: max K with J+K=d-2, i.e., up to d-2.

For dicritical m=2: need deg C(t1) = 2 EXACTLY.

Linear conditions:
  (i)  nu >= -2: p[J,K] = 0 for J+K < d-2.
  (ii) deg <= 2: p[J,K] = 0 for J+K = d-2, K > 2.
Open: deg == 2 requires p[d-4,2] != 0 (coefficient of t1^2).

We compute the nullspace of (i)+(ii), test J, get support.
Lowest d: need d-2 >= 2 for t1^2 to exist, so d >= 4.
"""
import sympy as sp

t1, s1, x, y = sp.symbols('t1 s1 x y')
print("=" * 70)
print("Solitary m=2 dicritical on E1 (first exceptional)")
print("=" * 70)
print("\nChart U1: s=s1, t=s1*t1. E1={s1=0}, transverse t1.")
print("S(t1,s1) = sum p[J,K] s1^{J+K-d} t1^K.")
print("s1^{-2} coeff: C(t1) = sum_{J+K=d-2} p[J,K] t1^K.")
print()


def analyze(d):
    p = {(J, K): sp.symbols(f'p{J}_{K}') for J in range(d + 1)
         for K in range(d + 1 - J)}
    varlist = list(p.values())
    rows = []
    # (i) p[J,K]=0 for J+K < d-2
    for (J, K), v in p.items():
        if J + K < d - 2:
            row = [0] * len(varlist)
            row[varlist.index(v)] = 1
            rows.append(row)
    # (ii) p[J,K]=0 for J+K=d-2, K>2
    for (J, K), v in p.items():
        if J + K == d - 2 and K > 2:
            row = [0] * len(varlist)
            row[varlist.index(v)] = 1
            rows.append(row)
    M = sp.Matrix(rows)
    ns = M.nullspace()
    Pb = []
    for v in ns:
        mp = dict(zip(varlist, v))
        Pb.append(sp.expand(sum(mp[p[J, K]] * x ** J * y ** K
                                for (J, K) in p)))
    # J test
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
    # Support of generic element
    import random
    random.seed(11)
    Pg = sp.expand(sum(random.randint(1, 9) * q for q in Pb))
    supp = set()
    poly = sp.Poly(Pg, x, y)
    if poly is not None:
        for mon, cf in poly.as_dict().items():
            if cf != 0:
                supp.add(mon)
    # C(t1) for generic: sum_{J+K=d-2} coeff * t1^K
    # (using basis)
    return {'d': d, 'nvars': len(varlist), 'nconds': len(rows),
            'nullity': len(ns), 'Jvanishes': Jvan, 'Jexample': Jex,
            'support': sorted(supp)}


print(f"{'d':>3} {'nvars':>6} {'nconds':>7} {'nullity':>8} "
      f"{'J=0?':>6}")
for d in [4, 5, 6]:
    r = analyze(d)
    print(f"{r['d']:>3} {r['nvars']:>6} {r['nconds']:>7} "
          f"{r['nullity']:>8} {str(r['Jvanishes']):>6}")
    if r['nullity'] > 0:
        print(f"    support: {r['support']}")
        if not r['Jvanishes'] and r['Jexample'] is not None:
            Pi, Pj, Jij = r['Jexample']
            print(f"    J({Pi},{Pj}) = {Jij}")
    print()

print("=" * 70)
print("Interpretation")
print("=" * 70)
print("""
The linear conditions (i)+(ii) define the span where nu>=-2 and
deg C(t1) <= 2. For a genuine m=2 dicritical we additionally need:
  - C(t1) != 0 (nu = -2 exactly), and
  - deg C(t1) = 2 exactly (coefficient of t1^2 nonzero).

If the nullspace is nontrivial and J does not vanish identically,
then a solitary m=2 dicritical on E1 is NOT ruled out by linear
algebra; it becomes a candidate constrained by global degree bounds.

If nullity=0 or J vanishes identically, then E1 cannot carry m=2.
""")
