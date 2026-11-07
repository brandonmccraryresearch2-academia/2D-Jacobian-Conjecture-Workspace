#!/usr/bin/env python3
"""depth5_global.py -- Depth-5 two-dicritical global analysis.

EPISTEMIC STATUS (2026-10-01). Every statement below is a FINITE computation
at explicit centers, not a general theorem:
- The m=1 "Vandermonde" nullity-2 is computed for d<=5 at centers {2,5}.
  No all-degree proof is supplied here.
- The adjacent "monomial restriction" is a generic degree-2 symbolic check;
  the non-cancellation C_P != 0 is assumed, not proved.
- Part 2 imposes ord_b(S) >= 2d-m (inequality). A genuine dicritical also
  needs exact order 2d-m and deg[phi_0:psi_0]=m (Riemann-Hurwitz); those are
  NOT checked here. So "J not forced to 0" is inconclusive, not a candidate.

Part 1: blowup-tree enumeration to depth 5. kappa = 3*nu - c.
        Dicritical candidate: kappa odd >= 3; m = (kappa-1)//2.
        Filter: trees carrying >= 2 candidates with m >= 2 (kappa >= 5).
Part 2: two-branch bridge topology, pole order m, at distinct centers.
        S_a(b) = sum p[J,K] (a+at*b)^{d-J-K} b^{2d-2J-K}; impose the
        b^0..b^{2d-m-1} coefficients = 0 at a=a3 and a=a4.
        Report nullity, whether J vanishes identically on the nullspace,
        and the generic support (= Newton support).
"""
import sympy as sp

print("=" * 70)
print("Part 1: depth-5 enumeration, dicritical candidates with m >= 2")
print("=" * 70)


class State:
    def __init__(self):
        self.divs = {'L': {'nu': 1, 'c': 0, 'selfint': 1}}
        self.edges = set()
        self.next_id = 0

    def copy(self):
        s = State.__new__(State)
        s.divs = {k: dict(v) for k, v in self.divs.items()}
        s.edges = set(self.edges)
        s.next_id = self.next_id
        return s

    def kappa(self, i):
        d = self.divs[i]
        return 3 * d['nu'] - d['c']

    def blowup_smooth(self, i):
        s = self.copy()
        j = f"E{s.next_id}"
        s.next_id += 1
        di = s.divs[i]
        s.divs[j] = {'nu': di['nu'], 'c': 1 + di['c'], 'selfint': -1}
        di['selfint'] -= 1
        s.edges.add(frozenset({i, j}))
        return s

    def blowup_crossing(self, i, k):
        s = self.copy()
        j = f"E{s.next_id}"
        s.next_id += 1
        di, dk = s.divs[i], s.divs[k]
        s.divs[j] = {'nu': di['nu'] + dk['nu'],
                     'c': 1 + di['c'] + dk['c'], 'selfint': -1}
        di['selfint'] -= 1
        dk['selfint'] -= 1
        s.edges.discard(frozenset({i, k}))
        s.edges.add(frozenset({i, j}))
        s.edges.add(frozenset({j, k}))
        return s

    def children(self):
        out = [self.blowup_smooth(i) for i in self.divs]
        for e in self.edges:
            i, k = tuple(e)
            out.append(self.blowup_crossing(i, k))
        return out

    def cands_m2(self):
        return [i for i in self.divs if i != 'L'
                and self.kappa(i) % 2 == 1 and self.kappa(i) >= 5]


states = [State()]
for depth in range(0, 6):
    twos = [s for s in states if len(s.cands_m2()) >= 2]
    ktypes = sorted(set(
        tuple(sorted((s.kappa(i), (s.kappa(i) - 1) // 2)
                     for i in s.cands_m2()))
        for s in twos))
    print(f"depth {depth}: {len(states)} trees, "
          f"{len(twos)} with >=2 m>=2 candidates")
    for kt in ktypes[:12]:
        print(f"    (kappa,m) of m>=2 cands: {kt}")
    if ktypes and len(ktypes) > 12:
        print(f"    ... and {len(ktypes) - 12} more kappa-types")
    if depth < 5:
        states = [c for s in states for c in s.children()]

print()
print("=" * 70)
print("Part 2: two-branch global vanishing, pole order m")
print("  ord_b(S) >= 2d-m at a3=2 and a4=5; nullity, J-test, support")
print("=" * 70)

b, at = sp.symbols('b at')
x, y = sp.symbols('x y')
import random


def analyze(d, m, a3=2, a4=5):
    p = {}
    for J in range(d + 1):
        for K in range(d + 1 - J):
            p[J, K] = sp.symbols(f'p{J}_{K}')
    varlist = list(p.values())
    need = 2 * d - m

    def rows_for(a):
        s = 0
        for (J, K), c in p.items():
            s += c * (a + at * b) ** (d - J - K) * b ** (2 * d - 2 * J - K)
        s = sp.expand(s)
        rows = []
        for t in range(need):
            cbt = s.coeff(b, t)
            if cbt == 0:
                continue
            poly_at = sp.Poly(cbt, at)
            if poly_at is None:
                rows.append([sp.expand(cbt).coeff(v) for v in varlist])
            else:
                for c in poly_at.all_coeffs():
                    rows.append([sp.expand(c).coeff(v) for v in varlist])
        return rows

    rows = rows_for(a3) + rows_for(a4)
    M = sp.Matrix(rows)
    ns = M.nullspace()
    Pbasis = []
    for v in ns:
        pmap = dict(zip(varlist, v))
        Pi = sum(pmap[p[J, K]] * x ** J * y ** K for (J, K) in p)
        Pbasis.append(sp.expand(Pi))
    Jvanishes = True
    for i in range(len(Pbasis)):
        for j in range(i + 1, len(Pbasis)):
            Jij = sp.expand(sp.diff(Pbasis[i], x) * sp.diff(Pbasis[j], y)
                            - sp.diff(Pbasis[i], y) * sp.diff(Pbasis[j], x))
            if Jij != 0:
                Jvanishes = False
                break
        if not Jvanishes:
            break
    # generic support via random combination (Newton support)
    random.seed(1234)
    Pg = sp.expand(sum(random.randint(1, 9) * Pb for Pb in Pbasis))
    supp = set()
    poly = sp.Poly(Pg, x, y)
    if poly is not None:
        for mon, coeff in poly.as_dict().items():
            if coeff != 0:
                supp.add(mon)
    return {'d': d, 'm': m, 'nvars': len(varlist), 'rank': M.rank(),
            'nullity': len(ns), 'Jvanishes': Jvanishes,
            'support': sorted(supp)}


for m in [1, 2, 3]:
    tag = " (control: reproduces Vandermonde)" if m == 1 else ""
    print(f"--- pole order m = {m} ---{tag}")
    for d in range(2, 7):
        r = analyze(d, m)
        print(f"  d={d}: nvars={r['nvars']} rank={r['rank']} "
              f"nullity={r['nullity']} J_identically_0={r['Jvanishes']}")
        print(f"       Newton support: {r['support']}")

print()
print("=" * 70)
print("Part 3: verdict")
print("=" * 70)
print("See per-(d,m) rows above. J_identically_0=True means the linear")
print("vanishing conditions alone rule out any Keller pair (J=1) in this")
print("bridge topology. J_identically_0=False is INCONCLUSIVE: the exact")
print("order and deg[phi_0:psi_0]=m still have to be imposed.")
