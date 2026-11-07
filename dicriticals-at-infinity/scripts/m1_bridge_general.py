#!/usr/bin/env python3
"""m1_bridge_general.py -- General m=1 two-branch bridge.

EPISTEMIC STATUS (2026-10-01): symbolic computation with general
centers a3 != a4. Attempts to prove the nullspace is span of y-powers.

Claim: For m=1 (ord_b >= 2d-1) at two distinct centers a3, a4,
the joint nullspace consists ONLY of polynomials in y (J=0).
Therefore J vanishes identically on the span.

We compute the nullspace symbolically and inspect.
"""
import sympy as sp

b, at = sp.symbols('b at')
a3, a4 = sp.symbols('a3 a4')
print("=" * 70)
print("m=1 bridge: general centers a3 != a4")
print("=" * 70)
print("\nConditions: ord_b(S) >= 2d-1 at a3 and at a4.")
print("Claim: nullspace = span{y^K} (only J=0 terms survive).")
print()


def nullspace_basis(d):
    """Compute nullspace with symbolic a3,a4. Return basis info."""
    p = {(J, K): sp.symbols(f'p{J}_{K}') for J in range(d + 1)
         for K in range(d + 1 - J)}
    varlist = list(p.values())

    def rows_for(a_val):
        need = 2 * d - 1
        s = sum(c * (a_val + at * b) ** (d - J - K) * b ** (2 * d - 2 * J - K)
                for (J, K), c in p.items())
        s = sp.expand(s)
        rows = []
        for t in range(need):
            cbt = s.coeff(b, t)
            if cbt == 0:
                continue
            pa = sp.Poly(cbt, at)
            if pa is None:
                # constant in at; single equation
                row = [sp.expand(cbt).coeff(v) for v in varlist]
                # cbt is linear in p's; extract coefficients
                # Actually cbt may not be linear if a_val is symbolic?
                # It IS linear in p's since p's appear linearly.
                rows.append(row)
            else:
                for cc in pa.all_coeffs():
                    cc = sp.expand(cc)
                    # cc is linear in p's; get coefficients
                    row = []
                    for v in varlist:
                        # coeff of v in cc
                        row.append(sp.expand(cc).coeff(v))
                    rows.append(row)
        return rows

    rows = rows_for(a3) + rows_for(a4)
    # Remove zero rows
    rows = [r for r in rows if any(x != 0 for x in r)]
    if not rows:
        return None, len(varlist), 0
    M = sp.Matrix(rows)
    # Nullspace over rationals with parameters a3,a4
    # This may be heavy; try for small d
    try:
        ns = M.nullspace()
        return ns, len(varlist), M.rank()
    except Exception as e:
        return None, len(varlist), -1


for d in [2, 3]:
    print(f"--- d={d} ---")
    ns, nvars, rank = nullspace_basis(d)
    if ns is None:
        print("  (computation failed or empty)")
    else:
        print(f"  nvars={nvars}, rank={rank}, nullity={len(ns)}")
        # Inspect: which p_{JK} appear in the nullspace?
        # For the claim, we expect only J=0 terms.
    print()

print("=" * 70)
print("Direct proof attempt: coefficient comparison")
print("=" * 70)
print("""
We attempt a direct proof that p_{JK}=0 for J>=1.

Fix (J,K) with J>=1. Consider the b^{2d-2J-K} coefficient at center a.

The term (J,K) contributes:
  p_{JK} * a^{d-J-K} * b^{2d-2J-K}   [lowest b-power from this term]

Other terms (J',K') contribute to b^{2d-2J-K} only if
  2d-2J'-K' <= 2d-2J-K, i.e., 2J'+K' >= 2J+K,
with equality only if (J',K')=(J,K) (for the a^{...} part).

Actually, the full coefficient of b^{2d-2J-K} is a polynomial in at.
The at^0 part (constant in at) comes from:
  sum_{(J',K'): 2J'+K' = 2J+K} p_{J'K'} * a^{d-J'-K'}.

This is getting intricate. Let's try a cleaner invariant.

ALTERNATIVE: Use the two centers.

At center a3, the b^{2d-2} coefficient (t=2d-2):
  Which (J,K) contribute? Need 2d-2J-K <= 2d-2, i.e., 2J+K >= 2.
  The at^0 part: sum_{2J+K=2} p_{JK} a3^{d-J-K} = 0.
  2J+K=2: (J,K) = (1,0), (0,2).
  So: p_{10} * a3^{d-1} + p_{02} * a3^{d-2} = 0.   ...(A3)

At center a4:
  p_{10} * a4^{d-1} + p_{02} * a4^{d-2} = 0.   ...(A4)

If a3 != a4 and both nonzero, this is a 2x2 system for (p10, p02).
Determinant: a3^{d-1} a4^{d-2} - a4^{d-1} a3^{d-2}
           = a3^{d-2} a4^{d-2} (a3 - a4) != 0.
Therefore p10 = p02 = 0.

Good! This kills two coefficients.

Continue: b^{2d-3} coefficient, at^0 part.
  Need 2J+K = 3: (J,K) = (1,1), (0,3).
  p_{11} a3^{d-2} + p_{03} a3^{d-3} = 0
  p_{11} a4^{d-2} + p_{03} a4^{d-3} = 0
  Determinant: a3^{d-3} a4^{d-3} (a3 - a4) != 0.
  So p11 = p03 = 0.

In general, for b^{2d-1-s} (s>=1), at^0 part:
  sum_{2J+K = s+1} p_{JK} a^{d-J-K} = 0 at a=a3,a4.

For fixed s, the pairs (J,K) with 2J+K = s+1 are:
  J=0: K=s+1
  J=1: K=s-1 (if s>=1)
  J=2: K=s-3 (if s>=3)
  ...

This is a Vandermonde-like system in a3,a4. With only TWO centers,
we can kill at most 2 coefficients per s. But there may be more
than 2 pairs (J,K) with 2J+K=s+1 for large s.

For s+1 >= 4: pairs include (0,s+1), (1,s-1), (2,s-3). That's 3.
Two equations, three unknowns. NOT enough to kill all!

So the simple at^0 argument FAILS for large s.

We need the FULL at-polynomial, not just at^0.

The b^{2d-1-s} coefficient is a polynomial in at of degree up to ...
Each (J,K) contributes at^i for i=0..(d-J-K).

This gives MORE equations (coefficients of at^i).

With two centers and multiple at-powers, we may get enough equations.

This is the Vandermonde structure: the full system should force
p_{JK}=0 for J>=1.

Let's verify computationally for d=2,3 with symbolic a3,a4.
""")

# Let's do the full computation for d=2 with symbolic centers
print()
print("=" * 70)
print("Full symbolic nullspace at d=2")
print("=" * 70)
d = 2
p = {(J, K): sp.symbols(f'p{J}_{K}') for J in range(d + 1)
     for K in range(d + 1 - J)}
varlist = list(p.values())
print(f"Monomials: {list(p.keys())}")

def full_rows(a_val, d, p, varlist):
    need = 2*d - 1
    s = sum(c * (a_val + at*b)**(d-J-K) * b**(2*d-2*J-K)
            for (J,K), c in p.items())
    s = sp.expand(s)
    rows = []
    for t in range(need):
        cbt = s.coeff(b, t)
        if cbt == 0:
            continue
        # cbt is a polynomial in at (and a_val); linear in p's
        pa = sp.Poly(cbt, at)
        if pa is None:
            # constant in at
            row = [sp.expand(cbt).coeff(v) for v in varlist]
            if any(x != 0 for x in row):
                rows.append(row)
        else:
            for cc in pa.all_coeffs():
                row = [sp.expand(cc).coeff(v) for v in varlist]
                if any(x != 0 for x in row):
                    rows.append(row)
    return rows

rows = full_rows(a3, d, p, varlist) + full_rows(a4, d, p, varlist)
M = sp.Matrix(rows)
print(f"Matrix: {M.rows} x {M.cols}, rank {M.rank()}")
ns = M.nullspace()
print(f"Nullity: {len(ns)}")
print()
print("Nullspace basis vectors (as coefficient dicts):")
for i, v in enumerate(ns):
    dct = {f"p{J}_{K}": sp.simplify(v[j])
           for j, (J,K) in enumerate(p.keys())}
    # Only show nonzero
    nz = {k: val for k, val in dct.items() if val != 0}
    print(f"  v{i}: {nz}")

# Check: do all basis vectors have J>=1 coefficients zero?
print()
print("Check: are all J>=1 coefficients zero in the nullspace?")
all_J0 = True
for v in ns:
    for j, (J,K) in enumerate(p.keys()):
        if J >= 1 and sp.simplify(v[j]) != 0:
            all_J0 = False
            print(f"  FOUND nonzero J>=1: p{J}_{K} = {v[j]}")
            break
    if not all_J0:
        break
if all_J0:
    print("  YES: nullspace uses only J=0 (y-powers).")
    print("  Therefore J(P,Q) = 0 identically on the span.")
    print("  The m=1 bridge is IMPOSSIBLE for general a3!=a4, d=2.")
else:
    print("  NO: counter-example found!")
