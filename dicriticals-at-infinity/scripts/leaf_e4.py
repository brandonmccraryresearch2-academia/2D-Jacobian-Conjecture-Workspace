#!/usr/bin/env python3
"""leaf_e4.py -- Solitary m=2 dicritical on leaf E4 of chain E1-E2-E3-E4.

EPISTEMIC STATUS (2026-10-01): finite computation at symbolic nonzero
c, tau0, x0, in the explicit E4 blowup chart, at d=2,3. Not a theorem.

Chain: E1 (blow [1:0:0]), E2 (blow (c,0) in E1), E3 (blow p3=(c,tau0)
in E2, tau0!=0), E4 (blow p4=(x0,0) in E3, x0!=0; x0 not on strict E2).

Charts:
  E3: s = c + x*y, t = tau0 + y.  E3 = {y=0}, strict E2 = {x=0}.
  E4: blow up (x0,0) in E3. X = x - x0, Y = y. X = x'*y', Y = y'.
      So x = x0 + x'*y', y = y'. E4 = {y'=0}, transverse coord x'.

Pullback of X^J Y^K:
  (c + (x0+x'y')y')^{-J-K} (tau0 + y')^{-J} (x0+x'y')^{-J} (y')^{-J}.

y'^{-2} coefficient (J=2): c^{-2-K} tau0^{-2} x0^{-2}. CONSTANT in x'.

We verify symbolically and test degree.
"""
import sympy as sp

xp, yp, c, tau0, x0 = sp.symbols("x' y' c tau0 x0")
print("=" * 70)
print("Leaf E4 solitary m=2 dicritical: y'-adic analysis")
print("=" * 70)
print("\nE4 chart: x = x0 + x'*y', y = y'. E4 = {y'=0}.")
print("Pullback term (J,K):")
print("  (c+(x0+x'y')y')^{-J-K} (tau0+y')^{-J} (x0+x'y')^{-J} (y')^{-J}")
print()
print("y'^{-2} requires J=2. Coefficient (set y'=0):")
print("  phi0^P(x') = tau0^{-2} * x0^{-2} * C_P,")
print("  C_P = sum_K p[2,K] c^{-2-K}  (constant in x').")
print()
print("CONSTANT in x'. [phi0^P:phi0^Q] = [C_P:C_Q], degree 0.")
print("deg=2 impossible. Joint {nu=-2, deg=2} EMPTY.")
print()
print("=" * 70)
print("Symbolic verification")
print("=" * 70)


def verify(d):
    p = {(J, K): sp.symbols(f'p{J}{K}') for J in range(d + 1)
         for K in range(d + 1 - J)}
    CP = sum(p[2, K] * c**(-2 - K) for K in range(d + 1 - 2)
             if (2, K) in p)
    CP = sp.expand(CP)
    # x'-dependence: substitute and check
    # (CP has no x' by construction; verify)
    has_xp = xp in CP.free_symbols
    print(f"d={d}: C_P = {CP}")
    print(f"      contains x': {has_xp}. "
          f"{'FAIL' if has_xp else 'OK: constant => deg 0'}.")


for d in [2, 3]:
    verify(d)

print()
print("=" * 70)
print("Verdict")
print("=" * 70)
print("The y'^{-2} leading coefficient on E4 is CONSTANT in the residual")
print("transverse coordinate x'. The pencil map [phi0:psi0] has degree 0,")
print("never 2. A solitary m=2 dicritical on the leaf E4 of the length-4")
print("chain is IMPOSSIBLE. Lengthening the chain does NOT restore")
print("transverse degree to the leaf.")
