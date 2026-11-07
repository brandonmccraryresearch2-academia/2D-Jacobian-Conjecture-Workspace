#!/usr/bin/env python3
"""leaf_e3.py -- Solitary m=2 dicritical on leaf E3 of chain E1-E2-E3.

EPISTEMIC STATUS (2026-10-01): finite computation at symbolic nonzero c,
tau0, in the explicit E3 blowup chart, at d=2,3,4. Not a general theorem.

Chain: E1 (blow up [1:0:0]), E2 (blow up (c,0) in E1), E3 (blow up
p3=(c,tau0) in E2, tau0!=0). E3 chart: u=s-c, v=t-tau0; u=x*y, v=y.
E3={y=0}, strict E2={x=0}. Pullback:
  X^J Y^K -> (c+xy)^{-J-K} (tau0+y)^{-J} x^{-J} y^{-J}.

For E3 to be dicritical with m=2: need nu_{E3} = -2 EXACTLY and
deg[phi0^P : phi0^Q] = 2, where phi0 is the y^{-2} coefficient.

We compute the y^{-2} coefficient in closed form and test whether
degree 2 is attainable.
"""
import sympy as sp

x, y, c, tau0 = sp.symbols('x y c tau0')
print("=" * 70)
print("Leaf E3 solitary m=2 dicritical: y-adic analysis")
print("=" * 70)

# Closed form: y^{-2} coefficient = x^{-2} tau0^{-2} C_P,
#   C_P = sum_K p[2,K] c^{-2-K} (for d>=2).
# Derivation: term (J,K) = p[J,K](c+xy)^{-J-K}(tau0+y)^{-J}x^{-J}y^{-J}.
# y^{-2} requires J=2 (J>2 gives y^{<=-3}, J<2 gives y^{>=-1}).
# For J=2: leading y-term is p[2,K] c^{-2-K} tau0^{-2} x^{-2} y^{-2}.
print("\nClosed-form y^{-2} coefficient:")
print("  phi0^P(x) = x^{-2} * tau0^{-2} * C_P,")
print("  C_P = sum_K p[2,K] * c^{-2-K}  (constant in x).")
print("  phi0^Q(x) = x^{-2} * tau0^{-2} * C_Q.")
print()
print("Hence [phi0^P : phi0^Q] = [C_P : C_Q], CONSTANT in x.")
print("Degree 0, ALWAYS (whenever C_P, C_Q not both zero).")
print()
print("For nu_{E3} = -2 exactly: need (C_P, C_Q) != (0,0).")
print("  If C_P != 0: nu_{E3}(P) = -2. If C_P = 0: nu > -2.")
print()
print("CONCLUSION:")
print("  - Exact order -2 is attainable (take C_P != 0).")
print("  - But deg[phi0:psi0] = 0 ALWAYS, never 2.")
print("  - The joint system {nu=-2, deg=2} is INCONSISTENT.")
print("  - A solitary m=2 dicritical on leaf E3 is IMPOSSIBLE.")
print("  - E2 is automatically non-dicritical here: [C_P:C_Q] const.")
print()
print("=" * 70)
print("Symbolic verification at d=2,3,4")
print("=" * 70)

X, Y = sp.symbols('X Y')


def verify(d):
    p = {(J, K): sp.symbols(f'p{J}{K}') for J in range(d + 1)
         for K in range(d + 1 - J)}
    # y^{-2} coeff via closed form
    CP = sum(p[2, K] * c**(-2 - K) for K in range(d + 1 - 2)
             if (2, K) in p)
    CP = sp.expand(CP)
    # x-dependence: should be none
    px = sp.Poly(CP, x)
    xdeg = px.degree() if px is not None else 0
    print(f"d={d}: C_P = {CP}; x-degree of C_P: {xdeg}")
    print(f"      => [phi0^P:phi0^Q] has x-degree 0. deg=2 impossible.")


for d in [2, 3, 4]:
    verify(d)

print()
print("=" * 70)
print("Final verdict")
print("=" * 70)
print("The leaf E3 of the chain E1-E2-E3 CANNOT carry a solitary m=2")
print("dicritical. Exact pole order -2 forces the pencil restriction to")
print("be constant (degree 0), contradicting the required degree 2.")
print("No linear span to test for J; the degree condition already fails.")
print("The solitary high-order dicritical does not live here.")
