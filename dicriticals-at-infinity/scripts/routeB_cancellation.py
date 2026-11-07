#!/usr/bin/env python3
"""routeB_cancellation.py -- Seal or open the Route B residual loophole.

EPISTEMIC STATUS (2026-10-01): finite computation at degree d=3, symbolic
nonzero c, in the (s',tau) chart of adjacent_obstruction.py. Not a theorem.

Setup: blow up p1=[1:0:0] -> E1, then p2=(c,0) in E1 (c!=0) -> E2.
Chart (s,t)=(s',tau): E2={s-c=0}. Pullback:
    P = sum p[J,K] s^{-J-K} t^{-J} (s-c)^{-J}.
Put w = s-c. Term (J,K) = p[J,K] t^{-J} w^{-J} (c+w)^{-J-K}.
(c+w)^{-J-K} = sum_{n>=0} binom(-J-K,n) c^{-J-K-n} w^n.
Hence the w^{-M} coefficient (M = max J) is t^{-M} C_P,
    C_P = sum_K p[M,K] c^{-M-K},
and, ON the locus C_P = 0, the w^{-(M-1)} coefficient is
    t^{-M} A_P + t^{-(M-1)} B_P,
    A_P = sum_K p[M,K](-M-K) c^{-M-K-1},
    B_P = sum_K p[M-1,K] c^{-(M-1)-K}.
We compute these directly (closed form) and test the dicritical conditions.
"""
import sympy as sp
from sympy import binomial

c, t = sp.symbols('c t')
print("=" * 70)
print("Route B cancellation locus: d=3, middle divisor E2")
print("=" * 70)

d = 3
M = 2  # highest x-degree

p = {(J, K): sp.symbols(f'p{J}{K}') for J in range(d + 1)
     for K in range(d + 1 - J)}
q = {(J, K): sp.symbols(f'q{J}{K}') for J in range(d + 1)
     for K in range(d + 1 - J)}

def CP(coefs):
    return sum(coefs[M, K] * c**(-M - K) for K in range(d + 1 - M))

def AP(coefs):
    return sum(coefs[M, K] * (-M - K) * c**(-M - K - 1)
               for K in range(d + 1 - M))

def BP(coefs):
    return sum(coefs[M - 1, K] * c**(-(M - 1) - K)
               for K in range(d + 1 - (M - 1)))

Cp, Cq = sp.expand(CP(p)), sp.expand(CP(q))
Ap, Bp = sp.expand(AP(p)), sp.expand(BP(p))
Aq, Bq = sp.expand(AP(q)), sp.expand(BP(q))
print(f"\nC_P = {Cp}")
print(f"C_Q = {Cq}")
print("Cancellation locus L: p21 + c*p20 = 0 AND q21 + c*q20 = 0")
print("(i.e. p[2,1] = -c*p[2,0]). Nonempty iff d>=3.")
print("At d=2: C_P = p20*c^{-2}, and mP=2 <=> p20!=0, so L is EMPTY.")

print(f"\nA_P = {Ap}")
print(f"B_P = {Bp}")
print(f"A_Q = {Aq}")
print(f"B_Q = {Bq}")

# restrict to L
subsL = {p[2, 1]: -c * p[2, 0], q[2, 1]: -c * q[2, 0]}
ApL, BpL = sp.expand(Ap.subs(subsL)), sp.expand(Bp.subs(subsL))
AqL, BqL = sp.expand(Aq.subs(subsL)), sp.expand(Bq.subs(subsL))
print(f"\nOn L:")
print(f"  A_P = {ApL}")
print(f"  B_P = {BpL}")
print(f"  A_Q = {AqL}")
print(f"  B_Q = {BqL}")

# A_P = p20*c^{-3} on L. Since mP=2 on L forces p20 != 0 (else p21=0 too),
# A_P != 0, so nu_{E2}(P) = -1 exactly. Same for Q.
print("\nKey: on L cap {mP=2}, p20 != 0 (else (p20,p21)=(0,0), mP<2).")
print("Thus A_P = p20*c^{-3} != 0, so nu_{E2}(P) = -1 EXACTLY.")
print("Similarly nu_{E2}(Q) = -1 when mQ=2.")
print("Equal valuations: YES.")

# pencil map [AP+BP*t : AQ+BQ*t]; degree 1 iff AP*BQ-AQ*BP != 0
det = sp.expand(ApL * BqL - AqL * BpL)
print(f"\nDegree-1 condition: A_P*B_Q - A_Q*B_P = {det}")
print("This is NOT identically zero on L.")

# explicit numerical example
print("\n--- Explicit example (c=1) ---")
ex = {c: 1, p[2, 0]: 1, q[2, 0]: 1,
      p[1, 0]: 0, p[1, 1]: 0, p[1, 2]: 0,
      q[1, 0]: 1, q[1, 1]: 0, q[1, 2]: 0}
# note p[2,1], q[2,1] via subsL
Apn = float(ApL.subs(ex).subs(subsL))
BPn = float(BpL.subs(ex).subs(subsL))
AQn = float(AqL.subs(ex).subs(subsL))
BQn = float(BqL.subs(ex).subs(subsL))
print(f"  P: p20=1,p21=-1; Q: q20=1,q21=-1; B_P=0, B_Q=1.")
print(f"  A_P={Apn}, B_P={BPn}, A_Q={AQn}, B_Q={BQn}")
print(f"  [phi0:psi0] = [{Apn}+{BPn}*t : {AQn}+{BQn}*t] = [1 : 1+t]")
print(f"  DEGREE 1. nu_E2(P)=nu_E2(Q)=-1.")
print(f"  => E2 IS DICRITICAL (m=1) on the cancellation locus.")
print(f"  A_P*B_Q - A_Q*B_P = {Apn*BQn-AQn*BPn} != 0. Confirmed.")

print("\n--- Newton support ---")
print("d=3. P: (2,0),(2,1) with p21=-c*p20, p20!=0; (1,*),(0,*) free;")
print("     (3,0)=0 (else mP=3). Q: same pattern.")
print("Newton polygon: (0,0),(0,3),(2,1); the (2,0)-(2,1) edge carries")
print("the relation p21 + c*p20 = 0.")

print()
print("=" * 70)
print("VERDICT")
print("=" * 70)
print("1. Cancellation locus L = {C_P=C_Q=0} is NONEMPTY at d>=3")
print("   (EMPTY at d=2: C_P=p20*c^{-2}, mP=2 forces p20!=0).")
print("2. On L cap {mP=mQ=2}: nu_{E2}(P)=nu_{E2}(Q)=-1 EXACTLY")
print("   (A_P=p20*c^{-3}!=0).")
print("3. [phi0:psi0]=[A_P+B_P*t : A_Q+B_Q*t] has degree 1 iff")
print("   A_P*B_Q-A_Q*B_P != 0, which is satisfiable (explicit example).")
print("4. => E2 CAN be dicritical (m=1) on L. The 'middle divisor NEVER")
print("   dicritical' is FALSE as stated.")
print("5. Route B is NOT fully closed. It holds off L (and fully at d=2),")
print("   but L yields a genuine m=1 dicritical candidate for E2.")
print("6. The ADJACENT PAIR (E2+E3 both dicritical) remains open: this")
print("   shows E2 can be dicritical on L; E3 needs its own chart analysis.")
