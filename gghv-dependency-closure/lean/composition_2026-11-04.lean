/- Scratch composition (2026-11-04): branch-(c) elimination, unconditional.
   Applies `main_theorem_c_of_chartEmpty_T1ne0` (bundle Combine) to
   `challenge_target` (bridge_attempt_2026_11_04). NOT part of the repo tree;
   run with `lean --root=/tmp` on lean-build-2. -/

import Jacobian.BranchC.T1Zero.Combine
import bridge_attempt_2026_11_04

open MvPolynomial BranchAb BranchC

/-- Branch (c) eliminated unconditionally: no NewtonNFc Keller pair exists
    over any field of characteristic 0 (type as stated in Combine). -/
theorem branch_c_eliminated {L : Type*} [Field L] [CharZero L] :
    ¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNFc P Q ∧
      jac P Q = C lam * X 0 ^ 2 :=
  BranchC.main_theorem_c_of_chartEmpty_T1ne0 challenge_target

#print axioms branch_c_eliminated
