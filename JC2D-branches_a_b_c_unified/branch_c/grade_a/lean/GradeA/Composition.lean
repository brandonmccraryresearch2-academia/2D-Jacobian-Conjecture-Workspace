/- Branch-(c) elimination, unconditional (2026-11-04), filed as tracked module
   `GradeA.Composition` 2026-11-06 (Step 1 of the six-step programme).
   Origin: scratch file `composition_2026-11-04.lean` (2026-11-04, proved on
   lean-build-2); the filed leg copy is `gghv-dependency-closure/lean/
   composition_2026-11-04.lean`. The theorem below is unchanged; only this
   header and the import of the bridge (now `GradeA.Bridge`, was the scratch
   filename `bridge_attempt_2026_11_04`) differ.
   Applies `main_theorem_c_of_chartEmpty_T1ne0` (bundle `Combine`) to
   `challenge_target` (`GradeA.Bridge`). Compiled by `grade_a/build_bridge.sh`;
   verified 2026-11-06 on lean-build-3 (see `BRIDGE_STATUS_2026-11-06.md`). -/

import Jacobian.BranchC.T1Zero.Combine
import GradeA.Bridge

open MvPolynomial BranchAb BranchC

/-- Branch (c) eliminated unconditionally: no NewtonNFc Keller pair exists
    over any field of characteristic 0 (type as stated in Combine). -/
theorem branch_c_eliminated {L : Type*} [Field L] [CharZero L] :
    ¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNFc P Q ∧
      jac P Q = C lam * X 0 ^ 2 :=
  BranchC.main_theorem_c_of_chartEmpty_T1ne0 challenge_target

#print axioms branch_c_eliminated
