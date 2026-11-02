/- A2 tuple-check chunk 260b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk260b : (2605 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk260b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2605 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2605) boundChunk260b⟩)).all (checkFun ⟨2605 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2605) boundChunk260b⟩) = true ∧ linkFun ⟨2605 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2605) boundChunk260b⟩ = true := by
  decide +kernel

end BranchC.A2Check
