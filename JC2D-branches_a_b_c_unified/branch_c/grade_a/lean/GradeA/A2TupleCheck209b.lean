/- A2 tuple-check chunk 209b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk209b : (2095 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk209b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2095 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2095) boundChunk209b⟩)).all (checkFun ⟨2095 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2095) boundChunk209b⟩) = true ∧ linkFun ⟨2095 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2095) boundChunk209b⟩ = true := by
  decide +kernel

end BranchC.A2Check
