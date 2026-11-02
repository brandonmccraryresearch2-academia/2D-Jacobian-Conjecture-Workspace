/- A2 tuple-check chunk 319b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk319b : (3195 + 4 : Nat) ≤ 3199 := by decide
theorem colCheckChunk319b : ∀ (j : Nat) (hj : j < 4),
    (dedup5 (unionTuples ⟨3195 + j, Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj 3195) boundChunk319b⟩)).all (checkFun ⟨3195 + j, Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj 3195) boundChunk319b⟩) = true ∧ linkFun ⟨3195 + j, Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj 3195) boundChunk319b⟩ = true := by
  decide +kernel

end BranchC.A2Check
