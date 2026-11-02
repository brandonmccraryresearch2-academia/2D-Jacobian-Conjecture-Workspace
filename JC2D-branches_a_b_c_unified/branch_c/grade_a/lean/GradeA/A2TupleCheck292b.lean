/- A2 tuple-check chunk 292b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk292b : (2925 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk292b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2925 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2925) boundChunk292b⟩)).all (checkFun ⟨2925 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2925) boundChunk292b⟩) = true ∧ linkFun ⟨2925 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2925) boundChunk292b⟩ = true := by
  decide +kernel

end BranchC.A2Check
