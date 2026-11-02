/- A2 tuple-check chunk 291b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk291b : (2915 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk291b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2915 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2915) boundChunk291b⟩)).all (checkFun ⟨2915 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2915) boundChunk291b⟩) = true ∧ linkFun ⟨2915 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2915) boundChunk291b⟩ = true := by
  decide +kernel

end BranchC.A2Check
