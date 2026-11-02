/- A2 tuple-check chunk 319a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk319a2 : (3192 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk319a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3192 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3192) boundChunk319a2⟩)).all (checkFun ⟨3192 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3192) boundChunk319a2⟩) = true ∧ linkFun ⟨3192 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3192) boundChunk319a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
