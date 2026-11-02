/- A2 tuple-check chunk 236b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk236b : (2365 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk236b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2365 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2365) boundChunk236b⟩)).all (checkFun ⟨2365 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2365) boundChunk236b⟩) = true ∧ linkFun ⟨2365 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2365) boundChunk236b⟩ = true := by
  decide +kernel

end BranchC.A2Check
