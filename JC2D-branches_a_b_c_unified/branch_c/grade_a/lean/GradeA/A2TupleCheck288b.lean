/- A2 tuple-check chunk 288b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk288b : (2885 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk288b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2885 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2885) boundChunk288b⟩)).all (checkFun ⟨2885 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2885) boundChunk288b⟩) = true ∧ linkFun ⟨2885 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2885) boundChunk288b⟩ = true := by
  decide +kernel

end BranchC.A2Check
