/- A2 tuple-check chunk 252b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk252b : (2525 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk252b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2525 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2525) boundChunk252b⟩)).all (checkFun ⟨2525 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2525) boundChunk252b⟩) = true ∧ linkFun ⟨2525 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2525) boundChunk252b⟩ = true := by
  decide +kernel

end BranchC.A2Check
