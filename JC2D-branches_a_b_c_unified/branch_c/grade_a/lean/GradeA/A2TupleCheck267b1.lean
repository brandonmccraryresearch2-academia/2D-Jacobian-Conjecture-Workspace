/- A2 tuple-check chunk 267b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk267b1 : (2675 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk267b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2675 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2675) boundChunk267b1⟩)).all (checkFun ⟨2675 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2675) boundChunk267b1⟩) = true ∧ linkFun ⟨2675 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2675) boundChunk267b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
