/- A2 tuple-check chunk 267b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk267b2 : (2677 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk267b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2677 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2677) boundChunk267b2⟩)).all (checkFun ⟨2677 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2677) boundChunk267b2⟩) = true ∧ linkFun ⟨2677 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2677) boundChunk267b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
