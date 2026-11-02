/- A2 tuple-check chunk 34 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk34 : (340 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk34 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨340 + j, Nat.lt_trans (Nat.add_lt_add_left hj 340) boundChunk34⟩)).all (checkFun ⟨340 + j, Nat.lt_trans (Nat.add_lt_add_left hj 340) boundChunk34⟩) = true ∧ linkFun ⟨340 + j, Nat.lt_trans (Nat.add_lt_add_left hj 340) boundChunk34⟩ = true := by
  decide +kernel

end BranchC.A2Check
