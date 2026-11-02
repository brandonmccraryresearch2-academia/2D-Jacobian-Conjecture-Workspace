/- A2 tuple-check chunk 271b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk271b1 : (2715 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk271b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2715 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2715) boundChunk271b1⟩)).all (checkFun ⟨2715 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2715) boundChunk271b1⟩) = true ∧ linkFun ⟨2715 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2715) boundChunk271b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
