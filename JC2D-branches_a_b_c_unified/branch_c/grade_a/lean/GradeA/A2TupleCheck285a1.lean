/- A2 tuple-check chunk 285a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk285a1 : (2850 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk285a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2850 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2850) boundChunk285a1⟩)).all (checkFun ⟨2850 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2850) boundChunk285a1⟩) = true ∧ linkFun ⟨2850 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2850) boundChunk285a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
