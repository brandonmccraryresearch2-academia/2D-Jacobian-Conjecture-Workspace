/- A2 tuple-check chunk 262b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk262b : (2625 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk262b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2625 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2625) boundChunk262b⟩)).all (checkFun ⟨2625 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2625) boundChunk262b⟩) = true ∧ linkFun ⟨2625 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2625) boundChunk262b⟩ = true := by
  decide +kernel

end BranchC.A2Check
