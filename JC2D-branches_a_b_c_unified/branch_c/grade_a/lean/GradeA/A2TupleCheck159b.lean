/- A2 tuple-check chunk 159b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk159b : (1595 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk159b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1595 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1595) boundChunk159b⟩)).all (checkFun ⟨1595 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1595) boundChunk159b⟩) = true ∧ linkFun ⟨1595 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1595) boundChunk159b⟩ = true := by
  decide +kernel

end BranchC.A2Check
