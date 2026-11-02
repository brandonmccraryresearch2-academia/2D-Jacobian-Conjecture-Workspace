/- A2 tuple-check chunk 164b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk164b : (1645 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk164b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1645 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1645) boundChunk164b⟩)).all (checkFun ⟨1645 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1645) boundChunk164b⟩) = true ∧ linkFun ⟨1645 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1645) boundChunk164b⟩ = true := by
  decide +kernel

end BranchC.A2Check
