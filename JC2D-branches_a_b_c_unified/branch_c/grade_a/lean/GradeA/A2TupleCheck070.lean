/- A2 tuple-check chunk 70 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk70 : (700 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk70 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨700 + j, Nat.lt_trans (Nat.add_lt_add_left hj 700) boundChunk70⟩)).all (checkFun ⟨700 + j, Nat.lt_trans (Nat.add_lt_add_left hj 700) boundChunk70⟩) = true ∧ linkFun ⟨700 + j, Nat.lt_trans (Nat.add_lt_add_left hj 700) boundChunk70⟩ = true := by
  decide +kernel

end BranchC.A2Check
