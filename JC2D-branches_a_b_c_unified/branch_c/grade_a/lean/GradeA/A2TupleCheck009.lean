/- A2 tuple-check chunk 9 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk9 : (90 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk9 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨90 + j, Nat.lt_trans (Nat.add_lt_add_left hj 90) boundChunk9⟩)).all (checkFun ⟨90 + j, Nat.lt_trans (Nat.add_lt_add_left hj 90) boundChunk9⟩) = true ∧ linkFun ⟨90 + j, Nat.lt_trans (Nat.add_lt_add_left hj 90) boundChunk9⟩ = true := by
  decide +kernel

end BranchC.A2Check
