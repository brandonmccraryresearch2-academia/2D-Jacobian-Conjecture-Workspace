/- A2 tuple-check chunk 204b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk204b : (2045 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk204b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2045 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2045) boundChunk204b⟩)).all (checkFun ⟨2045 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2045) boundChunk204b⟩) = true ∧ linkFun ⟨2045 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2045) boundChunk204b⟩ = true := by
  decide +kernel

end BranchC.A2Check
