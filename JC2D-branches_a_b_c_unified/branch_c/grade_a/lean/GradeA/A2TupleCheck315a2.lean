/- A2 tuple-check chunk 315a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk315a2 : (3152 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk315a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3152 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3152) boundChunk315a2⟩)).all (checkFun ⟨3152 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3152) boundChunk315a2⟩) = true ∧ linkFun ⟨3152 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3152) boundChunk315a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
