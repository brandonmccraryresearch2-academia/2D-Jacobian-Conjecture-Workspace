/- A2 tuple-check chunk 311b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk311b2 : (3117 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk311b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3117 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3117) boundChunk311b2⟩)).all (checkFun ⟨3117 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3117) boundChunk311b2⟩) = true ∧ linkFun ⟨3117 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3117) boundChunk311b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
