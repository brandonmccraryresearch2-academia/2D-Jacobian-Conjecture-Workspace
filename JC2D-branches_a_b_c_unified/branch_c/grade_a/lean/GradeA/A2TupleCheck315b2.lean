/- A2 tuple-check chunk 315b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk315b2 : (3157 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk315b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3157 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3157) boundChunk315b2⟩)).all (checkFun ⟨3157 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3157) boundChunk315b2⟩) = true ∧ linkFun ⟨3157 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3157) boundChunk315b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
