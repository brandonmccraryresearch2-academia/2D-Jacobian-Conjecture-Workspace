/- A2 tuple-check chunk 13 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk13 : (130 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk13 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 130) boundChunk13⟩)).all (checkFun ⟨130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 130) boundChunk13⟩) = true ∧ linkFun ⟨130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 130) boundChunk13⟩ = true := by
  decide +kernel

end BranchC.A2Check
