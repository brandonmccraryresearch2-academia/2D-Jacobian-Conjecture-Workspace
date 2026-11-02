/- A2 tuple-check chunk 278b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk278b2 : (2787 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk278b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2787 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2787) boundChunk278b2⟩)).all (checkFun ⟨2787 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2787) boundChunk278b2⟩) = true ∧ linkFun ⟨2787 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2787) boundChunk278b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
