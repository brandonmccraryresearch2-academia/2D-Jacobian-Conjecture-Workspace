/- A2 tuple-check chunk 280a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk280a2 : (2802 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk280a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2802 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2802) boundChunk280a2⟩)).all (checkFun ⟨2802 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2802) boundChunk280a2⟩) = true ∧ linkFun ⟨2802 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2802) boundChunk280a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
