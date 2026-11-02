/- A2 tuple-check chunk 285a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk285a2 : (2852 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk285a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2852 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2852) boundChunk285a2⟩)).all (checkFun ⟨2852 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2852) boundChunk285a2⟩) = true ∧ linkFun ⟨2852 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2852) boundChunk285a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
