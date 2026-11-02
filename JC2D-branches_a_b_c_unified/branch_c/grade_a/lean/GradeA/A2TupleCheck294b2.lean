/- A2 tuple-check chunk 294b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk294b2 : (2947 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk294b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2947 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2947) boundChunk294b2⟩)).all (checkFun ⟨2947 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2947) boundChunk294b2⟩) = true ∧ linkFun ⟨2947 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2947) boundChunk294b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
