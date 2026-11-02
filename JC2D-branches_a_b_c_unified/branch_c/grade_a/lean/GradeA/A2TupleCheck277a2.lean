/- A2 tuple-check chunk 277a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk277a2 : (2772 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk277a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2772 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2772) boundChunk277a2⟩)).all (checkFun ⟨2772 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2772) boundChunk277a2⟩) = true ∧ linkFun ⟨2772 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2772) boundChunk277a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
