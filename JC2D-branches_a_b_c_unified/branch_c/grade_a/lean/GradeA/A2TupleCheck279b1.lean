/- A2 tuple-check chunk 279b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk279b1 : (2795 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk279b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2795 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2795) boundChunk279b1⟩)).all (checkFun ⟨2795 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2795) boundChunk279b1⟩) = true ∧ linkFun ⟨2795 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2795) boundChunk279b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
