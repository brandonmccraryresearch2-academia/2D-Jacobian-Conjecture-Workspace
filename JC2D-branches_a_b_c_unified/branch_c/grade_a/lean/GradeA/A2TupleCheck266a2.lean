/- A2 tuple-check chunk 266a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk266a2 : (2662 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk266a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2662 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2662) boundChunk266a2⟩)).all (checkFun ⟨2662 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2662) boundChunk266a2⟩) = true ∧ linkFun ⟨2662 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2662) boundChunk266a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
