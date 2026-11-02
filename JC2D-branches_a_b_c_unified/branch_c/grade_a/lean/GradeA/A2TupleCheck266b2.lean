/- A2 tuple-check chunk 266b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk266b2 : (2667 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk266b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2667 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2667) boundChunk266b2⟩)).all (checkFun ⟨2667 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2667) boundChunk266b2⟩) = true ∧ linkFun ⟨2667 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2667) boundChunk266b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
