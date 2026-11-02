/- A2 tuple-check chunk 278a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk278a : (2780 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk278a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2780 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2780) boundChunk278a⟩)).all (checkFun ⟨2780 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2780) boundChunk278a⟩) = true ∧ linkFun ⟨2780 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2780) boundChunk278a⟩ = true := by
  decide +kernel

end BranchC.A2Check
