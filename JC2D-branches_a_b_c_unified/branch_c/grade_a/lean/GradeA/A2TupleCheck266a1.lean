/- A2 tuple-check chunk 266a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk266a1 : (2660 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk266a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2660 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2660) boundChunk266a1⟩)).all (checkFun ⟨2660 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2660) boundChunk266a1⟩) = true ∧ linkFun ⟨2660 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2660) boundChunk266a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
