/- A2 tuple-check chunk 279a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk279a1 : (2790 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk279a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2790 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2790) boundChunk279a1⟩)).all (checkFun ⟨2790 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2790) boundChunk279a1⟩) = true ∧ linkFun ⟨2790 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2790) boundChunk279a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
