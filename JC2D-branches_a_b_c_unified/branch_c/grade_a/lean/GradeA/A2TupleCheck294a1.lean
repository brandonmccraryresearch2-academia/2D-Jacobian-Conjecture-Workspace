/- A2 tuple-check chunk 294a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk294a1 : (2940 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk294a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2940 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2940) boundChunk294a1⟩)).all (checkFun ⟨2940 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2940) boundChunk294a1⟩) = true ∧ linkFun ⟨2940 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2940) boundChunk294a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
