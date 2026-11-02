/- A2 tuple-check chunk 171b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk171b : (1715 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk171b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1715 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1715) boundChunk171b⟩)).all (checkFun ⟨1715 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1715) boundChunk171b⟩) = true ∧ linkFun ⟨1715 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1715) boundChunk171b⟩ = true := by
  decide +kernel

end BranchC.A2Check
