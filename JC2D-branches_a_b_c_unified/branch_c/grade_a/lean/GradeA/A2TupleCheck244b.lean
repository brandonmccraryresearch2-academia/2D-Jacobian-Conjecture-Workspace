/- A2 tuple-check chunk 244b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk244b : (2445 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk244b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2445 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2445) boundChunk244b⟩)).all (checkFun ⟨2445 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2445) boundChunk244b⟩) = true ∧ linkFun ⟨2445 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2445) boundChunk244b⟩ = true := by
  decide +kernel

end BranchC.A2Check
