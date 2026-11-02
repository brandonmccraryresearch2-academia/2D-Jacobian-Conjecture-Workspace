/- A2 tuple-check chunk 305a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk305a1 : (3050 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk305a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3050 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3050) boundChunk305a1⟩)).all (checkFun ⟨3050 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3050) boundChunk305a1⟩) = true ∧ linkFun ⟨3050 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3050) boundChunk305a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
