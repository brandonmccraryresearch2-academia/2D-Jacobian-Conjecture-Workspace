/- A2 tuple-check chunk 264a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk264a1 : (2640 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk264a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2640 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2640) boundChunk264a1⟩)).all (checkFun ⟨2640 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2640) boundChunk264a1⟩) = true ∧ linkFun ⟨2640 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2640) boundChunk264a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
