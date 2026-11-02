/- A2 tuple-check chunk 217a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk217a : (2170 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk217a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2170 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2170) boundChunk217a⟩)).all (checkFun ⟨2170 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2170) boundChunk217a⟩) = true ∧ linkFun ⟨2170 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2170) boundChunk217a⟩ = true := by
  decide +kernel

end BranchC.A2Check
