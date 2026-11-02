/- A2 tuple-check chunk 42 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk42 : (420 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk42 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨420 + j, Nat.lt_trans (Nat.add_lt_add_left hj 420) boundChunk42⟩)).all (checkFun ⟨420 + j, Nat.lt_trans (Nat.add_lt_add_left hj 420) boundChunk42⟩) = true ∧ linkFun ⟨420 + j, Nat.lt_trans (Nat.add_lt_add_left hj 420) boundChunk42⟩ = true := by
  decide +kernel

end BranchC.A2Check
