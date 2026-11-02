/- A2 tuple-check chunk 139b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk139b : (1395 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk139b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1395 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1395) boundChunk139b⟩)).all (checkFun ⟨1395 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1395) boundChunk139b⟩) = true ∧ linkFun ⟨1395 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1395) boundChunk139b⟩ = true := by
  decide +kernel

end BranchC.A2Check
