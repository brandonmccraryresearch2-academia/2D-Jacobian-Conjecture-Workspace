/- A2 tuple-check chunk 158b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk158b : (1585 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk158b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1585 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1585) boundChunk158b⟩)).all (checkFun ⟨1585 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1585) boundChunk158b⟩) = true ∧ linkFun ⟨1585 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1585) boundChunk158b⟩ = true := by
  decide +kernel

end BranchC.A2Check
