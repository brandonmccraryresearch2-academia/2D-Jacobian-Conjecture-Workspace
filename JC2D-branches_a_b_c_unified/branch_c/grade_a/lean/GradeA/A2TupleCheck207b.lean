/- A2 tuple-check chunk 207b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk207b : (2075 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk207b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2075 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2075) boundChunk207b⟩)).all (checkFun ⟨2075 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2075) boundChunk207b⟩) = true ∧ linkFun ⟨2075 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2075) boundChunk207b⟩ = true := by
  decide +kernel

end BranchC.A2Check
