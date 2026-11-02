/- A2 tuple-check chunk 39 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk39 : (390 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk39 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨390 + j, Nat.lt_trans (Nat.add_lt_add_left hj 390) boundChunk39⟩)).all (checkFun ⟨390 + j, Nat.lt_trans (Nat.add_lt_add_left hj 390) boundChunk39⟩) = true ∧ linkFun ⟨390 + j, Nat.lt_trans (Nat.add_lt_add_left hj 390) boundChunk39⟩ = true := by
  decide +kernel

end BranchC.A2Check
