/- A2 tuple-check chunk 191b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk191b : (1915 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk191b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1915 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1915) boundChunk191b⟩)).all (checkFun ⟨1915 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1915) boundChunk191b⟩) = true ∧ linkFun ⟨1915 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1915) boundChunk191b⟩ = true := by
  decide +kernel

end BranchC.A2Check
