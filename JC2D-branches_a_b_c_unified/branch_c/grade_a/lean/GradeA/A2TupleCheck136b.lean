/- A2 tuple-check chunk 136b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk136b : (1365 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk136b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1365 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1365) boundChunk136b⟩)).all (checkFun ⟨1365 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1365) boundChunk136b⟩) = true ∧ linkFun ⟨1365 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1365) boundChunk136b⟩ = true := by
  decide +kernel

end BranchC.A2Check
