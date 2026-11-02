/- A2 tuple-check chunk 239b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk239b : (2395 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk239b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2395 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2395) boundChunk239b⟩)).all (checkFun ⟨2395 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2395) boundChunk239b⟩) = true ∧ linkFun ⟨2395 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2395) boundChunk239b⟩ = true := by
  decide +kernel

end BranchC.A2Check
