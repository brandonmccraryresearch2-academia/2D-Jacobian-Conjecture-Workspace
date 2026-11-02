/- A2 tuple-check chunk 246b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk246b : (2465 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk246b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2465 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2465) boundChunk246b⟩)).all (checkFun ⟨2465 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2465) boundChunk246b⟩) = true ∧ linkFun ⟨2465 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2465) boundChunk246b⟩ = true := by
  decide +kernel

end BranchC.A2Check
