/- A2 tuple-check chunk 309a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk309a1 : (3090 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk309a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3090 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3090) boundChunk309a1⟩)).all (checkFun ⟨3090 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3090) boundChunk309a1⟩) = true ∧ linkFun ⟨3090 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3090) boundChunk309a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
