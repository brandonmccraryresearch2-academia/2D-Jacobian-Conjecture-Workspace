/- A2 tuple-check chunk 309b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk309b1 : (3095 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk309b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3095 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3095) boundChunk309b1⟩)).all (checkFun ⟨3095 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3095) boundChunk309b1⟩) = true ∧ linkFun ⟨3095 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3095) boundChunk309b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
