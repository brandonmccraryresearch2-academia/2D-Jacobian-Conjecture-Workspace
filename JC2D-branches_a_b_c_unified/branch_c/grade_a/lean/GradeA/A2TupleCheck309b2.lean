/- A2 tuple-check chunk 309b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk309b2 : (3097 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk309b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3097 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3097) boundChunk309b2⟩)).all (checkFun ⟨3097 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3097) boundChunk309b2⟩) = true ∧ linkFun ⟨3097 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3097) boundChunk309b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
