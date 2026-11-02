/- A2 tuple-check chunk 36 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk36 : (360 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk36 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨360 + j, Nat.lt_trans (Nat.add_lt_add_left hj 360) boundChunk36⟩)).all (checkFun ⟨360 + j, Nat.lt_trans (Nat.add_lt_add_left hj 360) boundChunk36⟩) = true ∧ linkFun ⟨360 + j, Nat.lt_trans (Nat.add_lt_add_left hj 360) boundChunk36⟩ = true := by
  decide +kernel

end BranchC.A2Check
