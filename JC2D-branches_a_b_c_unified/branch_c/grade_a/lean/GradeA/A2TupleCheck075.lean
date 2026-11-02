/- A2 tuple-check chunk 75 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk75 : (750 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk75 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨750 + j, Nat.lt_trans (Nat.add_lt_add_left hj 750) boundChunk75⟩)).all (checkFun ⟨750 + j, Nat.lt_trans (Nat.add_lt_add_left hj 750) boundChunk75⟩) = true ∧ linkFun ⟨750 + j, Nat.lt_trans (Nat.add_lt_add_left hj 750) boundChunk75⟩ = true := by
  decide +kernel

end BranchC.A2Check
