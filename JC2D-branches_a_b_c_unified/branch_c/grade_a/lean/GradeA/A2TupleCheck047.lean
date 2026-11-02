/- A2 tuple-check chunk 47 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk47 : (470 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk47 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨470 + j, Nat.lt_trans (Nat.add_lt_add_left hj 470) boundChunk47⟩)).all (checkFun ⟨470 + j, Nat.lt_trans (Nat.add_lt_add_left hj 470) boundChunk47⟩) = true ∧ linkFun ⟨470 + j, Nat.lt_trans (Nat.add_lt_add_left hj 470) boundChunk47⟩ = true := by
  decide +kernel

end BranchC.A2Check
