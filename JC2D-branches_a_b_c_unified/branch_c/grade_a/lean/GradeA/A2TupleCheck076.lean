/- A2 tuple-check chunk 76 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk76 : (760 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk76 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨760 + j, Nat.lt_trans (Nat.add_lt_add_left hj 760) boundChunk76⟩)).all (checkFun ⟨760 + j, Nat.lt_trans (Nat.add_lt_add_left hj 760) boundChunk76⟩) = true ∧ linkFun ⟨760 + j, Nat.lt_trans (Nat.add_lt_add_left hj 760) boundChunk76⟩ = true := by
  decide +kernel

end BranchC.A2Check
