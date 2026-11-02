/- A2 tuple-check chunk 69 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk69 : (690 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk69 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨690 + j, Nat.lt_trans (Nat.add_lt_add_left hj 690) boundChunk69⟩)).all (checkFun ⟨690 + j, Nat.lt_trans (Nat.add_lt_add_left hj 690) boundChunk69⟩) = true ∧ linkFun ⟨690 + j, Nat.lt_trans (Nat.add_lt_add_left hj 690) boundChunk69⟩ = true := by
  decide +kernel

end BranchC.A2Check
