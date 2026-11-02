/- A2 tuple-check chunk 10 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk10 : (100 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk10 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 100) boundChunk10⟩)).all (checkFun ⟨100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 100) boundChunk10⟩) = true ∧ linkFun ⟨100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 100) boundChunk10⟩ = true := by
  decide +kernel

end BranchC.A2Check
