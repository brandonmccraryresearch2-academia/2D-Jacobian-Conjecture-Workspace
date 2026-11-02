/- A2 tuple-check chunk 54 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk54 : (540 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk54 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨540 + j, Nat.lt_trans (Nat.add_lt_add_left hj 540) boundChunk54⟩)).all (checkFun ⟨540 + j, Nat.lt_trans (Nat.add_lt_add_left hj 540) boundChunk54⟩) = true ∧ linkFun ⟨540 + j, Nat.lt_trans (Nat.add_lt_add_left hj 540) boundChunk54⟩ = true := by
  decide +kernel

end BranchC.A2Check
