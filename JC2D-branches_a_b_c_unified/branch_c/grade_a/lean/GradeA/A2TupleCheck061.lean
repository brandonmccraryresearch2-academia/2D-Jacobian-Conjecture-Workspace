/- A2 tuple-check chunk 61 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk61 : (610 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk61 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨610 + j, Nat.lt_trans (Nat.add_lt_add_left hj 610) boundChunk61⟩)).all (checkFun ⟨610 + j, Nat.lt_trans (Nat.add_lt_add_left hj 610) boundChunk61⟩) = true ∧ linkFun ⟨610 + j, Nat.lt_trans (Nat.add_lt_add_left hj 610) boundChunk61⟩ = true := by
  decide +kernel

end BranchC.A2Check
