/- A2 tuple-check chunk 78 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk78 : (780 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk78 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨780 + j, Nat.lt_trans (Nat.add_lt_add_left hj 780) boundChunk78⟩)).all (checkFun ⟨780 + j, Nat.lt_trans (Nat.add_lt_add_left hj 780) boundChunk78⟩) = true ∧ linkFun ⟨780 + j, Nat.lt_trans (Nat.add_lt_add_left hj 780) boundChunk78⟩ = true := by
  decide +kernel

end BranchC.A2Check
