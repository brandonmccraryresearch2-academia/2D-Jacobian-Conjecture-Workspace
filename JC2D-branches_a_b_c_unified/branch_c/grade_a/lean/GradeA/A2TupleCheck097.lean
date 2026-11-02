/- A2 tuple-check chunk 97 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk97 : (970 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk97 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨970 + j, Nat.lt_trans (Nat.add_lt_add_left hj 970) boundChunk97⟩)).all (checkFun ⟨970 + j, Nat.lt_trans (Nat.add_lt_add_left hj 970) boundChunk97⟩) = true ∧ linkFun ⟨970 + j, Nat.lt_trans (Nat.add_lt_add_left hj 970) boundChunk97⟩ = true := by
  decide +kernel

end BranchC.A2Check
