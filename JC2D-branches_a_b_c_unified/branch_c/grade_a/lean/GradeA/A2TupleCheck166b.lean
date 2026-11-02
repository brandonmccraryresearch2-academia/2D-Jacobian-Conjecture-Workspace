/- A2 tuple-check chunk 166b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk166b : (1665 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk166b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1665 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1665) boundChunk166b⟩)).all (checkFun ⟨1665 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1665) boundChunk166b⟩) = true ∧ linkFun ⟨1665 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1665) boundChunk166b⟩ = true := by
  decide +kernel

end BranchC.A2Check
