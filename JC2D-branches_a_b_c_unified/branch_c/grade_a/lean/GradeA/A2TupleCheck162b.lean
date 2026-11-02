/- A2 tuple-check chunk 162b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk162b : (1625 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk162b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1625 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1625) boundChunk162b⟩)).all (checkFun ⟨1625 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1625) boundChunk162b⟩) = true ∧ linkFun ⟨1625 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1625) boundChunk162b⟩ = true := by
  decide +kernel

end BranchC.A2Check
