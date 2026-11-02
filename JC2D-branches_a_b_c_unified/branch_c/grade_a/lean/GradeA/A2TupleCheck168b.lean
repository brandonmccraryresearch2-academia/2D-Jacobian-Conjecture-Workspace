/- A2 tuple-check chunk 168b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk168b : (1685 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk168b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1685 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1685) boundChunk168b⟩)).all (checkFun ⟨1685 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1685) boundChunk168b⟩) = true ∧ linkFun ⟨1685 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1685) boundChunk168b⟩ = true := by
  decide +kernel

end BranchC.A2Check
