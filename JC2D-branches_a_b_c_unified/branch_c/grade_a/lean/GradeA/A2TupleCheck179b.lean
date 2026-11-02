/- A2 tuple-check chunk 179b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk179b : (1795 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk179b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1795 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1795) boundChunk179b⟩)).all (checkFun ⟨1795 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1795) boundChunk179b⟩) = true ∧ linkFun ⟨1795 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1795) boundChunk179b⟩ = true := by
  decide +kernel

end BranchC.A2Check
