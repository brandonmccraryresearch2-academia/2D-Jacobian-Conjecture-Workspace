/- A2 tuple-check chunk 182b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk182b : (1825 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk182b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1825 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1825) boundChunk182b⟩)).all (checkFun ⟨1825 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1825) boundChunk182b⟩) = true ∧ linkFun ⟨1825 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1825) boundChunk182b⟩ = true := by
  decide +kernel

end BranchC.A2Check
