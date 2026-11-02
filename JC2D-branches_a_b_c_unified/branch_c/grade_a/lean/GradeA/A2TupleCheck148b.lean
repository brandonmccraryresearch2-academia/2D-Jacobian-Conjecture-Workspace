/- A2 tuple-check chunk 148b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk148b : (1485 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk148b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1485 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1485) boundChunk148b⟩)).all (checkFun ⟨1485 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1485) boundChunk148b⟩) = true ∧ linkFun ⟨1485 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1485) boundChunk148b⟩ = true := by
  decide +kernel

end BranchC.A2Check
