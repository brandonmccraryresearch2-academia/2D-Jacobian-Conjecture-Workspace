/- A2 tuple-check chunk 212b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk212b : (2125 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk212b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2125 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2125) boundChunk212b⟩)).all (checkFun ⟨2125 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2125) boundChunk212b⟩) = true ∧ linkFun ⟨2125 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2125) boundChunk212b⟩ = true := by
  decide +kernel

end BranchC.A2Check
