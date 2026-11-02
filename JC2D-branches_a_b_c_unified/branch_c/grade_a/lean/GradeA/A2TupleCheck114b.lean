/- A2 tuple-check chunk 114b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk114b : (1145 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk114b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1145 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1145) boundChunk114b⟩)).all (checkFun ⟨1145 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1145) boundChunk114b⟩) = true ∧ linkFun ⟨1145 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1145) boundChunk114b⟩ = true := by
  decide +kernel

end BranchC.A2Check
