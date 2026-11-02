/- A2 tuple-check chunk 178b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk178b : (1785 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk178b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1785 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1785) boundChunk178b⟩)).all (checkFun ⟨1785 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1785) boundChunk178b⟩) = true ∧ linkFun ⟨1785 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1785) boundChunk178b⟩ = true := by
  decide +kernel

end BranchC.A2Check
