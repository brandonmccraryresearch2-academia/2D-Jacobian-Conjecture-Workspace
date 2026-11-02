/- A2 tuple-check chunk 198b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk198b : (1985 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk198b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1985 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1985) boundChunk198b⟩)).all (checkFun ⟨1985 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1985) boundChunk198b⟩) = true ∧ linkFun ⟨1985 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1985) boundChunk198b⟩ = true := by
  decide +kernel

end BranchC.A2Check
