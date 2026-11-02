/- A2 tuple-check chunk 257b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk257b : (2575 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk257b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2575 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2575) boundChunk257b⟩)).all (checkFun ⟨2575 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2575) boundChunk257b⟩) = true ∧ linkFun ⟨2575 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2575) boundChunk257b⟩ = true := by
  decide +kernel

end BranchC.A2Check
