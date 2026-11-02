/- A2 tuple-check chunk 217b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk217b : (2175 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk217b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2175 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2175) boundChunk217b⟩)).all (checkFun ⟨2175 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2175) boundChunk217b⟩) = true ∧ linkFun ⟨2175 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2175) boundChunk217b⟩ = true := by
  decide +kernel

end BranchC.A2Check
