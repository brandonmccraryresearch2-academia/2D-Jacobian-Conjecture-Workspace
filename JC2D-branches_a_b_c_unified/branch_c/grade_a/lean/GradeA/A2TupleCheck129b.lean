/- A2 tuple-check chunk 129b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk129b : (1295 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk129b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1295 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1295) boundChunk129b⟩)).all (checkFun ⟨1295 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1295) boundChunk129b⟩) = true ∧ linkFun ⟨1295 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1295) boundChunk129b⟩ = true := by
  decide +kernel

end BranchC.A2Check
