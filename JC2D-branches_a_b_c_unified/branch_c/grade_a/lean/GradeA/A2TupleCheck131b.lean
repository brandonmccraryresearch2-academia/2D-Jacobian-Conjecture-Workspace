/- A2 tuple-check chunk 131b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk131b : (1315 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk131b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1315 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1315) boundChunk131b⟩)).all (checkFun ⟨1315 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1315) boundChunk131b⟩) = true ∧ linkFun ⟨1315 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1315) boundChunk131b⟩ = true := by
  decide +kernel

end BranchC.A2Check
