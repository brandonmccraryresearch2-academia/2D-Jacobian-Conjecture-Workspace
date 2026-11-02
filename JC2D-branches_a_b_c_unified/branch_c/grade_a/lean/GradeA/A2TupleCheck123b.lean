/- A2 tuple-check chunk 123b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk123b : (1235 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk123b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1235 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1235) boundChunk123b⟩)).all (checkFun ⟨1235 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1235) boundChunk123b⟩) = true ∧ linkFun ⟨1235 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1235) boundChunk123b⟩ = true := by
  decide +kernel

end BranchC.A2Check
