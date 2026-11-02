/- A2 tuple-check chunk 127b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk127b : (1275 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk127b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1275 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1275) boundChunk127b⟩)).all (checkFun ⟨1275 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1275) boundChunk127b⟩) = true ∧ linkFun ⟨1275 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1275) boundChunk127b⟩ = true := by
  decide +kernel

end BranchC.A2Check
