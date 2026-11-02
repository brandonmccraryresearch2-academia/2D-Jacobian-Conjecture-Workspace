/- A2 tuple-check chunk 140b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk140b : (1405 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk140b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1405 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1405) boundChunk140b⟩)).all (checkFun ⟨1405 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1405) boundChunk140b⟩) = true ∧ linkFun ⟨1405 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1405) boundChunk140b⟩ = true := by
  decide +kernel

end BranchC.A2Check
