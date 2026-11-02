/- A2 tuple-check chunk 165b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk165b : (1655 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk165b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1655 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1655) boundChunk165b⟩)).all (checkFun ⟨1655 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1655) boundChunk165b⟩) = true ∧ linkFun ⟨1655 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1655) boundChunk165b⟩ = true := by
  decide +kernel

end BranchC.A2Check
