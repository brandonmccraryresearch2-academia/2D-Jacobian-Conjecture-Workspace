/- A2 tuple-check chunk 161b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk161b : (1615 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk161b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1615 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1615) boundChunk161b⟩)).all (checkFun ⟨1615 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1615) boundChunk161b⟩) = true ∧ linkFun ⟨1615 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1615) boundChunk161b⟩ = true := by
  decide +kernel

end BranchC.A2Check
