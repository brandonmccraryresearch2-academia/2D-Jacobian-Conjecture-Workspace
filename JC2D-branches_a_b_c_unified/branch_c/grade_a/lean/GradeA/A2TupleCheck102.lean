/- A2 tuple-check chunk 102 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk102 : (1020 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk102 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨1020 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1020) boundChunk102⟩)).all (checkFun ⟨1020 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1020) boundChunk102⟩) = true ∧ linkFun ⟨1020 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1020) boundChunk102⟩ = true := by
  decide +kernel

end BranchC.A2Check
