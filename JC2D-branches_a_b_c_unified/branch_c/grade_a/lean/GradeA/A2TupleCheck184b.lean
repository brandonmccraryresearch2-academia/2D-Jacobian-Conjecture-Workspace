/- A2 tuple-check chunk 184b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk184b : (1845 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk184b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1845 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1845) boundChunk184b⟩)).all (checkFun ⟨1845 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1845) boundChunk184b⟩) = true ∧ linkFun ⟨1845 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1845) boundChunk184b⟩ = true := by
  decide +kernel

end BranchC.A2Check
