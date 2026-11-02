/- A2 tuple-check chunk 80 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk80 : (800 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk80 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨800 + j, Nat.lt_trans (Nat.add_lt_add_left hj 800) boundChunk80⟩)).all (checkFun ⟨800 + j, Nat.lt_trans (Nat.add_lt_add_left hj 800) boundChunk80⟩) = true ∧ linkFun ⟨800 + j, Nat.lt_trans (Nat.add_lt_add_left hj 800) boundChunk80⟩ = true := by
  decide +kernel

end BranchC.A2Check
