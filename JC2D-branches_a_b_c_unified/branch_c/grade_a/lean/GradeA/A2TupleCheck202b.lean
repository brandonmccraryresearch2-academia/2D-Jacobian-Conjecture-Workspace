/- A2 tuple-check chunk 202b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk202b : (2025 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk202b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2025 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2025) boundChunk202b⟩)).all (checkFun ⟨2025 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2025) boundChunk202b⟩) = true ∧ linkFun ⟨2025 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2025) boundChunk202b⟩ = true := by
  decide +kernel

end BranchC.A2Check
