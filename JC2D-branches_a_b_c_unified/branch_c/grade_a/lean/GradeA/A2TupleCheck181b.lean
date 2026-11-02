/- A2 tuple-check chunk 181b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk181b : (1815 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk181b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1815 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1815) boundChunk181b⟩)).all (checkFun ⟨1815 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1815) boundChunk181b⟩) = true ∧ linkFun ⟨1815 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1815) boundChunk181b⟩ = true := by
  decide +kernel

end BranchC.A2Check
