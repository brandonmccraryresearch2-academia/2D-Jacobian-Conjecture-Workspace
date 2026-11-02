/- A2 tuple-check chunk 176b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk176b : (1765 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk176b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1765 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1765) boundChunk176b⟩)).all (checkFun ⟨1765 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1765) boundChunk176b⟩) = true ∧ linkFun ⟨1765 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1765) boundChunk176b⟩ = true := by
  decide +kernel

end BranchC.A2Check
