/- A2 tuple-check chunk 185b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk185b : (1855 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk185b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1855 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1855) boundChunk185b⟩)).all (checkFun ⟨1855 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1855) boundChunk185b⟩) = true ∧ linkFun ⟨1855 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1855) boundChunk185b⟩ = true := by
  decide +kernel

end BranchC.A2Check
