/- A2 tuple-check chunk 177b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk177b : (1775 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk177b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1775 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1775) boundChunk177b⟩)).all (checkFun ⟨1775 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1775) boundChunk177b⟩) = true ∧ linkFun ⟨1775 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1775) boundChunk177b⟩ = true := by
  decide +kernel

end BranchC.A2Check
