/- A2 tuple-check chunk 163b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk163b : (1635 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk163b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1635 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1635) boundChunk163b⟩)).all (checkFun ⟨1635 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1635) boundChunk163b⟩) = true ∧ linkFun ⟨1635 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1635) boundChunk163b⟩ = true := by
  decide +kernel

end BranchC.A2Check
