/- A2 tuple-check chunk 173b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk173b : (1735 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk173b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1735 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1735) boundChunk173b⟩)).all (checkFun ⟨1735 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1735) boundChunk173b⟩) = true ∧ linkFun ⟨1735 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1735) boundChunk173b⟩ = true := by
  decide +kernel

end BranchC.A2Check
