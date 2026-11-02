/- A2 tuple-check chunk 141b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk141b : (1415 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk141b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1415 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1415) boundChunk141b⟩)).all (checkFun ⟨1415 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1415) boundChunk141b⟩) = true ∧ linkFun ⟨1415 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1415) boundChunk141b⟩ = true := by
  decide +kernel

end BranchC.A2Check
