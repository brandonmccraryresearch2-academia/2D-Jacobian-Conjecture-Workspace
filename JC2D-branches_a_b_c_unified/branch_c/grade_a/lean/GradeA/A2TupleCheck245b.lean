/- A2 tuple-check chunk 245b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk245b : (2455 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk245b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2455 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2455) boundChunk245b⟩)).all (checkFun ⟨2455 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2455) boundChunk245b⟩) = true ∧ linkFun ⟨2455 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2455) boundChunk245b⟩ = true := by
  decide +kernel

end BranchC.A2Check
