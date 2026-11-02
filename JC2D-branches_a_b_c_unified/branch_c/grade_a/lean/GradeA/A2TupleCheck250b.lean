/- A2 tuple-check chunk 250b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk250b : (2505 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk250b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2505 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2505) boundChunk250b⟩)).all (checkFun ⟨2505 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2505) boundChunk250b⟩) = true ∧ linkFun ⟨2505 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2505) boundChunk250b⟩ = true := by
  decide +kernel

end BranchC.A2Check
