/- A2 tuple-check chunk 281a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk281a1 : (2810 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk281a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2810 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2810) boundChunk281a1⟩)).all (checkFun ⟨2810 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2810) boundChunk281a1⟩) = true ∧ linkFun ⟨2810 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2810) boundChunk281a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
