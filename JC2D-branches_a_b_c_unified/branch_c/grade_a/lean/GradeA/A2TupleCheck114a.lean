/- A2 tuple-check chunk 114a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk114a : (1140 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk114a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1140 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1140) boundChunk114a⟩)).all (checkFun ⟨1140 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1140) boundChunk114a⟩) = true ∧ linkFun ⟨1140 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1140) boundChunk114a⟩ = true := by
  decide +kernel

end BranchC.A2Check
