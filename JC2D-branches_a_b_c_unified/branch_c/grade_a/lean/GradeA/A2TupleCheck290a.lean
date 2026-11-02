/- A2 tuple-check chunk 290a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk290a : (2900 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk290a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2900 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2900) boundChunk290a⟩)).all (checkFun ⟨2900 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2900) boundChunk290a⟩) = true ∧ linkFun ⟨2900 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2900) boundChunk290a⟩ = true := by
  decide +kernel

end BranchC.A2Check
