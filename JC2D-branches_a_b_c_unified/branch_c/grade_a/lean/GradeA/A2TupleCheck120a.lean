/- A2 tuple-check chunk 120a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk120a : (1200 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk120a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1200 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1200) boundChunk120a⟩)).all (checkFun ⟨1200 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1200) boundChunk120a⟩) = true ∧ linkFun ⟨1200 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1200) boundChunk120a⟩ = true := by
  decide +kernel

end BranchC.A2Check
