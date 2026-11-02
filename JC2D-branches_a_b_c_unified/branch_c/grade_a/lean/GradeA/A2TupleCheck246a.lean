/- A2 tuple-check chunk 246a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk246a : (2460 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk246a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2460 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2460) boundChunk246a⟩)).all (checkFun ⟨2460 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2460) boundChunk246a⟩) = true ∧ linkFun ⟨2460 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2460) boundChunk246a⟩ = true := by
  decide +kernel

end BranchC.A2Check
