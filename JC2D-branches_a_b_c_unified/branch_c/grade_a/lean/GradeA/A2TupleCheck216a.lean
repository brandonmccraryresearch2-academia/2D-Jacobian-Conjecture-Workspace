/- A2 tuple-check chunk 216a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk216a : (2160 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk216a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2160 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2160) boundChunk216a⟩)).all (checkFun ⟨2160 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2160) boundChunk216a⟩) = true ∧ linkFun ⟨2160 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2160) boundChunk216a⟩ = true := by
  decide +kernel

end BranchC.A2Check
