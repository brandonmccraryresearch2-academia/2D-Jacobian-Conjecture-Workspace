/- A2 tuple-check chunk 116a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk116a : (1160 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk116a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1160 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1160) boundChunk116a⟩)).all (checkFun ⟨1160 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1160) boundChunk116a⟩) = true ∧ linkFun ⟨1160 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1160) boundChunk116a⟩ = true := by
  decide +kernel

end BranchC.A2Check
