/- A2 tuple-check chunk 122a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk122a : (1220 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk122a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1220 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1220) boundChunk122a⟩)).all (checkFun ⟨1220 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1220) boundChunk122a⟩) = true ∧ linkFun ⟨1220 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1220) boundChunk122a⟩ = true := by
  decide +kernel

end BranchC.A2Check
