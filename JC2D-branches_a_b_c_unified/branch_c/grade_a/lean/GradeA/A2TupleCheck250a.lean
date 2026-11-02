/- A2 tuple-check chunk 250a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk250a : (2500 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk250a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2500 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2500) boundChunk250a⟩)).all (checkFun ⟨2500 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2500) boundChunk250a⟩) = true ∧ linkFun ⟨2500 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2500) boundChunk250a⟩ = true := by
  decide +kernel

end BranchC.A2Check
