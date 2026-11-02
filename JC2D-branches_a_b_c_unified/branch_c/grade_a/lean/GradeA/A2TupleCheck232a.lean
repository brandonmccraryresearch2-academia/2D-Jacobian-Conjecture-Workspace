/- A2 tuple-check chunk 232a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk232a : (2320 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk232a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2320 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2320) boundChunk232a⟩)).all (checkFun ⟨2320 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2320) boundChunk232a⟩) = true ∧ linkFun ⟨2320 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2320) boundChunk232a⟩ = true := by
  decide +kernel

end BranchC.A2Check
