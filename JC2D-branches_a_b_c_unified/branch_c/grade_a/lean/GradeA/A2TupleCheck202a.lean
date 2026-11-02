/- A2 tuple-check chunk 202a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk202a : (2020 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk202a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2020 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2020) boundChunk202a⟩)).all (checkFun ⟨2020 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2020) boundChunk202a⟩) = true ∧ linkFun ⟨2020 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2020) boundChunk202a⟩ = true := by
  decide +kernel

end BranchC.A2Check
