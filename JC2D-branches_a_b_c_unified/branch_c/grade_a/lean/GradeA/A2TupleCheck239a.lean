/- A2 tuple-check chunk 239a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk239a : (2390 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk239a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2390 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2390) boundChunk239a⟩)).all (checkFun ⟨2390 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2390) boundChunk239a⟩) = true ∧ linkFun ⟨2390 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2390) boundChunk239a⟩ = true := by
  decide +kernel

end BranchC.A2Check
