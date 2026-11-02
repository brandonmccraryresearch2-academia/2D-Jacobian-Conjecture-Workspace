/- A2 tuple-check chunk 229a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk229a : (2290 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk229a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2290 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2290) boundChunk229a⟩)).all (checkFun ⟨2290 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2290) boundChunk229a⟩) = true ∧ linkFun ⟨2290 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2290) boundChunk229a⟩ = true := by
  decide +kernel

end BranchC.A2Check
