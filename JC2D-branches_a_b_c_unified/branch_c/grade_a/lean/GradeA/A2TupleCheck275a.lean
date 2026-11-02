/- A2 tuple-check chunk 275a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk275a : (2750 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk275a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2750 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2750) boundChunk275a⟩)).all (checkFun ⟨2750 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2750) boundChunk275a⟩) = true ∧ linkFun ⟨2750 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2750) boundChunk275a⟩ = true := by
  decide +kernel

end BranchC.A2Check
