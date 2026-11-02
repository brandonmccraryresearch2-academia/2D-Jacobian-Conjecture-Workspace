/- A2 tuple-check chunk 245a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk245a : (2450 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk245a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2450 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2450) boundChunk245a⟩)).all (checkFun ⟨2450 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2450) boundChunk245a⟩) = true ∧ linkFun ⟨2450 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2450) boundChunk245a⟩ = true := by
  decide +kernel

end BranchC.A2Check
