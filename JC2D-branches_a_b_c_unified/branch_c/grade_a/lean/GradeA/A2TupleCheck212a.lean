/- A2 tuple-check chunk 212a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk212a : (2120 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk212a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2120) boundChunk212a⟩)).all (checkFun ⟨2120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2120) boundChunk212a⟩) = true ∧ linkFun ⟨2120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2120) boundChunk212a⟩ = true := by
  decide +kernel

end BranchC.A2Check
