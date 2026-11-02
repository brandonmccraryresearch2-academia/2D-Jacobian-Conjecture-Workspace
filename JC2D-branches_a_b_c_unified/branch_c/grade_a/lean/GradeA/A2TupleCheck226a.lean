/- A2 tuple-check chunk 226a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk226a : (2260 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk226a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2260 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2260) boundChunk226a⟩)).all (checkFun ⟨2260 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2260) boundChunk226a⟩) = true ∧ linkFun ⟨2260 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2260) boundChunk226a⟩ = true := by
  decide +kernel

end BranchC.A2Check
