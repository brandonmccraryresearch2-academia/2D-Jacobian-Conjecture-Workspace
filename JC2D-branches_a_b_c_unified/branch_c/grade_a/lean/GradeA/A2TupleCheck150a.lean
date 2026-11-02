/- A2 tuple-check chunk 150a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk150a : (1500 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk150a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1500 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1500) boundChunk150a⟩)).all (checkFun ⟨1500 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1500) boundChunk150a⟩) = true ∧ linkFun ⟨1500 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1500) boundChunk150a⟩ = true := by
  decide +kernel

end BranchC.A2Check
