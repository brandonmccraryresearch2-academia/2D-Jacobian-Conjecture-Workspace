/- A2 tuple-check chunk 163a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk163a : (1630 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk163a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1630 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1630) boundChunk163a⟩)).all (checkFun ⟨1630 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1630) boundChunk163a⟩) = true ∧ linkFun ⟨1630 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1630) boundChunk163a⟩ = true := by
  decide +kernel

end BranchC.A2Check
