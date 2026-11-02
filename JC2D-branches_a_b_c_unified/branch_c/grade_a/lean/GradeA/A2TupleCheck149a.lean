/- A2 tuple-check chunk 149a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk149a : (1490 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk149a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1490 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1490) boundChunk149a⟩)).all (checkFun ⟨1490 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1490) boundChunk149a⟩) = true ∧ linkFun ⟨1490 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1490) boundChunk149a⟩ = true := by
  decide +kernel

end BranchC.A2Check
