/- A2 tuple-check chunk 183a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk183a : (1830 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk183a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1830 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1830) boundChunk183a⟩)).all (checkFun ⟨1830 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1830) boundChunk183a⟩) = true ∧ linkFun ⟨1830 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1830) boundChunk183a⟩ = true := by
  decide +kernel

end BranchC.A2Check
