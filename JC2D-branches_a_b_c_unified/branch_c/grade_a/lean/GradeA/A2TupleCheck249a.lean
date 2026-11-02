/- A2 tuple-check chunk 249a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk249a : (2490 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk249a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2490 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2490) boundChunk249a⟩)).all (checkFun ⟨2490 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2490) boundChunk249a⟩) = true ∧ linkFun ⟨2490 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2490) boundChunk249a⟩ = true := by
  decide +kernel

end BranchC.A2Check
