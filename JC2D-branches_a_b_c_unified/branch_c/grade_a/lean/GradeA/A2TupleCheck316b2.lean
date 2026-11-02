/- A2 tuple-check chunk 316b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk316b2 : (3167 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk316b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3167 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3167) boundChunk316b2⟩)).all (checkFun ⟨3167 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3167) boundChunk316b2⟩) = true ∧ linkFun ⟨3167 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3167) boundChunk316b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
