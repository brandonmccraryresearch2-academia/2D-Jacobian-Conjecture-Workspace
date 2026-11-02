/- A2 tuple-check chunk 311a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk311a2 : (3112 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk311a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3112 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3112) boundChunk311a2⟩)).all (checkFun ⟨3112 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3112) boundChunk311a2⟩) = true ∧ linkFun ⟨3112 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3112) boundChunk311a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
