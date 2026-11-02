/- A2 tuple-check chunk 303a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk303a2 : (3032 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk303a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3032 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3032) boundChunk303a2⟩)).all (checkFun ⟨3032 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3032) boundChunk303a2⟩) = true ∧ linkFun ⟨3032 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3032) boundChunk303a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
