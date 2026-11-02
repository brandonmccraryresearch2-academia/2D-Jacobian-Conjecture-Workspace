/- A2 tuple-check chunk 121a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk121a : (1210 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk121a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1210 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1210) boundChunk121a⟩)).all (checkFun ⟨1210 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1210) boundChunk121a⟩) = true ∧ linkFun ⟨1210 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1210) boundChunk121a⟩ = true := by
  decide +kernel

end BranchC.A2Check
