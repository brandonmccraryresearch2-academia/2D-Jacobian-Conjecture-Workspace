/- A2 tuple-check chunk 139a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk139a : (1390 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk139a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1390 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1390) boundChunk139a⟩)).all (checkFun ⟨1390 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1390) boundChunk139a⟩) = true ∧ linkFun ⟨1390 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1390) boundChunk139a⟩ = true := by
  decide +kernel

end BranchC.A2Check
