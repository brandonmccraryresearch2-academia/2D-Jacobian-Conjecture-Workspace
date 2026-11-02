/- A2 tuple-check chunk 131a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk131a : (1310 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk131a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1310 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1310) boundChunk131a⟩)).all (checkFun ⟨1310 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1310) boundChunk131a⟩) = true ∧ linkFun ⟨1310 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1310) boundChunk131a⟩ = true := by
  decide +kernel

end BranchC.A2Check
