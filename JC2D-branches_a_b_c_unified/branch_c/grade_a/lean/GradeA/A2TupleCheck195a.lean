/- A2 tuple-check chunk 195a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk195a : (1950 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk195a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1950 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1950) boundChunk195a⟩)).all (checkFun ⟨1950 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1950) boundChunk195a⟩) = true ∧ linkFun ⟨1950 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1950) boundChunk195a⟩ = true := by
  decide +kernel

end BranchC.A2Check
