/- A2 tuple-check chunk 152a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk152a : (1520 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk152a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1520 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1520) boundChunk152a⟩)).all (checkFun ⟨1520 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1520) boundChunk152a⟩) = true ∧ linkFun ⟨1520 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1520) boundChunk152a⟩ = true := by
  decide +kernel

end BranchC.A2Check
