/- A2 tuple-check chunk 182a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk182a : (1820 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk182a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1820 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1820) boundChunk182a⟩)).all (checkFun ⟨1820 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1820) boundChunk182a⟩) = true ∧ linkFun ⟨1820 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1820) boundChunk182a⟩ = true := by
  decide +kernel

end BranchC.A2Check
