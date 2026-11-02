/- A2 tuple-check chunk 187a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk187a : (1870 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk187a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1870 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1870) boundChunk187a⟩)).all (checkFun ⟨1870 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1870) boundChunk187a⟩) = true ∧ linkFun ⟨1870 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1870) boundChunk187a⟩ = true := by
  decide +kernel

end BranchC.A2Check
