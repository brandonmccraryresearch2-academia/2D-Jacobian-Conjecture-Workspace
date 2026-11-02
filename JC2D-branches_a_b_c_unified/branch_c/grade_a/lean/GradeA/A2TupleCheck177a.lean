/- A2 tuple-check chunk 177a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk177a : (1770 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk177a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1770 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1770) boundChunk177a⟩)).all (checkFun ⟨1770 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1770) boundChunk177a⟩) = true ∧ linkFun ⟨1770 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1770) boundChunk177a⟩ = true := by
  decide +kernel

end BranchC.A2Check
