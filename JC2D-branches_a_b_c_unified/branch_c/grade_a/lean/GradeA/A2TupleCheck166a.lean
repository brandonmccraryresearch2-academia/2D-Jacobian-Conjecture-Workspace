/- A2 tuple-check chunk 166a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk166a : (1660 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk166a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1660 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1660) boundChunk166a⟩)).all (checkFun ⟨1660 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1660) boundChunk166a⟩) = true ∧ linkFun ⟨1660 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1660) boundChunk166a⟩ = true := by
  decide +kernel

end BranchC.A2Check
