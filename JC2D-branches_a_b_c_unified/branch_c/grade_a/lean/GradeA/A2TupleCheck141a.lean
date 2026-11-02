/- A2 tuple-check chunk 141a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk141a : (1410 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk141a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1410 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1410) boundChunk141a⟩)).all (checkFun ⟨1410 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1410) boundChunk141a⟩) = true ∧ linkFun ⟨1410 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1410) boundChunk141a⟩ = true := by
  decide +kernel

end BranchC.A2Check
