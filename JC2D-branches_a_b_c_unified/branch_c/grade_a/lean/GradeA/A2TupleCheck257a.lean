/- A2 tuple-check chunk 257a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk257a : (2570 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk257a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2570 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2570) boundChunk257a⟩)).all (checkFun ⟨2570 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2570) boundChunk257a⟩) = true ∧ linkFun ⟨2570 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2570) boundChunk257a⟩ = true := by
  decide +kernel

end BranchC.A2Check
