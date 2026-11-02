/- A2 tuple-check chunk 157a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk157a : (1570 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk157a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1570 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1570) boundChunk157a⟩)).all (checkFun ⟨1570 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1570) boundChunk157a⟩) = true ∧ linkFun ⟨1570 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1570) boundChunk157a⟩ = true := by
  decide +kernel

end BranchC.A2Check
