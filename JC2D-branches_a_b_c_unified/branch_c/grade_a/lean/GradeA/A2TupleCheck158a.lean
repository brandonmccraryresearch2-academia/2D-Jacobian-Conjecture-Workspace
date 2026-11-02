/- A2 tuple-check chunk 158a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk158a : (1580 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk158a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1580 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1580) boundChunk158a⟩)).all (checkFun ⟨1580 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1580) boundChunk158a⟩) = true ∧ linkFun ⟨1580 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1580) boundChunk158a⟩ = true := by
  decide +kernel

end BranchC.A2Check
