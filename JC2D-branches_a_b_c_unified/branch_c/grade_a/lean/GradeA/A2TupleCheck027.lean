/- A2 tuple-check chunk 27 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk27 : (270 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk27 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨270 + j, Nat.lt_trans (Nat.add_lt_add_left hj 270) boundChunk27⟩)).all (checkFun ⟨270 + j, Nat.lt_trans (Nat.add_lt_add_left hj 270) boundChunk27⟩) = true ∧ linkFun ⟨270 + j, Nat.lt_trans (Nat.add_lt_add_left hj 270) boundChunk27⟩ = true := by
  decide +kernel

end BranchC.A2Check
