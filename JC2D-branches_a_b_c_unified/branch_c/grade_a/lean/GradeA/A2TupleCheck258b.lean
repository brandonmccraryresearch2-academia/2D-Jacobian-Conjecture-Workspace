/- A2 tuple-check chunk 258b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk258b : (2585 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk258b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2585 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2585) boundChunk258b⟩)).all (checkFun ⟨2585 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2585) boundChunk258b⟩) = true ∧ linkFun ⟨2585 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2585) boundChunk258b⟩ = true := by
  decide +kernel

end BranchC.A2Check
