/- A2 tuple-check chunk 214b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk214b : (2145 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk214b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2145 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2145) boundChunk214b⟩)).all (checkFun ⟨2145 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2145) boundChunk214b⟩) = true ∧ linkFun ⟨2145 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2145) boundChunk214b⟩ = true := by
  decide +kernel

end BranchC.A2Check
