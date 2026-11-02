/- A2 tuple-check chunk 227b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk227b : (2275 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk227b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2275 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2275) boundChunk227b⟩)).all (checkFun ⟨2275 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2275) boundChunk227b⟩) = true ∧ linkFun ⟨2275 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2275) boundChunk227b⟩ = true := by
  decide +kernel

end BranchC.A2Check
