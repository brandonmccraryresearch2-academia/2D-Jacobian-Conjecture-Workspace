/- A2 tuple-check chunk 216b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk216b : (2165 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk216b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2165 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2165) boundChunk216b⟩)).all (checkFun ⟨2165 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2165) boundChunk216b⟩) = true ∧ linkFun ⟨2165 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2165) boundChunk216b⟩ = true := by
  decide +kernel

end BranchC.A2Check
