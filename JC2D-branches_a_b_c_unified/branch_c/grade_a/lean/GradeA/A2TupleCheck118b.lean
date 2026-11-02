/- A2 tuple-check chunk 118b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk118b : (1185 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk118b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1185 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1185) boundChunk118b⟩)).all (checkFun ⟨1185 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1185) boundChunk118b⟩) = true ∧ linkFun ⟨1185 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1185) boundChunk118b⟩ = true := by
  decide +kernel

end BranchC.A2Check
