/- A2 tuple-check chunk 227a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk227a : (2270 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk227a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2270 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2270) boundChunk227a⟩)).all (checkFun ⟨2270 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2270) boundChunk227a⟩) = true ∧ linkFun ⟨2270 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2270) boundChunk227a⟩ = true := by
  decide +kernel

end BranchC.A2Check
