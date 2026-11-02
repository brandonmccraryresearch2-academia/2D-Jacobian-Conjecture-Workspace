/- A2 tuple-check chunk 127a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk127a : (1270 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk127a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1270 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1270) boundChunk127a⟩)).all (checkFun ⟨1270 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1270) boundChunk127a⟩) = true ∧ linkFun ⟨1270 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1270) boundChunk127a⟩ = true := by
  decide +kernel

end BranchC.A2Check
