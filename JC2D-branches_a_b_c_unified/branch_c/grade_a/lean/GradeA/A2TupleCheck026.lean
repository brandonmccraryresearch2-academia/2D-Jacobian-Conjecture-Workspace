/- A2 tuple-check chunk 26 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk26 : (260 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk26 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨260 + j, Nat.lt_trans (Nat.add_lt_add_left hj 260) boundChunk26⟩)).all (checkFun ⟨260 + j, Nat.lt_trans (Nat.add_lt_add_left hj 260) boundChunk26⟩) = true ∧ linkFun ⟨260 + j, Nat.lt_trans (Nat.add_lt_add_left hj 260) boundChunk26⟩ = true := by
  decide +kernel

end BranchC.A2Check
