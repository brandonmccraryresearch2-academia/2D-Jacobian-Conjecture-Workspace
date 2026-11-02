/- A2 tuple-check chunk 91 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk91 : (910 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk91 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨910 + j, Nat.lt_trans (Nat.add_lt_add_left hj 910) boundChunk91⟩)).all (checkFun ⟨910 + j, Nat.lt_trans (Nat.add_lt_add_left hj 910) boundChunk91⟩) = true ∧ linkFun ⟨910 + j, Nat.lt_trans (Nat.add_lt_add_left hj 910) boundChunk91⟩ = true := by
  decide +kernel

end BranchC.A2Check
