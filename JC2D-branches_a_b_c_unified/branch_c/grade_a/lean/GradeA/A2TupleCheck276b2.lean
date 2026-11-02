/- A2 tuple-check chunk 276b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk276b2 : (2767 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk276b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2767 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2767) boundChunk276b2⟩)).all (checkFun ⟨2767 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2767) boundChunk276b2⟩) = true ∧ linkFun ⟨2767 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2767) boundChunk276b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
