/- A2 tuple-check chunk 268b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk268b2 : (2687 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk268b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2687 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2687) boundChunk268b2⟩)).all (checkFun ⟨2687 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2687) boundChunk268b2⟩) = true ∧ linkFun ⟨2687 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2687) boundChunk268b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
