/- A2 tuple-check chunk 286a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk286a2 : (2862 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk286a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2862 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2862) boundChunk286a2⟩)).all (checkFun ⟨2862 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2862) boundChunk286a2⟩) = true ∧ linkFun ⟨2862 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2862) boundChunk286a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
