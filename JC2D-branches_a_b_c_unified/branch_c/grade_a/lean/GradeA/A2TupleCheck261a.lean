/- A2 tuple-check chunk 261a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk261a : (2610 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk261a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2610 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2610) boundChunk261a⟩)).all (checkFun ⟨2610 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2610) boundChunk261a⟩) = true ∧ linkFun ⟨2610 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2610) boundChunk261a⟩ = true := by
  decide +kernel

end BranchC.A2Check
