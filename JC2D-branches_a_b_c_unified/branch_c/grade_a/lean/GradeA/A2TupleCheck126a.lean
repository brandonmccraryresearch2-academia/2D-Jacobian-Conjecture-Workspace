/- A2 tuple-check chunk 126a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk126a : (1260 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk126a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1260 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1260) boundChunk126a⟩)).all (checkFun ⟨1260 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1260) boundChunk126a⟩) = true ∧ linkFun ⟨1260 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1260) boundChunk126a⟩ = true := by
  decide +kernel

end BranchC.A2Check
