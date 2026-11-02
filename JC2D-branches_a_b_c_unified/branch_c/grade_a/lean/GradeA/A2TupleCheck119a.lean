/- A2 tuple-check chunk 119a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk119a : (1190 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk119a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1190 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1190) boundChunk119a⟩)).all (checkFun ⟨1190 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1190) boundChunk119a⟩) = true ∧ linkFun ⟨1190 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1190) boundChunk119a⟩ = true := by
  decide +kernel

end BranchC.A2Check
