/- A2 tuple-check chunk 308b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk308b2 : (3087 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk308b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3087 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3087) boundChunk308b2⟩)).all (checkFun ⟨3087 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3087) boundChunk308b2⟩) = true ∧ linkFun ⟨3087 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3087) boundChunk308b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
