/- A1 dispatch lemmas, core-Lean only (no Mathlib import).

    The six kernel re-checks over `Fin 3199` from `A1Instantiation.lean`,
    isolated here so the giant `decide +kernel` evaluations run in a process
    without Mathlib's environment loaded. If this file compiles, the
    instantiation file becomes a Mathlib assembly that imports this module
    and never evaluates the dispatch lemmas itself. If this file OOMs, the
    lemmas get chunked by column range (400 columns each, as in A1Data).
-/

import RCCommon
import A1Data
import MaskLemma

set_option exponentiation.threshold 200000
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A1Inst

open BranchC.A1Data

/-- The (coefficient, packed column) terms for pivot column n. -/
noncomputable def termsFunNat (n : Nat) : List (Nat × Nat) :=
  (colDataNat n).map (fun p => (p.2, CpkFunNat p.1))

theorem colThm : ∀ j : Fin 3199,
    BranchC.RankCheck.colOK j.val (XSumNat j.val) = true := by
  decide +kernel

theorem slotThm : ∀ i : Fin 3199,
    BranchC.RankCheck.slotOK (CpkFunNat i.val) = true := by
  decide +kernel

theorem coeff_bound : ∀ j : Fin 3199, ∀ t ∈ colDataNat j.val, t.2 < 32003 := by
  decide +kernel

theorem length_bound : ∀ j : Fin 3199, (colDataNat j.val).length ≤ 52 := by
  decide +kernel

theorem row_bound : ∀ j : Fin 3199, ∀ t ∈ colDataNat j.val, t.1 < 3199 := by
  decide +kernel

theorem hX_all : ∀ j : Fin 3199,
    ((termsFunNat j.val).map (fun t => t.1 * t.2)).sum = XSumNat j.val := by
  decide +kernel

end BranchC.A1Inst
