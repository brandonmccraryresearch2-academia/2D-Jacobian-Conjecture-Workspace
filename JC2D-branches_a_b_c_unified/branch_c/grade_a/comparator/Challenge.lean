import GradeA.Chart.Main
import GradeA.Chart.Poly
import GradeA.Macaulay
import GradeA.IrreducibleR
import Jacobian.BranchC.T1Zero.Combine

/-!
# Comparator challenge — branch (c), `ChartEmptyC_T1ne0` and deliverables A1/A2

PROTOTYPE (2026-10-21), modelled on the Comparator pattern of the openai/math
release (`lean/ComparatorChallenges/*.json` + statement-only challenge modules):
the declarations in this file are the *pinned statements*. A solution is any
module that proves exactly these statements (same names, same types) depending
only on the permitted axioms `propext`, `Classical.choice`, `Quot.sound`
(see `comparator.json`). Nothing in this file is a proof: the two `theorem`
pins are closed by `sorry` on purpose, and the `def`s are the two deliverables
stated as `Prop`s.

Pinned here:

* `challenge_target` — the grade-A goal itself: `ChartEmptyC_T1ne0 L` for
  every field `L` of characteristic 0, with no hypotheses. (Today this is
  grade B: it is exactly what A1/A2, fed through the interface, will give.)
* `challenge_interface` — the statement of
  `chartEmptyC_T1ne0_of_certificate` (`GradeA/Chart/Assembly.lean`), copied
  verbatim. A solution already exists (Assembly.lean itself), so this pin is
  the harness's reference/worked example.
* `A1_statement`, `A2_statement` — the two outstanding finite deliverables as
  standalone `Prop`s, with types verbatim the hypotheses `hA1`, `hA2` of the
  interface. A solution for A1 (resp. A2) is a term of `A1_statement` (resp.
  `A2_statement`) at the concrete data of `rank_lemma_check/`
  (`p = 32003`, `w₀ = 11147`, `ρ = Fin 3199`, the 3199 row monomials, pivot
  columns and support of the rank check, `MS`, `Cinv`, `scale` supplied by
  certgen). Those concrete data are not yet in Lean form; supplying them is
  the remaining work, and it does not change anything pinned here.

`Fpoly` is copied verbatim from `GradeA/Chart/Assembly.lean` (which defines
it) so that this challenge does not import its own solution module — the same
self-contained-definitions pattern as the openai/math challenge files. If
`Fpoly` is ever factored into `GradeA/Chart/Poly.lean`, delete the copy here
and import it instead; the pins do not change.
-/

namespace BranchC.GradeA.Comparator

open Lean.Grind.CommRing BranchAb.ChartProof Polynomial Matrix

/-- The six chart generators as polynomials over `ℤ[X]` (order Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃).
Verbatim copy of the definition in `GradeA/Chart/Assembly.lean`. -/
noncomputable def Fpoly : Fin 6 → MvPolynomial (Fin 5) ℤ[X]
  | 0 => polyOfTerms tl_Psi
  | 1 => polyOfTerms tl_Phi1
  | 2 => polyOfTerms tl_Phi2
  | 3 => polyOfTerms tl_Theta1
  | 4 => polyOfTerms tl_Theta2
  | 5 => polyOfTerms tl_Theta3

/-- **Deliverable A1, as a pinned statement.** For the concrete rank-check data
this is the packed kernel check `C · M_S = I` over `ZMod 32003`. The type is
verbatim the hypothesis `hA1` of `chartEmptyC_T1ne0_of_certificate`. -/
def A1_statement {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {p : ℕ} [Fact p.Prime]
    (MS Cinv : Matrix ρ ρ (ZMod p)) : Prop :=
  Cinv * MS = 1

/-- **Deliverable A2, as a pinned statement.** For the concrete rank-check data
this says `MS` is the Macaulay block of the chart generators `Fpoly`,
evaluated at `w₀`, up to one nonzero scale per generator. The type is verbatim
the hypothesis `hA2` of `chartEmptyC_T1ne0_of_certificate`. -/
def A2_statement {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (mon : ρ → Fin 5 →₀ ℕ) (gen : ρ → Fin 6) (mult : ρ → Fin 5 →₀ ℕ)
    {p : ℕ} [Fact p.Prime] (w₀ : ZMod p)
    (MS : Matrix ρ ρ (ZMod p)) (scale : Fin 6 → ZMod p) : Prop :=
  (eval₂RingHom (Int.castRingHom (ZMod p)) w₀).mapMatrix (macaulay Fpoly mon gen mult) =
    MS * Matrix.diagonal (fun c => scale (gen c))

/-- **The pinned interface.** Statement verbatim
`chartEmptyC_T1ne0_of_certificate` (`GradeA/Chart/Assembly.lean`), including
its `hsupp`, primality and root hypotheses. The existing proof in
Assembly.lean is the reference solution for this pin. -/
theorem challenge_interface {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (mon : ρ → Fin 5 →₀ ℕ) (hmon : Function.Injective mon) (r₁ : ρ) (hr₁ : mon r₁ = 0)
    (gen : ρ → Fin 6) (mult : ρ → Fin 5 →₀ ℕ)
    (hsupp : ∀ c, ∀ d ∈ (MvPolynomial.monomial (mult c) (1 : ℤ[X]) * Fpoly (gen c)).support, d ∈ Set.range mon)
    {p : ℕ} [Fact p.Prime] (w₀ : ZMod p) (hw₀ : eval₂ (Int.castRingHom (ZMod p)) w₀ Rint = 0)
    (MS Cinv : Matrix ρ ρ (ZMod p)) (scale : Fin 6 → ZMod p) (hscale : ∀ n, scale n ≠ 0)
    (hA1 : Cinv * MS = 1)
    (hA2 : (eval₂RingHom (Int.castRingHom (ZMod p)) w₀).mapMatrix (macaulay Fpoly mon gen mult) =
      MS * Matrix.diagonal (fun c => scale (gen c)))
    (L : Type*) [Field L] [CharZero L] : ChartEmptyC_T1ne0 L := by
  sorry

/-- **The pinned target.** `ChartEmptyC_T1ne0` outright, for every field of
characteristic 0 — the grade-A form of the branch-(c) premise. A solution is
`challenge_interface` applied to the concrete rank-check data together with
solutions of `A1_statement` and `A2_statement` at that data (plus the data
hypotheses `hmon`, `hr₁`, `hsupp`, `hw₀`, `hscale`, which are part of
supplying the data). -/
theorem challenge_target (L : Type*) [Field L] [CharZero L] :
    ChartEmptyC_T1ne0 L := by
  sorry

end BranchC.GradeA.Comparator
