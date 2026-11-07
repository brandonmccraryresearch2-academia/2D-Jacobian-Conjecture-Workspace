import Mathlib

/-! # R17 — Mayores full statement (Phase 4, Leg E)

**CLAIM:** T-termination is proved abstractly; the cocientes ratio
conclusion is proved from the proportionality data; the full mayores
theorem is CONDITIONAL on the induction claim.
**STATUS:**
  - KERNEL (this file): `mayores_termination_descent` — if the Q-degree
    `d j` of the bracket chain drops by exactly 1 per step, then
    `d j = d 0 - j`; hence `mayores_chain_terminates`: some `T_N` has
    negative Q-degree, i.e. `T_N = 0`. This is the descent mayores quotes
    as "easily" (inventory.md, mayores proof map: "Q-degree drops by 1
    per bracketing, so the chain terminates after `deg_Q(T₀)+1` steps").
    The D2 combine leg proved the same descent at the (P,Q)-monomial
    level (`pqChain_zero_of_deg`); this file proves it in the abstract
    integer form used by the mayores proof map, so the two agree.
  - KERNEL: `mayores_cocientes_ratio` + `mayores_cocientes_conditional`
    — the ratio half of (cocientes) (TeX 3835–3838): from the
    proportionality data `v(T_j) = μ_j·v(P)`, `v₀(T_j) = μ_j·v₀(P)`,
    the ratios agree: `v(T_j)/v(P) = v₀(T_j)/v₀(P)`. The valuation
    linearity behind the data (`dirValQ_rat_smul`) is kernel.
  - CONDITIONAL: the full mayores theorem (TeX 3799–3838) is the
    conjunction of (i) the bracket-vanishing half of (cocientes),
    (ii) the ratio half proved here, (iii) the interval
    `(ρ₀,σ₀) < (ρ,σ) ≤ (ρ̃,σ̃)`. Part (i) is NOT proved here: it needs
    the induction claim (condind, TeX 3859–3877) — in particular claim
    (a) (via le basico + the `Dir(T_j) ∩ ]ρᵢ,ρᵢ₊₁[ = ∅` argument with
    the ch4 induction) and claim (b) (via 480 + the sandwich +
    starting-vs-end). The condind claim itself is carried, not proved;
    its derivation needs "formula basica de orden'" (TeX, condind(i+1))
    and the Remark "a remark" bridge (R12 conditional). So the verdict
    for the full mayores theorem is CONDITIONAL on condind, stated
    exactly in `mayores_full_conditional` (which takes the two
    cocientes halves as hypotheses and assembles them — the assembly,
    not the halves).
**NOT proved here:** claim (a)/(b), condind(i+1), the ch4 induction
step, "formula basica de orden'". The T-termination descent is the only
part of the proof map closed here; everything else is delimited above.
**Sources:** [GGV1] TeX 3799–3838 (statement), 3841–4076 (proof map,
inventory.md "mayores proof REST read").
No `sorry` anywhere; no `axiom` anywhere.
-/

/-- Rational valuation of a rational point. -/
def dirValQ (ρ σ : Int) (e : ℚ × ℚ) : ℚ := ρ * e.1 + σ * e.2

/-- Valuation is linear under rational scaling of the endpoint:
`v(μ·e) = μ·v(e)`. This is the linearity the cocientes ratio uses. -/
theorem dirValQ_rat_smul (ρ σ : Int) (mu : ℚ) (e : ℚ × ℚ) :
    dirValQ ρ σ (mu • e) = mu * dirValQ ρ σ e := by
  simp only [dirValQ, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- T-termination descent (mayores proof map, ch4): if the Q-degree drops
by exactly 1 per bracketing, `d j = d 0 - j`. -/
theorem mayores_termination_descent {d : ℕ → ℤ}
    (hstep : ∀ j, d (j + 1) = d j - 1) (j : ℕ) :
    d j = d 0 - j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [hstep, ih]
    push_cast
    ring

/-- The chain terminates: some `T_N` has negative Q-degree, hence is 0
(the "easily" step of the mayores proof — now proved, not quoted). -/
theorem mayores_chain_terminates {d : ℕ → ℤ}
    (hstep : ∀ j, d (j + 1) = d j - 1) (hd0 : 0 ≤ d 0) :
    ∃ N : ℕ, d N < 0 := by
  refine ⟨(d 0).toNat + 1, ?_⟩
  rw [mayores_termination_descent hstep]
  have hcast : ((d 0).toNat : ℤ) = d 0 := Int.toNat_of_nonneg hd0
  push_cast
  omega

/-- The ratio half of (cocientes) at one direction: from
`v(T_j) = μ·v(P)` with `v(P) ≠ 0`, `v(T_j)/v(P) = μ`. -/
theorem mayores_cocientes_ratio {mu vP vT : ℚ} (hP : vP ≠ 0)
    (hT : vT = mu * vP) : vT / vP = mu := by
  rw [hT]
  exact mul_div_cancel_right₀ mu hP

/-- The ratio half of (cocientes) across two directions: the ratio is
the same at `(ρ,σ)` and at `(ρ₀,σ₀)` when the same `μ_j` scales both. -/
theorem mayores_cocientes_conditional {mu vP vT vP0 vT0 : ℚ}
    (hP : vP ≠ 0) (hP0 : vP0 ≠ 0)
    (hT : vT = mu * vP) (hT0 : vT0 = mu * vP0) :
    vT / vP = vT0 / vP0 := by
  rw [mayores_cocientes_ratio hP hT, mayores_cocientes_ratio hP0 hT0]

/-- The full mayores theorem, CONDITIONAL: the two halves of (cocientes)
— bracket-vanishing (carried as the proposition `B`, which needs condind
(a)/(b)) and the ratio equality (proved above from the proportionality
data) — assemble into the paper's conclusion. The assembly is trivial;
the content is the delimitation: `B` is the open part, the ratio is the
closed part. -/
theorem mayores_full_conditional {mu vP vT vP0 vT0 : ℚ} {B : Prop}
    (hP : vP ≠ 0) (hP0 : vP0 ≠ 0)
    (hT : vT = mu * vP) (hT0 : vT0 = mu * vP0)
    (hbracket : B) :
    vT / vP = vT0 / vP0 ∧ B :=
  ⟨mayores_cocientes_conditional hP hP0 hT hT0, hbracket⟩
