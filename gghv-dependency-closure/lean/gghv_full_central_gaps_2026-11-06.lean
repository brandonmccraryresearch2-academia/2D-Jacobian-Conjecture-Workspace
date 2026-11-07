import Mathlib

/-! # R9 — Central's gaps (Phase 4, Leg E)

**CLAIM:** The endnote cancellation `[F,ℓ(P)] = ℓ(P)`, central item (5),
and the Lema Joseph dimension-counting arithmetic are kernel; the two
external inputs are carried as explicit named premises.
**STATUS:**
  - KERNEL (this file): `central_cancellation` — from `F` defined by
    `[ℓ(G₀),ℓ(P)]·F = ℓ(G₀)·ℓ(P)` and `[[ℓ(G₀),ℓ(P)],ℓ(P)] = 0`,
    `[F,ℓ(P)] = ℓ(P)` by Leibniz + cancellation of the nonzero bracket.
    This is the paper's endnote computation (TeX 867–884), proved here in
    an abstract Poisson-bracket structure, so it applies to the KTerm
    list bracket of `d1_central` once that bracket is shown to satisfy
    the structure axioms (Leibniz is `leibniz_coeff` there; antisymmetry
    and `[P,P] = 0` are the remaining bridge — the structure is stated
    abstractly precisely so the bridge is one instantiation).
  - KERNEL: `central_item5` — `[ℓ(Gᵢ),ℓ(P)] = 0` for `i ≥ 1` by induction
    from the `i = 1` case (Lema Joseph's second property) and
    `[0,ℓ(P)] = 0`. This is central item (5) (TeX 854–855) and Lema
    Joseph's "moreover" clause (TeX 626–627), at the bracket level.
  - KERNEL: `joseph_counting_contradiction` + `int_interval_card` — the
    dimension-counting arithmetic of Lema Joseph's proof (TeX 630–677):
    `(t+1)² > d·t + 1` for `t ≥ d`, `t ≥ 1`, and the interval-cardinality
    bound that forces `dim M(t) ≤ l(M-m)t`.
  - CONDITIONAL: `central_eq_central_from_joseph22` — the eq-central
    bracket identity from the two carried premises (Joseph 2.2 +
    Lema Joseph's conclusions). Item (1) (`F ∈ L` when `P, Q ∈ L`) is
    carried inside the Joseph 2.2 premise as the `sub` predicate.
  - CARRIED (explicit premises, never hidden):
    * `Joseph22HomogForm` — Joseph Lemma 2.2 in the HOMOGENEOUS
      use-context form ONLY: for homogeneous `a, b` with `[a,b] ≠ 0` and
      `[[a,b],b] = 0`, there is `F` with `[a,b]·F = a·b` (and `F` in the
      sub-algebra when `a, b` are). The exact statement was NOT
      retrieved anywhere (retrieval leg COMPLETE, Target 2 NOT FOUND,
      routes T2-R1–R12; paper: A. Joseph, "The Weyl algebra —
      semisimple and nilpotent elements", Amer. J. Math. 97 (1975),
      597–615 — the shorthand "The Jacobian conjecture in dimension 2"
      is WRONG and is never used). The reconstruction from the use
      context (central's proof, TeX 859–866) is INFERENCE ONLY, never
      presented as Joseph's wording. The naive UN-homogeneous form is
      FALSE (counterexample `B = x`, `A = y(x²+1)+x`: `AB/[A,B] =
      -xy - x²/(x²+1) ∉ K[x,y]` — Phase 1 record, d2combine header);
      so the premise MUST include homogeneity (`homog`), and this file
      never states the un-homogeneous form.
    * Lema Joseph's conclusions (existence of `G₀` with the two bracket
      properties + algebraic independence giving `dim M(t) = (t+1)²`):
      the dimension-counting arithmetic is proved here, but the
      valuation bounds for `M(t)` (which need Remark "a remark",
      TeX 1197, conditional in R12) and the algebraic independence are
      NOT proved here — they are the remaining sub-gaps, stated in
      `LemaJosephRemaining` below.
**NOT proved here:** `v(F) = ρ+σ` (already kernel in `d1_central` as
`valF_from_def`); central items (2)(3)(4) (already kernel-conditional in
`d1_central` as `central_dichotomy_gen` / `central_four_gen`).
No `sorry` anywhere; no `axiom` anywhere.
-/

/-- An abstract Poisson bracket on a commutative domain: bilinear,
antisymmetric, Leibniz in the first argument, `[a,a] = 0`. The Jacobi
identity is NOT assumed here (it is R14's polynomial theorem); neither
the cancellation nor item (5) needs it. -/
structure PoissonBracket (A : Type*) [CommRing A] where
  br : A → A → A
  br_add_left : ∀ a b c, br (a + b) c = br a c + br b c
  br_add_right : ∀ a b c, br a (b + c) = br a b + br a c
  br_antisymm : ∀ a b, br a b = -br b a
  br_self : ∀ a, br a a = 0
  br_leibniz_left : ∀ a b c, br (a * b) c = a * br b c + br a c * b

/-- `[0, c] = 0` from additivity. -/
theorem PoissonBracket.br_zero_left {A : Type*} [CommRing A]
    (B : PoissonBracket A) (c : A) : B.br 0 c = 0 := by
  have h := B.br_add_left 0 0 c
  simp only [add_zero] at h
  exact add_eq_left.mp h.symm

/-- `[c, 0] = 0` from additivity. -/
theorem PoissonBracket.br_zero_right {A : Type*} [CommRing A]
    (B : PoissonBracket A) (c : A) : B.br c 0 = 0 := by
  have h := B.br_add_right c 0 0
  simp only [add_zero] at h
  exact add_eq_left.mp h.symm

/-- The endnote computation (TeX 867–884): if `[D,P]·F = D·P` and
`[[D,P],P] = 0` with `[D,P] ≠ 0`, then `[F,P] = P`.
Proof: `[D,P]·[F,P] = [[D,P]·F, P] - [[D,P],P]·F = [D·P, P] = [D,P]·P`
(Leibniz twice, `[P,P] = 0`), then cancel the nonzero `[D,P]`. -/
theorem central_cancellation {A : Type*} [CommRing A] [IsDomain A]
    (B : PoissonBracket A) {D P F : A}
    (hF : B.br D P * F = D * P)
    (hJJ : B.br (B.br D P) P = 0) (hne : B.br D P ≠ 0) :
    B.br F P = P := by
  have h1 : B.br (B.br D P * F) P = B.br D P * B.br F P := by
    rw [B.br_leibniz_left, hJJ, zero_mul, add_zero]
  have h2 : B.br (B.br D P * F) P = B.br D P * P := by
    rw [hF, B.br_leibniz_left, B.br_self, mul_zero, zero_add]
  have h3 : B.br D P * B.br F P = B.br D P * P := by rw [← h1, h2]
  exact mul_left_cancel₀ hne h3

/-- Joseph Lemma 2.2 (Joseph, "The Weyl algebra — semisimple and nilpotent
elements", Amer. J. Math. 97 (1975), 597–615) — CARRIED as an explicit
premise in the HOMOGENEOUS use-context form only. `homog a b` is the
(unspecified) homogeneity predicate for the pair; `sub` is the
sub-algebra predicate (e.g. `· ∈ L`). The exact wording was NOT
retrieved (retrieval leg, Target 2 NOT FOUND); this is the reconstruction
from the use context (central's proof, TeX 859–866) and is INFERENCE
ONLY, never Joseph's wording. The un-homogeneous form is FALSE and is
never stated. -/
def Joseph22HomogForm {A : Type*} [CommRing A] [IsDomain A]
    (B : PoissonBracket A) (homog : A → A → Prop) (sub : A → Prop) : Prop :=
  ∀ a b : A, homog a b → sub a → sub b → B.br a b ≠ 0 →
    B.br (B.br a b) b = 0 →
    ∃ F : A, sub F ∧ B.br a b * F = a * b

/-- Central's eq-central bracket identity, CONDITIONAL on Joseph 2.2
(homogeneous form) + Lema Joseph's conclusions for `G₀`. Item (1) is
the `sub F` component: `F` lies in the sub-algebra when `G₀, P` do. -/
theorem central_eq_central_from_joseph22 {A : Type*} [CommRing A] [IsDomain A]
    (B : PoissonBracket A) {homog : A → A → Prop} {sub : A → Prop}
    (hJ : Joseph22HomogForm B homog sub)
    {G0 P : A} (hhom : homog G0 P) (hsubG : sub G0) (hsubP : sub P)
    (hne : B.br G0 P ≠ 0) (hJJ : B.br (B.br G0 P) P = 0) :
    ∃ F : A, sub F ∧ B.br F P = P := by
  obtain ⟨F, hFsub, hF⟩ := hJ G0 P hhom hsubG hsubP hne hJJ
  exact ⟨F, hFsub, central_cancellation B hF hJJ hne⟩

/-- The bracket chain `Gᵢ := [Gᵢ₋₁, P]` (Lema Joseph / central(5)). -/
def pbChain {A : Type*} [CommRing A] (B : PoissonBracket A) (G0 P : A) :
    ℕ → A
  | 0 => G0
  | n + 1 => B.br (pbChain B G0 P n) P

/-- Central item (5) (TeX 854–855) / Lema Joseph "moreover" (TeX 626–627),
at the bracket level: `[Gᵢ, P] = 0` for `i ≥ 1`, by induction from the
`i = 1` case `[[G₀,P],P] = 0` (Lema Joseph's second property). -/
theorem central_item5 {A : Type*} [CommRing A] [IsDomain A]
    (B : PoissonBracket A) (G0 P : A)
    (h0 : B.br (B.br G0 P) P = 0) (i : ℕ) :
    B.br (pbChain B G0 P (i + 1)) P = 0 := by
  induction i with
  | zero => exact h0
  | succ i ih =>
    show B.br (pbChain B G0 P (i + 2)) P = 0
    have h2 : pbChain B G0 P (i + 2) = 0 := ih
    rw [h2]
    exact B.br_zero_left P

/-- Lema Joseph dimension counting (TeX 630–677): with `d = l(M-m)`,
`(t+1)² > d·t + 1` for `t ≥ d`, `t ≥ 1`. Combined with
`dim M(t) = (t+1)²` (algebraic independence — NOT proved here) and
`dim M(t) ≤ d·t + 1` (interval bound — `int_interval_card` below), this
is the contradiction that produces `H` with `[ℓ(P),ℓ(H)] ≠ 0`. -/
theorem joseph_counting_contradiction {d t : ℕ} (ht : 1 ≤ t) (hdt : d ≤ t) :
    d * t + 1 < (t + 1) ^ 2 := by
  have h1 : d * t ≤ t * t := Nat.mul_le_mul_right t hdt
  have h2 : t * t + 1 < (t + 1) ^ 2 := by
    have e : (t + 1) ^ 2 = t * t + (2 * t + 1) := by ring
    omega
  omega

/-- The interval bound used in the counting: a finite set of integers
inside `[a, b]` has at most `b - a + 1` elements. (In Lema Joseph's
proof, the valuations of `M(t) ∖ {0}` lie in `(1/l)ℤ ∩ [mt, Mt]`, an
interval of length `(M-m)t` with spacing `1/l`, hence at most
`l(M-m)t + 1` distinct values.) -/
theorem int_interval_card {S : Finset ℤ} {a b : ℤ} (hab : a ≤ b)
    (h : ∀ x ∈ S, a ≤ x ∧ x ≤ b) :
    (S.card : ℤ) ≤ b - a + 1 := by
  have hsub : S ⊆ Finset.Icc a b := by
    intro x hx
    rw [Finset.mem_Icc]
    exact h x hx
  have hcard : S.card ≤ (Finset.Icc a b).card := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hnn : 0 ≤ b + 1 - a := by omega
  have hcast : ((b + 1 - a).toNat : ℤ) = b + 1 - a :=
    Int.toNat_of_nonneg hnn
  have hcard' : (S.card : ℤ) ≤ ((b + 1 - a).toNat : ℤ) := by
    exact_mod_cast hcard
  omega

/- What remains of Lema Joseph (TeX 620), stated exactly in the file header
above — NOT proved here: (i) algebraic independence of `P, Q`, giving
`dim M(t) = (t+1)²`; (ii) the valuation bounds for `M(t)` (needs
Remark "a remark", TeX 1197 — conditional in R12); (iii) termination of
the `Hⱼ` recursion (Q-degree descent — proved abstractly in R17 as
`mayores_termination_descent`); (iv) the maximal-`j` step via 480 +
Remark 453(3). No vacuous `True` placeholder is stated as a theorem. -/
