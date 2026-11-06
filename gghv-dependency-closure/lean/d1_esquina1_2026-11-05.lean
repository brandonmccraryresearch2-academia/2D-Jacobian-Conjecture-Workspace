import Mathlib

/- LE BASICO — FULL ASSEMBLY (exponent level), 2026-11-05.
   Self-contained scratch, not a repo module.

   STATUS: this file assembles the FULL le basico from the proved D1
   pieces (all LEAN_EXIT=0 in their own files; nothing re-proved):
     * fragment (2026-11-04): base defs/lemmas, `inter_singleton`,
       `face_between_singleton`, `le_basico_conditional`,
       `le_basico_weak`, `consecutive_weak_lebasico` (with `hbreak`
       as a hypothesis);
     * Part17 slice layer: `stFaceAux`/`enFaceAux` + mem/max,
       `stFace`/`enFace`, `stFace_mem_max`/`enFace_mem_max`;
     * `slice_tie_unique` (tie on (ρ,σ) + (1,−1), ρ+σ ≠ 0);
     * `breakpoint_between` (+ `slope_min_exists`, `breakpoint_core`)
       — the replacement for the REFUTED chord-normal route;
     * `dir_between_pos_combo` (step (A)).
   NEW IN THIS FILE: `slice_tie_unique_en` (the (−1,1) mirror),
   `endpoint_slice_max` (the endpoint-incidence step), and
   `le_basico_full` (the assembly).

   THE INCIDENCE STEP (what was missing): a shared face point a1
   (in both the ρ₁-face and the ρ₂-face) maximizes the (−1,1)-slice
   over the ρ₁-face and the (1,−1)-slice over the ρ₂-face, provided
   ρ₁, ρ₂ ∈ V_{≥0} and crossProd ρ₁ ρ₂ > 0. Proof by the Cramer
   identities (checked by `ring`):
     C·(dirVal (−1) 1 d) = −(ρ₂.1+ρ₂.2)·(dirVal ρ₁ d) + (ρ₁.1+ρ₁.2)·(dirVal ρ₂ d)
     C·(dirVal 1 (−1) d) = (ρ₂.1+ρ₂.2)·(dirVal ρ₁ d) − (ρ₁.1+ρ₁.2)·(dirVal ρ₂ d)
   with C = crossProd ρ₁ ρ₂, d = t.1 − a1.1. On the ρ₁-face the
   ρ₁-difference vanishes and the ρ₂-difference is ≤ 0; on the ρ₂-face
   the ρ₂-difference vanishes and the ρ₁-difference is ≤ 0. With
   `slice_tie_unique` this identifies a1 with Part17's enFace/stFace
   outputs at exponent level — that is the polygon-boundary incidence.

   TARGET (exponent level): isSuccFrom ρ₁ ρ₂ dirs → dirLt ρ₁ ρ →
   dirLt ρ ρ₂ → en_{ρ₁} = a1 = st_{ρ₂} (via enFace/stFace) and the
   ρ-face is the single vertex a1. Qualifications (carried, not
   hidden): exponent level only (Term equality needs unique exponents
   of polynomial term lists as a separate step); `hvert` (vertical-face
   caveat: isDir is strictly weaker than Dir(P) at σ = 0) is carried
   by `hdirs` as a hypothesis, never asserted; the two V_{>0}
   hypotheses are the V_{>0} setting of the esquina application.
   No paper proof exists for le basico ("completely clear") — this
   is original polygon combinatorics, not a transcription. -/

/-- Weighted valuation (Part14, verbatim). -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- Maximal-valuation vertex, last-max tie-break (Part14, verbatim). -/
def maxVertDir (ρ σ : Int) : List (Int × Int) → Option (Int × Int)
  | [] => none
  | v :: vs =>
    match maxVertDir ρ σ vs with
    | none => some v
    | some w => if dirVal ρ σ v.1 v.2 ≤ dirVal ρ σ w.1 w.2 then some w else some v

/-- Membership: the maximal-valuation vertex lies in the list
    (Part14, verbatim). -/
theorem maxVert_mem {ρ σ : Int} {vs : List (Int × Int)} {v : Int × Int} :
    maxVertDir ρ σ vs = some v → v ∈ vs := by
  induction vs with
  | nil => simp [maxVertDir]
  | cons x xs ih =>
    intro h
    simp only [maxVertDir] at h
    cases hxs : maxVertDir ρ σ xs with
    | none =>
      simp only [hxs] at h
      have hv : x = v := Option.some.inj h
      subst hv
      exact List.mem_cons_self
    | some w =>
      simp only [hxs] at h
      by_cases hle : dirVal ρ σ x.1 x.2 ≤ dirVal ρ σ w.1 w.2
      · simp only [hle, ite_true] at h
        have hw : w = v := Option.some.inj h
        subst hw
        exact List.mem_cons_of_mem x (ih hxs)
      · simp only [hle, ite_false] at h
        have hv : x = v := Option.some.inj h
        subst hv
        exact List.mem_cons_self

/-- The maximal-valuation vertex is `none` only for the empty list
    (Part14, verbatim). -/
theorem maxVert_none {ρ σ : Int} {vs : List (Int × Int)} :
    maxVertDir ρ σ vs = none → vs = [] := by
  induction vs with
  | nil => intro _; rfl
  | cons x xs _ =>
    intro h
    simp only [maxVertDir] at h
    cases hxs : maxVertDir ρ σ xs with
    | none => simp [hxs] at h
    | some w =>
      by_cases hle : dirVal ρ σ x.1 x.2 ≤ dirVal ρ σ w.1 w.2
      · simp [hxs, hle] at h
      · simp [hxs, hle] at h

/-- Maximality: every vertex of the list has valuation at most the
    maximal-valuation vertex's valuation (Part14, verbatim). -/
theorem maxVert_max {ρ σ : Int} {vs : List (Int × Int)} {v w : Int × Int} :
    maxVertDir ρ σ vs = some v → w ∈ vs →
    dirVal ρ σ w.1 w.2 ≤ dirVal ρ σ v.1 v.2 := by
  induction vs generalizing v w with
  | nil => intro _ h; cases h
  | cons x xs ih =>
    intro h hmem
    simp only [maxVertDir] at h
    cases hxs : maxVertDir ρ σ xs with
    | none =>
      simp only [hxs] at h
      have hv : x = v := Option.some.inj h
      have hxs' : xs = [] := maxVert_none hxs
      subst hxs'; subst hv
      rcases List.mem_cons.mp hmem with rfl | hm
      · omega
      · cases hm
    | some u =>
      simp only [hxs] at h
      by_cases hle : dirVal ρ σ x.1 x.2 ≤ dirVal ρ σ u.1 u.2
      · simp only [hle, ite_true] at h
        have hu : u = v := Option.some.inj h
        subst hu
        rcases List.mem_cons.mp hmem with rfl | hm
        · exact hle
        · exact ih hxs hm
      · simp only [hle, ite_false] at h
        have hv : x = v := Option.some.inj h
        subst hv
        rcases List.mem_cons.mp hmem with rfl | hm
        · omega
        · have h1 := ih hxs hm
          omega

/-- A term: exponent paired with its coefficient (Part14, verbatim). -/
abbrev Term := (Int × Int) × Int

/-- Exponents of a term list (Part14, verbatim). -/
def termExps (terms : List Term) : List (Int × Int) := terms.map Prod.fst

/-- Terms attaining maximal (ρ,σ)-valuation (Part14, verbatim). -/
def faceTerms (ρ σ : Int) (terms : List Term) : List Term :=
  match maxVertDir ρ σ (termExps terms) with
  | none => []
  | some m => terms.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2)

/-- Membership characterization of the face terms (Part14, verbatim). -/
theorem faceTerms_mem {ρ σ : Int} {terms : List Term} {t : Term} :
    t ∈ faceTerms ρ σ terms ↔
    ∃ m, maxVertDir ρ σ (termExps terms) = some m ∧ t ∈ terms ∧
      dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2 := by
  cases h : maxVertDir ρ σ (termExps terms) with
  | none =>
    constructor
    · intro hv
      simp only [faceTerms, h] at hv
      cases hv
    · rintro ⟨m, hm, -, -⟩
      exact absurd hm.symm (Option.some_ne_none m)
  | some m =>
    have hface : faceTerms ρ σ terms =
        terms.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2) := by
      simp only [faceTerms, h]
    constructor
    · intro hv
      rw [hface, List.mem_filter] at hv
      exact ⟨m, rfl, hv.1, of_decide_eq_true hv.2⟩
    · rintro ⟨m', hm', hv, hval⟩
      have hmm : m' = m := (Option.some.inj hm').symm
      subst hmm
      rw [hface, List.mem_filter]
      exact ⟨hv, by simp [hval]⟩

theorem faceTerms_subset {ρ σ : Int} {terms : List Term} {t : Term} :
    t ∈ faceTerms ρ σ terms → t ∈ terms :=
  fun h => (faceTerms_mem.mp h).choose_spec.2.1

theorem faceTerms_max {ρ σ : Int} {terms : List Term} {t : Term}
    (h : t ∈ faceTerms ρ σ terms) {v : Int × Int} (hv : v ∈ termExps terms) :
    dirVal ρ σ v.1 v.2 ≤ dirVal ρ σ t.1.1 t.1.2 := by
  obtain ⟨m, hm, -, hval⟩ := faceTerms_mem.mp h
  have hle := maxVert_max hm hv
  omega

theorem faceTerms_nonempty {ρ σ : Int} {terms : List Term} :
    terms ≠ [] → faceTerms ρ σ terms ≠ [] := by
  intro hne hface
  cases h : maxVertDir ρ σ (termExps terms) with
  | none =>
    have he : termExps terms = [] := maxVert_none h
    simp [termExps] at he
    exact hne he
  | some m =>
    obtain ⟨t, ht, ht1⟩ := List.mem_map.mp (maxVert_mem h)
    have hm : t ∈ faceTerms ρ σ terms :=
      faceTerms_mem.mpr ⟨m, h, ht, by rw [ht1]⟩
    rw [hface] at hm
    cases hm

/-- Cross product of two exponent/direction pairs (Part20, verbatim). -/
def crossProd (a b : Int × Int) : Int := a.1 * b.2 - a.2 * b.1

/-- CCW order on directions (Part20, verbatim). -/
def dirLt (a b : Int × Int) : Prop := 0 < crossProd a b

/-- CCW order is irreflexive (Part20, verbatim). -/
theorem dirLt_irrefl (a : Int × Int) : ¬ dirLt a a := by
  show ¬ 0 < crossProd a a
  simp only [crossProd]
  rw [Int.mul_comm a.2 a.1]
  simp

/-- Dir(P) at list level (Part20, verbatim). -/
def isDir (ρ σ : Int) (terms : List Term) : Prop :=
  ∃ a b, a ∈ faceTerms ρ σ terms ∧ b ∈ faceTerms ρ σ terms ∧ a.1 ≠ b.1

/-- Succ from a direction, "no Dir element strictly between"
    characterization (Part20, verbatim). -/
def isSuccFrom (src δ : Int × Int) (dirs : List (Int × Int)) : Prop :=
  δ ∈ dirs ∧ dirLt src δ ∧
  ∀ δ' ∈ dirs, dirLt src δ' → dirLt δ' δ → δ' = δ

/-- Two points in the intersection of two non-parallel faces share
    their exponent: a vector perpendicular to two independent
    directions is zero. -/
theorem inter_singleton {ρ1 ρ2 : Int × Int} {terms : List Term}
    {u v : Term}
    (hu1 : u ∈ faceTerms ρ1.1 ρ1.2 terms) (hu2 : u ∈ faceTerms ρ2.1 ρ2.2 terms)
    (hv1 : v ∈ faceTerms ρ1.1 ρ1.2 terms) (hv2 : v ∈ faceTerms ρ2.1 ρ2.2 terms)
    (hcross : crossProd ρ1 ρ2 ≠ 0) :
    u.1 = v.1 := by
  have hu1terms : u ∈ terms := faceTerms_subset hu1
  have hv1terms : v ∈ terms := faceTerms_subset hv1
  have e1 : dirVal ρ1.1 ρ1.2 u.1.1 u.1.2 = dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 :=
    le_antisymm
      (faceTerms_max hv1 (List.mem_map.mpr ⟨u, hu1terms, rfl⟩))
      (faceTerms_max hu1 (List.mem_map.mpr ⟨v, hv1terms, rfl⟩))
  have e2 : dirVal ρ2.1 ρ2.2 u.1.1 u.1.2 = dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 :=
    le_antisymm
      (faceTerms_max hv2 (List.mem_map.mpr ⟨u, hu1terms, rfl⟩))
      (faceTerms_max hu2 (List.mem_map.mpr ⟨v, hv1terms, rfl⟩))
  have hd1 : crossProd ρ1 ρ2 * (u.1.1 - v.1.1) = 0 := by
    simp only [crossProd, dirVal] at e1 e2 ⊢
    linear_combination ρ2.2 * e1 - ρ1.2 * e2
  have hd2 : crossProd ρ1 ρ2 * (u.1.2 - v.1.2) = 0 := by
    simp only [crossProd, dirVal] at e1 e2 ⊢
    linear_combination ρ1.1 * e2 - ρ2.1 * e1
  have e1' : u.1.1 - v.1.1 = 0 := by
    rcases mul_eq_zero.mp hd1 with h | h
    · exact absurd h hcross
    · exact h
  have e2' : u.1.2 - v.1.2 = 0 := by
    rcases mul_eq_zero.mp hd2 with h | h
    · exact absurd h hcross
    · exact h
  exact Prod.ext (sub_eq_zero.mp e1') (sub_eq_zero.mp e2')

/-- The ρ-face of a positive rational combination is the single shared
    vertex: any term in both the ρ₁-face and the ρ₂-face is the unique
    exponent of the ρ-face, and lies in it. -/
theorem face_between_singleton {ρ1 ρ2 ρ : Int × Int} {terms : List Term}
    {v : Term}
    (hv1 : v ∈ faceTerms ρ1.1 ρ1.2 terms) (hv2 : v ∈ faceTerms ρ2.1 ρ2.2 terms)
    (hcross : crossProd ρ1 ρ2 ≠ 0)
    {α β : ℚ} (hα : 0 < α) (hβ : 0 < β)
    (hρ : (ρ.1 : ℚ) = α * (ρ1.1 : ℚ) + β * (ρ2.1 : ℚ) ∧
      (ρ.2 : ℚ) = α * (ρ1.2 : ℚ) + β * (ρ2.2 : ℚ)) :
    (∀ u ∈ faceTerms ρ.1 ρ.2 terms, u.1 = v.1) ∧ v ∈ faceTerms ρ.1 ρ.2 terms := by
  have hvterms : v ∈ terms := faceTerms_subset hv1
  have hcombo : ∀ e : Int × Int,
      (dirVal ρ.1 ρ.2 e.1 e.2 : ℚ)
        = α * (dirVal ρ1.1 ρ1.2 e.1 e.2 : ℚ)
          + β * (dirVal ρ2.1 ρ2.2 e.1 e.2 : ℚ) := by
    intro e
    simp only [dirVal]
    push_cast
    rw [hρ.1, hρ.2]
    ring
  have hkey : ∀ t ∈ terms,
      dirVal ρ.1 ρ.2 t.1.1 t.1.2 ≤ dirVal ρ.1 ρ.2 v.1.1 v.1.2 := by
    intro t ht
    have h1 : dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 ≤ dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 :=
      faceTerms_max hv1 (List.mem_map.mpr ⟨t, ht, rfl⟩)
    have h2 : dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 ≤ dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 :=
      faceTerms_max hv2 (List.mem_map.mpr ⟨t, ht, rfl⟩)
    have hq : (dirVal ρ.1 ρ.2 t.1.1 t.1.2 : ℚ)
        ≤ (dirVal ρ.1 ρ.2 v.1.1 v.1.2 : ℚ) := by
      rw [hcombo t.1, hcombo v.1]
      have h1q : (dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 : ℚ)
          ≤ (dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 : ℚ) := by exact_mod_cast h1
      have h2q : (dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 : ℚ)
          ≤ (dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 : ℚ) := by exact_mod_cast h2
      exact add_le_add (mul_le_mul_of_nonneg_left h1q (le_of_lt hα))
        (mul_le_mul_of_nonneg_left h2q (le_of_lt hβ))
    exact_mod_cast hq
  have htermsne : terms ≠ [] := by
    intro hnil
    rw [hnil] at hvterms
    exact List.not_mem_nil hvterms
  have hvface : v ∈ faceTerms ρ.1 ρ.2 terms := by
    cases hm : maxVertDir ρ.1 ρ.2 (termExps terms) with
    | none =>
      have he : termExps terms = [] := maxVert_none hm
      simp [termExps] at he
      exact absurd he htermsne
    | some m =>
      have hmexp : m ∈ termExps terms := maxVert_mem hm
      obtain ⟨tm, htmmem, htm1⟩ := List.mem_map.mp hmexp
      have hle1 : dirVal ρ.1 ρ.2 m.1 m.2 ≤ dirVal ρ.1 ρ.2 v.1.1 v.1.2 := by
        have hh := hkey tm htmmem
        rwa [htm1] at hh
      have hle2 : dirVal ρ.1 ρ.2 v.1.1 v.1.2 ≤ dirVal ρ.1 ρ.2 m.1 m.2 :=
        maxVert_max hm (List.mem_map.mpr ⟨v, hvterms, rfl⟩)
      exact faceTerms_mem.mpr ⟨m, hm, hvterms, le_antisymm hle2 hle1⟩
  refine ⟨?_, hvface⟩
  intro u hu
  have huterms : u ∈ terms := faceTerms_subset hu
  have hge : dirVal ρ.1 ρ.2 v.1.1 v.1.2 ≤ dirVal ρ.1 ρ.2 u.1.1 u.1.2 :=
    faceTerms_max hu (List.mem_map.mpr ⟨v, hvterms, rfl⟩)
  have hle : dirVal ρ.1 ρ.2 u.1.1 u.1.2 ≤ dirVal ρ.1 ρ.2 v.1.1 v.1.2 :=
    hkey u huterms
  have heq : dirVal ρ.1 ρ.2 u.1.1 u.1.2 = dirVal ρ.1 ρ.2 v.1.1 v.1.2 :=
    le_antisymm hle hge
  have hq : α * ((dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 : ℚ)
        - (dirVal ρ1.1 ρ1.2 u.1.1 u.1.2 : ℚ))
      + β * ((dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 : ℚ)
        - (dirVal ρ2.1 ρ2.2 u.1.1 u.1.2 : ℚ)) = 0 := by
    have e1 := hcombo u.1
    have e2 := hcombo v.1
    have heq' : (dirVal ρ.1 ρ.2 u.1.1 u.1.2 : ℚ)
        = (dirVal ρ.1 ρ.2 v.1.1 v.1.2 : ℚ) := by exact_mod_cast heq
    rw [e1, e2] at heq'
    linarith
  have h1nn : 0 ≤ α * ((dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 : ℚ)
      - (dirVal ρ1.1 ρ1.2 u.1.1 u.1.2 : ℚ)) :=
    mul_nonneg (le_of_lt hα) (by
      have h1 : dirVal ρ1.1 ρ1.2 u.1.1 u.1.2 ≤ dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 :=
        faceTerms_max hv1 (List.mem_map.mpr ⟨u, huterms, rfl⟩)
      have h1q : (dirVal ρ1.1 ρ1.2 u.1.1 u.1.2 : ℚ)
          ≤ (dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 : ℚ) := by exact_mod_cast h1
      linarith)
  have h2nn : 0 ≤ β * ((dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 : ℚ)
      - (dirVal ρ2.1 ρ2.2 u.1.1 u.1.2 : ℚ)) :=
    mul_nonneg (le_of_lt hβ) (by
      have h2 : dirVal ρ2.1 ρ2.2 u.1.1 u.1.2 ≤ dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 :=
        faceTerms_max hv2 (List.mem_map.mpr ⟨u, huterms, rfl⟩)
      have h2q : (dirVal ρ2.1 ρ2.2 u.1.1 u.1.2 : ℚ)
          ≤ (dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 : ℚ) := by exact_mod_cast h2
      linarith)
  have hz1 : α * ((dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 : ℚ)
      - (dirVal ρ1.1 ρ1.2 u.1.1 u.1.2 : ℚ)) = 0 := by linarith
  have hz2 : β * ((dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 : ℚ)
      - (dirVal ρ2.1 ρ2.2 u.1.1 u.1.2 : ℚ)) = 0 := by linarith
  have e1 : dirVal ρ1.1 ρ1.2 u.1.1 u.1.2 = dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 := by
    have hα0 : (α : ℚ) ≠ 0 := ne_of_gt hα
    have hdiff : (dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 : ℚ)
        - (dirVal ρ1.1 ρ1.2 u.1.1 u.1.2 : ℚ) = 0 := by
      rcases mul_eq_zero.mp hz1 with h | h
      · exact absurd h hα0
      · exact h
    have hcast : (dirVal ρ1.1 ρ1.2 u.1.1 u.1.2 : ℚ)
        = (dirVal ρ1.1 ρ1.2 v.1.1 v.1.2 : ℚ) := by linarith
    exact_mod_cast hcast
  have e2 : dirVal ρ2.1 ρ2.2 u.1.1 u.1.2 = dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 := by
    have hβ0 : (β : ℚ) ≠ 0 := ne_of_gt hβ
    have hdiff : (dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 : ℚ)
        - (dirVal ρ2.1 ρ2.2 u.1.1 u.1.2 : ℚ) = 0 := by
      rcases mul_eq_zero.mp hz2 with h | h
      · exact absurd h hβ0
      · exact h
    have hcast : (dirVal ρ2.1 ρ2.2 u.1.1 u.1.2 : ℚ)
        = (dirVal ρ2.1 ρ2.2 v.1.1 v.1.2 : ℚ) := by linarith
    exact_mod_cast hcast
  obtain ⟨m1, hm1, -, hval1⟩ := faceTerms_mem.mp hv1
  obtain ⟨m2, hm2, -, hval2⟩ := faceTerms_mem.mp hv2
  have hu1 : u ∈ faceTerms ρ1.1 ρ1.2 terms :=
    faceTerms_mem.mpr ⟨m1, hm1, huterms, by omega⟩
  have hu2 : u ∈ faceTerms ρ2.1 ρ2.2 terms :=
    faceTerms_mem.mpr ⟨m2, hm2, huterms, by omega⟩
  exact inter_singleton hu1 hu2 hv1 hv2 hcross

/-- le basico, CONDITIONAL on the two cross-memberships: if the en₁-term
    also lies in the ρ₂-face and the st₂-term also lies in the ρ₁-face,
    then (at exponent level) en₁ = st₂ and the ρ-face is that single
    vertex. The cross-memberships are hypotheses, not conclusions. -/
theorem le_basico_conditional {ρ1 ρ2 ρ : Int × Int} {terms : List Term}
    {eTerm sTerm : Term}
    (he1 : eTerm ∈ faceTerms ρ1.1 ρ1.2 terms)
    (hs2 : sTerm ∈ faceTerms ρ2.1 ρ2.2 terms)
    (he2 : eTerm ∈ faceTerms ρ2.1 ρ2.2 terms)
    (hs1 : sTerm ∈ faceTerms ρ1.1 ρ1.2 terms)
    (hcross : crossProd ρ1 ρ2 ≠ 0)
    {α β : ℚ} (hα : 0 < α) (hβ : 0 < β)
    (hρ : (ρ.1 : ℚ) = α * (ρ1.1 : ℚ) + β * (ρ2.1 : ℚ) ∧
      (ρ.2 : ℚ) = α * (ρ1.2 : ℚ) + β * (ρ2.2 : ℚ)) :
    eTerm.1 = sTerm.1 ∧ (∀ u ∈ faceTerms ρ.1 ρ.2 terms, u.1 = eTerm.1) ∧
      eTerm ∈ faceTerms ρ.1 ρ.2 terms := by
  have heq : eTerm.1 = sTerm.1 := inter_singleton he1 he2 hs1 hs2 hcross
  have hfb := face_between_singleton he1 he2 hcross hα hβ hρ
  exact ⟨heq, hfb.1, hfb.2⟩

/-- le basico, WEAK form: a shared face point already forces the ρ-face
    to be that single vertex. -/
theorem le_basico_weak {ρ1 ρ2 ρ : Int × Int} {terms : List Term}
    (hcross : crossProd ρ1 ρ2 ≠ 0)
    {α β : ℚ} (hα : 0 < α) (hβ : 0 < β)
    (hρ : (ρ.1 : ℚ) = α * (ρ1.1 : ℚ) + β * (ρ2.1 : ℚ) ∧
      (ρ.2 : ℚ) = α * (ρ1.2 : ℚ) + β * (ρ2.2 : ℚ)) :
    (∃ v : Term, v ∈ faceTerms ρ1.1 ρ1.2 terms ∧ v ∈ faceTerms ρ2.1 ρ2.2 terms) →
    ∃ v : Term, v ∈ faceTerms ρ1.1 ρ1.2 terms ∧ v ∈ faceTerms ρ2.1 ρ2.2 terms ∧
      (∀ u ∈ faceTerms ρ.1 ρ.2 terms, u.1 = v.1) ∧ v ∈ faceTerms ρ.1 ρ.2 terms := by
  rintro ⟨v, hv1, hv2⟩
  have hfb := face_between_singleton hv1 hv2 hcross hα hβ hρ
  exact ⟨v, hv1, hv2, hfb.1, hfb.2⟩

/-- Glue: consecutiveness + the breakpoint lemma yield a shared face
    point, hence (by `le_basico_weak`) the ρ-face is a single vertex.
    `hbreak` is exactly `breakpoint_between`'s statement from
    d1_leB_breakpoint_2026-11-04.lean, taken as a hypothesis so this
    file stays self-contained; plugging it is mechanical. -/
theorem consecutive_weak_lebasico {ρ1 ρ2 ρ : Int × Int} {terms : List Term}
    {dirs : List (Int × Int)}
    (hbreak : ∀ {a1 : Term},
      a1 ∈ faceTerms ρ1.1 ρ1.2 terms →
      (∀ t ∈ faceTerms ρ1.1 ρ1.2 terms,
        dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 ≤ dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2) →
      ∀ {b : Term}, b ∈ terms →
      dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 < dirVal ρ2.1 ρ2.2 b.1.1 b.1.2 →
      ∃ δ : Int × Int, dirLt ρ1 δ ∧ dirLt δ ρ2 ∧ isDir δ.1 δ.2 terms)
    (hsucc : isSuccFrom ρ1 ρ2 dirs)
    (hdirs : ∀ δ : Int × Int, δ ∈ dirs ↔ isDir δ.1 δ.2 terms)
    (hter : terms ≠ [])
    (hcross : crossProd ρ1 ρ2 ≠ 0)
    {α β : ℚ} (hα : 0 < α) (hβ : 0 < β)
    (hρ : (ρ.1 : ℚ) = α * (ρ1.1 : ℚ) + β * (ρ2.1 : ℚ) ∧
      (ρ.2 : ℚ) = α * (ρ1.2 : ℚ) + β * (ρ2.2 : ℚ)) :
    ∃ v : Term, v ∈ faceTerms ρ1.1 ρ1.2 terms ∧ v ∈ faceTerms ρ2.1 ρ2.2 terms ∧
      (∀ u ∈ faceTerms ρ.1 ρ.2 terms, u.1 = v.1) ∧ v ∈ faceTerms ρ.1 ρ.2 terms := by
  have hsucc' : ρ2 ∈ dirs ∧ dirLt ρ1 ρ2 ∧
      (∀ δ' ∈ dirs, dirLt ρ1 δ' → dirLt δ' ρ2 → δ' = ρ2) := hsucc
  obtain ⟨-, -, hsucc_no⟩ := hsucc'
  have hf1ne : faceTerms ρ1.1 ρ1.2 terms ≠ [] := faceTerms_nonempty hter
  obtain ⟨a1, ha1⟩ : ∃ a, a ∈ faceTerms ρ2.1 ρ2.2 (faceTerms ρ1.1 ρ1.2 terms) := by
    cases h : faceTerms ρ2.1 ρ2.2 (faceTerms ρ1.1 ρ1.2 terms) with
    | nil =>
      exfalso
      exact faceTerms_nonempty hf1ne h
    | cons a _ => exact ⟨a, by simp⟩
  have ha1face : a1 ∈ faceTerms ρ1.1 ρ1.2 terms := faceTerms_subset ha1
  have ha1max : ∀ t ∈ faceTerms ρ1.1 ρ1.2 terms,
      dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 ≤ dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 := by
    intro t ht
    exact faceTerms_max ha1 (List.mem_map.mpr ⟨t, ht, rfl⟩)
  by_cases hcase : ∃ b ∈ terms,
      dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 < dirVal ρ2.1 ρ2.2 b.1.1 b.1.2
  · obtain ⟨b, hbmem, hb⟩ := hcase
    obtain ⟨δ, hδ1, hδ2, hδdir⟩ := hbreak ha1face ha1max hbmem hb
    have hδmem : δ ∈ dirs := (hdirs δ).mpr hδdir
    have hEq : δ = ρ2 := hsucc_no δ hδmem hδ1 hδ2
    rw [hEq] at hδ2
    exact absurd hδ2 (dirLt_irrefl ρ2)
  · push Not at hcase
    have ha1terms : a1 ∈ terms := faceTerms_subset ha1face
    have ha1face2 : a1 ∈ faceTerms ρ2.1 ρ2.2 terms := by
      cases hm : maxVertDir ρ2.1 ρ2.2 (termExps terms) with
      | none =>
        have he : termExps terms = [] := maxVert_none hm
        simp [termExps] at he
        exact absurd he hter
      | some m =>
        have hmexp : m ∈ termExps terms := maxVert_mem hm
        obtain ⟨tm, htmmem, htm1⟩ := List.mem_map.mp hmexp
        have hle1 : dirVal ρ2.1 ρ2.2 m.1 m.2 ≤ dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 := by
          have hh := hcase tm htmmem
          rwa [htm1] at hh
        have hle2 : dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 ≤ dirVal ρ2.1 ρ2.2 m.1 m.2 :=
          maxVert_max hm (List.mem_map.mpr ⟨a1, ha1terms, rfl⟩)
        exact faceTerms_mem.mpr ⟨m, hm, ha1terms, le_antisymm hle2 hle1⟩
    have hfb := face_between_singleton ha1face ha1face2 hcross hα hβ hρ
    exact ⟨a1, ha1face, ha1face2, hfb.1, hfb.2⟩

/-- Face term maximizing the secondary valuation (1,−1): the
    st-candidate, by first-max recursion over the face list. -/
def stFaceAux : List Term → Option Term
  | [] => none
  | t :: ts =>
    match stFaceAux ts with
    | none => some t
    | some s => if dirVal 1 (-1) s.1.1 s.1.2 ≤ dirVal 1 (-1) t.1.1 t.1.2
                then some t else some s

/-- Face term maximizing the secondary valuation (−1,1): the
    en-candidate. -/
def enFaceAux : List Term → Option Term
  | [] => none
  | t :: ts =>
    match enFaceAux ts with
    | none => some t
    | some s => if dirVal (-1) 1 s.1.1 s.1.2 ≤ dirVal (-1) 1 t.1.1 t.1.2
                then some t else some s

theorem stFaceAux_mem {ts : List Term} {s : Term} :
    stFaceAux ts = some s → s ∈ ts := by
  induction ts with
  | nil => simp [stFaceAux]
  | cons t ts ih =>
    intro h
    simp only [stFaceAux] at h
    cases hs : stFaceAux ts with
    | none =>
      simp only [hs] at h
      have hv : t = s := Option.some.inj h
      subst hv
      exact List.mem_cons_self
    | some u =>
      simp only [hs] at h
      by_cases hle : dirVal 1 (-1) u.1.1 u.1.2 ≤ dirVal 1 (-1) t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        have hv : t = s := Option.some.inj h
        subst hv
        exact List.mem_cons_self
      · simp only [hle, ite_false] at h
        have hv : u = s := Option.some.inj h
        subst hv
        exact List.mem_cons_of_mem t (ih hs)

theorem stFaceAux_none {ts : List Term} :
    stFaceAux ts = none → ts = [] := by
  cases ts with
  | nil => intro _; rfl
  | cons t ts =>
    intro h
    simp only [stFaceAux] at h
    cases hs : stFaceAux ts with
    | none => rw [hs] at h; exact absurd h (Option.some_ne_none t)
    | some v =>
      rw [hs] at h
      dsimp only at h
      by_cases hle : dirVal 1 (-1) v.1.1 v.1.2 ≤ dirVal 1 (-1) t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        exact absurd h (Option.some_ne_none t)
      · simp only [hle, ite_false] at h
        exact absurd h (Option.some_ne_none v)

theorem stFaceAux_max {ts : List Term} {s u : Term} :
    stFaceAux ts = some s → u ∈ ts →
    dirVal 1 (-1) u.1.1 u.1.2 ≤ dirVal 1 (-1) s.1.1 s.1.2 := by
  induction ts generalizing s u with
  | nil => intro _ h; cases h
  | cons t ts ih =>
    intro h hmem
    simp only [stFaceAux] at h
    cases hs : stFaceAux ts with
    | none =>
      simp only [hs] at h
      have hv : t = s := Option.some.inj h
      have hts : ts = [] := stFaceAux_none hs
      subst hts; subst hv
      rcases List.mem_cons.mp hmem with rfl | hm
      · omega
      · cases hm
    | some v =>
      simp only [hs] at h
      by_cases hle : dirVal 1 (-1) v.1.1 v.1.2 ≤ dirVal 1 (-1) t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        have hv : t = s := Option.some.inj h
        subst hv
        rcases List.mem_cons.mp hmem with rfl | hm
        · omega
        · have h1 := ih hs hm
          omega
      · simp only [hle, ite_false] at h
        have hv : v = s := Option.some.inj h
        subst hv
        rcases List.mem_cons.mp hmem with rfl | hm
        · omega
        · exact ih hs hm

theorem enFaceAux_mem {ts : List Term} {s : Term} :
    enFaceAux ts = some s → s ∈ ts := by
  induction ts with
  | nil => simp [enFaceAux]
  | cons t ts ih =>
    intro h
    simp only [enFaceAux] at h
    cases hs : enFaceAux ts with
    | none =>
      simp only [hs] at h
      have hv : t = s := Option.some.inj h
      subst hv
      exact List.mem_cons_self
    | some u =>
      simp only [hs] at h
      by_cases hle : dirVal (-1) 1 u.1.1 u.1.2 ≤ dirVal (-1) 1 t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        have hv : t = s := Option.some.inj h
        subst hv
        exact List.mem_cons_self
      · simp only [hle, ite_false] at h
        have hv : u = s := Option.some.inj h
        subst hv
        exact List.mem_cons_of_mem t (ih hs)

theorem enFaceAux_none {ts : List Term} :
    enFaceAux ts = none → ts = [] := by
  cases ts with
  | nil => intro _; rfl
  | cons t ts =>
    intro h
    simp only [enFaceAux] at h
    cases hs : enFaceAux ts with
    | none => rw [hs] at h; exact absurd h (Option.some_ne_none t)
    | some v =>
      rw [hs] at h
      dsimp only at h
      by_cases hle : dirVal (-1) 1 v.1.1 v.1.2 ≤ dirVal (-1) 1 t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        exact absurd h (Option.some_ne_none t)
      · simp only [hle, ite_false] at h
        exact absurd h (Option.some_ne_none v)

theorem enFaceAux_max {ts : List Term} {s u : Term} :
    enFaceAux ts = some s → u ∈ ts →
    dirVal (-1) 1 u.1.1 u.1.2 ≤ dirVal (-1) 1 s.1.1 s.1.2 := by
  induction ts generalizing s u with
  | nil => intro _ h; cases h
  | cons t ts ih =>
    intro h hmem
    simp only [enFaceAux] at h
    cases hs : enFaceAux ts with
    | none =>
      simp only [hs] at h
      have hv : t = s := Option.some.inj h
      have hts : ts = [] := enFaceAux_none hs
      subst hts; subst hv
      rcases List.mem_cons.mp hmem with rfl | hm
      · omega
      · cases hm
    | some v =>
      simp only [hs] at h
      by_cases hle : dirVal (-1) 1 v.1.1 v.1.2 ≤ dirVal (-1) 1 t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        have hv : t = s := Option.some.inj h
        subst hv
        rcases List.mem_cons.mp hmem with rfl | hm
        · omega
        · have h1 := ih hs hm
          omega
      · simp only [hle, ite_false] at h
        have hv : v = s := Option.some.inj h
        subst hv
        rcases List.mem_cons.mp hmem with rfl | hm
        · omega
        · exact ih hs hm

/-- [GGV1] st of a face, for (ρ,σ) ∈ V_{>0}: the face term
    maximizing (1,−1), i.e. Supp(ℓ_{1,−1}(ℓ_{ρ,σ}(P))). -/
def stFace (ρ σ : Int) (terms : List Term) : Option Term :=
  stFaceAux (faceTerms ρ σ terms)

/-- [GGV1] en of a face, for (ρ,σ) ∈ V_{>0}: the face term
    maximizing (−1,1), i.e. Supp(ℓ_{−1,1}(ℓ_{ρ,σ}(P))). -/
def enFace (ρ σ : Int) (terms : List Term) : Option Term :=
  enFaceAux (faceTerms ρ σ terms)

/-- st lies in the face and maximizes (1,−1) over it. -/
theorem stFace_mem_max {ρ σ : Int} {terms : List Term} {s u : Term}
    (h : stFace ρ σ terms = some s) (hu : u ∈ faceTerms ρ σ terms) :
    s ∈ faceTerms ρ σ terms ∧
    dirVal 1 (-1) u.1.1 u.1.2 ≤ dirVal 1 (-1) s.1.1 s.1.2 :=
  ⟨stFaceAux_mem h, stFaceAux_max h hu⟩

/-- en lies in the face and maximizes (−1,1) over it. -/
theorem enFace_mem_max {ρ σ : Int} {terms : List Term} {s u : Term}
    (h : enFace ρ σ terms = some s) (hu : u ∈ faceTerms ρ σ terms) :
    s ∈ faceTerms ρ σ terms ∧
    dirVal (-1) 1 u.1.1 u.1.2 ≤ dirVal (-1) 1 s.1.1 s.1.2 :=
  ⟨enFaceAux_mem h, enFaceAux_max h hu⟩

/-- Slice-maximizer uniqueness: a tie on (ρ,σ) and on (1,−1) forces
    equality, provided ρ+σ ≠ 0. -/
theorem slice_tie_unique {ρ σ : Int} (hne : ρ + σ ≠ 0)
    {s t : Int × Int}
    (hρ : dirVal ρ σ s.1 s.2 = dirVal ρ σ t.1 t.2)
    (h1 : dirVal 1 (-1) s.1 s.2 = dirVal 1 (-1) t.1 t.2) :
    s = t := by
  simp only [dirVal] at hρ h1
  have hd : s.1 - t.1 = s.2 - t.2 := by omega
  have h3 : (ρ + σ) * (s.1 - t.1) = 0 := by
    calc (ρ + σ) * (s.1 - t.1)
        = ρ * (s.1 - t.1) + σ * (s.2 - t.2) := by rw [← hd]; ring
      _ = (ρ * s.1 + σ * s.2) - (ρ * t.1 + σ * t.2) := by ring
      _ = 0 := sub_eq_zero.mpr hρ
  have hd1 : s.1 - t.1 = 0 := by
    rcases (mul_eq_zero.mp h3) with h | h
    · exact absurd h hne
    · exact h
  have e1 : s.1 = t.1 := sub_eq_zero.mp hd1
  have e2 : s.2 = t.2 := by
    have : s.2 - t.2 = 0 := by rw [← hd]; exact hd1
    exact sub_eq_zero.mp this
  exact Prod.ext e1 e2

/-- Excess ρ₂-valuation of u over the base exponent A. -/
def slopeD1 (ρ2 : Int × Int) (A : Int × Int) (u : Term) : Int :=
  dirVal ρ2.1 ρ2.2 u.1.1 u.1.2 - dirVal ρ2.1 ρ2.2 A.1 A.2

/-- ρ₁-valuation deficit of u below the base exponent A. -/
def slopeD2 (ρ1 : Int × Int) (A : Int × Int) (u : Term) : Int :=
  dirVal ρ1.1 ρ1.2 A.1 A.2 - dirVal ρ1.1 ρ1.2 u.1.1 u.1.2

/-- Slope-minimal element of a nonempty list of terms above A, compared
    by cross-multiplication (so the slopes stay integers). -/
theorem slope_min_exists {ρ1 ρ2 : Int × Int} {A : Int × Int} :
    ∀ (L : List Term), L ≠ [] → (∀ u ∈ L, 0 < slopeD1 ρ2 A u) →
      ∃ us ∈ L, ∀ u ∈ L, slopeD2 ρ1 A us * slopeD1 ρ2 A u ≤
        slopeD2 ρ1 A u * slopeD1 ρ2 A us := by
  intro L
  induction L with
  | nil => intro hne _; exact absurd rfl hne
  | cons x xs ih =>
    intro _ habove
    cases xs with
    | nil =>
      refine ⟨x, List.mem_cons_self, ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hm
      · exact le_refl _
      · simp at hm
    | cons y ys =>
      have habove' : ∀ u ∈ (y :: ys), 0 < slopeD1 ρ2 A u :=
        fun u hu => habove u (List.mem_cons_of_mem x hu)
      obtain ⟨us, husmem, husmin⟩ := ih (by simp) habove'
      by_cases hcmp : slopeD2 ρ1 A x * slopeD1 ρ2 A us ≤
          slopeD2 ρ1 A us * slopeD1 ρ2 A x
      · refine ⟨x, List.mem_cons_self, ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hum
        · exact le_refl _
        · have h1 := husmin u hum
          have hp1 : 0 < slopeD1 ρ2 A u := habove' u hum
          have hp2 : 0 < slopeD1 ρ2 A us := habove' us husmem
          have hp3 : 0 < slopeD1 ρ2 A x := habove x List.mem_cons_self
          have m1 : slopeD2 ρ1 A us * slopeD1 ρ2 A u * slopeD1 ρ2 A x ≤
              slopeD2 ρ1 A u * slopeD1 ρ2 A us * slopeD1 ρ2 A x :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hp3)
          have m2 : slopeD2 ρ1 A x * slopeD1 ρ2 A us * slopeD1 ρ2 A u ≤
              slopeD2 ρ1 A us * slopeD1 ρ2 A x * slopeD1 ρ2 A u :=
            mul_le_mul_of_nonneg_right hcmp (le_of_lt hp1)
          have chain : slopeD2 ρ1 A x * slopeD1 ρ2 A u * slopeD1 ρ2 A us ≤
              slopeD2 ρ1 A u * slopeD1 ρ2 A x * slopeD1 ρ2 A us := by
            calc slopeD2 ρ1 A x * slopeD1 ρ2 A u * slopeD1 ρ2 A us
                = slopeD2 ρ1 A x * slopeD1 ρ2 A us * slopeD1 ρ2 A u := by ring
              _ ≤ slopeD2 ρ1 A us * slopeD1 ρ2 A x * slopeD1 ρ2 A u := m2
              _ = slopeD2 ρ1 A us * slopeD1 ρ2 A u * slopeD1 ρ2 A x := by ring
              _ ≤ slopeD2 ρ1 A u * slopeD1 ρ2 A us * slopeD1 ρ2 A x := m1
              _ = slopeD2 ρ1 A u * slopeD1 ρ2 A x * slopeD1 ρ2 A us := by ring
          exact le_of_mul_le_mul_right chain hp2
      · refine ⟨us, List.mem_cons_of_mem x husmem, ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hum
        · exact le_of_lt (lt_of_not_ge hcmp)
        · exact husmin u hum

/-- Breakpoint core: with D1, D2 abstract positive integers tied to us
    by hD1/hD2, the direction δ = D1·ρ₁ + D2·ρ₂ is strictly between
    ρ₁ and ρ₂ and isDir (a1 and us are both in its face). -/
theorem breakpoint_core {ρ1 ρ2 : Int × Int} {terms : List Term}
    {a1 us : Term} {D1 D2 : Int}
    (h12 : dirLt ρ1 ρ2)
    (ha1face : a1 ∈ faceTerms ρ1.1 ρ1.2 terms)
    (hD1 : D1 = dirVal ρ2.1 ρ2.2 us.1.1 us.1.2 - dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2)
    (hD2 : D2 = dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 - dirVal ρ1.1 ρ1.2 us.1.1 us.1.2)
    (hD1pos : 0 < D1) (hD2pos : 0 < D2)
    (hρ1max : ∀ t ∈ terms,
      dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 ≤ dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2)
    (hmin : ∀ t ∈ terms,
      dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 < dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 →
      D2 * (dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 - dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2) ≤
      (dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 - dirVal ρ1.1 ρ1.2 t.1.1 t.1.2) * D1)
    (husterms : us ∈ terms) :
    ∃ δ : Int × Int, dirLt ρ1 δ ∧ dirLt δ ρ2 ∧ isDir δ.1 δ.2 terms := by
  have h12' : 0 < crossProd ρ1 ρ2 := h12
  have ha1terms : a1 ∈ terms := faceTerms_subset ha1face
  have htermsne : terms ≠ [] := by
    intro hnil
    rw [hnil] at ha1terms
    exact List.not_mem_nil ha1terms
  -- Valuation difference of δ, as a linear form in D1, D2.
  have key : ∀ t : Term,
      dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) t.1.1 t.1.2
        - dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) a1.1.1 a1.1.2
        = D1 * (dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 - dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2)
          + D2 * (dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 - dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2) := by
    intro t
    simp only [dirVal]
    ring
  -- a1 maximizes δ-valuation over all terms.
  have hmax : ∀ t ∈ terms,
      dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) t.1.1 t.1.2 ≤
      dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) a1.1.1 a1.1.2 := by
    intro t ht
    have hρ1le := hρ1max t ht
    by_cases ht2 : dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 ≤ dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2
    · have h1 : D1 * (dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 - dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hD1pos) (sub_nonpos.mpr hρ1le)
      have h2 : D2 * (dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 - dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hD2pos) (sub_nonpos.mpr ht2)
      have hk := key t
      omega
    · push Not at ht2
      have hm := hmin t ht ht2
      have hk := key t
      nlinarith [hk, hm]
  -- a1 and us tie on δ.
  have htie : dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) us.1.1 us.1.2
      = dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) a1.1.1 a1.1.2 := by
    rw [hD1, hD2]
    simp only [dirVal]
    ring
  -- Any term tying a1 on δ lies in the δ-face.
  have hmem : ∀ t : Term, t ∈ terms →
      dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) t.1.1 t.1.2
        = dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) a1.1.1 a1.1.2 →
      t ∈ faceTerms (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) terms := by
    intro t ht hval
    cases hm : maxVertDir (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2)
        (termExps terms) with
    | none =>
      have hface : faceTerms (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2)
          terms = [] := by
        simp only [faceTerms, hm]
      exact absurd hface (faceTerms_nonempty htermsne)
    | some m =>
      have hmexp : m ∈ termExps terms := maxVert_mem hm
      obtain ⟨tm, htmmem, htm1⟩ := List.mem_map.mp hmexp
      have hle1 : dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) m.1 m.2
          ≤ dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) a1.1.1 a1.1.2 := by
        have hh := hmax tm htmmem
        rwa [htm1] at hh
      have hle2 : dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) a1.1.1 a1.1.2
          ≤ dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) m.1 m.2 :=
        maxVert_max hm (List.mem_map.mpr ⟨a1, ha1terms, rfl⟩)
      have heq : dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) a1.1.1 a1.1.2
          = dirVal (D1 * ρ1.1 + D2 * ρ2.1) (D1 * ρ1.2 + D2 * ρ2.2) m.1 m.2 :=
        le_antisymm hle2 hle1
      exact faceTerms_mem.mpr ⟨m, hm, ht, by omega⟩
  refine ⟨(D1 * ρ1.1 + D2 * ρ2.1, D1 * ρ1.2 + D2 * ρ2.2), ?_, ?_, ?_⟩
  · have e : crossProd ρ1 (D1 * ρ1.1 + D2 * ρ2.1, D1 * ρ1.2 + D2 * ρ2.2)
        = D2 * crossProd ρ1 ρ2 := by
      simp only [crossProd]
      ring
    show 0 < crossProd ρ1 _
    rw [e]
    exact mul_pos hD2pos h12'
  · have e : crossProd (D1 * ρ1.1 + D2 * ρ2.1, D1 * ρ1.2 + D2 * ρ2.2) ρ2
        = D1 * crossProd ρ1 ρ2 := by
      simp only [crossProd]
      ring
    show 0 < crossProd _ ρ2
    rw [e]
    exact mul_pos hD1pos h12'
  · dsimp only
    unfold isDir
    refine ⟨a1, us, hmem a1 ha1terms rfl, hmem us husterms htie, ?_⟩
    intro heq
    have hcontra : dirVal ρ2.1 ρ2.2 us.1.1 us.1.2
        = dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 := by
      rw [heq]
    omega

/-- Breakpoint lemma (replacement for sketched step (B)): let a1 be in
    the ρ₁-face and maximize ρ₂ over the ρ₁-face. If some term b beats
    a1 on ρ₂, then some direction strictly between ρ₁ and ρ₂ isDir. -/
theorem breakpoint_between {ρ1 ρ2 : Int × Int} {terms : List Term}
    {a1 : Term}
    (h12 : dirLt ρ1 ρ2)
    (ha1face : a1 ∈ faceTerms ρ1.1 ρ1.2 terms)
    (ha1max : ∀ t ∈ faceTerms ρ1.1 ρ1.2 terms,
      dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 ≤ dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2)
    {b : Term} (hbmem : b ∈ terms)
    (hb : dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 < dirVal ρ2.1 ρ2.2 b.1.1 b.1.2) :
    ∃ δ : Int × Int, dirLt ρ1 δ ∧ dirLt δ ρ2 ∧ isDir δ.1 δ.2 terms := by
  have ha1terms : a1 ∈ terms := faceTerms_subset ha1face
  set above : List Term := terms.filter
    (fun t => dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 < dirVal ρ2.1 ρ2.2 t.1.1 t.1.2)
    with habove_def
  have hbabove : b ∈ above := by
    rw [habove_def, List.mem_filter]
    exact ⟨hbmem, by simp [hb]⟩
  have habovene : above ≠ [] := by
    intro hnil
    rw [hnil] at hbabove
    exact List.not_mem_nil hbabove
  obtain ⟨us, husabove, husmin⟩ := slope_min_exists (ρ1 := ρ1) (ρ2 := ρ2) (A := a1.1) above habovene (by
    intro u hu
    rw [habove_def, List.mem_filter] at hu
    have hlt := of_decide_eq_true hu.2
    simp only [slopeD1]
    omega)
  have husterms : us ∈ terms := by
    have h := husabove
    rw [habove_def, List.mem_filter] at h
    exact h.1
  have hD1pos : 0 < slopeD1 ρ2 a1.1 us := by
    have h := husabove
    rw [habove_def, List.mem_filter] at h
    have hlt := of_decide_eq_true h.2
    simp only [slopeD1]
    omega
  have hρ1le : dirVal ρ1.1 ρ1.2 us.1.1 us.1.2 ≤ dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 :=
    faceTerms_max ha1face (List.mem_map.mpr ⟨us, husterms, rfl⟩)
  have hD2pos : 0 < slopeD2 ρ1 a1.1 us := by
    have hD2nn : 0 ≤ slopeD2 ρ1 a1.1 us := by
      simp only [slopeD2]
      omega
    apply lt_of_le_of_ne hD2nn
    intro hzero
    have hρ1eq : dirVal ρ1.1 ρ1.2 us.1.1 us.1.2
        = dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 := by
      simp only [slopeD2] at hzero
      omega
    obtain ⟨m, hm, -, hval⟩ := faceTerms_mem.mp ha1face
    have husface : us ∈ faceTerms ρ1.1 ρ1.2 terms :=
      faceTerms_mem.mpr ⟨m, hm, husterms, by omega⟩
    have hle := ha1max us husface
    have hD1pos' := hD1pos
    simp only [slopeD1] at hD1pos'
    omega
  refine breakpoint_core (D1 := slopeD1 ρ2 a1.1 us) (D2 := slopeD2 ρ1 a1.1 us)
    h12 ha1face (by simp only [slopeD1]) (by simp only [slopeD2])
    hD1pos hD2pos ?_ ?_ husterms
  · intro t ht
    exact faceTerms_max ha1face (List.mem_map.mpr ⟨t, ht, rfl⟩)
  · intro t ht ht2
    have htAbove : t ∈ above := by
      rw [habove_def, List.mem_filter]
      exact ⟨ht, by simp [ht2]⟩
    have hmin := husmin t htAbove
    simp only [slopeD1, slopeD2] at hmin
    simp only [slopeD1, slopeD2]
    exact hmin

/-- A direction strictly between two others is a positive rational
    combination of them. -/
theorem dir_between_pos_combo {ρ₁ ρ₂ ρ : Int × Int}
    (h1 : dirLt ρ₁ ρ) (h2 : dirLt ρ ρ₂) (h12 : dirLt ρ₁ ρ₂) :
    ∃ α β : ℚ, 0 < α ∧ 0 < β ∧
      (ρ.1 : ℚ) = α * (ρ₁.1 : ℚ) + β * (ρ₂.1 : ℚ) ∧
      (ρ.2 : ℚ) = α * (ρ₁.2 : ℚ) + β * (ρ₂.2 : ℚ) := by
  have hD : 0 < ((crossProd ρ₁ ρ₂ : Int) : ℚ) := by exact_mod_cast h12
  have hD0 : ((crossProd ρ₁ ρ₂ : Int) : ℚ) ≠ 0 := ne_of_gt hD
  have hC1 : 0 < ((crossProd ρ ρ₂ : Int) : ℚ) := by exact_mod_cast h2
  have hC2 : 0 < ((crossProd ρ₁ ρ : Int) : ℚ) := by exact_mod_cast h1
  -- Cramer identities, multiplied form (first and second components).
  have hI1 : ((crossProd ρ ρ₂ : Int) : ℚ) * (ρ₁.1 : ℚ) +
      ((crossProd ρ₁ ρ : Int) : ℚ) * (ρ₂.1 : ℚ)
      = ((crossProd ρ₁ ρ₂ : Int) : ℚ) * (ρ.1 : ℚ) := by
    simp only [crossProd]
    push_cast
    ring
  have hI2 : ((crossProd ρ ρ₂ : Int) : ℚ) * (ρ₁.2 : ℚ) +
      ((crossProd ρ₁ ρ : Int) : ℚ) * (ρ₂.2 : ℚ)
      = ((crossProd ρ₁ ρ₂ : Int) : ℚ) * (ρ.2 : ℚ) := by
    simp only [crossProd]
    push_cast
    ring
  refine ⟨((crossProd ρ ρ₂ : Int) : ℚ) / ((crossProd ρ₁ ρ₂ : Int) : ℚ),
    ((crossProd ρ₁ ρ : Int) : ℚ) / ((crossProd ρ₁ ρ₂ : Int) : ℚ),
    div_pos hC1 hD, div_pos hC2 hD, ?_, ?_⟩
  · calc (ρ.1 : ℚ)
        = ((crossProd ρ₁ ρ₂ : Int) : ℚ) * (ρ.1 : ℚ) /
            ((crossProd ρ₁ ρ₂ : Int) : ℚ) := by
          rw [mul_div_cancel_left₀ _ hD0]
      _ = (((crossProd ρ ρ₂ : Int) : ℚ) * (ρ₁.1 : ℚ) +
            ((crossProd ρ₁ ρ : Int) : ℚ) * (ρ₂.1 : ℚ)) /
            ((crossProd ρ₁ ρ₂ : Int) : ℚ) := by
          rw [hI1]
      _ = ((crossProd ρ ρ₂ : Int) : ℚ) / ((crossProd ρ₁ ρ₂ : Int) : ℚ) *
            (ρ₁.1 : ℚ) + ((crossProd ρ₁ ρ : Int) : ℚ) /
            ((crossProd ρ₁ ρ₂ : Int) : ℚ) * (ρ₂.1 : ℚ) := by
          rw [add_div, div_mul_eq_mul_div, div_mul_eq_mul_div]
  · calc (ρ.2 : ℚ)
        = ((crossProd ρ₁ ρ₂ : Int) : ℚ) * (ρ.2 : ℚ) /
            ((crossProd ρ₁ ρ₂ : Int) : ℚ) := by
          rw [mul_div_cancel_left₀ _ hD0]
      _ = (((crossProd ρ ρ₂ : Int) : ℚ) * (ρ₁.2 : ℚ) +
            ((crossProd ρ₁ ρ : Int) : ℚ) * (ρ₂.2 : ℚ)) /
            ((crossProd ρ₁ ρ₂ : Int) : ℚ) := by
          rw [hI2]
      _ = ((crossProd ρ ρ₂ : Int) : ℚ) / ((crossProd ρ₁ ρ₂ : Int) : ℚ) *
            (ρ₁.2 : ℚ) + ((crossProd ρ₁ ρ : Int) : ℚ) /
            ((crossProd ρ₁ ρ₂ : Int) : ℚ) * (ρ₂.2 : ℚ) := by
          rw [add_div, div_mul_eq_mul_div, div_mul_eq_mul_div]


/-- Slice-maximizer uniqueness, (−1,1) mirror: a tie on (ρ,σ) and on
    (−1,1) forces equality, provided ρ+σ ≠ 0. (A (−1,1)-tie is a
    (1,−1)-tie negated.) -/
theorem slice_tie_unique_en {ρ σ : Int} (hne : ρ + σ ≠ 0)
    {s t : Int × Int}
    (hρ : dirVal ρ σ s.1 s.2 = dirVal ρ σ t.1 t.2)
    (h1 : dirVal (-1) 1 s.1 s.2 = dirVal (-1) 1 t.1 t.2) :
    s = t := by
  apply slice_tie_unique hne hρ
  simp only [dirVal] at h1 ⊢
  omega

/-- Endpoint-incidence (the missing step to FULL le basico): a term `a1`
    lying in BOTH the ρ₁-face and the ρ₂-face maximizes the (−1,1)-slice
    over the ρ₁-face and the (1,−1)-slice over the ρ₂-face, provided
    ρ₁, ρ₂ ∈ V_{≥0} (sums ≥ 0) and `crossProd ρ₁ ρ₂ > 0`. -/
theorem endpoint_slice_max {ρ1 ρ2 : Int × Int} {terms : List Term}
    {a1 : Term}
    (hC : 0 < crossProd ρ1 ρ2)
    (h1sum : 0 ≤ ρ1.1 + ρ1.2) (h2sum : 0 ≤ ρ2.1 + ρ2.2)
    (ha1face1 : a1 ∈ faceTerms ρ1.1 ρ1.2 terms)
    (ha1face2 : a1 ∈ faceTerms ρ2.1 ρ2.2 terms) :
    (∀ t ∈ faceTerms ρ1.1 ρ1.2 terms,
      dirVal (-1) 1 t.1.1 t.1.2 ≤ dirVal (-1) 1 a1.1.1 a1.1.2) ∧
    (∀ t ∈ faceTerms ρ2.1 ρ2.2 terms,
      dirVal 1 (-1) t.1.1 t.1.2 ≤ dirVal 1 (-1) a1.1.1 a1.1.2) := by
  have ha1terms : a1 ∈ terms := faceTerms_subset ha1face1
  constructor
  · intro t ht
    have htterms : t ∈ terms := faceTerms_subset ht
    have eρ1 : dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 = dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 :=
      le_antisymm
        (faceTerms_max ha1face1 (List.mem_map.mpr ⟨t, htterms, rfl⟩))
        (faceTerms_max ht (List.mem_map.mpr ⟨a1, ha1terms, rfl⟩))
    have hρ2le : dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 ≤ dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 :=
      faceTerms_max ha1face2 (List.mem_map.mpr ⟨t, htterms, rfl⟩)
    have hId : crossProd ρ1 ρ2 *
        (dirVal (-1) 1 t.1.1 t.1.2 - dirVal (-1) 1 a1.1.1 a1.1.2)
        = -(ρ2.1 + ρ2.2) * (dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 - dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2)
          + (ρ1.1 + ρ1.2) * (dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 - dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2) := by
      simp only [crossProd, dirVal]
      ring
    have hprod : crossProd ρ1 ρ2 *
        (dirVal (-1) 1 t.1.1 t.1.2 - dirVal (-1) 1 a1.1.1 a1.1.2) ≤ 0 := by
      rw [hId]
      have hz : dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 - dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 = 0 :=
        sub_eq_zero.mpr eρ1
      rw [hz, mul_zero, zero_add]
      exact mul_nonpos_of_nonneg_of_nonpos h1sum (sub_nonpos.mpr hρ2le)
    have hle : dirVal (-1) 1 t.1.1 t.1.2 - dirVal (-1) 1 a1.1.1 a1.1.2 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have hpos : 0 < crossProd ρ1 ρ2 *
          (dirVal (-1) 1 t.1.1 t.1.2 - dirVal (-1) 1 a1.1.1 a1.1.2) :=
        mul_pos hC hcon
      omega
    exact sub_nonpos.mp hle
  · intro t ht
    have htterms : t ∈ terms := faceTerms_subset ht
    have eρ2 : dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 = dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 :=
      le_antisymm
        (faceTerms_max ha1face2 (List.mem_map.mpr ⟨t, htterms, rfl⟩))
        (faceTerms_max ht (List.mem_map.mpr ⟨a1, ha1terms, rfl⟩))
    have hρ1le : dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 ≤ dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 :=
      faceTerms_max ha1face1 (List.mem_map.mpr ⟨t, htterms, rfl⟩)
    have hId : crossProd ρ1 ρ2 *
        (dirVal 1 (-1) t.1.1 t.1.2 - dirVal 1 (-1) a1.1.1 a1.1.2)
        = (ρ2.1 + ρ2.2) * (dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 - dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2)
          - (ρ1.1 + ρ1.2) * (dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 - dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2) := by
      simp only [crossProd, dirVal]
      ring
    have hprod : crossProd ρ1 ρ2 *
        (dirVal 1 (-1) t.1.1 t.1.2 - dirVal 1 (-1) a1.1.1 a1.1.2) ≤ 0 := by
      rw [hId]
      have hz : dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 - dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 = 0 :=
        sub_eq_zero.mpr eρ2
      rw [hz, mul_zero, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos h2sum (sub_nonpos.mpr hρ1le)
    have hle : dirVal 1 (-1) t.1.1 t.1.2 - dirVal 1 (-1) a1.1.1 a1.1.2 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have hpos : 0 < crossProd ρ1 ρ2 *
          (dirVal 1 (-1) t.1.1 t.1.2 - dirVal 1 (-1) a1.1.1 a1.1.2) :=
        mul_pos hC hcon
      omega
    exact sub_nonpos.mp hle

/-- le basico, FULL (exponent level): for consecutive directions
    ρ₁ < ρ₂ in Dir(P) (via isSuccFrom + hdirs), both in V_{>0},
    and ρ strictly between them, the ρ-face is the single shared
    vertex a1, and a1 is both en_{ρ₁} and st_{ρ₂} (at exponent level,
    via Part17's enFace/stFace). Assembles `consecutive_weak_lebasico`
    (with `breakpoint_between` plugged for `hbreak`),
    `dir_between_pos_combo`, and the endpoint-incidence lemma
    `endpoint_slice_max`, with the st/en identification via
    `slice_tie_unique` (+ the (−1,1) mirror). -/
theorem le_basico_full {ρ1 ρ2 ρ : Int × Int} {terms : List Term}
    {dirs : List (Int × Int)}
    (hsucc : isSuccFrom ρ1 ρ2 dirs)
    (hdirs : ∀ δ : Int × Int, δ ∈ dirs ↔ isDir δ.1 δ.2 terms)
    (hter : terms ≠ [])
    (hρ1 : dirLt ρ1 ρ) (hρ : dirLt ρ ρ2)
    (h1sum : 0 < ρ1.1 + ρ1.2) (h2sum : 0 < ρ2.1 + ρ2.2) :
    ∃ a1 : Term, a1 ∈ faceTerms ρ1.1 ρ1.2 terms ∧ a1 ∈ faceTerms ρ2.1 ρ2.2 terms ∧
      (∀ u ∈ faceTerms ρ.1 ρ.2 terms, u.1 = a1.1) ∧ a1 ∈ faceTerms ρ.1 ρ.2 terms ∧
      (∃ e : Term, enFace ρ1.1 ρ1.2 terms = some e ∧ e.1 = a1.1) ∧
      (∃ s : Term, stFace ρ2.1 ρ2.2 terms = some s ∧ s.1 = a1.1) := by
  have h12 : dirLt ρ1 ρ2 := hsucc.2.1
  have hC : 0 < crossProd ρ1 ρ2 := h12
  have hcross : crossProd ρ1 ρ2 ≠ 0 := ne_of_gt hC
  obtain ⟨α, β, hα, hβ, hρcombo⟩ := dir_between_pos_combo hρ1 hρ h12
  obtain ⟨a1, ha1face1, ha1face2, hfaceρ, ha1faceρ⟩ :=
    consecutive_weak_lebasico (ρ1 := ρ1) (ρ2 := ρ2) (ρ := ρ)
      (hbreak := fun {a1} ha1f ha1m {b} hbmem hb =>
        breakpoint_between h12 ha1f ha1m hbmem hb)
      hsucc hdirs hter hcross hα hβ hρcombo
  have ha1terms : a1 ∈ terms := faceTerms_subset ha1face1
  obtain ⟨hinc1, hinc2⟩ :=
    endpoint_slice_max hC h1sum.le h2sum.le ha1face1 ha1face2
  obtain ⟨e, he, heq⟩ : ∃ e : Term,
      enFace ρ1.1 ρ1.2 terms = some e ∧ e.1 = a1.1 := by
    obtain ⟨e, he⟩ : ∃ e, enFace ρ1.1 ρ1.2 terms = some e := by
      cases hnone : enFace ρ1.1 ρ1.2 terms with
      | none =>
        exfalso
        have hnil : faceTerms ρ1.1 ρ1.2 terms = [] := enFaceAux_none hnone
        exact faceTerms_nonempty hter hnil
      | some e => exact ⟨e, rfl⟩
    refine ⟨e, he, ?_⟩
    obtain ⟨hemem, hemax⟩ := enFace_mem_max he ha1face1
    have heterms : e ∈ terms := faceTerms_subset hemem
    have eρ1 : dirVal ρ1.1 ρ1.2 e.1.1 e.1.2 = dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 :=
      le_antisymm
        (faceTerms_max ha1face1 (List.mem_map.mpr ⟨e, heterms, rfl⟩))
        (faceTerms_max hemem (List.mem_map.mpr ⟨a1, ha1terms, rfl⟩))
    have htie_en : dirVal (-1) 1 e.1.1 e.1.2 = dirVal (-1) 1 a1.1.1 a1.1.2 :=
      le_antisymm (hinc1 e hemem) hemax
    exact slice_tie_unique_en (ne_of_gt h1sum) eρ1 htie_en
  obtain ⟨s, hs, hsq⟩ : ∃ s : Term,
      stFace ρ2.1 ρ2.2 terms = some s ∧ s.1 = a1.1 := by
    obtain ⟨s, hs⟩ : ∃ s, stFace ρ2.1 ρ2.2 terms = some s := by
      cases hnone : stFace ρ2.1 ρ2.2 terms with
      | none =>
        exfalso
        have hnil : faceTerms ρ2.1 ρ2.2 terms = [] := stFaceAux_none hnone
        exact faceTerms_nonempty hter hnil
      | some s => exact ⟨s, rfl⟩
    refine ⟨s, hs, ?_⟩
    obtain ⟨hsmem, hsmax⟩ := stFace_mem_max hs ha1face2
    have hsterms : s ∈ terms := faceTerms_subset hsmem
    have eρ2 : dirVal ρ2.1 ρ2.2 s.1.1 s.1.2 = dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 :=
      le_antisymm
        (faceTerms_max ha1face2 (List.mem_map.mpr ⟨s, hsterms, rfl⟩))
        (faceTerms_max hsmem (List.mem_map.mpr ⟨a1, ha1terms, rfl⟩))
    have htie_st : dirVal 1 (-1) s.1.1 s.1.2 = dirVal 1 (-1) a1.1.1 a1.1.2 :=
      le_antisymm (hinc2 s hsmem) hsmax
    exact slice_tie_unique (ne_of_gt h2sum) eρ2 htie_st
  exact ⟨a1, ha1face1, ha1face2, hfaceρ, ha1faceρ, ⟨e, he, heq⟩, ⟨s, hs, hsq⟩⟩

/- LE BBASICO (converse of le basico, TeX 1359) — shared vertex ⟹
   consecutiveness, at exponent level. The paper gives NO proof
   ("completely clear") — original polygon combinatorics, like le basico.

   Proof (contrapositive): a δ strictly between with isDir δ has two
   face terms a, b with distinct exponents; but the shared vertex term
   e lies in both the ρ₁-face and the ρ₂-face, so by
   `face_between_singleton` (δ is a positive rational combination of
   ρ₁, ρ₂) every δ-face term shares e's exponent — contradicting
   a.1 ≠ b.1. The chord-normal route is NOT used (refuted 2026-11-04
   by the convex-octagon counterexample). No V_{>0} sum hypotheses
   are needed: the argument uses only face maximality + the
   combination, not slice uniqueness. -/
theorem le_bbasico {ρ1 ρ2 : Int × Int} {terms : List Term}
    {dirs : List (Int × Int)}
    (hdirs : ∀ δ : Int × Int, δ ∈ dirs ↔ isDir δ.1 δ.2 terms)
    (h12 : dirLt ρ1 ρ2)
    {e s : Term}
    (hen : enFace ρ1.1 ρ1.2 terms = some e)
    (hst : stFace ρ2.1 ρ2.2 terms = some s)
    (hshare : e.1 = s.1) :
    ∀ δ : Int × Int, δ ∈ dirs → ¬ (dirLt ρ1 δ ∧ dirLt δ ρ2) := by
  intro δ hδmem hbetween
  obtain ⟨hδ1, hδ2⟩ := hbetween
  have hδisDir : isDir δ.1 δ.2 terms := (hdirs δ).mp hδmem
  obtain ⟨a, b, ha, hb, hab⟩ := hδisDir
  have hemem : e ∈ faceTerms ρ1.1 ρ1.2 terms := enFaceAux_mem hen
  have hsmem : s ∈ faceTerms ρ2.1 ρ2.2 terms := stFaceAux_mem hst
  have he2 : e ∈ faceTerms ρ2.1 ρ2.2 terms := by
    obtain ⟨m, hm, -, hsval⟩ := faceTerms_mem.mp hsmem
    refine faceTerms_mem.mpr ⟨m, hm, faceTerms_subset hemem, ?_⟩
    have e1 : e.1.1 = s.1.1 := congrArg Prod.fst hshare
    have e2 : e.1.2 = s.1.2 := congrArg Prod.snd hshare
    rw [e1, e2]
    exact hsval
  obtain ⟨α, β, hα, hβ, hρcombo⟩ := dir_between_pos_combo hδ1 hδ2 h12
  have hC : 0 < crossProd ρ1 ρ2 := h12
  have hcross : crossProd ρ1 ρ2 ≠ 0 := ne_of_gt hC
  obtain ⟨hsingle, -⟩ := face_between_singleton hemem he2 hcross hα hβ hρcombo
  have ha1 : a.1 = e.1 := hsingle a ha
  have hb1 : b.1 = e.1 := hsingle b hb
  exact hab (ha1.trans hb1.symm)

/- EXTREMOS PAIR (TeX 694/721) + COMMUTATOR VALUATION (480) — exponent level.
   2026-11-05. Self-contained scratch (base = the D1 layer of
   d1_lebbasico_2026-11-05.lean through `slice_tie_unique_en`), not a repo module.

   MATHEMATICAL CONTENT. The paper proofs of both extremos reduce to ONE
   computation: the bracket of two monomials. If A, B are exponents with
   coefficients α, β, then [x^A, x^B] has coefficient αβ·(A×B) and
   exponent A+B−(1,1). The (ρ₀,σ₀)-slice of a face polynomial ℓ(P) is the
   monomial at st(P) (slice direction (1,−1)) resp. en(P) (direction
   (−1,1)) — for (ρ,σ) ∈ V_{>0} these are exactly Part17's stFace/enFace
   (inventory: "Starting-vs-end node CLOSED"). So both extremos are
   statements about the bracket of the two face polynomials seen through
   its (1,−1)- resp. (−1,1)-top slice, and the proofs are the slice
   lemmas `brkTerm_top_mem` / `brkTerm_top_pair_st|en` below.

   WORKING LEVEL AND HONEST HYPOTHESES. The paper states [ℓ(P),ℓ(Q)] = 0
   and [ℓ(P),ℓ(Q)] = ℓ(R) as identities of COMBINED polynomials (like
   terms merged, coefficient sums per exponent). This file works with the
   UNCOMBINED pairwise bracket list `bracket ps qs` (the D2 polynomial-
   bracket layer — bilinearity + combining like terms — is still open;
   Part7 proves only the monomial case). Therefore:
   * `extremos_alineados` takes the PAIRWISE vanishing hypothesis
     `∀ t ∈ bracket faceP faceQ, t.2 = 0`, which is STRONGER than the
     paper's combined vanishing (it rules out cancellation between
     different pairs at one exponent a priori). The slice argument below
     consumes only its top-face consequence; the upgrade to the combined
     form is exactly the open D2 step: prove
     `coeffAt (sP.1+sQ.1−(1,1)) (bracket faceP faceQ)
        = k * (sP.2 * sQ.2 * crossProd sP.1 sQ.1)` with `k ≥ 1`
     (all top-face terms share one exponent and one coefficient value,
     by `brkTerm_top_pair_st`), from which combined-vanishing gives
     cross = 0. That bridge lemma is NOT proved here.
   * `extremos_noalineados_st|en` take the SLICE hypothesis `hbr`: the
     top (1,−1)- resp. (−1,1)-slice of the bracket is the monomial at
     sR.1 resp. eR.1. This is exactly the slice form of [ℓ(P),ℓ(Q)] =
     ℓ(R) that the paper's proof consumes (its chvh4 step is the
     identification of the slice bracket with the slice of R); the
     passage from the full polynomial identity to `hbr` is the same
     open combine-like-terms step.
   * The (ρ,σ) ∈ V_{>0} hypothesis `hV : 0 < ρ + σ` is the SETTING
     hypothesis: it is what makes (1,−1) resp. (−1,1) a sandwich
     direction, hence what identifies Part17's stFace/enFace with the
     paper's st/en. The algebra below uses only `ρ + σ ≠ 0`.
   * Exponents are plain integers (l = 1, as in the le basico files);
     the bracket shift is (1,1). For general l the shift is (l,1) and
     the proofs are identical.
   * The aligned→multiple bridge (Remark ~497) is proved over ℚ below. -/

/-- Monomial bracket coefficient: cross product of the exponents
    (Part7's `bracketCoeff`). -/
def brkCoeff (m n : Int × Int) : Int := crossProd m n

/-- Monomial bracket exponent: sum minus (1,1) (Part7's `bracketExp`). -/
def brkExp (m n : Int × Int) : Int × Int := (m.1 + n.1 - 1, m.2 + n.2 - 1)

/-- Monomial bracket of two terms: coefficient αβ·(A×B), exponent
    A+B−(1,1). -/
def brkTerm (m n : Term) : Term :=
  (brkExp m.1 n.1, m.2 * n.2 * brkCoeff m.1 n.1)

/-- Bracket of two term lists: all pairwise monomial brackets,
    UNCOMBINED (see header). -/
def bracket (ps qs : List Term) : List Term :=
  ps.flatMap (fun m => qs.map (brkTerm m))

/-- Membership in the bracket list. -/
theorem bracket_mem {ps qs : List Term} {t : Term} :
    t ∈ bracket ps qs ↔ ∃ m ∈ ps, ∃ n ∈ qs, t = brkTerm m n := by
  simp only [bracket, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨m, hm, n, hn, rfl⟩
    exact ⟨m, hm, n, hn, rfl⟩
  · rintro ⟨m, hm, n, hn, rfl⟩
    exact ⟨m, hm, n, hn, rfl⟩

/-- Valuation of a monomial bracket term (Remark 453(1) at monomial
    level; the decomposition's valuation shift). -/
theorem brkTerm_val {ρ σ : Int} {m n : Term} :
    dirVal ρ σ (brkTerm m n).1.1 (brkTerm m n).1.2 =
    dirVal ρ σ m.1.1 m.1.2 + dirVal ρ σ n.1.1 n.1.2 - (ρ + σ) := by
  simp only [brkTerm, brkExp, dirVal]
  ring

/-- The bracket coefficient of a monomial bracket term. -/
theorem brkTerm_coeff {m n : Term} :
    (brkTerm m n).2 = m.2 * n.2 * crossProd m.1 n.1 := rfl

/-- The bracket exponent of a monomial bracket term. -/
theorem brkTerm_exp {m n : Term} :
    (brkTerm m n).1 = (m.1.1 + n.1.1 - 1, m.1.2 + n.1.2 - 1) := rfl

/- ### Commutator valuation (TeX 480) and Remark 453 -/

/-- (480) inequality: every bracket term's (ρ,σ)-valuation is at most
    vP + vQ − (ρ+σ), where vP, vQ bound the factors' valuations. -/
theorem bracket_val_le {ρ σ : Int} {termsP termsQ : List Term}
    {vP vQ : Int}
    (hP : ∀ m ∈ termsP, dirVal ρ σ m.1.1 m.1.2 ≤ vP)
    (hQ : ∀ n ∈ termsQ, dirVal ρ σ n.1.1 n.1.2 ≤ vQ)
    {t : Term} (ht : t ∈ bracket termsP termsQ) :
    dirVal ρ σ t.1.1 t.1.2 ≤ vP + vQ - (ρ + σ) := by
  obtain ⟨m, hm, n, hn, rfl⟩ := bracket_mem.mp ht
  rw [brkTerm_val]
  have h1 := hP m hm
  have h2 := hQ n hn
  omega

/-- (453)(1), homogeneous case: if all terms of each factor share one
    (ρ,σ)-value, every bracket term has value vP + vQ − (ρ+σ). -/
theorem bracket_homog_val {ρ σ : Int} {termsP termsQ : List Term}
    {vP vQ : Int}
    (hP : ∀ m ∈ termsP, dirVal ρ σ m.1.1 m.1.2 = vP)
    (hQ : ∀ n ∈ termsQ, dirVal ρ σ n.1.1 n.1.2 = vQ)
    {t : Term} (ht : t ∈ bracket termsP termsQ) :
    dirVal ρ σ t.1.1 t.1.2 = vP + vQ - (ρ + σ) := by
  obtain ⟨m, hm, n, hn, rfl⟩ := bracket_mem.mp ht
  rw [brkTerm_val, hP m hm, hQ n hn]

/-- Face membership via a given maximal-valuation vertex. -/
theorem faceTerms_mem_of_max {ρ σ : Int} {terms : List Term} {m0 : Int × Int}
    (h0 : maxVertDir ρ σ (termExps terms) = some m0) {t : Term} :
    t ∈ faceTerms ρ σ terms ↔
    t ∈ terms ∧ dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m0.1 m0.2 := by
  constructor
  · intro h
    obtain ⟨m, hm, ht, hval⟩ := faceTerms_mem.mp h
    have hmm : m = m0 := Option.some.inj (hm.symm.trans h0)
    subst hmm
    exact ⟨ht, hval⟩
  · rintro ⟨ht, hval⟩
    exact faceTerms_mem.mpr ⟨m0, h0, ht, hval⟩

/-- The maximal (ρ,σ)-valuation over the bracket list is
    vP + vQ − (ρ+σ): the max vertex of the bracket attains it. -/
theorem bracket_max_vert {ρ σ : Int} {termsP termsQ : List Term}
    {mP mQ : Int × Int}
    (hP : maxVertDir ρ σ (termExps termsP) = some mP)
    (hQ : maxVertDir ρ σ (termExps termsQ) = some mQ) :
    ∃ mB, maxVertDir ρ σ (termExps (bracket termsP termsQ)) = some mB ∧
      dirVal ρ σ mB.1 mB.2 =
        dirVal ρ σ mP.1 mP.2 + dirVal ρ σ mQ.1 mQ.2 - (ρ + σ) := by
  have hmP : mP ∈ termExps termsP := maxVert_mem hP
  have hmQ : mQ ∈ termExps termsQ := maxVert_mem hQ
  obtain ⟨tP, htP, htP1⟩ := List.mem_map.mp hmP
  obtain ⟨tQ, htQ, htQ1⟩ := List.mem_map.mp hmQ
  have hbr : brkTerm tP tQ ∈ bracket termsP termsQ :=
    bracket_mem.mpr ⟨tP, htP, tQ, htQ, rfl⟩
  have hbrne : bracket termsP termsQ ≠ [] := List.ne_nil_of_mem hbr
  have htexp : termExps (bracket termsP termsQ) ≠ [] :=
    List.ne_nil_of_mem (List.mem_map.mpr ⟨brkTerm tP tQ, hbr, rfl⟩)
  cases hB : maxVertDir ρ σ (termExps (bracket termsP termsQ)) with
  | none =>
    exfalso
    exact htexp (maxVert_none hB)
  | some mB =>
    refine ⟨mB, rfl, ?_⟩
    have hmB : mB ∈ termExps (bracket termsP termsQ) := maxVert_mem hB
    obtain ⟨tB, htB, htB1⟩ := List.mem_map.mp hmB
    obtain ⟨m, hm, n, hn, htBr⟩ := bracket_mem.mp htB
    have hle1 : dirVal ρ σ m.1.1 m.1.2 ≤ dirVal ρ σ mP.1 mP.2 :=
      maxVert_max hP (List.mem_map.mpr ⟨m, hm, rfl⟩)
    have hle2 : dirVal ρ σ n.1.1 n.1.2 ≤ dirVal ρ σ mQ.1 mQ.2 :=
      maxVert_max hQ (List.mem_map.mpr ⟨n, hn, rfl⟩)
    have hvalB : dirVal ρ σ mB.1 mB.2 =
        dirVal ρ σ m.1.1 m.1.2 + dirVal ρ σ n.1.1 n.1.2 - (ρ + σ) := by
      rw [← htB1, htBr]
      exact brkTerm_val
    have hle : dirVal ρ σ mB.1 mB.2 ≤
        dirVal ρ σ mP.1 mP.2 + dirVal ρ σ mQ.1 mQ.2 - (ρ + σ) := by
      rw [hvalB]; omega
    have hge : dirVal ρ σ mP.1 mP.2 + dirVal ρ σ mQ.1 mQ.2 - (ρ + σ) ≤
        dirVal ρ σ mB.1 mB.2 := by
      have hwit : dirVal ρ σ (brkTerm tP tQ).1.1 (brkTerm tP tQ).1.2 ≤
          dirVal ρ σ mB.1 mB.2 :=
        maxVert_max hB (List.mem_map.mpr ⟨brkTerm tP tQ, hbr, rfl⟩)
      rw [brkTerm_val, htP1, htQ1] at hwit
      exact hwit
    exact le_antisymm hle hge

/-- (480), identification: the (ρ,σ)-face of the bracket [P,Q] is the
    bracket of the (ρ,σ)-faces [ℓ(P),ℓ(Q)] (membership form). In
    particular the top component of [P,Q] is [ℓ(P),ℓ(Q)] when nonzero. -/
theorem face_bracket_mem {ρ σ : Int} {termsP termsQ : List Term}
    {mP mQ : Int × Int}
    (hP : maxVertDir ρ σ (termExps termsP) = some mP)
    (hQ : maxVertDir ρ σ (termExps termsQ) = some mQ)
    {t : Term} :
    t ∈ faceTerms ρ σ (bracket termsP termsQ) ↔
    t ∈ bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ) := by
  obtain ⟨mB, hB, hBval⟩ := bracket_max_vert hP hQ
  have hPmem : ∀ u : Term, u ∈ faceTerms ρ σ termsP ↔
      u ∈ termsP ∧ dirVal ρ σ u.1.1 u.1.2 = dirVal ρ σ mP.1 mP.2 :=
    fun u => faceTerms_mem_of_max hP
  have hQmem : ∀ u : Term, u ∈ faceTerms ρ σ termsQ ↔
      u ∈ termsQ ∧ dirVal ρ σ u.1.1 u.1.2 = dirVal ρ σ mQ.1 mQ.2 :=
    fun u => faceTerms_mem_of_max hQ
  have hBmem : ∀ u : Term, u ∈ faceTerms ρ σ (bracket termsP termsQ) ↔
      u ∈ bracket termsP termsQ ∧
        dirVal ρ σ u.1.1 u.1.2 = dirVal ρ σ mB.1 mB.2 :=
    fun u => faceTerms_mem_of_max hB
  constructor
  · intro ht
    obtain ⟨htbr, htval⟩ := (hBmem t).mp ht
    obtain ⟨m, hm, n, hn, rfl⟩ := bracket_mem.mp htbr
    rw [brkTerm_val] at htval
    have hle1 : dirVal ρ σ m.1.1 m.1.2 ≤ dirVal ρ σ mP.1 mP.2 :=
      maxVert_max hP (List.mem_map.mpr ⟨m, hm, rfl⟩)
    have hle2 : dirVal ρ σ n.1.1 n.1.2 ≤ dirVal ρ σ mQ.1 mQ.2 :=
      maxVert_max hQ (List.mem_map.mpr ⟨n, hn, rfl⟩)
    have hmval : dirVal ρ σ m.1.1 m.1.2 = dirVal ρ σ mP.1 mP.2 := by omega
    have hnval : dirVal ρ σ n.1.1 n.1.2 = dirVal ρ σ mQ.1 mQ.2 := by omega
    exact bracket_mem.mpr ⟨m, (hPmem m).mpr ⟨hm, hmval⟩,
      n, (hQmem n).mpr ⟨hn, hnval⟩, rfl⟩
  · intro ht
    obtain ⟨m, hm, n, hn, rfl⟩ := bracket_mem.mp ht
    obtain ⟨hmT, hmval⟩ := (hPmem m).mp hm
    obtain ⟨hnT, hnval⟩ := (hQmem n).mp hn
    apply (hBmem (brkTerm m n)).mpr
    constructor
    · exact bracket_mem.mpr ⟨m, hmT, n, hnT, rfl⟩
    · rw [brkTerm_val, hmval, hnval, hBval]

/-- (480), equality condition: the top component of [P,Q] is nonzero
    iff [ℓ(P),ℓ(Q)] is nonzero. -/
theorem bracket_top_nonzero_iff {ρ σ : Int} {termsP termsQ : List Term}
    {mP mQ : Int × Int}
    (hP : maxVertDir ρ σ (termExps termsP) = some mP)
    (hQ : maxVertDir ρ σ (termExps termsQ) = some mQ) :
    (∃ t ∈ faceTerms ρ σ (bracket termsP termsQ), t.2 ≠ 0) ↔
    (∃ t ∈ bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ),
      t.2 ≠ 0) := by
  constructor
  · rintro ⟨t, ht, h2⟩
    exact ⟨t, (face_bracket_mem hP hQ).mp ht, h2⟩
  · rintro ⟨t, ht, h2⟩
    exact ⟨t, (face_bracket_mem hP hQ).mpr ht, h2⟩

/-- A face term lies in the face iff it attains the maximal valuation:
    membership via a maximality bound (no max-vertex needed). -/
theorem faceTerms_mem_of_le_max {ρ σ : Int} {ts : List Term} {t : Term}
    (ht : t ∈ ts)
    (hmax : ∀ u ∈ ts, dirVal ρ σ u.1.1 u.1.2 ≤ dirVal ρ σ t.1.1 t.1.2) :
    t ∈ faceTerms ρ σ ts := by
  cases h : maxVertDir ρ σ (termExps ts) with
  | none =>
    have he : termExps ts = [] := maxVert_none h
    exact absurd he (List.ne_nil_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩))
  | some m =>
    apply faceTerms_mem.mpr
    refine ⟨m, h, ht, ?_⟩
    have hle : dirVal ρ σ t.1.1 t.1.2 ≤ dirVal ρ σ m.1 m.2 :=
      maxVert_max h (List.mem_map.mpr ⟨t, ht, rfl⟩)
    have hm : m ∈ termExps ts := maxVert_mem h
    obtain ⟨u, hu, hu1⟩ := List.mem_map.mp hm
    have hge : dirVal ρ σ m.1 m.2 ≤ dirVal ρ σ t.1.1 t.1.2 := by
      have := hmax u hu
      rw [hu1] at this
      exact this
    exact le_antisymm hle hge

/- ### Aligned vectors (Remark ~497) -/

/-- Aligned vectors: cross product zero (paper's `∼`). -/
def aligned (A B : Int × Int) : Prop := crossProd A B = 0

/-- Aligned→multiple bridge (Remark "relacion de equivalencia"): if
    A has positive second coordinate, B nonnegative second coordinate,
    and A ∼ B, then B = λA for some λ ≥ 0 (over ℚ). -/
theorem aligned_mul_of_cross {A B : Int × Int}
    (hA : 0 < A.2) (hB : 0 ≤ B.2) (h : crossProd A B = 0) :
    ∃ lam : ℚ, 0 ≤ lam ∧ (B.1 : ℚ) = lam * A.1 ∧ (B.2 : ℚ) = lam * A.2 := by
  have hcast : (A.1 : ℚ) * B.2 = (A.2 : ℚ) * B.1 := by
    have h0 : A.1 * B.2 - A.2 * B.1 = 0 := h
    have h1 : A.1 * B.2 = A.2 * B.1 := sub_eq_zero.mp h0
    exact_mod_cast h1
  have hA2 : (A.2 : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  refine ⟨(B.2 : ℚ) / A.2,
    div_nonneg (by exact_mod_cast hB) (by exact_mod_cast le_of_lt hA), ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_div_iff hA2]
    linear_combination -hcast
  · rw [div_mul_cancel₀ _ hA2]

/- ### Top-slice lemmas for the bracket of two faces -/

/-- The bracket of the two slice-maximizers lies in the top slice of
    the bracket of the faces. -/
theorem brkTerm_top_mem {ρ σ ρ0 σ0 : Int} {termsP termsQ : List Term}
    {sP sQ : Term}
    (hsP : sP ∈ faceTerms ρ σ termsP) (hsQ : sQ ∈ faceTerms ρ σ termsQ)
    (hmaxP : ∀ m ∈ faceTerms ρ σ termsP,
      dirVal ρ0 σ0 m.1.1 m.1.2 ≤ dirVal ρ0 σ0 sP.1.1 sP.1.2)
    (hmaxQ : ∀ n ∈ faceTerms ρ σ termsQ,
      dirVal ρ0 σ0 n.1.1 n.1.2 ≤ dirVal ρ0 σ0 sQ.1.1 sQ.1.2) :
    brkTerm sP sQ ∈
      faceTerms ρ0 σ0 (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)) := by
  apply faceTerms_mem_of_le_max
  · exact bracket_mem.mpr ⟨sP, hsP, sQ, hsQ, rfl⟩
  · intro u hu
    obtain ⟨m, hm, n, hn, rfl⟩ := bracket_mem.mp hu
    rw [brkTerm_val, brkTerm_val]
    have h1 := hmaxP m hm
    have h2 := hmaxQ n hn
    omega

/-- Every top-(1,−1)-slice term of the bracket of two faces is the
    bracket of a pair whose exponents are the two st-exponents
    (slice uniqueness: ties on (ρ,σ) + (1,−1) force the exponents). -/
theorem brkTerm_top_pair_st {ρ σ : Int} {termsP termsQ : List Term}
    (hne : ρ + σ ≠ 0)
    {sP sQ : Term}
    (hsP : sP ∈ faceTerms ρ σ termsP) (hsQ : sQ ∈ faceTerms ρ σ termsQ)
    (hmaxP : ∀ m ∈ faceTerms ρ σ termsP,
      dirVal 1 (-1) m.1.1 m.1.2 ≤ dirVal 1 (-1) sP.1.1 sP.1.2)
    (hmaxQ : ∀ n ∈ faceTerms ρ σ termsQ,
      dirVal 1 (-1) n.1.1 n.1.2 ≤ dirVal 1 (-1) sQ.1.1 sQ.1.2)
    {t : Term}
    (ht : t ∈ faceTerms 1 (-1)
      (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ))) :
    ∃ m ∈ faceTerms ρ σ termsP, ∃ n ∈ faceTerms ρ σ termsQ,
      t = brkTerm m n ∧ m.1 = sP.1 ∧ n.1 = sQ.1 := by
  have htsub : t ∈ bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ) :=
    faceTerms_subset ht
  obtain ⟨m, hm, n, hn, rfl⟩ := bracket_mem.mp htsub
  have htop : brkTerm sP sQ ∈ faceTerms 1 (-1)
      (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)) :=
    brkTerm_top_mem hsP hsQ hmaxP hmaxQ
  have hle : dirVal 1 (-1) (brkTerm sP sQ).1.1 (brkTerm sP sQ).1.2 ≤
      dirVal 1 (-1) (brkTerm m n).1.1 (brkTerm m n).1.2 :=
    faceTerms_max ht (List.mem_map.mpr ⟨brkTerm sP sQ,
      (faceTerms_subset htop), rfl⟩)
  rw [brkTerm_val, brkTerm_val] at hle
  have h1 := hmaxP m hm
  have h2 := hmaxQ n hn
  have hmval : dirVal 1 (-1) m.1.1 m.1.2 = dirVal 1 (-1) sP.1.1 sP.1.2 := by omega
  have hnval : dirVal 1 (-1) n.1.1 n.1.2 = dirVal 1 (-1) sQ.1.1 sQ.1.2 := by omega
  have hρm : dirVal ρ σ m.1.1 m.1.2 = dirVal ρ σ sP.1.1 sP.1.2 :=
    le_antisymm
      (faceTerms_max hsP (List.mem_map.mpr ⟨m, faceTerms_subset hm, rfl⟩))
      (faceTerms_max hm (List.mem_map.mpr ⟨sP, faceTerms_subset hsP, rfl⟩))
  have hρn : dirVal ρ σ n.1.1 n.1.2 = dirVal ρ σ sQ.1.1 sQ.1.2 :=
    le_antisymm
      (faceTerms_max hsQ (List.mem_map.mpr ⟨n, faceTerms_subset hn, rfl⟩))
      (faceTerms_max hn (List.mem_map.mpr ⟨sQ, faceTerms_subset hsQ, rfl⟩))
  exact ⟨m, hm, n, hn, rfl,
    slice_tie_unique hne hρm hmval, slice_tie_unique hne hρn hnval⟩

/-- The (−1,1) mirror: every top-(−1,1)-slice term of the bracket of
    two faces is the bracket of a pair whose exponents are the two
    en-exponents. -/
theorem brkTerm_top_pair_en {ρ σ : Int} {termsP termsQ : List Term}
    (hne : ρ + σ ≠ 0)
    {sP sQ : Term}
    (hsP : sP ∈ faceTerms ρ σ termsP) (hsQ : sQ ∈ faceTerms ρ σ termsQ)
    (hmaxP : ∀ m ∈ faceTerms ρ σ termsP,
      dirVal (-1) 1 m.1.1 m.1.2 ≤ dirVal (-1) 1 sP.1.1 sP.1.2)
    (hmaxQ : ∀ n ∈ faceTerms ρ σ termsQ,
      dirVal (-1) 1 n.1.1 n.1.2 ≤ dirVal (-1) 1 sQ.1.1 sQ.1.2)
    {t : Term}
    (ht : t ∈ faceTerms (-1) 1
      (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ))) :
    ∃ m ∈ faceTerms ρ σ termsP, ∃ n ∈ faceTerms ρ σ termsQ,
      t = brkTerm m n ∧ m.1 = sP.1 ∧ n.1 = sQ.1 := by
  have htsub : t ∈ bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ) :=
    faceTerms_subset ht
  obtain ⟨m, hm, n, hn, rfl⟩ := bracket_mem.mp htsub
  have htop : brkTerm sP sQ ∈ faceTerms (-1) 1
      (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)) :=
    brkTerm_top_mem hsP hsQ hmaxP hmaxQ
  have hle : dirVal (-1) 1 (brkTerm sP sQ).1.1 (brkTerm sP sQ).1.2 ≤
      dirVal (-1) 1 (brkTerm m n).1.1 (brkTerm m n).1.2 :=
    faceTerms_max ht (List.mem_map.mpr ⟨brkTerm sP sQ,
      (faceTerms_subset htop), rfl⟩)
  rw [brkTerm_val, brkTerm_val] at hle
  have h1 := hmaxP m hm
  have h2 := hmaxQ n hn
  have hmval : dirVal (-1) 1 m.1.1 m.1.2 = dirVal (-1) 1 sP.1.1 sP.1.2 := by omega
  have hnval : dirVal (-1) 1 n.1.1 n.1.2 = dirVal (-1) 1 sQ.1.1 sQ.1.2 := by omega
  have hρm : dirVal ρ σ m.1.1 m.1.2 = dirVal ρ σ sP.1.1 sP.1.2 :=
    le_antisymm
      (faceTerms_max hsP (List.mem_map.mpr ⟨m, faceTerms_subset hm, rfl⟩))
      (faceTerms_max hm (List.mem_map.mpr ⟨sP, faceTerms_subset hsP, rfl⟩))
  have hρn : dirVal ρ σ n.1.1 n.1.2 = dirVal ρ σ sQ.1.1 sQ.1.2 :=
    le_antisymm
      (faceTerms_max hsQ (List.mem_map.mpr ⟨n, faceTerms_subset hn, rfl⟩))
      (faceTerms_max hn (List.mem_map.mpr ⟨sQ, faceTerms_subset hsQ, rfl⟩))
  exact ⟨m, hm, n, hn, rfl,
    slice_tie_unique_en hne hρm hmval, slice_tie_unique_en hne hρn hnval⟩

/- ### Extremos alineados (TeX 694) -/

/-- extremosalineados (TeX 694): if the bracket of the two face
    polynomials vanishes (pairwise form — see header), then st(P) ∼
    st(Q) and en(P) ∼ en(Q). Proof (paper): the (1,−1)-slice of the
    bracket is the bracket of the two st-monomials, whose coefficient
    is the cross product; same at en with (−1,1). -/
theorem extremos_alineados {ρ σ : Int} {termsP termsQ : List Term}
    (hV : 0 < ρ + σ)
    {sP sQ eP eQ : Term}
    (hsP : stFace ρ σ termsP = some sP) (hsQ : stFace ρ σ termsQ = some sQ)
    (heP : enFace ρ σ termsP = some eP) (heQ : enFace ρ σ termsQ = some eQ)
    (hcP : sP.2 ≠ 0) (hcQ : sQ.2 ≠ 0) (hdP : eP.2 ≠ 0) (hdQ : eQ.2 ≠ 0)
    (hbr : ∀ t ∈ bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ),
      t.2 = 0) :
    crossProd sP.1 sQ.1 = 0 ∧ crossProd eP.1 eQ.1 = 0 := by
  have hsPmem : sP ∈ faceTerms ρ σ termsP := stFaceAux_mem hsP
  have hsQmem : sQ ∈ faceTerms ρ σ termsQ := stFaceAux_mem hsQ
  have hePmem : eP ∈ faceTerms ρ σ termsP := enFaceAux_mem heP
  have heQmem : eQ ∈ faceTerms ρ σ termsQ := enFaceAux_mem heQ
  have hst : crossProd sP.1 sQ.1 = 0 := by
    have hmem : brkTerm sP sQ ∈
        bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ) :=
      bracket_mem.mpr ⟨sP, hsPmem, sQ, hsQmem, rfl⟩
    have h0 := hbr _ hmem
    rw [brkTerm_coeff] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hcP
      · exact absurd h' hcQ
    · exact h
  have hen : crossProd eP.1 eQ.1 = 0 := by
    have hmem : brkTerm eP eQ ∈
        bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ) :=
      bracket_mem.mpr ⟨eP, hePmem, eQ, heQmem, rfl⟩
    have h0 := hbr _ hmem
    rw [brkTerm_coeff] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hdP
      · exact absurd h' hdQ
    · exact h
  exact ⟨hst, hen⟩

/- ### Extremos no alineados (TeX 721) -/

/-- extremosnoalineados(1) (TeX 721): [ℓ(P),ℓ(Q)] = ℓ(R) (in the slice
    form `hbr` — see header) implies st(P) ≁ st(Q) iff
    st(P)+st(Q)−(1,1) = st(R). Proof (paper): the (1,−1)-slice of the
    bracket is the bracket of the two st-monomials; it is nonzero iff
    the cross product is nonzero, and then its exponent is the sum
    minus (1,1), which the slice hypothesis identifies with st(R). -/
theorem extremos_noalineados_st {ρ σ : Int} {termsP termsQ termsR : List Term}
    (hV : 0 < ρ + σ)
    {sP sQ sR : Term}
    (hsP : stFace ρ σ termsP = some sP) (hsQ : stFace ρ σ termsQ = some sQ)
    (hsR : stFace ρ σ termsR = some sR)
    (hcP : sP.2 ≠ 0) (hcQ : sQ.2 ≠ 0) (hcR : sR.2 ≠ 0)
    (hbr : (∀ t ∈ faceTerms 1 (-1)
        (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)),
        t.2 ≠ 0 → t.1 = sR.1)
      ∧ (∃ t ∈ faceTerms 1 (-1)
        (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)),
        t.2 ≠ 0)) :
    crossProd sP.1 sQ.1 ≠ 0 ↔
      (sP.1.1 + sQ.1.1 - 1, sP.1.2 + sQ.1.2 - 1) = sR.1 := by
  obtain ⟨hbr_top, hbr_ne⟩ := hbr
  have hsPmem : sP ∈ faceTerms ρ σ termsP := stFaceAux_mem hsP
  have hsQmem : sQ ∈ faceTerms ρ σ termsQ := stFaceAux_mem hsQ
  have hmaxP : ∀ m ∈ faceTerms ρ σ termsP,
      dirVal 1 (-1) m.1.1 m.1.2 ≤ dirVal 1 (-1) sP.1.1 sP.1.2 :=
    fun m hm => (stFace_mem_max hsP hm).2
  have hmaxQ : ∀ n ∈ faceTerms ρ σ termsQ,
      dirVal 1 (-1) n.1.1 n.1.2 ≤ dirVal 1 (-1) sQ.1.1 sQ.1.2 :=
    fun n hn => (stFace_mem_max hsQ hn).2
  constructor
  · intro hcross
    have hmem : brkTerm sP sQ ∈ faceTerms 1 (-1)
        (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)) :=
      brkTerm_top_mem hsPmem hsQmem hmaxP hmaxQ
    have hcoeff : (brkTerm sP sQ).2 ≠ 0 := by
      rw [brkTerm_coeff]
      exact mul_ne_zero (mul_ne_zero hcP hcQ) hcross
    have htop := hbr_top _ hmem hcoeff
    rw [brkTerm_exp] at htop
    exact htop
  · intro hsum
    by_contra hcon
    have hcross : crossProd sP.1 sQ.1 = 0 := hcon
    obtain ⟨t, ht, ht2⟩ := hbr_ne
    obtain ⟨m, hm, n, hn, rfl, hm1, hn1⟩ :=
      brkTerm_top_pair_st (ne_of_gt hV) hsPmem hsQmem hmaxP hmaxQ ht
    rw [brkTerm_coeff, hm1, hn1, hcross, mul_zero] at ht2
    exact ht2 rfl

/-- extremosnoalineados(2) (TeX 721): the en-analogue. -/
theorem extremos_noalineados_en {ρ σ : Int} {termsP termsQ termsR : List Term}
    (hV : 0 < ρ + σ)
    {eP eQ eR : Term}
    (heP : enFace ρ σ termsP = some eP) (heQ : enFace ρ σ termsQ = some eQ)
    (heR : enFace ρ σ termsR = some eR)
    (hcP : eP.2 ≠ 0) (hcQ : eQ.2 ≠ 0) (hcR : eR.2 ≠ 0)
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)),
        t.2 ≠ 0)) :
    crossProd eP.1 eQ.1 ≠ 0 ↔
      (eP.1.1 + eQ.1.1 - 1, eP.1.2 + eQ.1.2 - 1) = eR.1 := by
  obtain ⟨hbr_top, hbr_ne⟩ := hbr
  have hePmem : eP ∈ faceTerms ρ σ termsP := enFaceAux_mem heP
  have heQmem : eQ ∈ faceTerms ρ σ termsQ := enFaceAux_mem heQ
  have hmaxP : ∀ m ∈ faceTerms ρ σ termsP,
      dirVal (-1) 1 m.1.1 m.1.2 ≤ dirVal (-1) 1 eP.1.1 eP.1.2 :=
    fun m hm => (enFace_mem_max heP hm).2
  have hmaxQ : ∀ n ∈ faceTerms ρ σ termsQ,
      dirVal (-1) 1 n.1.1 n.1.2 ≤ dirVal (-1) 1 eQ.1.1 eQ.1.2 :=
    fun n hn => (enFace_mem_max heQ hn).2
  constructor
  · intro hcross
    have hmem : brkTerm eP eQ ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)) :=
      brkTerm_top_mem hePmem heQmem hmaxP hmaxQ
    have hcoeff : (brkTerm eP eQ).2 ≠ 0 := by
      rw [brkTerm_coeff]
      exact mul_ne_zero (mul_ne_zero hcP hcQ) hcross
    have htop := hbr_top _ hmem hcoeff
    rw [brkTerm_exp] at htop
    exact htop
  · intro hsum
    by_contra hcon
    have hcross : crossProd eP.1 eQ.1 = 0 := hcon
    obtain ⟨t, ht, ht2⟩ := hbr_ne
    obtain ⟨m, hm, n, hn, rfl, hm1, hn1⟩ :=
      brkTerm_top_pair_en (ne_of_gt hV) hePmem heQmem hmaxP hmaxQ ht
    rw [brkTerm_coeff, hm1, hn1, hcross, mul_zero] at ht2
    exact ht2 rfl

/- ### Reusable (1,1)-sum lemma (propiedades(2) + esquina(2)) -/

/-- The reusable lemma factored out of the triple (480 + 694 + 721(2)):
    nonsimilar en-endpoints + [P,Q] a nonzero constant (so en(R) =
    (0,0)) imply en(P) + en(Q) = (1,1). Used by propiedades de los
    pares(2) (TeX 1559, eq e8) and by esquina(2) (TeX 5440-5470), where
    R = [P,Q] ∈ K^×. The hypothesis `hbr` is the slice form of
    [ℓ(P),ℓ(Q)] = ℓ(R); `hR0` is the constant-bracket fact en(R) =
    (0,0). -/
theorem en_sum_eq_one_one {ρ σ : Int} {termsP termsQ termsR : List Term}
    (hV : 0 < ρ + σ)
    {eP eQ eR : Term}
    (heP : enFace ρ σ termsP = some eP) (heQ : enFace ρ σ termsQ = some eQ)
    (heR : enFace ρ σ termsR = some eR)
    (hcP : eP.2 ≠ 0) (hcQ : eQ.2 ≠ 0) (hcR : eR.2 ≠ 0)
    (hR0 : eR.1 = (0, 0))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ σ termsP) (faceTerms ρ σ termsQ)),
        t.2 ≠ 0))
    (hnonsim : crossProd eP.1 eQ.1 ≠ 0) :
    (eP.1.1 + eQ.1.1, eP.1.2 + eQ.1.2) = (1, 1) := by
  have h := (extremos_noalineados_en hV heP heQ heR hcP hcQ hcR hbr).mp hnonsim
  rw [hR0] at h
  have h1 : eP.1.1 + eQ.1.1 - 1 = 0 := congrArg Prod.fst h
  have h2 : eP.1.2 + eQ.1.2 - 1 = 0 := congrArg Prod.snd h
  exact Prod.ext (by omega) (by omega)

/- ESQUINA (2) — [GGV1] Prop 8.2 item (2): statement layer + proof opening + item (2).
   Scratch section, to be appended to the D1 base (le bbasico file + extremos file from
   line 987). Exponent level, l = 1 (bracket shift (1,1)), as in the le basico / extremos files.

   QUALIFICATIONS (carried, not hidden):
   (1) Pairwise bracket form: the extremos file works with the UNCOMBINED pairwise bracket
       list, so `en_sum_eq_one_one` and the extremos theorems take pairwise-form hypotheses,
       strictly stronger than the paper's combined-polynomial identities. The upgrade to the
       combined form is the open D2 step (bridge lemma in the extremos file header). This
       file inherits that working-level hypothesis via `hbr` (the slice form of
       [ℓ(P),ℓ(Q)] = ℓ(R)); it must NOT be presented as the paper's statement until the D2
       combine step lands.
   (2) m, n > 1 STRENGTHENING: the paper's statement (TeX 5320-5328) says only a,b,m,n in N,
       a > b, m != n, gcd(m,n) = 1. Its (2) proof asserts "st(P) = m(a,b), st(Q) = n(a,b),
       nb,mb > 1" — which needs m,n > 1 given b >= 1 (if (m,b) = (1,1), st_2(P) = (a,1)
       could coincide with en_2(P) = (k+1,1) and the Dir conclusion would not follow). The
       (m,n)-pair context of [GGV1] §8 has m,n > 1 (cf. the F statement, TeX 4077), so this
       file carries hm : 1 < m, hn : 1 < n as explicit hypotheses in each theorem. This is a genuine
       (minor) gap in the proposition's statement as literally written, flagged here.
   (3) `hmn : m ≠ n` and `hgcd : Int.gcd m n = 1` are in the paper's statement but are NOT
       carried as binders here (unused by item (2)'s proof); they matter for item (1).
   (4) Exponent level only: Term equality needs unique exponents of polynomial term lists
       as a separate step. `hvert` is carried via `hdirs` (isDir = Dir(P) never asserted
       unconditionally; vertical faces at sigma = 0 are the obstruction).
   (5) The (rho_2,sigma_2) sum is PROVED (esquina_rho2_lt), not assumed: the successor's
       sum is not known a priori (a valid abstract successor could be (0,-1)).
-/

/-- The min of the two successors, in V order (dirLt = crossProd > 0). -/
def succMin (δP δQ : Int × Int) : Int × Int :=
  if 0 < crossProd δQ δP then δQ else δP

theorem succMin_eq {δP δQ : Int × Int} :
    succMin δP δQ = δP ∨ succMin δP δQ = δQ := by
  unfold succMin
  by_cases h : 0 < crossProd δQ δP
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

theorem succMin_le_P {δP δQ : Int × Int} :
    dirLt (succMin δP δQ) δP ∨ succMin δP δQ = δP := by
  unfold succMin
  by_cases h : 0 < crossProd δQ δP
  · rw [if_pos h]; exact Or.inl h
  · rw [if_neg h]; exact Or.inr rfl

theorem succMin_le_Q_or_prop {δP δQ : Int × Int} :
    dirLt (succMin δP δQ) δQ ∨ succMin δP δQ = δQ ∨ crossProd δP δQ = 0 := by
  unfold succMin
  by_cases h : 0 < crossProd δQ δP
  · rw [if_pos h]; exact Or.inr (Or.inl rfl)
  · rw [if_neg h]
    by_cases h0 : crossProd δP δQ = 0
    · exact Or.inr (Or.inr h0)
    · left
      have hle : crossProd δQ δP ≤ 0 := by omega
      have hanti : crossProd δP δQ = -crossProd δQ δP := by
        simp only [crossProd]; ring
      have hpos : 0 < crossProd δP δQ := by rw [hanti]; omega
      exact hpos

/-- First half of `endpoint_slice_max`, split off: a term in both the rho1-face and the
    rho2-face maximizes the (-1,1)-slice over the rho1-face. Needs only rho1's sum >= 0. -/
theorem endpoint_slice_max_en {ρ1 ρ2 : Int × Int} {terms : List Term} {a1 : Term}
    (hC : 0 < crossProd ρ1 ρ2) (h1sum : 0 ≤ ρ1.1 + ρ1.2)
    (ha1face1 : a1 ∈ faceTerms ρ1.1 ρ1.2 terms)
    (ha1face2 : a1 ∈ faceTerms ρ2.1 ρ2.2 terms) :
    ∀ t ∈ faceTerms ρ1.1 ρ1.2 terms,
      dirVal (-1) 1 t.1.1 t.1.2 ≤ dirVal (-1) 1 a1.1.1 a1.1.2 := by
  have ha1terms : a1 ∈ terms := faceTerms_subset ha1face1
  intro t ht
  have htterms : t ∈ terms := faceTerms_subset ht
  have eρ1 : dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 = dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 :=
    le_antisymm
      (faceTerms_max ha1face1 (List.mem_map.mpr ⟨t, htterms, rfl⟩))
      (faceTerms_max ht (List.mem_map.mpr ⟨a1, ha1terms, rfl⟩))
  have hρ2le : dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 ≤ dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 :=
    faceTerms_max ha1face2 (List.mem_map.mpr ⟨t, htterms, rfl⟩)
  have hId : crossProd ρ1 ρ2 *
      (dirVal (-1) 1 t.1.1 t.1.2 - dirVal (-1) 1 a1.1.1 a1.1.2)
      = -(ρ2.1 + ρ2.2) * (dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 - dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2)
        + (ρ1.1 + ρ1.2) * (dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 - dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2) := by
    simp only [crossProd, dirVal]
    ring
  have hprod : crossProd ρ1 ρ2 *
      (dirVal (-1) 1 t.1.1 t.1.2 - dirVal (-1) 1 a1.1.1 a1.1.2) ≤ 0 := by
    rw [hId]
    have hz : dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 - dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 = 0 :=
      sub_eq_zero.mpr eρ1
    rw [hz, mul_zero, zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos h1sum (sub_nonpos.mpr hρ2le)
  have hle : dirVal (-1) 1 t.1.1 t.1.2 - dirVal (-1) 1 a1.1.1 a1.1.2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < crossProd ρ1 ρ2 *
        (dirVal (-1) 1 t.1.1 t.1.2 - dirVal (-1) 1 a1.1.1 a1.1.2) :=
      mul_pos hC hcon
    omega
  exact sub_nonpos.mp hle

/-- Second half of `endpoint_slice_max`, split off: a term in both faces maximizes the
    (1,-1)-slice over the rho2-face. Needs only rho2's sum >= 0. -/
theorem endpoint_slice_max_st {ρ1 ρ2 : Int × Int} {terms : List Term} {a1 : Term}
    (hC : 0 < crossProd ρ1 ρ2) (h2sum : 0 ≤ ρ2.1 + ρ2.2)
    (ha1face1 : a1 ∈ faceTerms ρ1.1 ρ1.2 terms)
    (ha1face2 : a1 ∈ faceTerms ρ2.1 ρ2.2 terms) :
    ∀ t ∈ faceTerms ρ2.1 ρ2.2 terms,
      dirVal 1 (-1) t.1.1 t.1.2 ≤ dirVal 1 (-1) a1.1.1 a1.1.2 := by
  have ha1terms : a1 ∈ terms := faceTerms_subset ha1face1
  intro t ht
  have htterms : t ∈ terms := faceTerms_subset ht
  have eρ2 : dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 = dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 :=
    le_antisymm
      (faceTerms_max ha1face2 (List.mem_map.mpr ⟨t, htterms, rfl⟩))
      (faceTerms_max ht (List.mem_map.mpr ⟨a1, ha1terms, rfl⟩))
  have hρ1le : dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 ≤ dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 :=
    faceTerms_max ha1face1 (List.mem_map.mpr ⟨t, htterms, rfl⟩)
  have hId : crossProd ρ1 ρ2 *
      (dirVal 1 (-1) t.1.1 t.1.2 - dirVal 1 (-1) a1.1.1 a1.1.2)
      = (ρ2.1 + ρ2.2) * (dirVal ρ1.1 ρ1.2 t.1.1 t.1.2 - dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2)
        - (ρ1.1 + ρ1.2) * (dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 - dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2) := by
    simp only [crossProd, dirVal]
    ring
  have hprod : crossProd ρ1 ρ2 *
      (dirVal 1 (-1) t.1.1 t.1.2 - dirVal 1 (-1) a1.1.1 a1.1.2) ≤ 0 := by
    rw [hId]
    have hz : dirVal ρ2.1 ρ2.2 t.1.1 t.1.2 - dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 = 0 :=
      sub_eq_zero.mpr eρ2
    rw [hz, mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos h2sum (sub_nonpos.mpr hρ1le)
  have hle : dirVal 1 (-1) t.1.1 t.1.2 - dirVal 1 (-1) a1.1.1 a1.1.2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < crossProd ρ1 ρ2 *
        (dirVal 1 (-1) t.1.1 t.1.2 - dirVal 1 (-1) a1.1.1 a1.1.2) :=
      mul_pos hC hcon
    omega
  exact sub_nonpos.mp hle

/-- Shared-vertex identification, en side: the en_{rho1} term is the shared vertex a1
    (at exponent level), given rho1's sum > 0. -/
theorem shared_vertex_en {ρ1 ρ2 : Int × Int} {terms : List Term} {a1 e : Term}
    (hC : 0 < crossProd ρ1 ρ2) (h1sum : 0 < ρ1.1 + ρ1.2)
    (ha1face1 : a1 ∈ faceTerms ρ1.1 ρ1.2 terms)
    (ha1face2 : a1 ∈ faceTerms ρ2.1 ρ2.2 terms)
    (he : enFace ρ1.1 ρ1.2 terms = some e) : e.1 = a1.1 := by
  have hinc1 := endpoint_slice_max_en hC (le_of_lt h1sum) ha1face1 ha1face2
  have hemem : e ∈ faceTerms ρ1.1 ρ1.2 terms := enFaceAux_mem he
  have hemax : dirVal (-1) 1 a1.1.1 a1.1.2 ≤ dirVal (-1) 1 e.1.1 e.1.2 :=
    (enFace_mem_max he ha1face1).2
  have eρ1 : dirVal ρ1.1 ρ1.2 e.1.1 e.1.2 = dirVal ρ1.1 ρ1.2 a1.1.1 a1.1.2 := by
    have ha1terms : a1 ∈ terms := faceTerms_subset ha1face1
    have heterms : e ∈ terms := faceTerms_subset hemem
    exact le_antisymm
      (faceTerms_max ha1face1 (List.mem_map.mpr ⟨e, heterms, rfl⟩))
      (faceTerms_max hemem (List.mem_map.mpr ⟨a1, ha1terms, rfl⟩))
  have htie : dirVal (-1) 1 e.1.1 e.1.2 = dirVal (-1) 1 a1.1.1 a1.1.2 :=
    le_antisymm (hinc1 e hemem) hemax
  exact slice_tie_unique_en (ne_of_gt h1sum) eρ1 htie

/-- Shared-vertex identification, st side: the st_{rho2} term is the shared vertex a1
    (at exponent level), given rho2's sum > 0. -/
theorem shared_vertex_st {ρ1 ρ2 : Int × Int} {terms : List Term} {a1 s : Term}
    (hC : 0 < crossProd ρ1 ρ2) (h2sum : 0 < ρ2.1 + ρ2.2)
    (ha1face1 : a1 ∈ faceTerms ρ1.1 ρ1.2 terms)
    (ha1face2 : a1 ∈ faceTerms ρ2.1 ρ2.2 terms)
    (hs : stFace ρ2.1 ρ2.2 terms = some s) : s.1 = a1.1 := by
  have hinc2 := endpoint_slice_max_st hC (le_of_lt h2sum) ha1face1 ha1face2
  have hsmem : s ∈ faceTerms ρ2.1 ρ2.2 terms := stFaceAux_mem hs
  have hsmax : dirVal 1 (-1) a1.1.1 a1.1.2 ≤ dirVal 1 (-1) s.1.1 s.1.2 :=
    (stFace_mem_max hs ha1face2).2
  have eρ2 : dirVal ρ2.1 ρ2.2 s.1.1 s.1.2 = dirVal ρ2.1 ρ2.2 a1.1.1 a1.1.2 := by
    have ha1terms : a1 ∈ terms := faceTerms_subset ha1face2
    have hsterms : s ∈ terms := faceTerms_subset hsmem
    exact le_antisymm
      (faceTerms_max ha1face2 (List.mem_map.mpr ⟨s, hsterms, rfl⟩))
      (faceTerms_max hsmem (List.mem_map.mpr ⟨a1, ha1terms, rfl⟩))
  have htie : dirVal 1 (-1) s.1.1 s.1.2 = dirVal 1 (-1) a1.1.1 a1.1.2 :=
    le_antisymm (hinc2 s hsmem) hsmax
  exact slice_tie_unique (ne_of_gt h2sum) eρ2 htie

/-- Face-max vertex is invariant under positive integer scaling of the direction. -/
theorem maxVertDir_smul {c : Int} (hc : 0 < c) (ρ σ : Int) :
    ∀ vs : List (Int × Int), maxVertDir (c * ρ) (c * σ) vs = maxVertDir ρ σ vs := by
  intro vs
  induction vs with
  | nil => rfl
  | cons x xs ih =>
    simp only [maxVertDir]
    rw [ih]
    cases hxs : maxVertDir ρ σ xs with
    | none => rfl
    | some w =>
      simp only [hxs]
      have hiff : dirVal (c * ρ) (c * σ) x.1 x.2 ≤ dirVal (c * ρ) (c * σ) w.1 w.2 ↔
          dirVal ρ σ x.1 x.2 ≤ dirVal ρ σ w.1 w.2 := by
        have e1 : dirVal (c * ρ) (c * σ) x.1 x.2 = c * dirVal ρ σ x.1 x.2 := by
          simp only [dirVal]; ring
        have e2 : dirVal (c * ρ) (c * σ) w.1 w.2 = c * dirVal ρ σ w.1 w.2 := by
          simp only [dirVal]; ring
        rw [e1, e2]
        constructor
        · intro h; exact le_of_mul_le_mul_left h hc
        · intro h; exact mul_le_mul_of_nonneg_left h (le_of_lt hc)
      by_cases hle : dirVal ρ σ x.1 x.2 ≤ dirVal ρ σ w.1 w.2
      · rw [if_pos (hiff.mpr hle), if_pos hle]
      · rw [if_neg (fun h => hle (hiff.mp h)), if_neg hle]

/-- Faces are invariant under positive integer scaling of the direction. -/
theorem faceTerms_smul {c : Int} (hc : 0 < c) (ρ σ : Int) (terms : List Term) :
    faceTerms (c * ρ) (c * σ) terms = faceTerms ρ σ terms := by
  simp only [faceTerms]
  rw [maxVertDir_smul hc]
  cases h : maxVertDir ρ σ (termExps terms) with
  | none => rfl
  | some m =>
    apply List.filter_congr
    intro t ht
    have e1 : dirVal (c * ρ) (c * σ) t.1.1 t.1.2 = c * dirVal ρ σ t.1.1 t.1.2 := by
      simp only [dirVal]; ring
    have e2 : dirVal (c * ρ) (c * σ) m.1 m.2 = c * dirVal ρ σ m.1 m.2 := by
      simp only [dirVal]; ring
    simp only [e1, e2]
    have hiff : (c * dirVal ρ σ t.1.1 t.1.2 = c * dirVal ρ σ m.1 m.2) ↔
        (dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2) := by
      constructor
      · intro hh; exact mul_left_cancel₀ (ne_of_gt hc) hh
      · intro hh; rw [hh]
    simp only [hiff]

/-- Cross-zero directions are rationally proportional (one direction nonzero). -/
theorem exists_rat_smul_of_cross_zero {δP δQ : Int × Int}
    (hP0 : δP ≠ (0, 0)) (hcross : crossProd δP δQ = 0) :
    ∃ q : ℚ, (δQ.1 : ℚ) = q * δP.1 ∧ (δQ.2 : ℚ) = q * δP.2 := by
  by_cases h1 : δP.1 ≠ 0
  · have h1q : (δP.1 : ℚ) ≠ 0 := by exact_mod_cast h1
    refine ⟨(δQ.1 : ℚ) / δP.1, ?_, ?_⟩
    · field_simp
    · have hc : (δP.1 : ℚ) * δQ.2 = (δP.2 : ℚ) * δQ.1 := by
        have h := hcross
        simp only [crossProd] at h
        have h' : (δP.1 : ℚ) * δQ.2 - (δP.2 : ℚ) * δQ.1 = 0 := by exact_mod_cast h
        linarith
      field_simp
      linear_combination hc
  · have h1' : δP.1 = 0 := by omega
    have h2 : δP.2 ≠ 0 := by
      intro h2
      apply hP0
      exact Prod.ext (by omega) h2
    have h2q : (δP.2 : ℚ) ≠ 0 := by exact_mod_cast h2
    have hq1 : (δQ.1 : ℚ) = 0 := by
      have h := hcross
      simp only [crossProd] at h
      rw [h1'] at h
      simp at h
      rcases h with h' | h'
      · exact absurd h' h2
      · exact_mod_cast h'
    refine ⟨(δQ.2 : ℚ) / δP.2, ?_, ?_⟩
    · rw [hq1, h1']
      simp
    · field_simp

/-- Proportional directions (positive ratio) have the same faces. -/
theorem faceTerms_eq_of_cross_zero {δP δQ : Int × Int} (terms : List Term)
    (hP0 : δP ≠ (0, 0))
    (hcross : crossProd δP δQ = 0)
    (hq : ∃ q : ℚ, 0 < q ∧ (δQ.1 : ℚ) = q * δP.1 ∧ (δQ.2 : ℚ) = q * δP.2) :
    faceTerms δQ.1 δQ.2 terms = faceTerms δP.1 δP.2 terms := by
  obtain ⟨q, hq0, hq1, hq2⟩ := hq
  have hD : 0 < q.den := q.den_pos
  have hN : 0 < q.num := Rat.num_pos.mpr hq0
  have hDq0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have hnum : (q.num : ℚ) = q * q.den := (div_eq_iff hDq0).mp (Rat.num_div_den q)
  have e1 : (q.den : Int) * δQ.1 = q.num * δP.1 := by
    have h : (((q.den : Int) * δQ.1 : ℤ) : ℚ) = (((q.num * δP.1 : ℤ)) : ℚ) := by
      push_cast
      rw [hq1]
      have hDq : (q.den : ℚ) * q = (q.num : ℚ) := by rw [mul_comm, hnum]
      calc (q.den : ℚ) * (q * (δP.1 : ℚ)) = ((q.den : ℚ) * q) * (δP.1 : ℚ) := by ring
        _ = (q.num : ℚ) * (δP.1 : ℚ) := by rw [hDq]
    exact_mod_cast h
  have e2 : (q.den : Int) * δQ.2 = q.num * δP.2 := by
    have h : (((q.den : Int) * δQ.2 : ℤ) : ℚ) = (((q.num * δP.2 : ℤ)) : ℚ) := by
      push_cast
      rw [hq2]
      have hDq : (q.den : ℚ) * q = (q.num : ℚ) := by rw [mul_comm, hnum]
      calc (q.den : ℚ) * (q * (δP.2 : ℚ)) = ((q.den : ℚ) * q) * (δP.2 : ℚ) := by ring
        _ = (q.num : ℚ) * (δP.2 : ℚ) := by rw [hDq]
    exact_mod_cast h
  have hpair : ((q.den : Int) * δQ.1, (q.den : Int) * δQ.2)
      = (q.num * δP.1, q.num * δP.2) := Prod.ext e1 e2
  calc faceTerms δQ.1 δQ.2 terms
      = faceTerms ((q.den : Int) * δQ.1) ((q.den : Int) * δQ.2) terms :=
        (faceTerms_smul (show (0 : Int) < q.den by exact_mod_cast hD) δQ.1 δQ.2 terms).symm
    _ = faceTerms (q.num * δP.1) (q.num * δP.2) terms := by rw [e1, e2]
    _ = faceTerms δP.1 δP.2 terms :=
        faceTerms_smul (show (0 : Int) < q.num by exact_mod_cast hN) δP.1 δP.2 terms

/-- Endpoint positivity: for rho2 < rho3 < (-1,1) (in V order), the en-endpoint of the
    rho2-face has strictly larger rho3-valuation than the st-endpoint, which has value 0.
    (The paper's "v del endpoint positivo" step; the strictness is the Dir(P)/Dir(Q)
    input, carried here via hne : e.1 != s.1.) -/
theorem endpoint_val_pos {ρ₂ ρ₃ : Int × Int} {terms : List Term} {e s : Term}
    (h23 : dirLt ρ₂ ρ₃) (h3m : dirLt ρ₃ (-1, 1)) (h12 : dirLt ρ₂ (-1, 1))
    (h2sum : ρ₂.1 + ρ₂.2 ≠ 0)
    (he : enFace ρ₂.1 ρ₂.2 terms = some e) (hs : stFace ρ₂.1 ρ₂.2 terms = some s)
    (hne : e.1 ≠ s.1)
    (hsval : dirVal ρ₃.1 ρ₃.2 s.1.1 s.1.2 = 0) :
    0 < dirVal ρ₃.1 ρ₃.2 e.1.1 e.1.2 := by
  obtain ⟨α, β, hα, hβ, hρ⟩ := dir_between_pos_combo h23 h3m h12
  have hemem : e ∈ faceTerms ρ₂.1 ρ₂.2 terms := enFaceAux_mem he
  have hsmem : s ∈ faceTerms ρ₂.1 ρ₂.2 terms := stFaceAux_mem hs
  have hfaceval : dirVal ρ₂.1 ρ₂.2 e.1.1 e.1.2 = dirVal ρ₂.1 ρ₂.2 s.1.1 s.1.2 := by
    obtain ⟨m, hm, -, hve⟩ := faceTerms_mem.mp hemem
    obtain ⟨m', hm', -, hvs⟩ := faceTerms_mem.mp hsmem
    have hmm : m = m' := Option.some.inj (hm.symm.trans hm')
    subst hmm
    rw [hve, hvs]
  have hlin : ∀ u : Int × Int, (dirVal ρ₃.1 ρ₃.2 u.1 u.2 : ℚ)
      = α * (dirVal ρ₂.1 ρ₂.2 u.1 u.2 : ℚ) + β * (dirVal (-1) 1 u.1 u.2 : ℚ) := by
    intro u
    have hρ1 : (ρ₃.1 : ℚ) = α * (ρ₂.1 : ℚ) + β * (-1) := hρ.1
    have hρ2 : (ρ₃.2 : ℚ) = α * (ρ₂.2 : ℚ) + β * 1 := hρ.2
    simp only [dirVal]
    push_cast
    rw [hρ1, hρ2]
    ring
  have hslice : dirVal (-1) 1 s.1.1 s.1.2 < dirVal (-1) 1 e.1.1 e.1.2 := by
    have hle : dirVal (-1) 1 s.1.1 s.1.2 ≤ dirVal (-1) 1 e.1.1 e.1.2 :=
      (enFace_mem_max he hsmem).2
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      apply hne
      exact slice_tie_unique_en h2sum hfaceval h.symm
  have hdiff : (0 : ℚ) < (dirVal ρ₃.1 ρ₃.2 e.1.1 e.1.2 : ℚ)
      - (dirVal ρ₃.1 ρ₃.2 s.1.1 s.1.2 : ℚ) := by
    rw [hlin e.1, hlin s.1, hfaceval]
    have hE : (dirVal (-1) 1 s.1.1 s.1.2 : ℚ) < (dirVal (-1) 1 e.1.1 e.1.2 : ℚ) := by
      exact_mod_cast hslice
    have hpos : 0 < β * ((dirVal (-1) 1 e.1.1 e.1.2 : ℚ)
        - (dirVal (-1) 1 s.1.1 s.1.2 : ℚ)) :=
      mul_pos hβ (sub_pos.mpr hE)
    linarith
  have hs0 : (dirVal ρ₃.1 ρ₃.2 s.1.1 s.1.2 : ℚ) = 0 := by exact_mod_cast hsval
  rw [hs0, sub_zero] at hdiff
  exact_mod_cast hdiff

/-- Pure arithmetic: two points with nonnegative second coordinates summing to (1,1)
    are {(-k,0),(k+1,1)} for some integer k. -/
theorem pair_form_of_sum {eP eQ : Int × Int}
    (hP2 : 0 ≤ eP.2) (hQ2 : 0 ≤ eQ.2)
    (hsum : (eP.1 + eQ.1, eP.2 + eQ.2) = (1, 1)) :
    ∃ k : Int, (eP = (-k, 0) ∧ eQ = (k + 1, 1)) ∨ (eP = (k + 1, 1) ∧ eQ = (-k, 0)) := by
  have h1 : eP.1 + eQ.1 = 1 := congrArg Prod.fst hsum
  have h2 : eP.2 + eQ.2 = 1 := congrArg Prod.snd hsum
  rcases (by omega : eP.2 = 0 ∨ eP.2 = 1) with h | h
  · refine ⟨-eP.1, Or.inl ⟨?_, ?_⟩⟩
    · exact Prod.ext (by simp) h
    · exact Prod.ext (by omega) (by omega)
  · refine ⟨-eQ.1, Or.inr ⟨?_, ?_⟩⟩
    · exact Prod.ext (by omega) (by omega)
    · exact Prod.ext (by simp) (by omega)

section Esquina2

/- Value parameters. (Lean 4 only brings a `variable` into a theorem's scope when the
   theorem's statement mentions it, directly or transitively through a hypothesis binder's
   type — so hypotheses are taken as EXPLICIT binders in each theorem below, in the
   canonical order
     ha hb hba hm hn h1sum [h1neg] hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
     he1P he1Pval he1Q he1Qval hbr hR0 [heR hcR hPcoeff hQcoeff hP2 hQ2]
   with `hmn : m ≠ n` and `hgcd : Int.gcd m n = 1` carried in the header only (unused by
   item (2); they matter for item (1)). -/
variable {a b m n : Int}
variable {ρ₁ δP δQ ρ₂ : Int × Int}
variable {termsP termsQ : List Term}
variable {dirsP dirsQ : List (Int × Int)}
variable {e1P e1Q : Term}
variable {termsR : List Term} {eR : Term}

/-- Shared vertex for P (le basico, no sums needed): the rho1-face and the deltaP-face
    share a vertex a1, which is en_{rho1}(P) = (m*a, m*b). -/
theorem esquina_a1P
    (hsuccP : isSuccFrom ρ₁ δP dirsP)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hPne : termsP ≠ [])
    (h1sum : 0 < ρ₁.1 + ρ₁.2)
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b)) :
    ∃ a1 : Term, a1 ∈ faceTerms ρ₁.1 ρ₁.2 termsP ∧ a1 ∈ faceTerms δP.1 δP.2 termsP ∧
      a1.1 = (m * a, m * b) := by
  have h12P : dirLt ρ₁ δP := hsuccP.2.1
  set μ : Int × Int := (ρ₁.1 + δP.1, ρ₁.2 + δP.2) with hμ
  have hμ1 : dirLt ρ₁ μ := by
    show (0 : Int) < crossProd ρ₁ μ
    have e : crossProd ρ₁ μ = crossProd ρ₁ δP := by simp only [hμ, crossProd]; ring
    rw [e]; exact h12P
  have hμ2 : dirLt μ δP := by
    show (0 : Int) < crossProd μ δP
    have e : crossProd μ δP = crossProd ρ₁ δP := by simp only [hμ, crossProd]; ring
    rw [e]; exact h12P
  obtain ⟨α, β, hα, hβ, hρ⟩ := dir_between_pos_combo hμ1 hμ2 h12P
  obtain ⟨a1, ha1f1, ha1f2, -, -⟩ :=
    consecutive_weak_lebasico (ρ1 := ρ₁) (ρ2 := δP) (ρ := μ)
      (hbreak := fun {a1} ha1f ha1m {b} hbmem hb =>
        breakpoint_between h12P ha1f ha1m hbmem hb)
      hsuccP hdirsP hPne (ne_of_gt h12P) hα hβ hρ
  have heq : e1P.1 = a1.1 := shared_vertex_en h12P h1sum ha1f1 ha1f2 he1P
  exact ⟨a1, ha1f1, ha1f2, by rw [← heq]; exact he1Pval⟩

/-- Shared vertex for Q. -/
theorem esquina_a1Q
    (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hQne : termsQ ≠ [])
    (h1sum : 0 < ρ₁.1 + ρ₁.2)
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b)) :
    ∃ a1 : Term, a1 ∈ faceTerms ρ₁.1 ρ₁.2 termsQ ∧ a1 ∈ faceTerms δQ.1 δQ.2 termsQ ∧
      a1.1 = (n * a, n * b) := by
  have h12Q : dirLt ρ₁ δQ := hsuccQ.2.1
  set μ : Int × Int := (ρ₁.1 + δQ.1, ρ₁.2 + δQ.2) with hμ
  have hμ1 : dirLt ρ₁ μ := by
    show (0 : Int) < crossProd ρ₁ μ
    have e : crossProd ρ₁ μ = crossProd ρ₁ δQ := by simp only [hμ, crossProd]; ring
    rw [e]; exact h12Q
  have hμ2 : dirLt μ δQ := by
    show (0 : Int) < crossProd μ δQ
    have e : crossProd μ δQ = crossProd ρ₁ δQ := by simp only [hμ, crossProd]; ring
    rw [e]; exact h12Q
  obtain ⟨α, β, hα, hβ, hρ⟩ := dir_between_pos_combo hμ1 hμ2 h12Q
  obtain ⟨a1, ha1f1, ha1f2, -, -⟩ :=
    consecutive_weak_lebasico (ρ1 := ρ₁) (ρ2 := δQ) (ρ := μ)
      (hbreak := fun {a1} ha1f ha1m {b} hbmem hb =>
        breakpoint_between h12Q ha1f ha1m hbmem hb)
      hsuccQ hdirsQ hQne (ne_of_gt h12Q) hα hβ hρ
  have heq : e1Q.1 = a1.1 := shared_vertex_en h12Q h1sum ha1f1 ha1f2 he1Q
  exact ⟨a1, ha1f1, ha1f2, by rw [← heq]; exact he1Qval⟩

/-- The P shared vertex lies in the rho2-face; if rho2 is strictly below deltaP,
    the rho2-face is the singleton a1. -/
theorem esquina_a1P_in_rho2
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    {a1 : Term}
    (ha1f1 : a1 ∈ faceTerms ρ₁.1 ρ₁.2 termsP) (ha1f2 : a1 ∈ faceTerms δP.1 δP.2 termsP) :
    a1 ∈ faceTerms ρ₂.1 ρ₂.2 termsP ∧
      (dirLt ρ₂ δP → ∀ u ∈ faceTerms ρ₂.1 ρ₂.2 termsP, u.1 = a1.1) := by
  have h12P : dirLt ρ₁ δP := hsuccP.2.1
  have h12 : dirLt ρ₁ ρ₂ := by
    rw [hρ₂]
    rcases succMin_eq (δP := δP) (δQ := δQ) with h | h
    · rw [h]; exact h12P
    · rw [h]; exact hsuccQ.2.1
  have hleP : dirLt ρ₂ δP ∨ ρ₂ = δP := by rw [hρ₂]; exact succMin_le_P
  rcases hleP with hlt | heq
  · obtain ⟨α, β, hα, hβ, hρ⟩ := dir_between_pos_combo h12 hlt h12P
    obtain ⟨hsingle, hmem⟩ := face_between_singleton ha1f1 ha1f2 (ne_of_gt h12P) hα hβ hρ
    exact ⟨hmem, fun _ => hsingle⟩
  · subst heq
    exact ⟨ha1f2, fun hlt => absurd hlt (dirLt_irrefl ρ₂)⟩

/-- The Q shared vertex lies in the rho2-face; if rho2 is strictly below deltaQ,
    the rho2-face is the singleton a1. The proportional-successors case (cross = 0)
    is handled by face invariance under positive scaling. -/
theorem esquina_a1Q_in_rho2
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    {a1 : Term}
    (ha1f1 : a1 ∈ faceTerms ρ₁.1 ρ₁.2 termsQ) (ha1f2 : a1 ∈ faceTerms δQ.1 δQ.2 termsQ) :
    a1 ∈ faceTerms ρ₂.1 ρ₂.2 termsQ ∧
      (dirLt ρ₂ δQ → ∀ u ∈ faceTerms ρ₂.1 ρ₂.2 termsQ, u.1 = a1.1) := by
  have h12Q : dirLt ρ₁ δQ := hsuccQ.2.1
  have h12 : dirLt ρ₁ ρ₂ := by
    rw [hρ₂]
    rcases succMin_eq (δP := δP) (δQ := δQ) with h | h
    · rw [h]; exact hsuccP.2.1
    · rw [h]; exact h12Q
  have hleQ : dirLt ρ₂ δQ ∨ ρ₂ = δQ ∨ crossProd δP δQ = 0 := by
    rw [hρ₂]; exact succMin_le_Q_or_prop
  rcases hleQ with hlt | heq | hprop
  · obtain ⟨α, β, hα, hβ, hρ⟩ := dir_between_pos_combo h12 hlt h12Q
    obtain ⟨hsingle, hmem⟩ := face_between_singleton ha1f1 ha1f2 (ne_of_gt h12Q) hα hβ hρ
    exact ⟨hmem, fun _ => hsingle⟩
  · subst heq
    exact ⟨ha1f2, fun hlt => absurd hlt (dirLt_irrefl ρ₂)⟩
  · have hP0 : δP ≠ (0, 0) := by
      intro hh
      rw [hh] at hsuccP
      exact absurd hsuccP.2.1 (by simp [dirLt, crossProd])
    obtain ⟨q, hq1, hq2⟩ := exists_rat_smul_of_cross_zero hP0 hprop
    have hq0 : 0 < q := by
      have hC1 : (0 : ℚ) < crossProd ρ₁ δP := by exact_mod_cast hsuccP.2.1
      have hC2 : (0 : ℚ) < crossProd ρ₁ δQ := by exact_mod_cast hsuccQ.2.1
      have hEq : (crossProd ρ₁ δQ : ℚ) = q * crossProd ρ₁ δP := by
        simp only [crossProd]
        push_cast
        rw [hq1, hq2]
        ring
      by_contra hcon
      push Not at hcon
      have hle : q * (crossProd ρ₁ δP : ℚ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcon (le_of_lt hC1)
      rw [← hEq] at hle
      linarith
    have hface : faceTerms δQ.1 δQ.2 termsQ = faceTerms δP.1 δP.2 termsQ :=
      faceTerms_eq_of_cross_zero termsQ hP0 hprop ⟨q, hq0, hq1, hq2⟩
    have hcross2 : crossProd δQ δP = 0 := by
      have e : crossProd δQ δP = -crossProd δP δQ := by simp only [crossProd]; ring
      rw [e, hprop, neg_zero]
    have hρ₂P : ρ₂ = δP := by
      rw [hρ₂]
      unfold succMin
      rw [if_neg (by omega : ¬ (0 : Int) < crossProd δQ δP)]
    subst hρ₂P
    have ha1f2' : a1 ∈ faceTerms ρ₂.1 ρ₂.2 termsQ := by
      rw [← hface]; exact ha1f2
    exact ⟨ha1f2', fun hlt => by
      have hlt' : (0 : Int) < crossProd ρ₂ δQ := hlt
      rw [hprop] at hlt'
      exact absurd hlt' (lt_irrefl 0)⟩

/-- Opening, first part: (rho2,sigma2) < (-1,1) in V order. By contradiction via le basico:
    otherwise the (-1,1)-face is a single vertex and both valuations are m(b-a), n(b-a) < 0,
    contradicting the commutator valuation (480) applied to the constant bracket term. -/
theorem esquina_rho2_lt
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hm : 1 < m) (hn : 1 < n)
    (h1sum : 0 < ρ₁.1 + ρ₁.2)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    (hPne : termsP ≠ []) (hQne : termsQ ≠ [])
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b))
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0))
    (hR0 : eR.1 = (0, 0)) :
    dirLt ρ₂ (-1, 1) := by
  by_contra hcon
  have hle : crossProd ρ₂ (-1, 1) ≤ 0 := by
    have h : ¬ (0 : Int) < crossProd ρ₂ (-1, 1) := hcon
    omega
  have h12 : dirLt ρ₁ ρ₂ := by
    rw [hρ₂]
    rcases succMin_eq (δP := δP) (δQ := δQ) with h | h
    · rw [h]; exact hsuccP.2.1
    · rw [h]; exact hsuccQ.2.1
  have h1m : dirLt ρ₁ (-1, 1) := by
    show (0 : Int) < crossProd ρ₁ (-1, 1)
    have e : crossProd ρ₁ (-1, 1) = ρ₁.1 + ρ₁.2 := by simp only [crossProd]; ring
    rw [e]; exact h1sum
  obtain ⟨a1P, ha1Pf1, ha1Pf2, ha1Pval⟩ :=
    esquina_a1P hsuccP hdirsP hPne h1sum he1P he1Pval
  obtain ⟨a1Q, ha1Qf1, ha1Qf2, ha1Qval⟩ :=
    esquina_a1Q hsuccQ hdirsQ hQne h1sum he1Q he1Qval
  obtain ⟨ha1Pρ2, -⟩ := esquina_a1P_in_rho2 hsuccP hsuccQ hρ₂ ha1Pf1 ha1Pf2
  obtain ⟨ha1Qρ2, -⟩ := esquina_a1Q_in_rho2 hsuccP hsuccQ hρ₂ ha1Qf1 ha1Qf2
  have hfaces : a1P ∈ faceTerms (-1) 1 termsP ∧ a1Q ∈ faceTerms (-1) 1 termsQ := by
    rcases (by omega : crossProd ρ₂ (-1, 1) = 0 ∨ crossProd ρ₂ (-1, 1) < 0) with hcross0 | hcrossneg
    · have hsum0 : ρ₂.1 + ρ₂.2 = 0 := by
        have h := hcross0
        have e : crossProd ρ₂ (-1, 1) = ρ₂.1 + ρ₂.2 := by simp only [crossProd]; ring
        rw [e] at h; exact h
      have hρ₂1 : ρ₂.1 = -ρ₂.2 := by omega
      have hc : 0 < ρ₂.2 := by
        have hcr : crossProd ρ₁ ρ₂ = (ρ₁.1 + ρ₁.2) * ρ₂.2 := by
          simp only [crossProd]
          rw [hρ₂1]; ring
        have hpos : 0 < (ρ₁.1 + ρ₁.2) * ρ₂.2 := by rw [← hcr]; exact h12
        by_contra hcon2
        push Not at hcon2
        have hle2 : (ρ₁.1 + ρ₁.2) * ρ₂.2 ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt h1sum) hcon2
        linarith
      have hmemP : a1P ∈ faceTerms (-1) 1 termsP := by
        have e : faceTerms ρ₂.1 ρ₂.2 termsP = faceTerms (-1) 1 termsP := by
          have h1 : ρ₂.1 = ρ₂.2 * (-1) := by rw [hρ₂1]; ring
          calc faceTerms ρ₂.1 ρ₂.2 termsP
              = faceTerms (ρ₂.2 * (-1)) ρ₂.2 termsP := by rw [h1]
            _ = faceTerms (ρ₂.2 * (-1)) (ρ₂.2 * 1) termsP := by rw [mul_one]
            _ = faceTerms (-1) 1 termsP := faceTerms_smul hc (-1) 1 termsP
        rw [e] at ha1Pρ2
        exact ha1Pρ2
      have hmemQ : a1Q ∈ faceTerms (-1) 1 termsQ := by
        have e : faceTerms ρ₂.1 ρ₂.2 termsQ = faceTerms (-1) 1 termsQ := by
          have h1 : ρ₂.1 = ρ₂.2 * (-1) := by rw [hρ₂1]; ring
          calc faceTerms ρ₂.1 ρ₂.2 termsQ
              = faceTerms (ρ₂.2 * (-1)) ρ₂.2 termsQ := by rw [h1]
            _ = faceTerms (ρ₂.2 * (-1)) (ρ₂.2 * 1) termsQ := by rw [mul_one]
            _ = faceTerms (-1) 1 termsQ := faceTerms_smul hc (-1) 1 termsQ
        rw [e] at ha1Qρ2
        exact ha1Qρ2
      exact ⟨hmemP, hmemQ⟩
    · have hlt : dirLt (-1, 1) ρ₂ := by
        show (0 : Int) < crossProd (-1, 1) ρ₂
        have h := hcrossneg
        have e : crossProd (-1, 1) ρ₂ = -crossProd ρ₂ (-1, 1) := by
          simp only [crossProd]; ring
        rw [e]; omega
      obtain ⟨α, β, hα, hβ, hρ⟩ := dir_between_pos_combo h1m hlt h12
      obtain ⟨-, hmemP⟩ := face_between_singleton ha1Pf1 ha1Pρ2 (ne_of_gt h12) hα hβ hρ
      obtain ⟨α', β', hα', hβ', hρ'⟩ := dir_between_pos_combo h1m hlt h12
      obtain ⟨-, hmemQ⟩ := face_between_singleton ha1Qf1 ha1Qρ2 (ne_of_gt h12) hα' hβ' hρ'
      exact ⟨hmemP, hmemQ⟩
  obtain ⟨hfaceP, hfaceQ⟩ := hfaces
  have hboundP : ∀ m' ∈ termsP, dirVal (-1) 1 m'.1.1 m'.1.2 ≤ m * (b - a) := by
    intro m' hm'
    have h := faceTerms_max hfaceP (List.mem_map.mpr ⟨m', hm', rfl⟩)
    have h1 : a1P.1.1 = m * a := congrArg Prod.fst ha1Pval
    have h2 : a1P.1.2 = m * b := congrArg Prod.snd ha1Pval
    have hv : dirVal (-1) 1 a1P.1.1 a1P.1.2 = m * (b - a) := by
      simp only [dirVal, h1, h2]; ring
    rw [hv] at h
    exact h
  have hboundQ : ∀ n' ∈ termsQ, dirVal (-1) 1 n'.1.1 n'.1.2 ≤ n * (b - a) := by
    intro n' hn'
    have h := faceTerms_max hfaceQ (List.mem_map.mpr ⟨n', hn', rfl⟩)
    have h1 : a1Q.1.1 = n * a := congrArg Prod.fst ha1Qval
    have h2 : a1Q.1.2 = n * b := congrArg Prod.snd ha1Qval
    have hv : dirVal (-1) 1 a1Q.1.1 a1Q.1.2 = n * (b - a) := by
      simp only [dirVal, h1, h2]; ring
    rw [hv] at h
    exact h
  obtain ⟨t, htface, ht2⟩ := hbr.2
  have htbr : t ∈ bracket termsP termsQ := by
    have hmem : t ∈ bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ) :=
      faceTerms_subset htface
    obtain ⟨m, hm, n, hn, rfl⟩ := bracket_mem.mp hmem
    exact bracket_mem.mpr ⟨m, faceTerms_subset hm, n, faceTerms_subset hn, rfl⟩
  have ht0 : t.1 = (0, 0) := by
    have h := hbr.1 t htface ht2
    rw [hR0] at h
    exact h
  have hbrle := bracket_val_le (ρ := (-1)) (σ := 1) (vP := m * (b - a)) (vQ := n * (b - a))
    hboundP hboundQ htbr
  have htval : dirVal (-1) 1 t.1.1 t.1.2 = 0 := by
    rw [ht0]
    simp [dirVal]
  rw [htval] at hbrle
  have hneg : m * (b - a) + n * (b - a) < 0 := by
    have h2 : m * (b - a) + n * (b - a) = (m + n) * (b - a) := by ring
    rw [h2]
    exact mul_neg_of_pos_of_neg (by omega) (by omega)
  omega

/-- (rho2,sigma2) lies in V_{>0}: its sum is positive. -/
theorem esquina_rho2_sum
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hm : 1 < m) (hn : 1 < n)
    (h1sum : 0 < ρ₁.1 + ρ₁.2)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    (hPne : termsP ≠ []) (hQne : termsQ ≠ [])
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b))
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0))
    (hR0 : eR.1 = (0, 0)) :
    0 < ρ₂.1 + ρ₂.2 := by
  have h := esquina_rho2_lt ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
    he1P he1Pval he1Q he1Qval hbr hR0
  have e : crossProd ρ₂ (-1, 1) = ρ₂.1 + ρ₂.2 := by simp only [crossProd]; ring
  have h' : (0 : Int) < crossProd ρ₂ (-1, 1) := h
  rw [e] at h'
  exact h'

/-- Opening: rho2 < 0. -/
theorem esquina_rho2_neg
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hm : 1 < m) (hn : 1 < n)
    (h1sum : 0 < ρ₁.1 + ρ₁.2) (h1neg : ρ₁.1 < 0)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    (hPne : termsP ≠ []) (hQne : termsQ ≠ [])
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b))
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0))
    (hR0 : eR.1 = (0, 0)) :
    ρ₂.1 < 0 := by
  have h12 : dirLt ρ₁ ρ₂ := by
    rw [hρ₂]
    rcases succMin_eq (δP := δP) (δQ := δQ) with h | h
    · rw [h]; exact hsuccP.2.1
    · rw [h]; exact hsuccQ.2.1
  have hS2 : 0 < ρ₂.1 + ρ₂.2 :=
    esquina_rho2_sum ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  have hId : (ρ₁.1 + ρ₁.2) * (-ρ₂.1) = crossProd ρ₁ ρ₂ - ρ₁.1 * (ρ₂.1 + ρ₂.2) := by
    simp only [crossProd]; ring
  have hpos : 0 < (ρ₁.1 + ρ₁.2) * (-ρ₂.1) := by
    rw [hId]
    have hB : (0 : Int) < crossProd ρ₁ ρ₂ := h12
    have h2 : 0 < -ρ₁.1 * (ρ₂.1 + ρ₂.2) := mul_pos (by omega : (0 : Int) < -ρ₁.1) hS2
    linarith
  by_contra hcon
  push Not at hcon
  have hle : (ρ₁.1 + ρ₁.2) * (-ρ₂.1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt h1sum) (by omega : -ρ₂.1 ≤ 0)
  linarith

/-- eq:proporcionalidad: st_2(P) = en_1(P) = (m*a, m*b) and st_2(Q) = (n*a, n*b). -/
theorem esquina_proporcionalidad
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hm : 1 < m) (hn : 1 < n)
    (h1sum : 0 < ρ₁.1 + ρ₁.2)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    (hPne : termsP ≠ []) (hQne : termsQ ≠ [])
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b))
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0))
    (hR0 : eR.1 = (0, 0)) :
    (∃ s2P : Term, stFace ρ₂.1 ρ₂.2 termsP = some s2P ∧ s2P.1 = (m * a, m * b)) ∧
    (∃ s2Q : Term, stFace ρ₂.1 ρ₂.2 termsQ = some s2Q ∧ s2Q.1 = (n * a, n * b)) := by
  obtain ⟨a1P, ha1Pf1, ha1Pf2, ha1Pval⟩ :=
    esquina_a1P hsuccP hdirsP hPne h1sum he1P he1Pval
  obtain ⟨a1Q, ha1Qf1, ha1Qf2, ha1Qval⟩ :=
    esquina_a1Q hsuccQ hdirsQ hQne h1sum he1Q he1Qval
  obtain ⟨ha1Pρ2, hsingP⟩ := esquina_a1P_in_rho2 hsuccP hsuccQ hρ₂ ha1Pf1 ha1Pf2
  obtain ⟨ha1Qρ2, hsingQ⟩ := esquina_a1Q_in_rho2 hsuccP hsuccQ hρ₂ ha1Qf1 ha1Qf2
  have h2sum : 0 < ρ₂.1 + ρ₂.2 :=
    esquina_rho2_sum ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  have h12P : dirLt ρ₁ δP := hsuccP.2.1
  have h12Q : dirLt ρ₁ δQ := hsuccQ.2.1
  constructor
  · obtain ⟨s2P, hs2P⟩ : ∃ s2P : Term, stFace ρ₂.1 ρ₂.2 termsP = some s2P := by
      cases hnone : stFace ρ₂.1 ρ₂.2 termsP with
      | none =>
        exfalso
        have hnil : faceTerms ρ₂.1 ρ₂.2 termsP = [] := stFaceAux_none hnone
        exact faceTerms_nonempty hPne hnil
      | some s => exact ⟨s, rfl⟩
    refine ⟨s2P, hs2P, ?_⟩
    by_cases hlt : dirLt ρ₂ δP
    · have h := hsingP hlt s2P (stFaceAux_mem hs2P)
      rw [h]; exact ha1Pval
    · have hleP : dirLt ρ₂ δP ∨ ρ₂ = δP := by rw [hρ₂]; exact succMin_le_P
      rcases hleP with h | h
      · exact absurd h hlt
      · subst h
        have h := shared_vertex_st h12P h2sum ha1Pf1 ha1Pf2 hs2P
        rw [h]; exact ha1Pval
  · obtain ⟨s2Q, hs2Q⟩ : ∃ s2Q : Term, stFace ρ₂.1 ρ₂.2 termsQ = some s2Q := by
      cases hnone : stFace ρ₂.1 ρ₂.2 termsQ with
      | none =>
        exfalso
        have hnil : faceTerms ρ₂.1 ρ₂.2 termsQ = [] := stFaceAux_none hnone
        exact faceTerms_nonempty hQne hnil
      | some s => exact ⟨s, rfl⟩
    refine ⟨s2Q, hs2Q, ?_⟩
    by_cases hlt : dirLt ρ₂ δQ
    · have h := hsingQ hlt s2Q (stFaceAux_mem hs2Q)
      rw [h]; exact ha1Qval
    · have hleQ : dirLt ρ₂ δQ ∨ ρ₂ = δQ ∨ crossProd δP δQ = 0 := by
        rw [hρ₂]; exact succMin_le_Q_or_prop
      rcases hleQ with h | h | hprop
      · exact absurd h hlt
      · subst h
        have h := shared_vertex_st h12Q h2sum ha1Qf1 ha1Qf2 hs2Q
        rw [h]; exact ha1Qval
      · have hP0 : δP ≠ (0, 0) := by
          intro hh
          rw [hh] at hsuccP
          exact absurd hsuccP.2.1 (by simp [dirLt, crossProd])
        obtain ⟨q, hq1, hq2⟩ := exists_rat_smul_of_cross_zero hP0 hprop
        have hq0 : 0 < q := by
          have hC1 : (0 : ℚ) < crossProd ρ₁ δP := by exact_mod_cast hsuccP.2.1
          have hC2 : (0 : ℚ) < crossProd ρ₁ δQ := by exact_mod_cast hsuccQ.2.1
          have hEq : (crossProd ρ₁ δQ : ℚ) = q * crossProd ρ₁ δP := by
            simp only [crossProd]
            push_cast
            rw [hq1, hq2]
            ring
          by_contra hcon
          push Not at hcon
          have hle : q * (crossProd ρ₁ δP : ℚ) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hcon (le_of_lt hC1)
          rw [← hEq] at hle
          linarith
        have hface : faceTerms δQ.1 δQ.2 termsQ = faceTerms δP.1 δP.2 termsQ :=
          faceTerms_eq_of_cross_zero termsQ hP0 hprop ⟨q, hq0, hq1, hq2⟩
        have hcross2 : crossProd δQ δP = 0 := by
          have e : crossProd δQ δP = -crossProd δP δQ := by simp only [crossProd]; ring
          rw [e, hprop, neg_zero]
        have hρ₂P : ρ₂ = δP := by
          rw [hρ₂]
          unfold succMin
          rw [if_neg (by omega : ¬ (0 : Int) < crossProd δQ δP)]
        subst hρ₂P
        have ha1QδP : a1Q ∈ faceTerms ρ₂.1 ρ₂.2 termsQ := by
          rw [← hface]; exact ha1Qf2
        have h := shared_vertex_st h12P h2sum ha1Qf1 ha1QδP hs2Q
        rw [h]; exact ha1Qval

/-- eq:cociente: v_2(P) = m * v_2(a,b), v_2(Q) = n * v_2(a,b). -/
theorem esquina_cociente {s2P s2Q : Term}
    (hs2P : stFace ρ₂.1 ρ₂.2 termsP = some s2P) (hs2Pval : s2P.1 = (m * a, m * b))
    (hs2Q : stFace ρ₂.1 ρ₂.2 termsQ = some s2Q) (hs2Qval : s2Q.1 = (n * a, n * b)) :
    dirVal ρ₂.1 ρ₂.2 s2P.1.1 s2P.1.2 = m * dirVal ρ₂.1 ρ₂.2 a b ∧
    dirVal ρ₂.1 ρ₂.2 s2Q.1.1 s2Q.1.2 = n * dirVal ρ₂.1 ρ₂.2 a b := by
  have h1 : s2P.1.1 = m * a := congrArg Prod.fst hs2Pval
  have h2 : s2P.1.2 = m * b := congrArg Prod.snd hs2Pval
  have h3 : s2Q.1.1 = n * a := congrArg Prod.fst hs2Qval
  have h4 : s2Q.1.2 = n * b := congrArg Prod.snd hs2Qval
  constructor
  · simp only [dirVal, h1, h2]; ring
  · simp only [dirVal, h3, h4]; ring

/-- Opening, desigualdades: v_2(P) > 0, v_2(Q) > 0, and v_2(a,b) > 0, via the
    commutator valuation (480) at rho2 applied to the constant bracket term. -/
theorem esquina_desig
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hm : 1 < m) (hn : 1 < n)
    (h1sum : 0 < ρ₁.1 + ρ₁.2)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    (hPne : termsP ≠ []) (hQne : termsQ ≠ [])
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b))
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0))
    (hR0 : eR.1 = (0, 0))
    {s2P s2Q : Term}
    (hs2P : stFace ρ₂.1 ρ₂.2 termsP = some s2P) (hs2Pval : s2P.1 = (m * a, m * b))
    (hs2Q : stFace ρ₂.1 ρ₂.2 termsQ = some s2Q) (hs2Qval : s2Q.1 = (n * a, n * b)) :
    0 < dirVal ρ₂.1 ρ₂.2 s2P.1.1 s2P.1.2 ∧ 0 < dirVal ρ₂.1 ρ₂.2 s2Q.1.1 s2Q.1.2 ∧
    0 < dirVal ρ₂.1 ρ₂.2 a b := by
  obtain ⟨hcP, hcQ⟩ := esquina_cociente hs2P hs2Pval hs2Q hs2Qval
  have h2sum : 0 < ρ₂.1 + ρ₂.2 :=
    esquina_rho2_sum ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  obtain ⟨t, htface, ht2⟩ := hbr.2
  have htbr : t ∈ bracket termsP termsQ := by
    have hmem : t ∈ bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ) :=
      faceTerms_subset htface
    obtain ⟨m, hm, n, hn, rfl⟩ := bracket_mem.mp hmem
    exact bracket_mem.mpr ⟨m, faceTerms_subset hm, n, faceTerms_subset hn, rfl⟩
  have ht0 : t.1 = (0, 0) := by
    have h := hbr.1 t htface ht2
    rw [hR0] at h
    exact h
  have hP : ∀ m' ∈ termsP, dirVal ρ₂.1 ρ₂.2 m'.1.1 m'.1.2 ≤ dirVal ρ₂.1 ρ₂.2 s2P.1.1 s2P.1.2 :=
    fun m' hm' => faceTerms_max (stFaceAux_mem hs2P) (List.mem_map.mpr ⟨m', hm', rfl⟩)
  have hQ : ∀ n' ∈ termsQ, dirVal ρ₂.1 ρ₂.2 n'.1.1 n'.1.2 ≤ dirVal ρ₂.1 ρ₂.2 s2Q.1.1 s2Q.1.2 :=
    fun n' hn' => faceTerms_max (stFaceAux_mem hs2Q) (List.mem_map.mpr ⟨n', hn', rfl⟩)
  have hle := bracket_val_le (ρ := ρ₂.1) (σ := ρ₂.2) hP hQ htbr
  have htval : dirVal ρ₂.1 ρ₂.2 t.1.1 t.1.2 = 0 := by
    rw [ht0]
    simp [dirVal]
  rw [htval, hcP, hcQ] at hle
  have hV : 0 < dirVal ρ₂.1 ρ₂.2 a b := by
    by_contra hcon
    push Not at hcon
    have h1 : m * dirVal ρ₂.1 ρ₂.2 a b + n * dirVal ρ₂.1 ρ₂.2 a b ≤ 0 := by
      have e : m * dirVal ρ₂.1 ρ₂.2 a b + n * dirVal ρ₂.1 ρ₂.2 a b
          = (m + n) * dirVal ρ₂.1 ρ₂.2 a b := by ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (by omega : (0 : Int) ≤ m + n) hcon
    linarith
  refine ⟨?_, ?_, hV⟩
  · rw [hcP]; exact mul_pos (by omega : (0 : Int) < m) hV
  · rw [hcQ]; exact mul_pos (by omega : (0 : Int) < n) hV

/-- The direction rho3 := dir(a,b), factored via g := gcd(a,b): rho2 < rho3 < (-1,1). -/
theorem esquina_rho3
    (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hV : 0 < dirVal ρ₂.1 ρ₂.2 a b) :
    ∃ (g a' b' : Int) (ρ₃ : Int × Int),
      0 < g ∧ a = g * a' ∧ b = g * b' ∧ 0 < b' ∧ b' < a' ∧
      ρ₃ = (-b', a') ∧ dirLt ρ₂ ρ₃ ∧ dirLt ρ₃ (-1, 1) := by
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
  set g : Int := (Int.gcd a b : Int) with hgdef
  have hg : (0 : Int) < g := by
    rw [hgdef]
    exact_mod_cast Int.gcd_pos_of_ne_zero_left b (ne_of_gt ha)
  have hb'pos : 0 < b' := by
    by_contra hcon
    push Not at hcon
    have hle : g * b' ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hg) hcon
    rw [← hb'] at hle
    linarith
  have hba' : b' < a' := by
    by_contra hcon
    push Not at hcon
    have hle : g * a' ≤ g * b' := mul_le_mul_of_nonneg_left hcon (le_of_lt hg)
    have h : g * b' < g * a' := by rw [← hb', ← ha']; exact hba
    linarith
  refine ⟨g, a', b', (-b', a'), hg, ha', hb', hb'pos, hba', rfl, ?_, ?_⟩
  · show (0 : Int) < crossProd ρ₂ (-b', a')
    have hEq : g * crossProd ρ₂ (-b', a') = dirVal ρ₂.1 ρ₂.2 a b := by
      have e1 : crossProd ρ₂ (-b', a') = ρ₂.1 * a' + ρ₂.2 * b' := by
        simp only [crossProd]; ring
      rw [e1]
      simp only [dirVal]
      linear_combination (-ρ₂.1) * ha' + (-ρ₂.2) * hb'
    have hpos : 0 < g * crossProd ρ₂ (-b', a') := by rw [hEq]; exact hV
    by_contra hcon
    push Not at hcon
    have hle : g * crossProd ρ₂ (-b', a') ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hg) hcon
    linarith
  · show (0 : Int) < crossProd (-b', a') (-1, 1)
    have e : crossProd (-b', a') (-1, 1) = a' - b' := by simp only [crossProd]; ring
    rw [e]; omega

/-- Esquina item (2) (TeX 5440-5470), at exponent level, l = 1: if the rho2-endpoints
    are nonsimilar, then {en_2(P), en_2(Q)} = {(-k,0),(k+1,1)} for some k in N with
    (k+1)b < a, and (rho2,sigma2) lies in Dir(P) ∩ Dir(Q). -/
theorem esquina_item2
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hm : 1 < m) (hn : 1 < n)
    (h1sum : 0 < ρ₁.1 + ρ₁.2) (h1neg : ρ₁.1 < 0)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    (hPne : termsP ≠ []) (hQne : termsQ ≠ [])
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b))
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0))
    (hR0 : eR.1 = (0, 0))
    (heR : enFace ρ₂.1 ρ₂.2 termsR = some eR) (hcR : eR.2 ≠ 0)
    (hPcoeff : ∀ t ∈ termsP, t.2 ≠ 0) (hQcoeff : ∀ t ∈ termsQ, t.2 ≠ 0)
    (hP2 : ∀ t ∈ termsP, 0 ≤ t.1.2) (hQ2 : ∀ t ∈ termsQ, 0 ≤ t.1.2)
    {e2P e2Q : Term}
    (he2P : enFace ρ₂.1 ρ₂.2 termsP = some e2P)
    (he2Q : enFace ρ₂.1 ρ₂.2 termsQ = some e2Q)
    (hnonsim : crossProd e2P.1 e2Q.1 ≠ 0) :
    ∃ k : Int, 0 < k ∧ (k + 1) * b < a ∧
      ((e2P.1 = (-k, 0) ∧ e2Q.1 = (k + 1, 1)) ∨ (e2P.1 = (k + 1, 1) ∧ e2Q.1 = (-k, 0))) ∧
      isDir ρ₂.1 ρ₂.2 termsP ∧ isDir ρ₂.1 ρ₂.2 termsQ := by
  obtain ⟨⟨s2P, hs2P, hs2Pval⟩, ⟨s2Q, hs2Q, hs2Qval⟩⟩ :=
    esquina_proporcionalidad ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  obtain ⟨hvP, hvQ, hV⟩ :=
    esquina_desig ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0 hs2P hs2Pval hs2Q hs2Qval
  have h2sum : 0 < ρ₂.1 + ρ₂.2 :=
    esquina_rho2_sum ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  have h2neg : ρ₂.1 < 0 :=
    esquina_rho2_neg ha hb hba hm hn h1sum h1neg hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  have hsum := en_sum_eq_one_one h2sum he2P he2Q heR
    (hPcoeff e2P (faceTerms_subset (enFaceAux_mem he2P)))
    (hQcoeff e2Q (faceTerms_subset (enFaceAux_mem he2Q)))
    hcR hR0 hbr hnonsim
  have he2P2 : 0 ≤ e2P.1.2 := hP2 e2P (faceTerms_subset (enFaceAux_mem he2P))
  have he2Q2 : 0 ≤ e2Q.1.2 := hQ2 e2Q (faceTerms_subset (enFaceAux_mem he2Q))
  obtain ⟨k, hpair⟩ := pair_form_of_sum he2P2 he2Q2 hsum
  have hfaceP : dirVal ρ₂.1 ρ₂.2 e2P.1.1 e2P.1.2 = dirVal ρ₂.1 ρ₂.2 s2P.1.1 s2P.1.2 := by
    have hem : e2P ∈ faceTerms ρ₂.1 ρ₂.2 termsP := enFaceAux_mem he2P
    have hsm : s2P ∈ faceTerms ρ₂.1 ρ₂.2 termsP := stFaceAux_mem hs2P
    obtain ⟨m, hm, -, hve⟩ := faceTerms_mem.mp hem
    obtain ⟨m', hm', -, hvs⟩ := faceTerms_mem.mp hsm
    have hmm : m = m' := Option.some.inj (hm.symm.trans hm')
    subst hmm
    rw [hve, hvs]
  have hfaceQ : dirVal ρ₂.1 ρ₂.2 e2Q.1.1 e2Q.1.2 = dirVal ρ₂.1 ρ₂.2 s2Q.1.1 s2Q.1.2 := by
    have hem : e2Q ∈ faceTerms ρ₂.1 ρ₂.2 termsQ := enFaceAux_mem he2Q
    have hsm : s2Q ∈ faceTerms ρ₂.1 ρ₂.2 termsQ := stFaceAux_mem hs2Q
    obtain ⟨m, hm, -, hve⟩ := faceTerms_mem.mp hem
    obtain ⟨m', hm', -, hvs⟩ := faceTerms_mem.mp hsm
    have hmm : m = m' := Option.some.inj (hm.symm.trans hm')
    subst hmm
    rw [hve, hvs]
  have hk0 : 0 < k := by
    rcases hpair with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · have h1 : e2P.1.1 = -k := congrArg Prod.fst hP
      have h2 : e2P.1.2 = 0 := congrArg Prod.snd hP
      rw [h1, h2] at hfaceP
      have hv2 : dirVal ρ₂.1 ρ₂.2 (-k) 0 = -k * ρ₂.1 := by simp only [dirVal]; ring
      rw [hv2] at hfaceP
      have hpos : 0 < -k * ρ₂.1 := by rw [hfaceP]; exact hvP
      by_contra hcon
      push Not at hcon
      have hle : -k * ρ₂.1 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by omega : (0 : Int) ≤ -k) (le_of_lt h2neg)
      linarith
    · have h1 : e2Q.1.1 = -k := congrArg Prod.fst hQ
      have h2 : e2Q.1.2 = 0 := congrArg Prod.snd hQ
      rw [h1, h2] at hfaceQ
      have hv2 : dirVal ρ₂.1 ρ₂.2 (-k) 0 = -k * ρ₂.1 := by simp only [dirVal]; ring
      rw [hv2] at hfaceQ
      have hpos : 0 < -k * ρ₂.1 := by rw [hfaceQ]; exact hvQ
      by_contra hcon
      push Not at hcon
      have hle : -k * ρ₂.1 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by omega : (0 : Int) ≤ -k) (le_of_lt h2neg)
      linarith
  have hkb : (k + 1) * b < a := by
    obtain ⟨g, a', b', ρ₃, hg, ha', hb', hb'pos, hba', hρ₃, h23, h3m⟩ :=
      esquina_rho3 ha hb hba hV
    have h12 : dirLt ρ₂ (-1, 1) :=
      esquina_rho2_lt ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
        he1P he1Pval he1Q he1Qval hbr hR0
    have hmb : 1 < m * b := by
      have h1 : (1 : Int) ≤ b := hb
      have h2 : m * 1 ≤ m * b := mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ m)
      rw [mul_one] at h2
      omega
    have hnb : 1 < n * b := by
      have h1 : (1 : Int) ≤ b := hb
      have h2 : n * 1 ≤ n * b := mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ n)
      rw [mul_one] at h2
      omega
    rcases hpair with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · have hne : e2Q.1 ≠ s2Q.1 := by
        intro hEq
        have h2 : e2Q.1.2 = 1 := congrArg Prod.snd hQ
        have h4 : s2Q.1.2 = n * b := congrArg Prod.snd hs2Qval
        rw [hEq, h4] at h2
        omega
      have hsval : dirVal ρ₃.1 ρ₃.2 s2Q.1.1 s2Q.1.2 = 0 := by
        have h1 : s2Q.1.1 = n * a := congrArg Prod.fst hs2Qval
        have h2 : s2Q.1.2 = n * b := congrArg Prod.snd hs2Qval
        have e : dirVal ρ₃.1 ρ₃.2 s2Q.1.1 s2Q.1.2 = n * (-b' * a + a' * b) := by
          have hp1 : ρ₃.1 = -b' := congrArg Prod.fst hρ₃
          have hp2 : ρ₃.2 = a' := congrArg Prod.snd hρ₃
          rw [hp1, hp2]
          simp only [dirVal, h1, h2]
          ring
        rw [e]
        have hz : -b' * a + a' * b = 0 := by rw [ha', hb']; ring
        rw [hz, mul_zero]
      have hpos := endpoint_val_pos h23 h3m h12 (ne_of_gt h2sum) he2Q hs2Q hne hsval
      have hval : dirVal ρ₃.1 ρ₃.2 e2Q.1.1 e2Q.1.2 = a' - b' * (k + 1) := by
        have h1 : e2Q.1.1 = k + 1 := congrArg Prod.fst hQ
        have h2 : e2Q.1.2 = 1 := congrArg Prod.snd hQ
        have hp1 : ρ₃.1 = -b' := congrArg Prod.fst hρ₃
        have hp2 : ρ₃.2 = a' := congrArg Prod.snd hρ₃
        rw [hp1, hp2]
        simp only [dirVal, h1, h2]
        ring
      rw [hval] at hpos
      have h1 : b' * (k + 1) < a' := by omega
      have h2 : g * (b' * (k + 1)) < g * a' := mul_lt_mul_of_pos_left h1 hg
      have e1 : g * (b' * (k + 1)) = b * (k + 1) := by
        calc g * (b' * (k + 1)) = (g * b') * (k + 1) := by ring
          _ = b * (k + 1) := by rw [← hb']
      have e2 : g * a' = a := ha'.symm
      rw [e1, e2] at h2
      exact by rwa [mul_comm] at h2
    · have hne : e2P.1 ≠ s2P.1 := by
        intro hEq
        have h2 : e2P.1.2 = 1 := congrArg Prod.snd hP
        have h4 : s2P.1.2 = m * b := congrArg Prod.snd hs2Pval
        rw [hEq, h4] at h2
        omega
      have hsval : dirVal ρ₃.1 ρ₃.2 s2P.1.1 s2P.1.2 = 0 := by
        have h1 : s2P.1.1 = m * a := congrArg Prod.fst hs2Pval
        have h2 : s2P.1.2 = m * b := congrArg Prod.snd hs2Pval
        have e : dirVal ρ₃.1 ρ₃.2 s2P.1.1 s2P.1.2 = m * (-b' * a + a' * b) := by
          have hp1 : ρ₃.1 = -b' := congrArg Prod.fst hρ₃
          have hp2 : ρ₃.2 = a' := congrArg Prod.snd hρ₃
          rw [hp1, hp2]
          simp only [dirVal, h1, h2]
          ring
        rw [e]
        have hz : -b' * a + a' * b = 0 := by rw [ha', hb']; ring
        rw [hz, mul_zero]
      have hpos := endpoint_val_pos h23 h3m h12 (ne_of_gt h2sum) he2P hs2P hne hsval
      have hval : dirVal ρ₃.1 ρ₃.2 e2P.1.1 e2P.1.2 = a' - b' * (k + 1) := by
        have h1 : e2P.1.1 = k + 1 := congrArg Prod.fst hP
        have h2 : e2P.1.2 = 1 := congrArg Prod.snd hP
        have hp1 : ρ₃.1 = -b' := congrArg Prod.fst hρ₃
        have hp2 : ρ₃.2 = a' := congrArg Prod.snd hρ₃
        rw [hp1, hp2]
        simp only [dirVal, h1, h2]
        ring
      rw [hval] at hpos
      have h1 : b' * (k + 1) < a' := by omega
      have h2 : g * (b' * (k + 1)) < g * a' := mul_lt_mul_of_pos_left h1 hg
      have e1 : g * (b' * (k + 1)) = b * (k + 1) := by
        calc g * (b' * (k + 1)) = (g * b') * (k + 1) := by ring
          _ = b * (k + 1) := by rw [← hb']
      have e2 : g * a' = a := ha'.symm
      rw [e1, e2] at h2
      exact by rwa [mul_comm] at h2
  have hdirP : isDir ρ₂.1 ρ₂.2 termsP := by
    refine ⟨s2P, e2P, stFaceAux_mem hs2P, enFaceAux_mem he2P, ?_⟩
    intro hEq
    have h2 : e2P.1.2 = 0 ∨ e2P.1.2 = 1 := by
      rcases hpair with ⟨hP, -⟩ | ⟨hP, -⟩
      · rw [hP]; simp
      · rw [hP]; simp
    have h4 : s2P.1.2 = m * b := congrArg Prod.snd hs2Pval
    have hmb : 1 < m * b := by
      have h1 : (1 : Int) ≤ b := hb
      have h2' : m * 1 ≤ m * b := mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ m)
      rw [mul_one] at h2'
      omega
    rw [← hEq, h4] at h2
    omega
  have hdirQ : isDir ρ₂.1 ρ₂.2 termsQ := by
    refine ⟨s2Q, e2Q, stFaceAux_mem hs2Q, enFaceAux_mem he2Q, ?_⟩
    intro hEq
    have h2 : e2Q.1.2 = 0 ∨ e2Q.1.2 = 1 := by
      rcases hpair with ⟨-, hQ⟩ | ⟨-, hQ⟩
      · rw [hQ]; simp
      · rw [hQ]; simp
    have h4 : s2Q.1.2 = n * b := congrArg Prod.snd hs2Qval
    have hnb : 1 < n * b := by
      have h1 : (1 : Int) ≤ b := hb
      have h2' : n * 1 ≤ n * b := mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ n)
      rw [mul_one] at h2'
      omega
    rw [← hEq, h4] at h2
    omega
  exact ⟨k, hk0, hkb, hpair, hdirP, hdirQ⟩

/-- k = 1 corollary, in Part18's exact conclusion form: if a < 3b (as in GGHV's
    applications, e.g. (a,b) = (8,3)), the pair is {(-1,0),(2,1)}. -/
theorem esquina_item2_k1
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hm : 1 < m) (hn : 1 < n)
    (h1sum : 0 < ρ₁.1 + ρ₁.2) (h1neg : ρ₁.1 < 0)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    (hPne : termsP ≠ []) (hQne : termsQ ≠ [])
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b))
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0))
    (hR0 : eR.1 = (0, 0))
    (heR : enFace ρ₂.1 ρ₂.2 termsR = some eR) (hcR : eR.2 ≠ 0)
    (hPcoeff : ∀ t ∈ termsP, t.2 ≠ 0) (hQcoeff : ∀ t ∈ termsQ, t.2 ≠ 0)
    (hP2 : ∀ t ∈ termsP, 0 ≤ t.1.2) (hQ2 : ∀ t ∈ termsQ, 0 ≤ t.1.2)
    {e2P e2Q : Term}
    (he2P : enFace ρ₂.1 ρ₂.2 termsP = some e2P)
    (he2Q : enFace ρ₂.1 ρ₂.2 termsQ = some e2Q)
    (hnonsim : crossProd e2P.1 e2Q.1 ≠ 0) (ha2 : a < 3 * b) :
    (e2P.1 = (-1, 0) ∧ e2Q.1 = (2, 1)) ∨ (e2P.1 = (2, 1) ∧ e2Q.1 = (-1, 0)) := by
  obtain ⟨k, hk0, hk1, hpair, -, -⟩ :=
    esquina_item2 ha hb hba hm hn h1sum h1neg hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0 heR hcR hPcoeff hQcoeff hP2 hQ2 he2P he2Q hnonsim
  have hk : k = 1 := by
    have h1 : (k + 1) * b < 3 * b := lt_trans hk1 ha2
    have h2 : k + 1 < 3 := by
      by_contra hcon
      push Not at hcon
      have hle : 3 * b ≤ (k + 1) * b := mul_le_mul_of_nonneg_right hcon (le_of_lt hb)
      linarith
    omega
  subst hk
  rcases hpair with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · left
    exact ⟨by simpa using hP, by simpa using hQ⟩
  · right
    exact ⟨by simpa using hP, by simpa using hQ⟩

end Esquina2

/- ESQUINA ITEM (1) — caso alineado (TeX 5320-5360 + 5420-5440), 2026-11-05.
   Self-contained scratch section, assembled on top of the proved
   d1_esquina2_2026-11-05.lean (whole file). Nothing in the proved files
   is modified.

   CLAIM: if en₂(P) ∼ en₂(Q) (aligned, crossProd = 0), then
   (ρ₂,σ₂) ∈ Dir(P) ∩ Dir(Q) and the caso-alineado triple holds:
   (a',b') := (1/m)en₂(P) = (1/n)en₂(Q) ∈ ℤ × ℕ₀,
   v_{ρ₁}(a',b') < v_{ρ₁}(a,b), and ab' − ba' > 0.
   STATUS: PROVED 2026-11-05 — round 2 foreground re-check LEAN_EXIT=0,
   0 errors (Lean 4.34.0, lean-build-3); axioms check AXIOMS_EXIT=0, all
   five new theorems on exactly [propext, Classical.choice, Quot.sound],
   no extra axioms. Round 1 FAILED (LEAN_EXIT=1, 7 errors, all diagnosed:
   `rw [hve, hvs]` needs `← hvs` when the goal has only one face
   valuation; `subst h` on h : ρ₂ = δP eliminates δP, use `rw [h] at hP`;
   a shadowed `h` in he2f made `h.symm` hit an Int ≤ proof).

   Proof route (paper TeX 5410-5440):
   * eqq13 (`esquina_eqq13`): en₂(P) = λ·en₂(Q) ⟹ λ = m/n, from the
     cociente valuations (esquina_cociente + esquina_desig,
     v₂(a,b) > 0) and the rational proportionality from alignment
     (`exists_rat_smul_of_cross_zero`). Integer form:
     n·en₂(P) = m·en₂(Q).
   * "esta en dir" (`esquina_esta_en_dir`): en₂(P) = st₂(P) ⟺
     en₂(Q) = st₂(Q) (from eqq13 + proporcionalidad, pure integer
     arithmetic); if ρ₂ ∉ Dir(P) then the ρ₂-face of P is a single
     exponent, hence so is Q's (via the two-tie face-singleton lemma),
     contradicting ρ₂ = min{Succ_P, Succ_Q} (one side attains it, and
     a successor is in Dir).
   * (a',b') ∈ ℤ × ℕ₀: m ∣ en₂(P) by Bézout from gcd(m,n) = 1 and
     eqq13; bp ≥ 0 from hP2.
   * v_{ρ₁}(a',b') < v_{ρ₁}(a,b): v_{ρ₁}(en₂(P)) ≤ v_{ρ₁}(st₂(P)) by
     face maximality, strict by the two-tie argument (ties on ρ₁ and
     ρ₂ force en₂(P) = st₂(P), contradicting Dir(P) via the
     face-singleton lemma); divide by m.
   * ab' − ba' > 0: ab' − ba' = gcd(a,b)·v_{ρ₃}(a',b') with
     ρ₃ = dir(a,b); v_{ρ₃}(en₂(P)) > 0 by `endpoint_val_pos`
     (st₂(P) has ρ₃-value 0, en₂(P) ≠ st₂(P) by Dir(P)).

   Carried qualifications (not hidden):
   (1) Pairwise bracket form inherited from the extremos file — the
       vanishing hypotheses are strictly stronger than the paper's
       combined-polynomial identities; the D2 combine step is still
       open; do NOT present this as the paper's statement until it lands.
   (2) m, n > 1 strengthening (paper says only m,n ∈ ℕ; the (2) proof
       needs nb,mb > 1) — a genuine minor gap in the proposition as
       literally written.
   (3) hmn : m ≠ n is carried as a binder (it is a hypothesis of the
       proposition) but is NOT used by the (1) proof — only hgcd is
       used (Step C). h1neg : ρ₁.1 < 0 and hQ2 are likewise carried
       but unused here (h1neg was needed for esquina_rho2_neg in
       item (2); hQ2 is the Q-side of the y-polynomial hypothesis).
   (4) Exponent level only; hvert carried via hdirs.
-/

section Esquina1

/- Value parameters. (Lean 4 only brings a `variable` into a theorem's scope when the
   theorem's statement mentions it, directly or transitively through a hypothesis binder's
   type — so hypotheses are taken as EXPLICIT binders in each theorem below, in the
   canonical order
     ha hb hba hm hn [hmn hgcd] h1sum [h1neg] hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
     he1P he1Pval he1Q he1Qval hbr hR0 [hP2 hQ2]
   with `hmn`, `hgcd`, `h1neg`, `hP2`, `hQ2` carried where the target needs them. -/
variable {a b m n : Int}
variable {ρ₁ δP δQ ρ₂ : Int × Int}
variable {termsP termsQ : List Term}
variable {dirsP dirsQ : List (Int × Int)}
variable {e1P e1Q : Term}
variable {termsR : List Term} {eR : Term}

/-- Two-tie uniqueness (general form of `slice_tie_unique`): terms tying on two
    independent directions are equal as exponents. The determinant is crossProd. -/
theorem tie_unique_of_cross {ρ₁ ρ₂ : Int × Int} (hC : crossProd ρ₁ ρ₂ ≠ 0)
    {u w : Int × Int}
    (h1 : dirVal ρ₁.1 ρ₁.2 u.1 u.2 = dirVal ρ₁.1 ρ₁.2 w.1 w.2)
    (h2 : dirVal ρ₂.1 ρ₂.2 u.1 u.2 = dirVal ρ₂.1 ρ₂.2 w.1 w.2) :
    u = w := by
  have e1 : ρ₁.1 * (u.1 - w.1) + ρ₁.2 * (u.2 - w.2) = 0 := by
    simp only [dirVal] at h1
    linear_combination h1
  have e2 : ρ₂.1 * (u.1 - w.1) + ρ₂.2 * (u.2 - w.2) = 0 := by
    simp only [dirVal] at h2
    linear_combination h2
  have hdx : (ρ₁.1 * ρ₂.2 - ρ₁.2 * ρ₂.1) * (u.1 - w.1) = 0 := by
    linear_combination ρ₂.2 * e1 - ρ₁.2 * e2
  have hdy : (ρ₁.1 * ρ₂.2 - ρ₁.2 * ρ₂.1) * (u.2 - w.2) = 0 := by
    linear_combination ρ₁.1 * e2 - ρ₂.1 * e1
  have hC' : ρ₁.1 * ρ₂.2 - ρ₁.2 * ρ₂.1 ≠ 0 := by
    simpa only [crossProd] using hC
  have dx0 : u.1 - w.1 = 0 := by
    rcases mul_eq_zero.mp hdx with h | h
    · exact absurd h hC'
    · exact h
  have dy0 : u.2 - w.2 = 0 := by
    rcases mul_eq_zero.mp hdy with h | h
    · exact absurd h hC'
    · exact h
  exact Prod.ext (sub_eq_zero.mp dx0) (sub_eq_zero.mp dy0)

/-- If the st- and en-exponents of a face agree, the face is a single exponent:
    every face term ties st on (ρ,σ) (face) and on (1,−1) (the two slice
    maxima force the tie, since (1,−1) + (−1,1) = 0), and crossProd ρ (1,−1)
    = −(ρ.1+ρ.2) ≠ 0. -/
theorem face_singleton_of_st_eq_en {ρ : Int × Int} {terms : List Term} {s e : Term}
    (hsum : 0 < ρ.1 + ρ.2)
    (hs : stFace ρ.1 ρ.2 terms = some s) (he : enFace ρ.1 ρ.2 terms = some e)
    (hse : s.1 = e.1) :
    ∀ u ∈ faceTerms ρ.1 ρ.2 terms, u.1 = s.1 := by
  intro u hu
  have hρval : dirVal ρ.1 ρ.2 u.1.1 u.1.2 = dirVal ρ.1 ρ.2 s.1.1 s.1.2 := by
    have hsm : s ∈ faceTerms ρ.1 ρ.2 terms := stFaceAux_mem hs
    obtain ⟨v, hv, -, hve⟩ := faceTerms_mem.mp hu
    obtain ⟨v', hv', -, hvs⟩ := faceTerms_mem.mp hsm
    have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
    subst hvv
    rw [hve, hvs]
  have h1le : dirVal 1 (-1) u.1.1 u.1.2 ≤ dirVal 1 (-1) s.1.1 s.1.2 :=
    (stFace_mem_max hs hu).2
  have h1le' : dirVal (-1) 1 u.1.1 u.1.2 ≤ dirVal (-1) 1 s.1.1 s.1.2 := by
    have h := (enFace_mem_max he hu).2
    rw [← hse] at h
    exact h
  have h1eq : dirVal 1 (-1) u.1.1 u.1.2 = dirVal 1 (-1) s.1.1 s.1.2 := by
    have hsum0 : dirVal 1 (-1) u.1.1 u.1.2 + dirVal (-1) 1 u.1.1 u.1.2 = 0 := by
      simp only [dirVal]; ring
    have hsum0' : dirVal 1 (-1) s.1.1 s.1.2 + dirVal (-1) 1 s.1.1 s.1.2 = 0 := by
      simp only [dirVal]; ring
    omega
  have hC : crossProd ρ (1, -1) ≠ 0 := by
    have e : crossProd ρ (1, -1) = -(ρ.1 + ρ.2) := by simp only [crossProd]; ring
    rw [e]
    omega
  exact tie_unique_of_cross hC hρval h1eq

/-- eqq13 (TeX 5412), integer form: aligned rho2-endpoints satisfy
    n·en₂(P) = m·en₂(Q) componentwise, i.e. λ = m/n. -/
theorem esquina_eqq13
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hm : 1 < m) (hn : 1 < n)
    (h1sum : 0 < ρ₁.1 + ρ₁.2)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    (hPne : termsP ≠ []) (hQne : termsQ ≠ [])
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b))
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0))
    (hR0 : eR.1 = (0, 0))
    {e2P e2Q : Term}
    (he2P : enFace ρ₂.1 ρ₂.2 termsP = some e2P)
    (he2Q : enFace ρ₂.1 ρ₂.2 termsQ = some e2Q)
    (halign : crossProd e2P.1 e2Q.1 = 0) :
    n * e2P.1.1 = m * e2Q.1.1 ∧ n * e2P.1.2 = m * e2Q.1.2 := by
  obtain ⟨⟨s2P, hs2P, hs2Pval⟩, ⟨s2Q, hs2Q, hs2Qval⟩⟩ :=
    esquina_proporcionalidad ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  obtain ⟨-, -, hV⟩ :=
    esquina_desig ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0 hs2P hs2Pval hs2Q hs2Qval
  have hfaceP : dirVal ρ₂.1 ρ₂.2 e2P.1.1 e2P.1.2 = m * dirVal ρ₂.1 ρ₂.2 a b := by
    have hem : e2P ∈ faceTerms ρ₂.1 ρ₂.2 termsP := enFaceAux_mem he2P
    have hsm : s2P ∈ faceTerms ρ₂.1 ρ₂.2 termsP := stFaceAux_mem hs2P
    obtain ⟨v, hv, -, hve⟩ := faceTerms_mem.mp hem
    obtain ⟨v', hv', -, hvs⟩ := faceTerms_mem.mp hsm
    have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
    subst hvv
    rw [hve, ← hvs]
    have h1 : s2P.1.1 = m * a := congrArg Prod.fst hs2Pval
    have h2 : s2P.1.2 = m * b := congrArg Prod.snd hs2Pval
    simp only [dirVal, h1, h2]; ring
  have hfaceQ : dirVal ρ₂.1 ρ₂.2 e2Q.1.1 e2Q.1.2 = n * dirVal ρ₂.1 ρ₂.2 a b := by
    have hem : e2Q ∈ faceTerms ρ₂.1 ρ₂.2 termsQ := enFaceAux_mem he2Q
    have hsm : s2Q ∈ faceTerms ρ₂.1 ρ₂.2 termsQ := stFaceAux_mem hs2Q
    obtain ⟨v, hv, -, hve⟩ := faceTerms_mem.mp hem
    obtain ⟨v', hv', -, hvs⟩ := faceTerms_mem.mp hsm
    have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
    subst hvv
    rw [hve, ← hvs]
    have h1 : s2Q.1.1 = n * a := congrArg Prod.fst hs2Qval
    have h2 : s2Q.1.2 = n * b := congrArg Prod.snd hs2Qval
    simp only [dirVal, h1, h2]; ring
  have hP0 : e2P.1 ≠ (0, 0) := by
    intro hh
    have h0 : dirVal ρ₂.1 ρ₂.2 e2P.1.1 e2P.1.2 = 0 := by
      rw [hh]; simp [dirVal]
    rw [hfaceP] at h0
    have hpos : 0 < m * dirVal ρ₂.1 ρ₂.2 a b := mul_pos (by omega) hV
    linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_smul_of_cross_zero hP0 halign
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : (0 : Int) < m))
  have hVq : (dirVal ρ₂.1 ρ₂.2 a b : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hV
  have hq : q = (n : ℚ) / m := by
    have hlin : (dirVal ρ₂.1 ρ₂.2 e2Q.1.1 e2Q.1.2 : ℚ)
        = q * (dirVal ρ₂.1 ρ₂.2 e2P.1.1 e2P.1.2 : ℚ) := by
      simp only [dirVal]
      push_cast
      rw [hq1, hq2]
      ring
    have hPq : (dirVal ρ₂.1 ρ₂.2 e2P.1.1 e2P.1.2 : ℚ)
        = (m : ℚ) * dirVal ρ₂.1 ρ₂.2 a b := by exact_mod_cast hfaceP
    have hQq : (dirVal ρ₂.1 ρ₂.2 e2Q.1.1 e2Q.1.2 : ℚ)
        = (n : ℚ) * dirVal ρ₂.1 ρ₂.2 a b := by exact_mod_cast hfaceQ
    rw [hQq, hPq] at hlin
    have h2 : ((n : ℚ) - q * m) * dirVal ρ₂.1 ρ₂.2 a b = 0 := by
      linear_combination hlin
    rcases mul_eq_zero.mp h2 with h | h
    · have h3 : (n : ℚ) = q * m := by linarith
      rw [eq_div_iff hmq]
      exact h3.symm
    · exact absurd h hVq
  constructor
  · have key1 : (m : ℚ) * (e2Q.1.1 : ℚ) = (n : ℚ) * (e2P.1.1 : ℚ) := by
      calc (m : ℚ) * (e2Q.1.1 : ℚ)
          = (m : ℚ) * (((n : ℚ) / m) * (e2P.1.1 : ℚ)) := by rw [hq1, hq]
        _ = (((n : ℚ) / m) * m) * (e2P.1.1 : ℚ) := by ring
        _ = (n : ℚ) * (e2P.1.1 : ℚ) := by rw [div_mul_cancel₀ _ hmq]
    have key1' : m * e2Q.1.1 = n * e2P.1.1 := by exact_mod_cast key1
    exact key1'.symm
  · have key2 : (m : ℚ) * (e2Q.1.2 : ℚ) = (n : ℚ) * (e2P.1.2 : ℚ) := by
      calc (m : ℚ) * (e2Q.1.2 : ℚ)
          = (m : ℚ) * (((n : ℚ) / m) * (e2P.1.2 : ℚ)) := by rw [hq2, hq]
        _ = (((n : ℚ) / m) * m) * (e2P.1.2 : ℚ) := by ring
        _ = (n : ℚ) * (e2P.1.2 : ℚ) := by rw [div_mul_cancel₀ _ hmq]
    have key2' : m * e2Q.1.2 = n * e2P.1.2 := by exact_mod_cast key2
    exact key2'.symm

/-- "esta en dir" (TeX 5418): aligned rho2-endpoints force
    (ρ₂,σ₂) ∈ Dir(P) ∩ Dir(Q). -/
theorem esquina_esta_en_dir
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hm : 1 < m) (hn : 1 < n)
    (h1sum : 0 < ρ₁.1 + ρ₁.2)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    (hPne : termsP ≠ []) (hQne : termsQ ≠ [])
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b))
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0))
    (hR0 : eR.1 = (0, 0))
    {e2P e2Q : Term}
    (he2P : enFace ρ₂.1 ρ₂.2 termsP = some e2P)
    (he2Q : enFace ρ₂.1 ρ₂.2 termsQ = some e2Q)
    (halign : crossProd e2P.1 e2Q.1 = 0) :
    isDir ρ₂.1 ρ₂.2 termsP ∧ isDir ρ₂.1 ρ₂.2 termsQ := by
  obtain ⟨⟨s2P, hs2P, hs2Pval⟩, ⟨s2Q, hs2Q, hs2Qval⟩⟩ :=
    esquina_proporcionalidad ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  obtain ⟨heq1, heq2⟩ :=
    esquina_eqq13 ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0 he2P he2Q halign
  have h2sum : 0 < ρ₂.1 + ρ₂.2 :=
    esquina_rho2_sum ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  have hm0 : (m : Int) ≠ 0 := ne_of_gt (by omega)
  have hn0 : (n : Int) ≠ 0 := ne_of_gt (by omega)
  have hiff : e2P.1 = s2P.1 ↔ e2Q.1 = s2Q.1 := by
    constructor
    · intro h
      have h1 : e2P.1.1 = m * a := by
        rw [h]; exact congrArg Prod.fst hs2Pval
      have h2 : e2P.1.2 = m * b := by
        rw [h]; exact congrArg Prod.snd hs2Pval
      have e1 : e2Q.1.1 = n * a := by
        apply mul_left_cancel₀ hm0
        calc m * e2Q.1.1 = n * e2P.1.1 := heq1.symm
          _ = n * (m * a) := by rw [h1]
          _ = m * (n * a) := by ring
      have e2 : e2Q.1.2 = n * b := by
        apply mul_left_cancel₀ hm0
        calc m * e2Q.1.2 = n * e2P.1.2 := heq2.symm
          _ = n * (m * b) := by rw [h2]
          _ = m * (n * b) := by ring
      have e : e2Q.1 = (n * a, n * b) := Prod.ext e1 e2
      rw [e]; exact hs2Qval.symm
    · intro h
      have h1 : e2Q.1.1 = n * a := by
        rw [h]; exact congrArg Prod.fst hs2Qval
      have h2 : e2Q.1.2 = n * b := by
        rw [h]; exact congrArg Prod.snd hs2Qval
      have e1 : e2P.1.1 = m * a := by
        apply mul_left_cancel₀ hn0
        calc n * e2P.1.1 = m * e2Q.1.1 := heq1
          _ = m * (n * a) := by rw [h1]
          _ = n * (m * a) := by ring
      have e2 : e2P.1.2 = m * b := by
        apply mul_left_cancel₀ hn0
        calc n * e2P.1.2 = m * e2Q.1.2 := heq2
          _ = m * (n * b) := by rw [h2]
          _ = n * (m * b) := by ring
      have e : e2P.1 = (m * a, m * b) := Prod.ext e1 e2
      rw [e]; exact hs2Pval.symm
  have hnotP : ¬ isDir ρ₂.1 ρ₂.2 termsP → ¬ isDir ρ₂.1 ρ₂.2 termsQ := by
    intro hP
    have hse : s2P.1 = e2P.1 := by
      by_contra hcon
      exact hP ⟨s2P, e2P, stFaceAux_mem hs2P, enFaceAux_mem he2P, hcon⟩
    have hseQ : e2Q.1 = s2Q.1 := hiff.mp hse.symm
    rintro ⟨a, b, ha, hb, hab⟩
    have ha1 : a.1 = s2Q.1 := face_singleton_of_st_eq_en h2sum hs2Q he2Q hseQ.symm a ha
    have hb1 : b.1 = s2Q.1 := face_singleton_of_st_eq_en h2sum hs2Q he2Q hseQ.symm b hb
    exact hab (ha1.trans hb1.symm)
  have hnotQ : ¬ isDir ρ₂.1 ρ₂.2 termsQ → ¬ isDir ρ₂.1 ρ₂.2 termsP := by
    intro hQ
    have hse : s2Q.1 = e2Q.1 := by
      by_contra hcon
      exact hQ ⟨s2Q, e2Q, stFaceAux_mem hs2Q, enFaceAux_mem he2Q, hcon⟩
    have hseP : e2P.1 = s2P.1 := hiff.mpr hse.symm
    rintro ⟨a, b, ha, hb, hab⟩
    have ha1 : a.1 = s2P.1 := face_singleton_of_st_eq_en h2sum hs2P he2P hseP.symm a ha
    have hb1 : b.1 = s2P.1 := face_singleton_of_st_eq_en h2sum hs2P he2P hseP.symm b hb
    exact hab (ha1.trans hb1.symm)
  have hmin : ρ₂ = δP ∨ ρ₂ = δQ := by
    rw [hρ₂]
    exact succMin_eq
  constructor
  · by_contra hP
    have hQ := hnotP hP
    rcases hmin with h | h
    · rw [h] at hP
      exact hP ((hdirsP δP).mp hsuccP.1)
    · rw [h] at hQ
      exact hQ ((hdirsQ δQ).mp hsuccQ.1)
  · by_contra hQ
    have hP := hnotQ hQ
    rcases hmin with h | h
    · rw [h] at hP
      exact hP ((hdirsP δP).mp hsuccP.1)
    · rw [h] at hQ
      exact hQ ((hdirsQ δQ).mp hsuccQ.1)

/-- Esquina item (1) (TeX 5320-5360 + 5420-5440), at exponent level, l = 1: if the
    rho2-endpoints are similar, then (ρ₂,σ₂) lies in Dir(P) ∩ Dir(Q) and the
    caso-alineado triple holds for (a',b') := (1/m)en₂(P) = (1/n)en₂(Q). -/
theorem esquina_item1
    (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hm : 1 < m) (hn : 1 < n)
    (hmn : m ≠ n) (hgcd : Int.gcd m n = 1)
    (h1sum : 0 < ρ₁.1 + ρ₁.2) (h1neg : ρ₁.1 < 0)
    (hdirsP : ∀ δ, δ ∈ dirsP ↔ isDir δ.1 δ.2 termsP)
    (hdirsQ : ∀ δ, δ ∈ dirsQ ↔ isDir δ.1 δ.2 termsQ)
    (hsuccP : isSuccFrom ρ₁ δP dirsP) (hsuccQ : isSuccFrom ρ₁ δQ dirsQ)
    (hρ₂ : ρ₂ = succMin δP δQ)
    (hPne : termsP ≠ []) (hQne : termsQ ≠ [])
    (he1P : enFace ρ₁.1 ρ₁.2 termsP = some e1P) (he1Pval : e1P.1 = (m * a, m * b))
    (he1Q : enFace ρ₁.1 ρ₁.2 termsQ = some e1Q) (he1Qval : e1Q.1 = (n * a, n * b))
    (hbr : (∀ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0 → t.1 = eR.1)
      ∧ (∃ t ∈ faceTerms (-1) 1
        (bracket (faceTerms ρ₂.1 ρ₂.2 termsP) (faceTerms ρ₂.1 ρ₂.2 termsQ)),
        t.2 ≠ 0))
    (hR0 : eR.1 = (0, 0))
    (hP2 : ∀ t ∈ termsP, 0 ≤ t.1.2) (hQ2 : ∀ t ∈ termsQ, 0 ≤ t.1.2)
    {e2P e2Q : Term}
    (he2P : enFace ρ₂.1 ρ₂.2 termsP = some e2P)
    (he2Q : enFace ρ₂.1 ρ₂.2 termsQ = some e2Q)
    (halign : crossProd e2P.1 e2Q.1 = 0) :
    isDir ρ₂.1 ρ₂.2 termsP ∧ isDir ρ₂.1 ρ₂.2 termsQ ∧
    ∃ ap bp : Int, 0 ≤ bp ∧ e2P.1 = (m * ap, m * bp) ∧ e2Q.1 = (n * ap, n * bp) ∧
      dirVal ρ₁.1 ρ₁.2 ap bp < dirVal ρ₁.1 ρ₁.2 a b ∧ 0 < a * bp - b * ap := by
  obtain ⟨hdirP, hdirQ⟩ :=
    esquina_esta_en_dir ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0 he2P he2Q halign
  obtain ⟨⟨s2P, hs2P, hs2Pval⟩, ⟨s2Q, hs2Q, hs2Qval⟩⟩ :=
    esquina_proporcionalidad ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  obtain ⟨-, -, hV⟩ :=
    esquina_desig ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0 hs2P hs2Pval hs2Q hs2Qval
  obtain ⟨heq1, heq2⟩ :=
    esquina_eqq13 ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0 he2P he2Q halign
  have h2sum : 0 < ρ₂.1 + ρ₂.2 :=
    esquina_rho2_sum ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
      he1P he1Pval he1Q he1Qval hbr hR0
  have hmpos : (0 : Int) < m := by omega
  have hm0 : (m : Int) ≠ 0 := ne_of_gt hmpos
  -- Step C: (ap, bp) := (1/m)en₂(P), integral by Bézout from gcd(m,n) = 1.
  have hdvd1 : m ∣ e2P.1.1 := by
    have hbez1 : (1 : ℤ) = m * Int.gcdA m n + n * Int.gcdB m n := by
      have h := Int.gcd_eq_gcd_ab m n
      rw [hgcd] at h
      exact_mod_cast h
    refine ⟨Int.gcdA m n * e2P.1.1 + Int.gcdB m n * e2Q.1.1, ?_⟩
    calc e2P.1.1 = 1 * e2P.1.1 := (one_mul _).symm
      _ = (m * Int.gcdA m n + n * Int.gcdB m n) * e2P.1.1 := by rw [hbez1]
      _ = m * (Int.gcdA m n * e2P.1.1 + Int.gcdB m n * e2Q.1.1) := by
          linear_combination (Int.gcdB m n) * heq1
  have hdvd2 : m ∣ e2P.1.2 := by
    have hbez1 : (1 : ℤ) = m * Int.gcdA m n + n * Int.gcdB m n := by
      have h := Int.gcd_eq_gcd_ab m n
      rw [hgcd] at h
      exact_mod_cast h
    refine ⟨Int.gcdA m n * e2P.1.2 + Int.gcdB m n * e2Q.1.2, ?_⟩
    calc e2P.1.2 = 1 * e2P.1.2 := (one_mul _).symm
      _ = (m * Int.gcdA m n + n * Int.gcdB m n) * e2P.1.2 := by rw [hbez1]
      _ = m * (Int.gcdA m n * e2P.1.2 + Int.gcdB m n * e2Q.1.2) := by
          linear_combination (Int.gcdB m n) * heq2
  obtain ⟨ap, hap⟩ := hdvd1
  obtain ⟨bp, hbp⟩ := hdvd2
  have hbp0 : 0 ≤ bp := by
    have h2 : 0 ≤ e2P.1.2 := hP2 e2P (faceTerms_subset (enFaceAux_mem he2P))
    rw [hbp] at h2
    by_contra hcon
    push Not at hcon
    have hneg : m * bp < 0 := mul_neg_of_pos_of_neg hmpos hcon
    linarith
  have hPpt : e2P.1 = (m * ap, m * bp) := Prod.ext hap hbp
  have hQ1 : e2Q.1.1 = n * ap := by
    apply mul_left_cancel₀ hm0
    calc m * e2Q.1.1 = n * e2P.1.1 := heq1.symm
      _ = n * (m * ap) := by rw [hap]
      _ = m * (n * ap) := by ring
  have hQ2 : e2Q.1.2 = n * bp := by
    apply mul_left_cancel₀ hm0
    calc m * e2Q.1.2 = n * e2P.1.2 := heq2.symm
      _ = n * (m * bp) := by rw [hbp]
      _ = m * (n * bp) := by ring
  have hQpt : e2Q.1 = (n * ap, n * bp) := Prod.ext hQ1 hQ2
  -- Step D: v_{ρ₁}(a',b') < v_{ρ₁}(a,b).
  have hval1 : dirVal ρ₁.1 ρ₁.2 e1P.1.1 e1P.1.2 = dirVal ρ₁.1 ρ₁.2 s2P.1.1 s2P.1.2 := by
    have h1 : e1P.1.1 = m * a := congrArg Prod.fst he1Pval
    have h2 : e1P.1.2 = m * b := congrArg Prod.snd he1Pval
    have h3 : s2P.1.1 = m * a := congrArg Prod.fst hs2Pval
    have h4 : s2P.1.2 = m * b := congrArg Prod.snd hs2Pval
    simp only [dirVal, h1, h2, h3, h4]
  have hD : dirVal ρ₁.1 ρ₁.2 ap bp < dirVal ρ₁.1 ρ₁.2 a b := by
    have hlinP : dirVal ρ₁.1 ρ₁.2 e2P.1.1 e2P.1.2 = m * dirVal ρ₁.1 ρ₁.2 ap bp := by
      rw [hap, hbp]
      simp only [dirVal]; ring
    have hlinS : dirVal ρ₁.1 ρ₁.2 s2P.1.1 s2P.1.2 = m * dirVal ρ₁.1 ρ₁.2 a b := by
      have h1 : s2P.1.1 = m * a := congrArg Prod.fst hs2Pval
      have h2 : s2P.1.2 = m * b := congrArg Prod.snd hs2Pval
      simp only [dirVal, h1, h2]; ring
    have hlt : dirVal ρ₁.1 ρ₁.2 e2P.1.1 e2P.1.2 < dirVal ρ₁.1 ρ₁.2 s2P.1.1 s2P.1.2 := by
      have hle : dirVal ρ₁.1 ρ₁.2 e2P.1.1 e2P.1.2 ≤ dirVal ρ₁.1 ρ₁.2 s2P.1.1 s2P.1.2 := by
        have hmax : ∀ t ∈ termsP, dirVal ρ₁.1 ρ₁.2 t.1.1 t.1.2
            ≤ dirVal ρ₁.1 ρ₁.2 e1P.1.1 e1P.1.2 :=
          fun t ht => faceTerms_max (enFaceAux_mem he1P) (List.mem_map.mpr ⟨t, ht, rfl⟩)
        have he2 : e2P ∈ termsP := faceTerms_subset (enFaceAux_mem he2P)
        have h := hmax e2P he2
        rwa [hval1] at h
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        have he2f : e2P ∈ faceTerms ρ₁.1 ρ₁.2 termsP := by
          apply faceTerms_mem_of_le_max (faceTerms_subset (enFaceAux_mem he2P))
          intro u hu
          have hm := faceTerms_max (enFaceAux_mem he1P) (List.mem_map.mpr ⟨u, hu, rfl⟩)
          have heq : dirVal ρ₁.1 ρ₁.2 e1P.1.1 e1P.1.2
              = dirVal ρ₁.1 ρ₁.2 e2P.1.1 e2P.1.2 := hval1.trans h.symm
          rw [heq] at hm
          exact hm
        have hs2f : s2P ∈ faceTerms ρ₁.1 ρ₁.2 termsP := by
          apply faceTerms_mem_of_le_max (faceTerms_subset (stFaceAux_mem hs2P))
          intro u hu
          have h := faceTerms_max (enFaceAux_mem he1P) (List.mem_map.mpr ⟨u, hu, rfl⟩)
          rwa [hval1] at h
        have htie1 : dirVal ρ₁.1 ρ₁.2 e2P.1.1 e2P.1.2
            = dirVal ρ₁.1 ρ₁.2 s2P.1.1 s2P.1.2 := h
        have htie2 : dirVal ρ₂.1 ρ₂.2 e2P.1.1 e2P.1.2
            = dirVal ρ₂.1 ρ₂.2 s2P.1.1 s2P.1.2 := by
          have hem : e2P ∈ faceTerms ρ₂.1 ρ₂.2 termsP := enFaceAux_mem he2P
          have hsm : s2P ∈ faceTerms ρ₂.1 ρ₂.2 termsP := stFaceAux_mem hs2P
          obtain ⟨v, hv, -, hve⟩ := faceTerms_mem.mp hem
          obtain ⟨v', hv', -, hvs⟩ := faceTerms_mem.mp hsm
          have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
          subst hvv
          rw [hve, hvs]
        have hC : crossProd ρ₁ ρ₂ ≠ 0 := by
          have h12 : dirLt ρ₁ ρ₂ := by
            rw [hρ₂]
            rcases succMin_eq (δP := δP) (δQ := δQ) with hh | hh
            · rw [hh]; exact hsuccP.2.1
            · rw [hh]; exact hsuccQ.2.1
          exact ne_of_gt h12
        have heq : e2P.1 = s2P.1 := tie_unique_of_cross hC htie1 htie2
        have hnot : ¬ isDir ρ₂.1 ρ₂.2 termsP := by
          intro ⟨a, b, ha, hb, hab⟩
          have ha1 : a.1 = s2P.1 := face_singleton_of_st_eq_en h2sum hs2P he2P heq.symm a ha
          have hb1 : b.1 = s2P.1 := face_singleton_of_st_eq_en h2sum hs2P he2P heq.symm b hb
          exact hab (ha1.trans hb1.symm)
        exact hnot hdirP
    have hlt2 : m * dirVal ρ₁.1 ρ₁.2 ap bp < m * dirVal ρ₁.1 ρ₁.2 a b := by
      rw [← hlinP, ← hlinS]; exact hlt
    exact lt_of_mul_lt_mul_left hlt2 (le_of_lt hmpos)
  -- Step E: ab' − ba' > 0.
  have hE : 0 < a * bp - b * ap := by
    obtain ⟨g, ar, br, ρ₃, hg, har, hbr', hbrpos, hbra, hρ₃, h23, h3m⟩ :=
      esquina_rho3 ha hb hba hV
    have h12 : dirLt ρ₂ (-1, 1) :=
      esquina_rho2_lt ha hb hba hm hn h1sum hdirsP hdirsQ hsuccP hsuccQ hρ₂ hPne hQne
        he1P he1Pval he1Q he1Qval hbr hR0
    have hne : e2P.1 ≠ s2P.1 := by
      intro hh
      have hnot : ¬ isDir ρ₂.1 ρ₂.2 termsP := by
        intro ⟨a, b, ha, hb, hab⟩
        have ha1 : a.1 = s2P.1 := face_singleton_of_st_eq_en h2sum hs2P he2P hh.symm a ha
        have hb1 : b.1 = s2P.1 := face_singleton_of_st_eq_en h2sum hs2P he2P hh.symm b hb
        exact hab (ha1.trans hb1.symm)
      exact hnot hdirP
    have hsval : dirVal ρ₃.1 ρ₃.2 s2P.1.1 s2P.1.2 = 0 := by
      have h1 : s2P.1.1 = m * a := congrArg Prod.fst hs2Pval
      have h2 : s2P.1.2 = m * b := congrArg Prod.snd hs2Pval
      have hp1 : ρ₃.1 = -br := congrArg Prod.fst hρ₃
      have hp2 : ρ₃.2 = ar := congrArg Prod.snd hρ₃
      rw [hp1, hp2]
      simp only [dirVal, h1, h2]
      linear_combination (-m * br) * har + (m * ar) * hbr'
    have hpos : 0 < dirVal ρ₃.1 ρ₃.2 e2P.1.1 e2P.1.2 :=
      endpoint_val_pos h23 h3m h12 (ne_of_gt h2sum) he2P hs2P hne hsval
    have hlin3 : dirVal ρ₃.1 ρ₃.2 e2P.1.1 e2P.1.2 = m * dirVal ρ₃.1 ρ₃.2 ap bp := by
      rw [hap, hbp]
      simp only [dirVal]; ring
    have hpos2 : 0 < dirVal ρ₃.1 ρ₃.2 ap bp := by
      rw [hlin3] at hpos
      exact pos_of_mul_pos_right hpos (le_of_lt hmpos)
    have hfin : a * bp - b * ap = g * dirVal ρ₃.1 ρ₃.2 ap bp := by
      have hp1 : ρ₃.1 = -br := congrArg Prod.fst hρ₃
      have hp2 : ρ₃.2 = ar := congrArg Prod.snd hρ₃
      rw [hp1, hp2]
      simp only [dirVal]
      linear_combination bp * har - ap * hbr'
    rw [hfin]
    exact mul_pos hg hpos2
  exact ⟨hdirP, hdirQ, ap, bp, hbp0, hPpt, hQpt, hD, hE⟩

end Esquina1
