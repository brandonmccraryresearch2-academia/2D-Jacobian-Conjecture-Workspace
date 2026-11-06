import Mathlib

/- EXTREMOS PAIR (TeX 694/721) + COMMUTATOR VALUATION (480) — exponent
   level, 2026-11-05. Self-contained scratch, not a repo module.

   BASE (lines below, unchanged from d1_lebbasico_2026-11-05.lean
   through `slice_tie_unique_en`): dirVal, maxVertDir + lemmas,
   faceTerms + mem/subset/max/nonempty, crossProd, dirLt, isDir,
   isSuccFrom, inter_singleton, face_between_singleton, the Part17
   slice layer (stFaceAux/enFaceAux, stFace/enFace, mem/max),
   slice_tie_unique (+ en mirror), breakpoint_between,
   dir_between_pos_combo. endpoint_slice_max / le_basico_full /
   le_bbasico are NOT included (not needed here).
   NEW IN THIS FILE: the bracket layer (brkTerm/bracket), commutator
   valuation (480) + Remark 453, the aligned→multiple bridge,
   the top-slice lemmas, extremos_alineados, extremos_noalineados_st|en,
   and the reusable en_sum_eq_one_one lemma. See the section header
   below for the working-level hypotheses (pairwise vs combined
   bracket vanishing). -/


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

/- ### CENTRAL — D2-mini layer: K-coefficient term lists + Leibniz (STAGE A) -/

/- Part (a) JOSEPH LEMMA 2.2 — STATUS: NOT LOCATED in the original text.
    Three web-search rounds (2026-11-05): the citation is verified
    (Joseph, "The Weyl algebra — semisimple and nilpotent elements",
    Amer. J. Math. 97 (1975), 597–615, MR 0379615 — from the [GGV1]
    bibliography itself and corroborating citations), but JSTOR is
    paywalled and no open PDF of the paper surfaced; Lemma 2.2's exact
    original wording is therefore UNVERIFIED. DECISION: CARRIED as an
    explicit hypothesis `hJoseph22` in the assembly theorem (see Stage D),
    in the exact form [GGV1] uses it (central proof, TeX 860–867):
    for (ρ,σ)-homogeneous A, B ∈ L^{(l)} with [A,B] ≠ 0 and
    [[A,B],B] = 0, the quotient AB/[A,B] ∈ L^{(l)} (and ∈ L if
    A, B ∈ L). The homogeneity hypothesis is LOAD-BEARING: the naive
    un-homogeneous form is FALSE — e.g. in K[x,y] with B = x and
    A = y(x²+1)+x, {A,B} = −(x²+1) ≠ 0 and {{A,B},B} = 0, but
    AB/{A,B} = −xy − x²/(x²+1) ∉ K[x,y]. So the carried form MUST
    include homogeneity; do not weaken it. -/

/- Part (b) LEMA JOSEPH (TeX 620) — STATUS: NOT PROVED in this leg.
    DECISION: CARRIED as an explicit hypothesis `hLemaJoseph` in the
    assembly theorem (Stage D), in face/valuation form. Remaining gap,
    stated precisely: (i) algebraic independence of P,Q giving
    dim M(t) = (t+1)² (M(t) = span of monomials P^i Q^j with i+j ≤ t);
    (ii) the valuation bounds for M(t) forcing the H_j recursion to
    start (needs the (2b) common-power form — Remark "a remark", TeX
    1197, itself unproved at exponent level); (iii) termination of the
    H_j recursion (Q-degree descent, unproved); (iv) the maximal-j step
    via 480 + Remark 453(3) (the latter unproved). The carried form
    states only the two bracket conclusions + the G_i moreover clause,
    as coeffAt identities on the faces. -/

/- Part (c) CENTRAL ASSEMBLY — STAGED. Stage A (this section): the
    D2-mini layer — K-coefficient term lists, coeffAt, pmul/pbracket,
    and the Leibniz identity (coeffAt form), which is the engine of the
    endnote computation [F,ℓ(P)] = ℓ(P). Stages B–D to follow:
    B = faces/valuations/st/en for K-terms + top-slice lemma;
    C = endnote computation + v(F) = ρ+σ + eq central;
    D = items (2)(3)(4) via the K-port of 721 + (5) + (1) + assembly
    theorem `central_conditional` with hJoseph22 + hLemaJoseph as
    explicit hypotheses. No `axiom` anywhere; carried premises are
    theorem hypotheses, not axioms. -/

/-- A K-coefficient term: exponent paired with a field coefficient. -/
abbrev KTerm (K : Type*) := (Int × Int) × K

/-- Coefficient of the exponent `e` in a K-term list (sum of all matching
    terms). This is the "combined polynomial" view: two lists represent
    the same polynomial iff their coeffAt functions agree everywhere. -/
def coeffAt {K : Type*} [Field K] (e : Int × Int) (ps : List (KTerm K)) : K :=
  (ps.map fun m => if m.1 = e then m.2 else 0).sum

/-- Pointwise exponent addition. -/
def expAdd (e f : Int × Int) : Int × Int := (e.1 + f.1, e.2 + f.2)

/-- Pairwise product of K-term lists. -/
def pmul {K : Type*} [Field K] (ps qs : List (KTerm K)) : List (KTerm K) :=
  ps.flatMap fun m => qs.map fun n => (expAdd m.1 n.1, m.2 * n.2)

/-- Pairwise Poisson bracket of K-term lists (integer `brkExp`/`crossProd`
    from the exponent-level base). -/
def pbracket {K : Type*} [Field K] (ps qs : List (KTerm K)) : List (KTerm K) :=
  ps.flatMap fun m => qs.map fun n => (brkExp m.1 n.1, m.2 * n.2 * (crossProd m.1 n.1 : K))

/-- Scalar multiple of a K-term list. -/
def pscale {K : Type*} [Field K] (c : K) (ps : List (KTerm K)) : List (KTerm K) :=
  ps.map fun m => (m.1, c * m.2)

/-- Combined equality: two K-term lists represent the same polynomial. -/
def pEq {K : Type*} [Field K] (ps qs : List (KTerm K)) : Prop :=
  ∀ e : Int × Int, coeffAt e ps = coeffAt e qs

/- ### List-sum helpers (Mathlib lacks `List.sum_flatMap`) -/

/-- Sum over a flatMap is the sum of the sums. -/
theorem sum_flatMap {α β : Type*} [AddCommMonoid β] (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [show (a :: l).flatMap f = f a ++ l.flatMap f from rfl,
      List.sum_append, List.map_cons, List.sum_cons, ih]

/-- Sum over a mapped list is congruent under a pointwise equality. -/
theorem sum_map_congr {α M : Type*} [AddCommMonoid M] {l : List α} {f g : α → M}
    (h : ∀ x ∈ l, f x = g x) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons,
      h a (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

/-- Double sums over two lists commute. -/
theorem sum_map_swap {α β M : Type*} [AddCommMonoid M] (l : List α) (m : List β)
    (f : α → β → M) :
    (l.map fun x => (m.map fun y => f x y).sum).sum =
      (m.map fun y => (l.map fun x => f x y).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, ← List.sum_map_add]

/- ### coeffAt basics -/

theorem coeffAt_nil {K : Type*} [Field K] (e : Int × Int) :
    coeffAt e ([] : List (KTerm K)) = 0 := rfl

theorem coeffAt_append {K : Type*} [Field K] (e : Int × Int)
    (ps qs : List (KTerm K)) :
    coeffAt e (ps ++ qs) = coeffAt e ps + coeffAt e qs := by
  unfold coeffAt
  rw [List.map_append, List.sum_append]

theorem coeffAt_pscale {K : Type*} [Field K] (e : Int × Int) (c : K)
    (ps : List (KTerm K)) :
    coeffAt e (pscale c ps) = c * coeffAt e ps := by
  induction ps with
  | nil => simp [coeffAt, pscale]
  | cons m ps ih =>
    simp only [pscale, List.map_cons, coeffAt, List.map_cons, List.sum_cons] at *
    by_cases h : m.1 = e
    · simp only [h, ite_true] at *
      rw [ih]; ring
    · simp only [h, ite_false] at *
      rw [ih]; ring

/- ### coeffAt of products and brackets (double-sum forms) -/

/-- Sum over a mapped product list, collapsing the flatMap. -/
theorem map_pmul_sum {K : Type*} [Field K] {M : Type*} [AddCommMonoid M]
    (ps qs : List (KTerm K)) (F : KTerm K → M) :
    ((pmul ps qs).map F).sum =
      (ps.map fun m => (qs.map fun n => F (expAdd m.1 n.1, m.2 * n.2)).sum).sum := by
  unfold pmul
  rw [List.map_flatMap, sum_flatMap]
  apply sum_map_congr
  intro m _
  simp only [List.map_map, Function.comp_def]

/-- Sum over a mapped bracket list, collapsing the flatMap. -/
theorem map_pbracket_sum {K : Type*} [Field K] {M : Type*} [AddCommMonoid M]
    (ps qs : List (KTerm K)) (F : KTerm K → M) :
    ((pbracket ps qs).map F).sum =
      (ps.map fun m => (qs.map fun n =>
        F (brkExp m.1 n.1, m.2 * n.2 * crossProd m.1 n.1)).sum).sum := by
  unfold pbracket
  rw [List.map_flatMap, sum_flatMap]
  apply sum_map_congr
  intro m _
  simp only [List.map_map, Function.comp_def]

theorem coeffAt_pmul {K : Type*} [Field K] (e : Int × Int)
    (ps qs : List (KTerm K)) :
    coeffAt e (pmul ps qs) =
      (ps.map fun m => (qs.map fun n =>
        if expAdd m.1 n.1 = e then m.2 * n.2 else 0).sum).sum := by
  unfold coeffAt
  rw [map_pmul_sum]

theorem coeffAt_pbracket {K : Type*} [Field K] (e : Int × Int)
    (ps qs : List (KTerm K)) :
    coeffAt e (pbracket ps qs) =
      (ps.map fun m => (qs.map fun n =>
        if brkExp m.1 n.1 = e then m.2 * n.2 * (crossProd m.1 n.1 : K) else 0).sum).sum := by
  unfold coeffAt
  rw [map_pbracket_sum]

/- ### Cross-product identities (integer level) -/

/-- The bracket coefficient is additive in its first argument. -/
theorem cross_add_left (a b c : Int × Int) :
    crossProd (expAdd a b) c = crossProd a c + crossProd b c := by
  unfold crossProd expAdd
  ring

/-- The bracket coefficient is antisymmetric. -/
theorem cross_antisymm (a b : Int × Int) :
    crossProd b a = -crossProd a b := by
  unfold crossProd
  ring

/-- The bracket coefficient of a pair with itself vanishes. -/
theorem crossProd_self (a : Int × Int) : crossProd a a = 0 := by
  unfold crossProd
  ring

/-- The three bracket exponents in Leibniz coincide. -/
theorem brkExp_leibniz_left (a b c : Int × Int) :
    brkExp (expAdd a b) c = expAdd (brkExp a c) b := by
  unfold brkExp expAdd
  ext <;> simp <;> omega

theorem brkExp_leibniz_right (a b c : Int × Int) :
    brkExp (expAdd a b) c = expAdd a (brkExp b c) := by
  unfold brkExp expAdd
  ext <;> simp <;> omega

/- ### Triple-sum helpers -/

/-- Triple sums are congruent under a pointwise equality. -/
theorem triple_sum_congr {K : Type*} [Field K] (ps qs rs : List (KTerm K))
    (f g : KTerm K → KTerm K → KTerm K → K)
    (h : ∀ m n p, f m n p = g m n p) :
    (ps.map fun m => (qs.map fun n => (rs.map fun p => f m n p).sum).sum).sum =
      (ps.map fun m => (qs.map fun n => (rs.map fun p => g m n p).sum).sum).sum := by
  apply sum_map_congr
  intro m _
  apply sum_map_congr
  intro n _
  apply sum_map_congr
  intro p _
  exact h m n p

/-- Triple sums distribute over addition of the summand. -/
theorem triple_sum_add {K : Type*} [Field K] (ps qs rs : List (KTerm K))
    (f g : KTerm K → KTerm K → KTerm K → K) :
    (ps.map fun m => (qs.map fun n => (rs.map fun p => f m n p).sum).sum).sum +
      (ps.map fun m => (qs.map fun n => (rs.map fun p => g m n p).sum).sum).sum =
    (ps.map fun m => (qs.map fun n =>
      (rs.map fun p => f m n p + g m n p).sum).sum).sum := by
  rw [← List.sum_map_add]
  apply sum_map_congr
  intro m _
  rw [← List.sum_map_add]
  apply sum_map_congr
  intro n _
  rw [← List.sum_map_add]

/-- In a triple sum, the inner two lists may be swapped. -/
theorem triple_sum_swap23 {K : Type*} [Field K] (ps qs rs : List (KTerm K))
    (f : KTerm K → KTerm K → KTerm K → K) :
    (ps.map fun m => (rs.map fun p => (qs.map fun n => f m n p).sum).sum).sum =
      (ps.map fun m => (qs.map fun n => (rs.map fun p => f m n p).sum).sum).sum := by
  apply sum_map_congr
  intro m _
  exact sum_map_swap rs qs (fun p n => f m n p)

/- ### Leibniz identity (coeffAt form) -/

/-- The bracket of a product, expanded as a triple sum. -/
theorem coeffAt_bracket_mul {K : Type*} [Field K] (e : Int × Int)
    (ps qs rs : List (KTerm K)) :
    coeffAt e (pbracket (pmul ps qs) rs) =
      (ps.map fun m => (qs.map fun n => (rs.map fun p =>
        if brkExp (expAdd m.1 n.1) p.1 = e then
          (m.2 * n.2) * p.2 * (crossProd (expAdd m.1 n.1) p.1 : K)
        else 0).sum).sum).sum := by
  rw [coeffAt_pbracket, map_pmul_sum]

/-- Leibniz, coeffAt form: [AB, C] = [A,C]B + A[B,C] coefficientwise. -/
theorem leibniz_coeff {K : Type*} [Field K] (e : Int × Int)
    (ps qs rs : List (KTerm K)) :
    coeffAt e (pbracket (pmul ps qs) rs) =
      coeffAt e (pmul (pbracket ps rs) qs) +
        coeffAt e (pmul ps (pbracket qs rs)) := by
  have hL : coeffAt e (pbracket (pmul ps qs) rs) =
      (ps.map fun m => (qs.map fun n => (rs.map fun p =>
        if brkExp (expAdd m.1 n.1) p.1 = e then
          (m.2 * n.2) * p.2 * (crossProd (expAdd m.1 n.1) p.1 : K)
        else 0).sum).sum).sum := coeffAt_bracket_mul e ps qs rs
  have hR1 : coeffAt e (pmul (pbracket ps rs) qs) =
      (ps.map fun m => (qs.map fun n => (rs.map fun p =>
        if expAdd (brkExp m.1 p.1) n.1 = e then
          (m.2 * p.2 * (crossProd m.1 p.1 : K)) * n.2
        else 0).sum).sum).sum := by
    rw [coeffAt_pmul, map_pbracket_sum]
    rw [triple_sum_swap23]
  have hR2 : coeffAt e (pmul ps (pbracket qs rs)) =
      (ps.map fun m => (qs.map fun n => (rs.map fun p =>
        if expAdd m.1 (brkExp n.1 p.1) = e then
          m.2 * (n.2 * p.2 * (crossProd n.1 p.1 : K))
        else 0).sum).sum).sum := by
    rw [coeffAt_pmul]
    simp only [map_pbracket_sum]
  rw [hL, hR1, hR2, triple_sum_add]
  apply triple_sum_congr
  intro m n p
  have hexp1 : brkExp (expAdd m.1 n.1) p.1 = expAdd (brkExp m.1 p.1) n.1 :=
    brkExp_leibniz_left m.1 n.1 p.1
  have hexp2 : brkExp (expAdd m.1 n.1) p.1 = expAdd m.1 (brkExp n.1 p.1) :=
    brkExp_leibniz_right m.1 n.1 p.1
  have hcross : crossProd (expAdd m.1 n.1) p.1 =
      crossProd m.1 p.1 + crossProd n.1 p.1 := cross_add_left m.1 n.1 p.1
  by_cases h : brkExp (expAdd m.1 n.1) p.1 = e
  · have h1 : expAdd (brkExp m.1 p.1) n.1 = e := by
      rw [← hexp1]; exact h
    have h2 : expAdd m.1 (brkExp n.1 p.1) = e := by
      rw [← hexp2]; exact h
    simp only [h, h1, h2, ite_true]
    rw [hcross]
    push_cast
    ring
  · have h1 : ¬ expAdd (brkExp m.1 p.1) n.1 = e := by
      rw [← hexp1]; exact h
    have h2 : ¬ expAdd m.1 (brkExp n.1 p.1) = e := by
      rw [← hexp2]; exact h
    simp only [h, h1, h2, ite_false, add_zero]
/- ### CENTRAL — STAGE B: faces, st/en, coeffAt support, top-coefficient lemmas -/

/- The (u,v)-maximal exponent of a K-term list (st = (1,-1), en = (-1,1)). -/
def maxExpK {K : Type*} [Field K] (u v : Int) (ps : List (KTerm K)) : Option (Int × Int) :=
  maxVertDir u v (ps.map (·.1))

/-- The st exponent: the (1,−1)-maximal exponent of a K-term list. -/
abbrev stExpK {K : Type*} [Field K] (ps : List (KTerm K)) : Option (Int × Int) :=
  maxExpK 1 (-1) ps

/-- The en exponent: the (−1,1)-maximal exponent of a K-term list. -/
abbrev enExpK {K : Type*} [Field K] (ps : List (KTerm K)) : Option (Int × Int) :=
  maxExpK (-1) 1 ps

/-- Homogeneity: every nonzero term has (ρ,σ)-valuation exactly `v`. -/
def IsHomog {K : Type*} [Field K] (ρ σ : Int) (v : Int) (ps : List (KTerm K)) : Prop :=
  ∀ m ∈ ps, m.2 ≠ 0 → dirVal ρ σ m.1.1 m.1.2 = v

/- ### Generalized slice-tie uniqueness -/

/-- Slice-maximizer uniqueness, general direction: a tie on (ρ,σ) and
    on (u,v) forces equality, provided the determinant u*σ − v*ρ ≠ 0.
    Specializes to `slice_tie_unique` at (u,v) = (1,-1) (det = ρ+σ)
    and to `slice_tie_unique_en` at (u,v) = (-1,1) (det = -(ρ+σ)). -/
theorem slice_tie_unique_gen {ρ σ u v : Int} (hdet : u * σ - v * ρ ≠ 0)
    {s t : Int × Int}
    (hρ : dirVal ρ σ s.1 s.2 = dirVal ρ σ t.1 t.2)
    (h1 : dirVal u v s.1 s.2 = dirVal u v t.1 t.2) :
    s = t := by
  simp only [dirVal] at hρ h1
  have e1 : u * (s.1 - t.1) + v * (s.2 - t.2) = 0 := by
    linear_combination h1
  have e2 : ρ * (s.1 - t.1) + σ * (s.2 - t.2) = 0 := by
    linear_combination hρ
  have h3 : (u * σ - v * ρ) * (s.1 - t.1) = 0 := by
    linear_combination σ * e1 - v * e2
  have h4 : (u * σ - v * ρ) * (s.2 - t.2) = 0 := by
    linear_combination u * e2 - ρ * e1
  have hd1 : s.1 - t.1 = 0 := by
    rcases (mul_eq_zero.mp h3) with h | h
    · exact absurd h hdet
    · exact h
  have hd2 : s.2 - t.2 = 0 := by
    rcases (mul_eq_zero.mp h4) with h | h
    · exact absurd h hdet
    · exact h
  exact Prod.ext (sub_eq_zero.mp hd1) (sub_eq_zero.mp hd2)

/- ### maxExpK basics -/

/-- The maximizer lies in the list and maximizes (u,v) over it. -/
theorem maxExpK_mem_max {K : Type*} [Field K] {u v : Int} {ps : List (KTerm K)}
    {s : Int × Int} (h : maxExpK u v ps = some s) :
    (∃ m ∈ ps, m.1 = s) ∧ ∀ m ∈ ps, dirVal u v m.1.1 m.1.2 ≤ dirVal u v s.1 s.2 := by
  unfold maxExpK at h
  constructor
  · obtain ⟨m, hm, hmw⟩ := List.mem_map.mp (maxVert_mem h)
    exact ⟨m, hm, hmw⟩
  · intro m hm
    exact maxVert_max h (List.mem_map.mpr ⟨m, hm, rfl⟩)

/-- A (u,v)-maximizer of a homogeneous reduced list IS the maxExpK
    (maximizers are unique by `slice_tie_unique_gen`). -/
theorem maxExpK_eq_of_max {K : Type*} [Field K] {ρ σ u v : Int}
    (hdet : u * σ - v * ρ ≠ 0)
    {ps : List (KTerm K)} {w : Int} (hhom : IsHomog ρ σ w ps)
    (hred : ∀ m ∈ ps, m.2 ≠ 0)
    {e : Int × Int} (he : ∃ m ∈ ps, m.1 = e)
    (hmax : ∀ m ∈ ps, dirVal u v m.1.1 m.1.2 ≤ dirVal u v e.1 e.2) :
    maxExpK u v ps = some e := by
  obtain ⟨m0, hm0, hm0e⟩ := he
  have hne' : ps.map (·.1) ≠ [] := by
    intro hnil
    have hmem : m0.1 ∈ ps.map (·.1) := List.mem_map.mpr ⟨m0, hm0, rfl⟩
    rw [hnil] at hmem
    exact List.not_mem_nil hmem
  obtain ⟨s, hs⟩ : ∃ s, maxVertDir u v (ps.map (·.1)) = some s := by
    cases hmv : maxVertDir u v (ps.map (·.1)) with
    | none => exact absurd (maxVert_none hmv) hne'
    | some s => exact ⟨s, rfl⟩
  obtain ⟨ms, hms, hmse⟩ := List.mem_map.mp (maxVert_mem hs)
  have hle1 : dirVal u v s.1 s.2 ≤ dirVal u v e.1 e.2 := by
    rw [← hmse]; exact hmax ms hms
  have hle2 : dirVal u v e.1 e.2 ≤ dirVal u v s.1 s.2 := by
    rw [← hm0e]; exact maxVert_max hs (List.mem_map.mpr ⟨m0, hm0, rfl⟩)
  have h1 : dirVal u v s.1 s.2 = dirVal u v e.1 e.2 := le_antisymm hle1 hle2
  have hρ : dirVal ρ σ s.1 s.2 = dirVal ρ σ e.1 e.2 := by
    rw [← hmse, ← hm0e]
    exact (hhom ms hms (hred ms hms)).trans (hhom m0 hm0 (hred m0 hm0)).symm
  have hseq : s = e := slice_tie_unique_gen hdet hρ h1
  rw [hseq] at hs
  exact hs

/-- A nonempty list has a maximizer. -/
theorem maxExpK_some_of_ne {K : Type*} [Field K] {u v : Int} {ps : List (KTerm K)}
    (hne : ps ≠ []) : ∃ s, maxExpK u v ps = some s := by
  unfold maxExpK
  cases h : maxVertDir u v (ps.map (·.1)) with
  | none =>
    exfalso
    apply hne
    have hnil := maxVert_none h
    cases ps with
    | nil => rfl
    | cons a ps => simp at hnil
  | some s => exact ⟨s, rfl⟩

/- ### coeffAt support lemmas -/

theorem coeffAt_cons {K : Type*} [Field K] (e : Int × Int) (a : KTerm K)
    (ps : List (KTerm K)) :
    coeffAt e (a :: ps) = (if a.1 = e then a.2 else 0) + coeffAt e ps := by
  simp only [coeffAt, List.map_cons, List.sum_cons]

theorem coeffAt_filter {K : Type*} [Field K] (e : Int × Int) (ps : List (KTerm K)) :
    coeffAt e ps = ((ps.filter fun m => m.1 = e).map (·.2)).sum := by
  induction ps with
  | nil => rfl
  | cons a ps ih =>
    rw [coeffAt_cons]
    by_cases h : a.1 = e
    · simp [h, ih]
    · simp [h, ih]

theorem coeffAt_eq_zero_of_not_mem {K : Type*} [Field K] {ps : List (KTerm K)}
    {e : Int × Int} (h : ∀ x ∈ ps, x.1 ≠ e) : coeffAt e ps = 0 := by
  induction ps with
  | nil => rfl
  | cons a ps ih =>
    rw [coeffAt_cons, if_neg (h a (List.mem_cons.mpr (Or.inl rfl))), zero_add]
    exact ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

theorem sum_map_eq_zero {α M : Type*} [AddCommMonoid M] {l : List α} {f : α → M}
    (h : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, h a (List.mem_cons.mpr (Or.inl rfl)),
      zero_add]
    exact ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

theorem sum_ne_zero_exists {α M : Type*} [AddCommMonoid M] {l : List α} {f : α → M}
    (h : (l.map f).sum ≠ 0) : ∃ x ∈ l, f x ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (sum_map_eq_zero hc)

/-- A nonzero coefficient forces a nonzero term at that exponent. -/
theorem coeffAt_ne_zero_mem {K : Type*} [Field K] {ps : List (KTerm K)} {e : Int × Int}
    (h : coeffAt e ps ≠ 0) : ∃ m ∈ ps, m.1 = e ∧ m.2 ≠ 0 := by
  rw [coeffAt_filter] at h
  obtain ⟨m, hm, hm0⟩ := sum_ne_zero_exists h
  rw [List.mem_filter] at hm
  exact ⟨m, hm.1, of_decide_eq_true hm.2, hm0⟩

/-- With distinct exponents, the coefficient at a present exponent is
    exactly that term's coefficient (no cancellation possible). -/
theorem coeffAt_eq_of_nodup {K : Type*} [Field K] {ps : List (KTerm K)}
    (hnd : (ps.map (·.1)).Nodup) {m : KTerm K} (hm : m ∈ ps) :
    coeffAt m.1 ps = m.2 := by
  induction ps with
  | nil => exact absurd hm (by simp)
  | cons a ps ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hna, hnd'⟩ := hnd
    rcases List.mem_cons.mp hm with rfl | hmps
    · have h0 : coeffAt m.1 ps = 0 :=
        coeffAt_eq_zero_of_not_mem (fun x hx hxe => hna (List.mem_map.mpr ⟨x, hx, hxe⟩))
      rw [coeffAt_cons, if_pos rfl, h0, add_zero]
    · have hne : a.1 ≠ m.1 := by
        intro h
        apply hna
        rw [h]
        exact List.mem_map.mpr ⟨m, hmps, rfl⟩
      rw [coeffAt_cons, if_neg hne, zero_add]
      exact ih hnd' hmps

theorem sum_map_mul_const {α K : Type*} [Field K] {l : List α} {f : α → K} (c : K) :
    (l.map fun x => f x * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, add_mul]

theorem sum_map_const_mul {α K : Type*} [Field K] {l : List α} {f : α → K} (c : K) :
    (l.map fun x => c * f x).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

/- ### dirVal of expAdd / brkExp -/

theorem dirVal_expAdd_gen (u v : Int) (a b : Int × Int) :
    dirVal u v (expAdd a b).1 (expAdd a b).2 =
      dirVal u v a.1 a.2 + dirVal u v b.1 b.2 := by
  unfold dirVal expAdd; ring

theorem dirVal_brkExp {ρ σ : Int} (a b : Int × Int) :
    dirVal ρ σ (brkExp a b).1 (brkExp a b).2 =
      dirVal ρ σ a.1 a.2 + dirVal ρ σ b.1 b.2 - (ρ + σ) := by
  unfold dirVal brkExp; ring

theorem dirVal_brkExp_gen {u v : Int} (huv : u + v = 0) (a b : Int × Int) :
    dirVal u v (brkExp a b).1 (brkExp a b).2 =
      dirVal u v a.1 a.2 + dirVal u v b.1 b.2 := by
  unfold dirVal brkExp
  linear_combination -huv

/- ### Slice sub-lemmas: a top exponent pair is forced -/

/-- If `m.1 + n.1 = sP + sQ` (as exponents) with m, n in homogeneous
    lists whose (u,v)-maximizers are sP, sQ, then m.1 = sP and n.1 = sQ. -/
theorem expAdd_eq_of_max_gen {K : Type*} [Field K] {ρ σ u v : Int}
    (hdet : u * σ - v * ρ ≠ 0)
    {ps qs : List (KTerm K)} {vP vQ : Int}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs)
    (hredP : ∀ m ∈ ps, m.2 ≠ 0) (hredQ : ∀ n ∈ qs, n.2 ≠ 0)
    {sP sQ : Int × Int}
    (hsP : maxExpK u v ps = some sP) (hsQ : maxExpK u v qs = some sQ)
    {m : KTerm K} {n : KTerm K} (hm : m ∈ ps) (hn : n ∈ qs)
    (h : expAdd m.1 n.1 = expAdd sP sQ) : m.1 = sP ∧ n.1 = sQ := by
  have h1 : dirVal u v m.1.1 m.1.2 + dirVal u v n.1.1 n.1.2 =
      dirVal u v sP.1 sP.2 + dirVal u v sQ.1 sQ.2 := by
    have hc := congrArg (fun e => dirVal u v e.1 e.2) h
    rw [dirVal_expAdd_gen, dirVal_expAdd_gen] at hc
    exact hc
  have hmP := (maxExpK_mem_max hsP).2 m hm
  have hmQ := (maxExpK_mem_max hsQ).2 n hn
  have hm1 : dirVal u v m.1.1 m.1.2 = dirVal u v sP.1 sP.2 := by omega
  have hn1 : dirVal u v n.1.1 n.1.2 = dirVal u v sQ.1 sQ.2 := by omega
  obtain ⟨mP, hmP', hmP1⟩ := (maxExpK_mem_max hsP).1
  obtain ⟨nQ, hnQ', hnQ1⟩ := (maxExpK_mem_max hsQ).1
  have hρm : dirVal ρ σ m.1.1 m.1.2 = dirVal ρ σ sP.1 sP.2 := by
    rw [← hmP1]
    exact (hhomP m hm (hredP m hm)).trans (hhomP mP hmP' (hredP mP hmP')).symm
  have hρn : dirVal ρ σ n.1.1 n.1.2 = dirVal ρ σ sQ.1 sQ.2 := by
    rw [← hnQ1]
    exact (hhomQ n hn (hredQ n hn)).trans (hhomQ nQ hnQ' (hredQ nQ hnQ')).symm
  exact ⟨slice_tie_unique_gen hdet hρm hm1, slice_tie_unique_gen hdet hρn hn1⟩

/-- The bracket analogue: `brkExp m.1 n.1 = brkExp sP sQ` forces
    m.1 = sP and n.1 = sQ (needs u+v = 0 so the bracket preserves the
    (u,v)-valuation additively). -/
theorem brkExp_eq_of_max_gen {K : Type*} [Field K] {ρ σ u v : Int}
    (hdet : u * σ - v * ρ ≠ 0) (huv : u + v = 0)
    {ps qs : List (KTerm K)} {vP vQ : Int}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs)
    (hredP : ∀ m ∈ ps, m.2 ≠ 0) (hredQ : ∀ n ∈ qs, n.2 ≠ 0)
    {sP sQ : Int × Int}
    (hsP : maxExpK u v ps = some sP) (hsQ : maxExpK u v qs = some sQ)
    {m : KTerm K} {n : KTerm K} (hm : m ∈ ps) (hn : n ∈ qs)
    (h : brkExp m.1 n.1 = brkExp sP sQ) : m.1 = sP ∧ n.1 = sQ := by
  have h1 : dirVal u v m.1.1 m.1.2 + dirVal u v n.1.1 n.1.2 =
      dirVal u v sP.1 sP.2 + dirVal u v sQ.1 sQ.2 := by
    have hc := congrArg (fun e => dirVal u v e.1 e.2) h
    rw [dirVal_brkExp_gen huv, dirVal_brkExp_gen huv] at hc
    exact hc
  have hmP := (maxExpK_mem_max hsP).2 m hm
  have hmQ := (maxExpK_mem_max hsQ).2 n hn
  have hm1 : dirVal u v m.1.1 m.1.2 = dirVal u v sP.1 sP.2 := by omega
  have hn1 : dirVal u v n.1.1 n.1.2 = dirVal u v sQ.1 sQ.2 := by omega
  obtain ⟨mP, hmP', hmP1⟩ := (maxExpK_mem_max hsP).1
  obtain ⟨nQ, hnQ', hnQ1⟩ := (maxExpK_mem_max hsQ).1
  have hρm : dirVal ρ σ m.1.1 m.1.2 = dirVal ρ σ sP.1 sP.2 := by
    rw [← hmP1]
    exact (hhomP m hm (hredP m hm)).trans (hhomP mP hmP' (hredP mP hmP')).symm
  have hρn : dirVal ρ σ n.1.1 n.1.2 = dirVal ρ σ sQ.1 sQ.2 := by
    rw [← hnQ1]
    exact (hhomQ n hn (hredQ n hn)).trans (hhomQ nQ hnQ' (hredQ nQ hnQ')).symm
  exact ⟨slice_tie_unique_gen hdet hρm hm1, slice_tie_unique_gen hdet hρn hn1⟩

/- ### Top-coefficient lemmas -/

/-- The coefficient of a product at the sum of the maximizers is the
    product of the maximizer coefficients. -/
theorem coeffAt_pmul_top_gen {K : Type*} [Field K] {ρ σ u v : Int}
    (hdet : u * σ - v * ρ ≠ 0)
    {ps qs : List (KTerm K)} {vP vQ : Int}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs)
    (hredP : ∀ m ∈ ps, m.2 ≠ 0) (hredQ : ∀ n ∈ qs, n.2 ≠ 0)
    {sP sQ : Int × Int}
    (hsP : maxExpK u v ps = some sP) (hsQ : maxExpK u v qs = some sQ) :
    coeffAt (expAdd sP sQ) (pmul ps qs) = coeffAt sP ps * coeffAt sQ qs := by
  rw [coeffAt_pmul]
  show (ps.map fun m => (qs.map fun n =>
      if expAdd m.1 n.1 = expAdd sP sQ then m.2 * n.2 else 0).sum).sum =
    (ps.map fun m => if m.1 = sP then m.2 else 0).sum *
      (qs.map fun n => if n.1 = sQ then n.2 else 0).sum
  have hcond : ∀ m ∈ ps, ∀ n ∈ qs,
      (expAdd m.1 n.1 = expAdd sP sQ) ↔ (m.1 = sP ∧ n.1 = sQ) := by
    intro m hm n hn
    constructor
    · intro h
      exact expAdd_eq_of_max_gen hdet hhomP hhomQ hredP hredQ hsP hsQ hm hn h
    · rintro ⟨rfl, rfl⟩
      rfl
  have hinner : ∀ m ∈ ps,
      (qs.map fun n => if expAdd m.1 n.1 = expAdd sP sQ then m.2 * n.2 else 0).sum =
        (if m.1 = sP then m.2 else 0) *
          (qs.map fun n => if n.1 = sQ then n.2 else 0).sum := by
    intro m hm
    by_cases hm1 : m.1 = sP
    · rw [if_pos hm1]
      have h1 : (qs.map fun n => if expAdd m.1 n.1 = expAdd sP sQ then m.2 * n.2 else 0).sum =
          (qs.map fun n => if n.1 = sQ then m.2 * n.2 else 0).sum := by
        apply sum_map_congr
        intro n hn
        by_cases hn1 : n.1 = sQ
        · have hc : expAdd m.1 n.1 = expAdd sP sQ := by rw [hm1, hn1]
          rw [if_pos hc, if_pos hn1]
        · have hc : ¬ expAdd m.1 n.1 = expAdd sP sQ := by
            intro h
            exact hn1 ((hcond m hm n hn).mp h).2
          rw [if_neg hc, if_neg hn1]
      have h2 : (qs.map fun n => if n.1 = sQ then m.2 * n.2 else 0).sum =
          (qs.map fun n => m.2 * (if n.1 = sQ then n.2 else 0)).sum := by
        apply sum_map_congr
        intro n _
        by_cases hn : n.1 = sQ
        · simp only [hn, ite_true]
        · simp only [hn, ite_false, mul_zero]
      rw [h1, h2, sum_map_const_mul]
    · rw [if_neg hm1]
      have h0 : (qs.map fun n => if expAdd m.1 n.1 = expAdd sP sQ then m.2 * n.2 else 0).sum = 0 := by
        apply sum_map_eq_zero
        intro n hn
        rw [if_neg]
        intro h
        exact hm1 ((hcond m hm n hn).mp h).1
      rw [h0, zero_mul]
  rw [sum_map_congr hinner, sum_map_mul_const]

/-- The coefficient of a bracket at the bracket of the maximizers is the
    product of the maximizer coefficients times the cross product. -/
theorem coeffAt_pbracket_top_gen {K : Type*} [Field K] {ρ σ u v : Int}
    (hdet : u * σ - v * ρ ≠ 0) (huv : u + v = 0)
    {ps qs : List (KTerm K)} {vP vQ : Int}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs)
    (hredP : ∀ m ∈ ps, m.2 ≠ 0) (hredQ : ∀ n ∈ qs, n.2 ≠ 0)
    {sP sQ : Int × Int}
    (hsP : maxExpK u v ps = some sP) (hsQ : maxExpK u v qs = some sQ) :
    coeffAt (brkExp sP sQ) (pbracket ps qs) =
      coeffAt sP ps * coeffAt sQ qs * (crossProd sP sQ : K) := by
  rw [coeffAt_pbracket]
  show (ps.map fun m => (qs.map fun n =>
      if brkExp m.1 n.1 = brkExp sP sQ then
        m.2 * n.2 * (crossProd m.1 n.1 : K) else 0).sum).sum =
    (ps.map fun m => if m.1 = sP then m.2 else 0).sum *
      (qs.map fun n => if n.1 = sQ then n.2 else 0).sum * (crossProd sP sQ : K)
  have hcond : ∀ m ∈ ps, ∀ n ∈ qs,
      (brkExp m.1 n.1 = brkExp sP sQ) ↔ (m.1 = sP ∧ n.1 = sQ) := by
    intro m hm n hn
    constructor
    · intro h
      exact brkExp_eq_of_max_gen hdet huv hhomP hhomQ hredP hredQ hsP hsQ hm hn h
    · rintro ⟨rfl, rfl⟩
      rfl
  have hinner : ∀ m ∈ ps,
      (qs.map fun n => if brkExp m.1 n.1 = brkExp sP sQ then
          m.2 * n.2 * (crossProd m.1 n.1 : K) else 0).sum =
        (if m.1 = sP then m.2 else 0) *
          ((crossProd sP sQ : K) *
            (qs.map fun n => if n.1 = sQ then n.2 else 0).sum) := by
    intro m hm
    by_cases hm1 : m.1 = sP
    · rw [if_pos hm1, hm1]
      have hcondB : ∀ n : KTerm K, (brkExp sP n.1 = brkExp sP sQ) ↔ n.1 = sQ := by
        intro n
        simp only [brkExp, Prod.mk.injEq]
        constructor
        · rintro ⟨h1, h2⟩
          exact Prod.ext (by omega) (by omega)
        · intro h
          subst h
          exact ⟨rfl, rfl⟩
      have h1 : (qs.map fun n => if brkExp sP n.1 = brkExp sP sQ then
            m.2 * n.2 * (crossProd sP n.1 : K) else 0).sum =
          (qs.map fun n => if n.1 = sQ then
            m.2 * n.2 * (crossProd sP sQ : K) else 0).sum := by
        apply sum_map_congr
        intro n hn
        by_cases hn1 : n.1 = sQ
        · have hc : brkExp sP n.1 = brkExp sP sQ := (hcondB n).mpr hn1
          rw [if_pos hc, if_pos hn1, hn1]
        · have hc : ¬ brkExp sP n.1 = brkExp sP sQ := by
            intro h
            exact hn1 ((hcondB n).mp h)
          rw [if_neg hc, if_neg hn1]
      have h2 : (qs.map fun n => if n.1 = sQ then
            m.2 * n.2 * (crossProd sP sQ : K) else 0).sum =
          (qs.map fun n => (m.2 * (crossProd sP sQ : K)) *
            (if n.1 = sQ then n.2 else 0)).sum := by
        apply sum_map_congr
        intro n _
        by_cases hn : n.1 = sQ
        · simp only [hn, ite_true]; ring
        · simp only [hn, ite_false, mul_zero]
      rw [h1, h2, sum_map_const_mul, mul_assoc]
    · rw [if_neg hm1]
      have h0 : (qs.map fun n => if brkExp m.1 n.1 = brkExp sP sQ then
          m.2 * n.2 * (crossProd m.1 n.1 : K) else 0).sum = 0 := by
        apply sum_map_eq_zero
        intro n hn
        rw [if_neg]
        intro h
        exact hm1 ((hcond m hm n hn).mp h).1
      rw [h0, zero_mul]
  rw [sum_map_congr hinner, sum_map_mul_const]
  ring

/- ### st / en specializations -/

theorem coeffAt_pmul_top {K : Type*} [Field K] {ρ σ : Int} (hne : ρ + σ ≠ 0)
    {ps qs : List (KTerm K)} {vP vQ : Int}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs)
    (hredP : ∀ m ∈ ps, m.2 ≠ 0) (hredQ : ∀ n ∈ qs, n.2 ≠ 0)
    {sP sQ : Int × Int}
    (hsP : stExpK ps = some sP) (hsQ : stExpK qs = some sQ) :
    coeffAt (expAdd sP sQ) (pmul ps qs) = coeffAt sP ps * coeffAt sQ qs :=
  coeffAt_pmul_top_gen (u := 1) (v := -1)
    (by have h : (1 : Int) * σ - (-1) * ρ = ρ + σ := by ring
        rw [h]; exact hne)
    hhomP hhomQ hredP hredQ hsP hsQ

theorem coeffAt_pbracket_top {K : Type*} [Field K] {ρ σ : Int} (hne : ρ + σ ≠ 0)
    {ps qs : List (KTerm K)} {vP vQ : Int}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs)
    (hredP : ∀ m ∈ ps, m.2 ≠ 0) (hredQ : ∀ n ∈ qs, n.2 ≠ 0)
    {sP sQ : Int × Int}
    (hsP : stExpK ps = some sP) (hsQ : stExpK qs = some sQ) :
    coeffAt (brkExp sP sQ) (pbracket ps qs) =
      coeffAt sP ps * coeffAt sQ qs * (crossProd sP sQ : K) :=
  coeffAt_pbracket_top_gen (u := 1) (v := -1)
    (by have h : (1 : Int) * σ - (-1) * ρ = ρ + σ := by ring
        rw [h]; exact hne)
    (by ring)
    hhomP hhomQ hredP hredQ hsP hsQ

theorem coeffAt_pmul_top_en {K : Type*} [Field K] {ρ σ : Int} (hne : ρ + σ ≠ 0)
    {ps qs : List (KTerm K)} {vP vQ : Int}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs)
    (hredP : ∀ m ∈ ps, m.2 ≠ 0) (hredQ : ∀ n ∈ qs, n.2 ≠ 0)
    {sP sQ : Int × Int}
    (hsP : enExpK ps = some sP) (hsQ : enExpK qs = some sQ) :
    coeffAt (expAdd sP sQ) (pmul ps qs) = coeffAt sP ps * coeffAt sQ qs :=
  coeffAt_pmul_top_gen (u := -1) (v := 1)
    (by have h : (-1 : Int) * σ - (1 : Int) * ρ = -(ρ + σ) := by ring
        rw [h]; exact neg_ne_zero.mpr hne)
    hhomP hhomQ hredP hredQ hsP hsQ

theorem coeffAt_pbracket_top_en {K : Type*} [Field K] {ρ σ : Int} (hne : ρ + σ ≠ 0)
    {ps qs : List (KTerm K)} {vP vQ : Int}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs)
    (hredP : ∀ m ∈ ps, m.2 ≠ 0) (hredQ : ∀ n ∈ qs, n.2 ≠ 0)
    {sP sQ : Int × Int}
    (hsP : enExpK ps = some sP) (hsQ : enExpK qs = some sQ) :
    coeffAt (brkExp sP sQ) (pbracket ps qs) =
      coeffAt sP ps * coeffAt sQ qs * (crossProd sP sQ : K) :=
  coeffAt_pbracket_top_gen (u := -1) (v := 1)
    (by have h : (-1 : Int) * σ - (1 : Int) * ρ = -(ρ + σ) := by ring
        rw [h]; exact neg_ne_zero.mpr hne)
    (by ring)
    hhomP hhomQ hredP hredQ hsP hsQ

/- ### Homogeneity of products and brackets; valuation comparison -/

theorem pmul_homog {K : Type*} [Field K] {ρ σ : Int} {vP vQ : Int}
    {ps qs : List (KTerm K)}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs) :
    IsHomog ρ σ (vP + vQ) (pmul ps qs) := by
  intro t ht ht2
  have hex : ∃ m ∈ ps, ∃ n ∈ qs, t = (expAdd m.1 n.1, m.2 * n.2) := by
    unfold pmul at ht
    rw [List.mem_flatMap] at ht
    obtain ⟨m, hm, ht⟩ := ht
    rw [List.mem_map] at ht
    obtain ⟨n, hn, htn⟩ := ht
    exact ⟨m, hm, n, hn, htn.symm⟩
  obtain ⟨m, hm, n, hn, rfl⟩ := hex
  have hm2 : m.2 ≠ 0 := by
    intro h
    apply ht2
    simp [h]
  have hn2 : n.2 ≠ 0 := by
    intro h
    apply ht2
    simp [h]
  rw [dirVal_expAdd_gen]
  rw [hhomP m hm hm2, hhomQ n hn hn2]

theorem pbracket_homog {K : Type*} [Field K] {ρ σ : Int} {vP vQ : Int}
    {ps qs : List (KTerm K)}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs) :
    IsHomog ρ σ (vP + vQ - (ρ + σ)) (pbracket ps qs) := by
  intro t ht ht2
  have hex : ∃ m ∈ ps, ∃ n ∈ qs,
      t = (brkExp m.1 n.1, m.2 * n.2 * (crossProd m.1 n.1 : K)) := by
    unfold pbracket at ht
    rw [List.mem_flatMap] at ht
    obtain ⟨m, hm, ht⟩ := ht
    rw [List.mem_map] at ht
    obtain ⟨n, hn, htn⟩ := ht
    exact ⟨m, hm, n, hn, htn.symm⟩
  obtain ⟨m, hm, n, hn, rfl⟩ := hex
  have hm2 : m.2 ≠ 0 := by
    intro h
    apply ht2
    simp [h]
  have hn2 : n.2 ≠ 0 := by
    intro h
    apply ht2
    simp [h]
  rw [dirVal_brkExp]
  rw [hhomP m hm hm2, hhomQ n hn hn2]

/-- A nonzero coefficient at `e` forces e's (u,v)-valuation to be at
    most the maximizer's. -/
theorem coeffAt_val_le {K : Type*} [Field K] {u v : Int} {ps : List (KTerm K)}
    {s : Int × Int} (hs : maxExpK u v ps = some s) {e : Int × Int}
    (h : coeffAt e ps ≠ 0) : dirVal u v e.1 e.2 ≤ dirVal u v s.1 s.2 := by
  obtain ⟨m, hm, hme, hm2⟩ := coeffAt_ne_zero_mem h
  rw [← hme]
  exact (maxExpK_mem_max hs).2 m hm

/-- A product of two nonzero homogeneous lists is nonzero (combined),
    witnessed at the sum of the maximizers. -/
theorem pmul_nonzero_of_nonzero {K : Type*} [Field K] {ρ σ : Int} (hne : ρ + σ ≠ 0)
    {ps qs : List (KTerm K)} {vP vQ : Int}
    (hhomP : IsHomog ρ σ vP ps) (hhomQ : IsHomog ρ σ vQ qs)
    (hredP : ∀ m ∈ ps, m.2 ≠ 0) (hredQ : ∀ n ∈ qs, n.2 ≠ 0)
    (hndP : (ps.map (·.1)).Nodup) (hndQ : (qs.map (·.1)).Nodup)
    (hP : ∃ e, coeffAt e ps ≠ 0) (hQ : ∃ e, coeffAt e qs ≠ 0) :
    ∃ e, coeffAt e (pmul ps qs) ≠ 0 := by
  have hneP : ps ≠ [] := by
    rintro rfl
    obtain ⟨e, he⟩ := hP
    rw [coeffAt_nil] at he
    exact he rfl
  have hneQ : qs ≠ [] := by
    rintro rfl
    obtain ⟨e, he⟩ := hQ
    rw [coeffAt_nil] at he
    exact he rfl
  obtain ⟨sP, hsP⟩ := maxExpK_some_of_ne (u := 1) (v := -1) hneP
  obtain ⟨sQ, hsQ⟩ := maxExpK_some_of_ne (u := 1) (v := -1) hneQ
  obtain ⟨mP, hmP, hmP1⟩ := (maxExpK_mem_max hsP).1
  obtain ⟨nQ, hnQ, hnQ1⟩ := (maxExpK_mem_max hsQ).1
  have hcP : coeffAt sP ps ≠ 0 := by
    rw [← hmP1, coeffAt_eq_of_nodup hndP hmP]
    exact hredP mP hmP
  have hcQ : coeffAt sQ qs ≠ 0 := by
    rw [← hnQ1, coeffAt_eq_of_nodup hndQ hnQ]
    exact hredQ nQ hnQ
  refine ⟨expAdd sP sQ, ?_⟩
  rw [coeffAt_pmul_top hne hhomP hhomQ hredP hredQ hsP hsQ]
  exact mul_ne_zero hcP hcQ

/- ### CENTRAL — STAGE C: congr lemmas, the endnote, and the valuation of F -/

/-- Componentwise subtraction form of the product exponent identity. -/
theorem expAdd_eq_iff {a b e : Int × Int} :
    expAdd a b = e ↔ a = (e.1 - b.1, e.2 - b.2) := by
  simp only [expAdd, Prod.ext_iff]
  omega

/-- Componentwise subtraction form of the bracket exponent identity. -/
theorem brkExp_eq_iff {a b e : Int × Int} :
    brkExp a b = e ↔ a = (e.1 - b.1 + 1, e.2 - b.2 + 1) := by
  simp only [brkExp, Prod.ext_iff]
  omega

/-- The bracket exponent is symmetric. -/
theorem brkExp_symm (a b : Int × Int) : brkExp a b = brkExp b a := by
  simp only [brkExp, Prod.mk.injEq]
  constructor <;> omega

/-- coeffAt of a flatMap is the sum of the coeffAts. -/
theorem coeffAt_flatMap {K : Type*} [Field K] {e : Int × Int} {X : List (KTerm K)}
    {f : KTerm K → List (KTerm K)} :
    coeffAt e (X.flatMap f) = (X.map fun m => coeffAt e (f m)).sum := by
  show ((X.flatMap f).map fun t => if t.1 = e then t.2 else 0).sum =
    (X.map fun m => ((f m).map fun t => if t.1 = e then t.2 else 0).sum).sum
  rw [List.map_flatMap, sum_flatMap]

/-- coeffAt of a product, as a double sum. -/
theorem coeffAt_pmul_exp {K : Type*} [Field K] {e : Int × Int} {X Y : List (KTerm K)} :
    coeffAt e (pmul X Y) =
      (X.map fun m => (Y.map fun n => if expAdd m.1 n.1 = e then m.2 * n.2 else 0).sum).sum := by
  unfold pmul
  rw [coeffAt_flatMap]
  apply sum_map_congr
  intro m _
  show ((Y.map fun n => (expAdd m.1 n.1, m.2 * n.2)).map fun t =>
      if t.1 = e then t.2 else 0).sum = _
  rw [List.map_map]
  rfl

/-- coeffAt of a bracket, as a double sum. -/
theorem coeffAt_pbracket_exp {K : Type*} [Field K] {e : Int × Int} {X Y : List (KTerm K)} :
    coeffAt e (pbracket X Y) =
      (X.map fun m => (Y.map fun n =>
        if brkExp m.1 n.1 = e then m.2 * n.2 * (crossProd m.1 n.1 : K) else 0).sum).sum := by
  unfold pbracket
  rw [coeffAt_flatMap]
  apply sum_map_congr
  intro m _
  show ((Y.map fun n => (brkExp m.1 n.1, m.2 * n.2 * (crossProd m.1 n.1 : K))).map fun t =>
      if t.1 = e then t.2 else 0).sum = _
  rw [List.map_map]
  rfl

/-- A product with `[]` on the right is `[]`. -/
theorem pmul_nil_right {K : Type*} [Field K] {X : List (KTerm K)} : pmul X [] = [] := by
  induction X with
  | nil => rfl
  | cons a X ih =>
    unfold pmul at ih ⊢
    rw [List.flatMap_cons, List.map_nil, List.nil_append]
    exact ih

/-- A bracket with `[]` on the right is `[]`. -/
theorem pbracket_nil_right {K : Type*} [Field K] {X : List (KTerm K)} : pbracket X [] = [] := by
  induction X with
  | nil => rfl
  | cons a X ih =>
    unfold pbracket at ih ⊢
    rw [List.flatMap_cons, List.map_nil, List.nil_append]
    exact ih

/-- coeffAt of a product with a singleton on the right, as a single sum. -/
theorem coeffAt_pmul_single_exp {K : Type*} [Field K] {e : Int × Int}
    {X : List (KTerm K)} {b : KTerm K} :
    coeffAt e (pmul X [b]) =
      (X.map fun m => if expAdd m.1 b.1 = e then m.2 * b.2 else 0).sum := by
  rw [coeffAt_pmul_exp]
  apply sum_map_congr
  intro m _
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- coeffAt of a product with a singleton on the right, via coeffAt of the left factor. -/
theorem coeffAt_pmul_single_right {K : Type*} [Field K] {e : Int × Int}
    {X : List (KTerm K)} {b : KTerm K} :
    coeffAt e (pmul X [b]) =
      coeffAt (e.1 - b.1.1, e.2 - b.1.2) X * b.2 := by
  rw [coeffAt_pmul_single_exp]
  have h1 : ∀ m : KTerm K,
      (if expAdd m.1 b.1 = e then m.2 * b.2 else 0) =
        (if m.1 = (e.1 - b.1.1, e.2 - b.1.2) then m.2 else 0) * b.2 := by
    intro m
    by_cases h : m.1 = (e.1 - b.1.1, e.2 - b.1.2)
    · rw [if_pos h]
      have he : expAdd m.1 b.1 = e := expAdd_eq_iff.mpr h
      rw [if_pos he]
    · rw [if_neg h]
      have he : ¬ expAdd m.1 b.1 = e := fun hcon => h (expAdd_eq_iff.mp hcon)
      rw [if_neg he, zero_mul]
  rw [sum_map_congr (fun m _ => h1 m), sum_map_mul_const]
  rfl

/-- coeffAt of a product splits over a cons on the right. -/
theorem coeffAt_pmul_cons_right {K : Type*} [Field K] {e : Int × Int}
    {X : List (KTerm K)} {b : KTerm K} {Y : List (KTerm K)} :
    coeffAt e (pmul X (b :: Y)) =
      coeffAt e (pmul X [b]) + coeffAt e (pmul X Y) := by
  rw [coeffAt_pmul_exp, coeffAt_pmul_single_exp, coeffAt_pmul_exp]
  have hsplit : ∀ m : KTerm K,
      ((b :: Y).map fun n => if expAdd m.1 n.1 = e then m.2 * n.2 else 0).sum =
        (if expAdd m.1 b.1 = e then m.2 * b.2 else 0) +
          (Y.map fun n => if expAdd m.1 n.1 = e then m.2 * n.2 else 0).sum := by
    intro m
    simp only [List.map_cons, List.sum_cons]
  rw [sum_map_congr (fun m _ => hsplit m), List.sum_map_add]

/-- If two lists agree at every coefficient, their products with a fixed
    list agree at every coefficient. (Induction on the right factor.) -/
theorem coeffAt_pmul_congr_left {K : Type*} [Field K] {X X' Y : List (KTerm K)}
    (h : ∀ e, coeffAt e X = coeffAt e X') (e : Int × Int) :
    coeffAt e (pmul X Y) = coeffAt e (pmul X' Y) := by
  induction Y generalizing e with
  | nil =>
    rw [pmul_nil_right, pmul_nil_right]
  | cons b Y ih =>
    conv_lhs => rw [coeffAt_pmul_cons_right, coeffAt_pmul_single_right]
    conv_rhs => rw [coeffAt_pmul_cons_right, coeffAt_pmul_single_right]
    rw [h, ih]

/-- A product with a coefficientwise-zero left factor is coefficientwise zero. -/
theorem coeffAt_pmul_eq_zero_of_left {K : Type*} [Field K] {X Y : List (KTerm K)}
    (h : ∀ e, coeffAt e X = 0) (e : Int × Int) :
    coeffAt e (pmul X Y) = 0 := by
  have hcongr : coeffAt e (pmul X Y) = coeffAt e (pmul [] Y) :=
    coeffAt_pmul_congr_left (X' := []) (fun e' => (h e').trans rfl) e
  exact hcongr.trans rfl

/-- coeffAt of a bracket with a singleton on the right, as a single sum. -/
theorem coeffAt_pbracket_single_exp {K : Type*} [Field K] {e : Int × Int}
    {X : List (KTerm K)} {b : KTerm K} :
    coeffAt e (pbracket X [b]) =
      (X.map fun m => if brkExp m.1 b.1 = e then
        m.2 * b.2 * (crossProd m.1 b.1 : K) else 0).sum := by
  rw [coeffAt_pbracket_exp]
  apply sum_map_congr
  intro m _
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- coeffAt of a bracket with a singleton on the right, via coeffAt of the left factor. -/
theorem coeffAt_pbracket_single_right {K : Type*} [Field K] {e : Int × Int}
    {X : List (KTerm K)} {b : KTerm K} :
    coeffAt e (pbracket X [b]) =
      coeffAt (e.1 - b.1.1 + 1, e.2 - b.1.2 + 1) X *
        (b.2 * ((crossProd (e.1 - b.1.1 + 1, e.2 - b.1.2 + 1) b.1 : Int) : K)) := by
  rw [coeffAt_pbracket_single_exp]
  have h1 : ∀ m : KTerm K,
      (if brkExp m.1 b.1 = e then m.2 * b.2 * (crossProd m.1 b.1 : K) else 0) =
        (if m.1 = (e.1 - b.1.1 + 1, e.2 - b.1.2 + 1) then m.2 else 0) *
          (b.2 * ((crossProd (e.1 - b.1.1 + 1, e.2 - b.1.2 + 1) b.1 : Int) : K)) := by
    intro m
    by_cases h : m.1 = (e.1 - b.1.1 + 1, e.2 - b.1.2 + 1)
    · rw [if_pos h, if_pos (brkExp_eq_iff.mpr h), h, mul_assoc]
    · rw [if_neg h]
      have he : ¬ brkExp m.1 b.1 = e := fun hcon => h (brkExp_eq_iff.mp hcon)
      rw [if_neg he, zero_mul]
  rw [sum_map_congr (fun m _ => h1 m), sum_map_mul_const]
  rfl

/-- coeffAt of a bracket splits over a cons on the right. -/
theorem coeffAt_pbracket_cons_right {K : Type*} [Field K] {e : Int × Int}
    {X : List (KTerm K)} {b : KTerm K} {Y : List (KTerm K)} :
    coeffAt e (pbracket X (b :: Y)) =
      coeffAt e (pbracket X [b]) + coeffAt e (pbracket X Y) := by
  rw [coeffAt_pbracket_exp, coeffAt_pbracket_single_exp, coeffAt_pbracket_exp]
  have hsplit : ∀ m : KTerm K,
      ((b :: Y).map fun n =>
        if brkExp m.1 n.1 = e then m.2 * n.2 * (crossProd m.1 n.1 : K) else 0).sum =
        (if brkExp m.1 b.1 = e then m.2 * b.2 * (crossProd m.1 b.1 : K) else 0) +
          (Y.map fun n =>
            if brkExp m.1 n.1 = e then m.2 * n.2 * (crossProd m.1 n.1 : K) else 0).sum := by
    intro m
    simp only [List.map_cons, List.sum_cons]
  rw [sum_map_congr (fun m _ => hsplit m), List.sum_map_add]

/-- If two lists agree at every coefficient, their brackets with a fixed
    list agree at every coefficient. (Induction on the right factor.) -/
theorem coeffAt_pbracket_congr_left {K : Type*} [Field K] {X X' Y : List (KTerm K)}
    (h : ∀ e, coeffAt e X = coeffAt e X') (e : Int × Int) :
    coeffAt e (pbracket X Y) = coeffAt e (pbracket X' Y) := by
  induction Y generalizing e with
  | nil =>
    rw [pbracket_nil_right, pbracket_nil_right]
  | cons b Y ih =>
    conv_lhs => rw [coeffAt_pbracket_cons_right, coeffAt_pbracket_single_right]
    conv_rhs => rw [coeffAt_pbracket_cons_right, coeffAt_pbracket_single_right]
    rw [h, ih]

/-- A flatMap of constantly-`[]` functions is `[]`. -/
theorem flatMap_const_nil {α β : Type*} {l : List α} :
    (l.flatMap fun _ => ([] : List β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- Swapping the order of a double sum. -/
theorem sum_flatMap_swap {α β : Type*} {K : Type*} [Field K] {X : List α} {Y : List β}
    {f : α → β → K} :
    (X.flatMap fun a => Y.map fun b => f a b).sum =
      (Y.flatMap fun b => X.map fun a => f a b).sum := by
  induction X with
  | nil =>
    simp only [List.flatMap_nil, List.map_nil, List.sum_nil, flatMap_const_nil]
  | cons a X ih =>
    rw [List.flatMap_cons, List.sum_append, ih]
    conv_rhs => rw [sum_flatMap]
    have h2 : ∀ b : β, ((a :: X).map fun a' => f a' b).sum =
        f a b + (X.map fun a' => f a' b).sum := by
      intro b
      simp only [List.map_cons, List.sum_cons]
    rw [sum_map_congr (fun b _ => h2 b), List.sum_map_add, ← sum_flatMap]

/-- Negation distributes over a mapped sum. -/
theorem sum_map_neg_distrib {α : Type*} {β : Type*} [AddCommGroup β] {l : List α} {f : α → β} :
    (l.map fun a => - f a).sum = - (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have e1 : ((a :: l).map fun x => - f x).sum = - f a + (l.map fun x => - f x).sum := by
      simp only [List.map_cons, List.sum_cons]
    have e2 : - (((a :: l).map f).sum) = - (f a + (l.map f).sum) := by
      simp only [List.map_cons, List.sum_cons]
    rw [e1, e2, ih, neg_add]

/-- If `f a = - g a` pointwise, the mapped sums are negatives. -/
theorem sum_map_neg_of_pointwise {α : Type*} {β : Type*} [AddCommGroup β] {l : List α}
    {f g : α → β} (h : ∀ a ∈ l, f a = - g a) :
    (l.map f).sum = - (l.map g).sum := by
  rw [sum_map_congr h, sum_map_neg_distrib]

/-- The double sum of the self-bracket is zero (swap + antisymmetry + char 0). -/
theorem double_sum_antisymm {K : Type*} [Field K] [CharZero K]
    {X : List (KTerm K)} {e : Int × Int} :
    (X.map fun m => (X.map fun n =>
      if brkExp m.1 n.1 = e then m.2 * n.2 * (crossProd m.1 n.1 : K) else 0).sum).sum = 0 := by
  set S : K := (X.map fun m => (X.map fun n =>
      if brkExp m.1 n.1 = e then m.2 * n.2 * (crossProd m.1 n.1 : K) else 0).sum).sum with hSdef
  have hneg : ∀ m n : KTerm K,
      (if brkExp m.1 n.1 = e then m.2 * n.2 * (crossProd m.1 n.1 : K) else 0) =
        - (if brkExp n.1 m.1 = e then n.2 * m.2 * (crossProd n.1 m.1 : K) else 0) := by
    intro m n
    rw [brkExp_symm m.1 n.1, cross_antisymm n.1 m.1]
    by_cases h : brkExp n.1 m.1 = e
    · rw [if_pos h, if_pos h]
      push_cast
      ring
    · rw [if_neg h, if_neg h, neg_zero]
  have hS : S = - S := by
    rw [hSdef]
    conv_lhs => rw [← sum_flatMap, sum_flatMap_swap, sum_flatMap]
    rw [sum_map_congr (fun m _ => sum_map_neg_of_pointwise (fun n _ => hneg n m)), sum_map_neg_distrib]
  have h2 : S + S = 0 := by
    have hstep : S + S = S + - S := congrArg (fun x => S + x) hS
    rw [hstep, add_neg_cancel]
  have h2S : (2 : K) * S = 0 := by
    rw [two_mul]
    exact h2
  have h2ne : (2 : K) ≠ 0 := by exact_mod_cast (show (2 : Int) ≠ 0 by norm_num)
  exact (mul_eq_zero.mp h2S).resolve_left h2ne

/-- The bracket of a list with itself is coefficientwise zero
    (needs characteristic zero: the sum equals its own negation). -/
theorem coeffAt_pbracket_self {K : Type*} [Field K] [CharZero K]
    {X : List (KTerm K)} (e : Int × Int) :
    coeffAt e (pbracket X X) = 0 := by
  rw [coeffAt_pbracket_exp]
  exact double_sum_antisymm

/-- The product exponent is commutative. -/
theorem expAdd_comm (a b : Int × Int) : expAdd a b = expAdd b a := by
  simp only [expAdd, Prod.mk.injEq]
  constructor <;> omega

/-- coeffAt of a product is symmetric in the two factors. -/
theorem coeffAt_pmul_comm {K : Type*} [Field K] {e : Int × Int} {X Y : List (KTerm K)} :
    coeffAt e (pmul X Y) = coeffAt e (pmul Y X) := by
  rw [coeffAt_pmul_exp, coeffAt_pmul_exp, ← sum_flatMap, sum_flatMap_swap, sum_flatMap]
  apply sum_map_congr
  intro n _
  apply sum_map_congr
  intro m _
  by_cases h : expAdd m.1 n.1 = e
  · have h2 : expAdd n.1 m.1 = e := by rw [expAdd_comm]; exact h
    rw [if_pos h, if_pos h2, mul_comm]
  · have h2 : ¬ expAdd n.1 m.1 = e := by rw [expAdd_comm]; exact h
    rw [if_neg h, if_neg h2]

/-- A product with a coefficientwise-zero right factor is coefficientwise zero. -/
theorem coeffAt_pmul_eq_zero_of_right {K : Type*} [Field K] {X Y : List (KTerm K)}
    (h : ∀ e, coeffAt e Y = 0) (e : Int × Int) :
    coeffAt e (pmul X Y) = 0 := by
  rw [coeffAt_pmul_comm]
  exact coeffAt_pmul_eq_zero_of_left h e

/-- The endnote: D·[F,ℓ(P)] = D·ℓ(P) coefficientwise, where D = [G₀,P].
    From Leibniz + the defining equation of F + [D,P] = 0 + [P,P] = 0. -/
theorem endnote_D_mul {K : Type*} [Field K] [CharZero K]
    {faceD faceF faceG0 faceP : List (KTerm K)}
    (hDdef : faceD = pbracket faceG0 faceP)
    (hdef : ∀ e, coeffAt e (pmul faceD faceF) = coeffAt e (pmul faceG0 faceP))
    (hDD : ∀ e, coeffAt e (pbracket faceD faceP) = 0)
    (e : Int × Int) :
    coeffAt e (pmul faceD (pbracket faceF faceP)) = coeffAt e (pmul faceD faceP) := by
  have hL1 := leibniz_coeff e faceD faceF faceP
  have hL2 : coeffAt e (pbracket (pmul faceD faceF) faceP) =
      coeffAt e (pbracket (pmul faceG0 faceP) faceP) :=
    coeffAt_pbracket_congr_left hdef e
  have hL3 := leibniz_coeff e faceG0 faceP faceP
  have hPP : ∀ e', coeffAt e' (pbracket faceP faceP) = 0 :=
    fun e' => coeffAt_pbracket_self e'
  have hzero1 : coeffAt e (pmul (pbracket faceD faceP) faceF) = 0 :=
    coeffAt_pmul_eq_zero_of_left hDD e
  have hzero2 : coeffAt e (pmul faceG0 (pbracket faceP faceP)) = 0 :=
    coeffAt_pmul_eq_zero_of_right hPP e
  have hEG : coeffAt e (pmul (pbracket faceG0 faceP) faceP) = coeffAt e (pmul faceD faceP) := by
    rw [hDdef]
  have hstep : coeffAt e (pmul (pbracket faceG0 faceP) faceP) +
        coeffAt e (pmul faceG0 (pbracket faceP faceP)) =
      coeffAt e (pmul (pbracket faceD faceP) faceF) +
        coeffAt e (pmul faceD (pbracket faceF faceP)) := by
    rw [← hL3, ← hL2, hL1]
  rw [hzero1, hzero2, hEG] at hstep
  rw [add_zero, zero_add] at hstep
  exact hstep.symm

/-- The defining equation of F forces its (ρ,σ)-valuation to be ρ+σ:
    vD + vF = vG0 + vP (both products agree coefficientwise and the
    top coefficient of D·F is nonzero), and vD = vG0 + vP − (ρ+σ). -/
theorem valF_from_def {K : Type*} [Field K] {ρ σ : Int} (hne : ρ + σ ≠ 0)
    {faceD faceF faceG0 faceP : List (KTerm K)}
    {vD vF vG0 vP : Int}
    (hhomD : IsHomog ρ σ vD faceD) (hhomF : IsHomog ρ σ vF faceF)
    (hhomG0 : IsHomog ρ σ vG0 faceG0) (hhomP : IsHomog ρ σ vP faceP)
    (hredD : ∀ m ∈ faceD, m.2 ≠ 0) (hredF : ∀ m ∈ faceF, m.2 ≠ 0)
    (hndD : (faceD.map (·.1)).Nodup) (hndF : (faceF.map (·.1)).Nodup)
    (hneD : faceD ≠ []) (hneF : faceF ≠ [])
    (hdef : ∀ e, coeffAt e (pmul faceD faceF) = coeffAt e (pmul faceG0 faceP))
    (hvD : vD = vG0 + vP - (ρ + σ)) :
    vF = ρ + σ := by
  obtain ⟨sD, hsD⟩ := maxExpK_some_of_ne (u := 1) (v := -1) hneD
  obtain ⟨sF, hsF⟩ := maxExpK_some_of_ne (u := 1) (v := -1) hneF
  obtain ⟨mD, hmD, hmD1⟩ := (maxExpK_mem_max hsD).1
  obtain ⟨mF, hmF, hmF1⟩ := (maxExpK_mem_max hsF).1
  have hcD : coeffAt sD faceD ≠ 0 := by
    rw [← hmD1, coeffAt_eq_of_nodup hndD hmD]
    exact hredD mD hmD
  have hcF : coeffAt sF faceF ≠ 0 := by
    rw [← hmF1, coeffAt_eq_of_nodup hndF hmF]
    exact hredF mF hmF
  have htopDF : coeffAt (expAdd sD sF) (pmul faceD faceF) ≠ 0 := by
    rw [coeffAt_pmul_top hne hhomD hhomF hredD hredF hsD hsF]
    exact mul_ne_zero hcD hcF
  have h1 : vD + vF = vG0 + vP := by
    have hne' : coeffAt (expAdd sD sF) (pmul faceG0 faceP) ≠ 0 := by
      rw [← hdef]
      exact htopDF
    obtain ⟨m, hm, hme, hm2⟩ := coeffAt_ne_zero_mem hne'
    have hval := (pmul_homog hhomG0 hhomP) m hm hm2
    rw [hme, dirVal_expAdd_gen] at hval
    have hDv : dirVal ρ σ sD.1 sD.2 = vD := by
      rw [← hmD1]
      exact hhomD mD hmD (hredD mD hmD)
    have hFv : dirVal ρ σ sF.1 sF.2 = vF := by
      rw [← hmF1]
      exact hhomF mF hmF (hredF mF hmF)
    rw [hDv, hFv] at hval
    exact hval
  omega

/- ### CENTRAL — STAGE D: the assembly -/

/-- Membership in a product list. -/
theorem pmul_mem {K : Type*} [Field K] {X Y : List (KTerm K)} {t : KTerm K} :
    t ∈ pmul X Y ↔ ∃ m ∈ X, ∃ n ∈ Y, t = (expAdd m.1 n.1, m.2 * n.2) := by
  unfold pmul
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨m, hm, ht⟩
    rw [List.mem_map] at ht
    obtain ⟨n, hn, htn⟩ := ht
    exact ⟨m, hm, n, hn, htn.symm⟩
  · rintro ⟨m, hm, n, hn, rfl⟩
    exact ⟨m, hm, List.mem_map.mpr ⟨n, hn, rfl⟩⟩

/-- Membership in a bracket list. -/
theorem pbracket_mem {K : Type*} [Field K] {X Y : List (KTerm K)} {t : KTerm K} :
    t ∈ pbracket X Y ↔
      ∃ m ∈ X, ∃ n ∈ Y, t = (brkExp m.1 n.1, m.2 * n.2 * (crossProd m.1 n.1 : K)) := by
  unfold pbracket
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨m, hm, ht⟩
    rw [List.mem_map] at ht
    obtain ⟨n, hn, htn⟩ := ht
    exact ⟨m, hm, n, hn, htn.symm⟩
  · rintro ⟨m, hm, n, hn, rfl⟩
    exact ⟨m, hm, List.mem_map.mpr ⟨n, hn, rfl⟩⟩

/-- A bracket term's (u,v)-valuation is at most the sum of the
    maximizers' (u,v)-valuations, when u + v = 0. -/
theorem pbracket_dirVal_le {K : Type*} [Field K] {u v : Int} (huv : u + v = 0)
    {faceF faceP : List (KTerm K)}
    {sF sP : Int × Int}
    (hsF : maxExpK u v faceF = some sF) (hsP : maxExpK u v faceP = some sP)
    {n : KTerm K} (hn : n ∈ pbracket faceF faceP) :
    dirVal u v n.1.1 n.1.2 ≤ dirVal u v (brkExp sF sP).1 (brkExp sF sP).2 := by
  obtain ⟨a, ha, b, hb, hn'⟩ := pbracket_mem.mp hn
  have hval : dirVal u v n.1.1 n.1.2 = dirVal u v a.1.1 a.1.2 + dirVal u v b.1.1 b.1.2 := by
    rw [hn']
    exact dirVal_brkExp_gen huv a.1 b.1
  have hval2 : dirVal u v (brkExp sF sP).1 (brkExp sF sP).2 =
      dirVal u v sF.1 sF.2 + dirVal u v sP.1 sP.2 :=
    dirVal_brkExp_gen huv sF sP
  have h1 := (maxExpK_mem_max hsF).2 a ha
  have h2 := (maxExpK_mem_max hsP).2 b hb
  rw [hval, hval2]
  omega

/-- Cancellation for the product exponent on the left. -/
theorem expAdd_left_cancel {a b c : Int × Int} :
    expAdd a b = expAdd a c ↔ b = c := by
  simp only [expAdd, Prod.ext_iff]
  omega

/-- Top coefficient of a product, generalized: the right factor need not
    be homogeneous, reduced, or Nodup — only its (u,v)-valuations must
    be bounded by sY. The left factor is homogeneous, reduced, Nodup,
    with (u,v)-maximizer sX. -/
theorem coeffAt_pmul_top_gen2 {K : Type*} [Field K] {ρ σ u v : Int}
    (hdet : u * σ - v * ρ ≠ 0)
    {X Y : List (KTerm K)} {vX : Int}
    (hhomX : IsHomog ρ σ vX X)
    (hredX : ∀ m ∈ X, m.2 ≠ 0) (hndX : (X.map (·.1)).Nodup)
    {sX sY : Int × Int}
    (hsX : maxExpK u v X = some sX)
    (hYle : ∀ n ∈ Y, dirVal u v n.1.1 n.1.2 ≤ dirVal u v sY.1 sY.2) :
    coeffAt (expAdd sX sY) (pmul X Y) = coeffAt sX X * coeffAt sY Y := by
  obtain ⟨mX, hmX, hmX1⟩ := (maxExpK_mem_max hsX).1
  have hmX2 : mX.2 ≠ 0 := hredX mX hmX
  have hXval : dirVal ρ σ sX.1 sX.2 = vX := by
    rw [← hmX1]
    exact hhomX mX hmX hmX2
  have hforce_m : ∀ m ∈ X, ∀ n ∈ Y, m.2 ≠ 0 →
      expAdd m.1 n.1 = expAdd sX sY → m.1 = sX := by
    intro m hm n hn hm2 heq
    have hle1 := (maxExpK_mem_max hsX).2 m hm
    have hle2 := hYle n hn
    have hdir : dirVal u v m.1.1 m.1.2 + dirVal u v n.1.1 n.1.2 =
        dirVal u v sX.1 sX.2 + dirVal u v sY.1 sY.2 := by
      have h := congrArg (fun e => dirVal u v e.1 e.2) heq
      rw [dirVal_expAdd_gen, dirVal_expAdd_gen] at h
      exact h
    have hm_eq : dirVal u v m.1.1 m.1.2 = dirVal u v sX.1 sX.2 := by omega
    apply slice_tie_unique_gen hdet
    · rw [hhomX m hm hm2, hXval]
    · exact hm_eq
  rw [coeffAt_pmul_exp]
  have hinner : ∀ m ∈ X,
      (Y.map fun n => if expAdd m.1 n.1 = expAdd sX sY then m.2 * n.2 else 0).sum =
        (if m.1 = sX then m.2 else 0) *
          (Y.map fun n => if n.1 = sY then n.2 else 0).sum := by
    intro m hm
    by_cases hm1 : m.1 = sX
    · have hstep : ∀ n ∈ Y,
          (if expAdd m.1 n.1 = expAdd sX sY then m.2 * n.2 else 0) =
            (if n.1 = sY then n.2 else 0) * m.2 := by
        intro n hn
        rw [hm1]
        by_cases hn1 : n.1 = sY
        · rw [if_pos hn1]
          have he : expAdd sX n.1 = expAdd sX sY := by rw [hn1]
          rw [if_pos he]
          ring
        · rw [if_neg hn1]
          have hne : ¬ expAdd sX n.1 = expAdd sX sY := by
            intro hcon
            exact hn1 (expAdd_left_cancel.mp hcon)
          rw [if_neg hne, zero_mul]
      rw [sum_map_congr hstep, sum_map_mul_const, if_pos hm1, mul_comm]
    · have h0 : (Y.map fun n => if expAdd m.1 n.1 = expAdd sX sY then m.2 * n.2 else 0).sum = 0 := by
        apply sum_map_eq_zero
        intro n hn
        by_cases hcon : expAdd m.1 n.1 = expAdd sX sY
        · by_cases hm2 : m.2 = 0
          · rw [if_pos hcon, hm2, zero_mul]
          · exact absurd (hforce_m m hm n hn hm2 hcon) hm1
        · rw [if_neg hcon]
      rw [h0, if_neg hm1, zero_mul]
  rw [sum_map_congr hinner, sum_map_mul_const]
  rfl

/-- The central dichotomy, general direction (u,v) with u + v = 0, u ≠ 0:
    st(P) ∼ st(F) or st(F) = (1,1). Proved by comparing the (u,v)-maximal
    valuations of D·[F,P] and D·P (which agree coefficientwise by the
    endnote): the bracket's top is brkExp sF sP, and the two directions
    force dirVal u v sF = 0, hence sF = (1,1) via v(F) = ρ+σ. -/
theorem central_dichotomy_gen {K : Type*} [Field K] [CharZero K]
    {ρ σ u v : Int} (hne : ρ + σ ≠ 0) (huv : u + v = 0) (hu : u ≠ 0)
    {faceD faceF faceG0 faceP : List (KTerm K)}
    {vD vF vG0 vP : Int}
    (hhomD : IsHomog ρ σ vD faceD) (hhomF : IsHomog ρ σ vF faceF)
    (hhomG0 : IsHomog ρ σ vG0 faceG0) (hhomP : IsHomog ρ σ vP faceP)
    (hredD : ∀ m ∈ faceD, m.2 ≠ 0) (hredF : ∀ m ∈ faceF, m.2 ≠ 0)
    (hredP : ∀ m ∈ faceP, m.2 ≠ 0)
    (hndD : (faceD.map (·.1)).Nodup) (hndF : (faceF.map (·.1)).Nodup)
    (hndP : (faceP.map (·.1)).Nodup)
    (hneD : faceD ≠ []) (hneF : faceF ≠ [])
    (hDdef : faceD = pbracket faceG0 faceP)
    (hdef : ∀ e, coeffAt e (pmul faceD faceF) = coeffAt e (pmul faceG0 faceP))
    (hDD : ∀ e, coeffAt e (pbracket faceD faceP) = 0)
    (hvD : vD = vG0 + vP - (ρ + σ))
    {sD sF sP : Int × Int}
    (hsD : maxExpK u v faceD = some sD) (hsF : maxExpK u v faceF = some sF)
    (hsP : maxExpK u v faceP = some sP) :
    crossProd sP sF = 0 ∨ sF = (1, 1) := by
  have hdet : u * σ - v * ρ ≠ 0 := by
    have hv' : v = -u := by omega
    have h : u * σ - v * ρ = u * (ρ + σ) := by rw [hv']; ring
    rw [h]
    exact mul_ne_zero hu hne
  have hvF : vF = ρ + σ :=
    valF_from_def hne hhomD hhomF hhomG0 hhomP hredD hredF hndD hndF hneD hneF hdef hvD
  obtain ⟨mD, hmD, hmD1⟩ := (maxExpK_mem_max hsD).1
  obtain ⟨mF, hmF, hmF1⟩ := (maxExpK_mem_max hsF).1
  obtain ⟨mP, hmP, hmP1⟩ := (maxExpK_mem_max hsP).1
  have hcD : coeffAt sD faceD ≠ 0 := by
    rw [← hmD1, coeffAt_eq_of_nodup hndD hmD]
    exact hredD mD hmD
  have hcF : coeffAt sF faceF ≠ 0 := by
    rw [← hmF1, coeffAt_eq_of_nodup hndF hmF]
    exact hredF mF hmF
  have hcP : coeffAt sP faceP ≠ 0 := by
    rw [← hmP1, coeffAt_eq_of_nodup hndP hmP]
    exact hredP mP hmP
  by_cases hcross : crossProd sP sF = 0
  · exact Or.inl hcross
  · right
    have hcrossFS : crossProd sF sP ≠ 0 := by
      rw [cross_antisymm]
      exact neg_ne_zero.mpr hcross
    have hend2 := endnote_D_mul hDdef hdef hDD (expAdd sD (brkExp sF sP))
    have hend1 := endnote_D_mul hDdef hdef hDD (expAdd sD sP)
    have hBtop : coeffAt (brkExp sF sP) (pbracket faceF faceP) ≠ 0 := by
      rw [coeffAt_pbracket_top_gen hdet huv hhomF hhomP hredF hredP hsF hsP]
      exact mul_ne_zero (mul_ne_zero hcF hcP) (Int.cast_ne_zero.mpr hcrossFS)
    have hPtop : coeffAt (expAdd sD sP) (pmul faceD faceP) ≠ 0 := by
      rw [coeffAt_pmul_top_gen hdet hhomD hhomP hredD hredP hsD hsP]
      exact mul_ne_zero hcD hcP
    -- Direction A: coeffAt e2 (pmul faceD B) ≠ 0, e2 := expAdd sD (brkExp sF sP)
    have hA : coeffAt (expAdd sD (brkExp sF sP)) (pmul faceD (pbracket faceF faceP)) ≠ 0 := by
      have hgen : coeffAt (expAdd sD (brkExp sF sP)) (pmul faceD (pbracket faceF faceP)) =
          coeffAt sD faceD * coeffAt (brkExp sF sP) (pbracket faceF faceP) :=
        coeffAt_pmul_top_gen2 hdet hhomD hredD hndD hsD
          (fun n hn => pbracket_dirVal_le huv hsF hsP hn :
            ∀ n ∈ pbracket faceF faceP,
              dirVal u v n.1.1 n.1.2 ≤ dirVal u v (brkExp sF sP).1 (brkExp sF sP).2)
      rw [hgen]
      exact mul_ne_zero hcD hBtop
    -- Step A: via the endnote, coeffAt e2 (pmul faceD faceP) ≠ 0
    have hA' : coeffAt (expAdd sD (brkExp sF sP)) (pmul faceD faceP) ≠ 0 := by
      rw [← hend2]
      exact hA
    obtain ⟨t2, ht2, ht2e, ht2c⟩ := coeffAt_ne_zero_mem hA'
    obtain ⟨a2, ha2, b2, hb2, ht2'⟩ := pmul_mem.mp ht2
    have hpair2 : expAdd a2.1 b2.1 = expAdd sD (brkExp sF sP) := by
      rw [ht2'] at ht2e
      exact ht2e
    have hleA : dirVal u v sF.1 sF.2 ≤ 0 := by
      have ha2le := (maxExpK_mem_max hsD).2 a2 ha2
      have hb2le := (maxExpK_mem_max hsP).2 b2 hb2
      have hsum : dirVal u v (expAdd a2.1 b2.1).1 (expAdd a2.1 b2.1).2 =
          dirVal u v a2.1.1 a2.1.2 + dirVal u v b2.1.1 b2.1.2 :=
        dirVal_expAdd_gen u v a2.1 b2.1
      have hsum2 : dirVal u v (expAdd sD (brkExp sF sP)).1 (expAdd sD (brkExp sF sP)).2 =
          dirVal u v sD.1 sD.2 + dirVal u v (brkExp sF sP).1 (brkExp sF sP).2 :=
        dirVal_expAdd_gen u v sD (brkExp sF sP)
      have hbrk : dirVal u v (brkExp sF sP).1 (brkExp sF sP).2 =
          dirVal u v sF.1 sF.2 + dirVal u v sP.1 sP.2 :=
        dirVal_brkExp_gen huv sF sP
      rw [hpair2] at hsum
      omega
    -- Direction B: via the endnote, coeffAt e1 (pmul faceD B) ≠ 0, e1 := expAdd sD sP
    have hB' : coeffAt (expAdd sD sP) (pmul faceD (pbracket faceF faceP)) ≠ 0 := by
      rw [hend1]
      exact hPtop
    obtain ⟨t1, ht1, ht1e, ht1c⟩ := coeffAt_ne_zero_mem hB'
    obtain ⟨a1, ha1, b1, hb1, ht1'⟩ := pmul_mem.mp ht1
    have hpair1 : expAdd a1.1 b1.1 = expAdd sD sP := by
      rw [ht1'] at ht1e
      exact ht1e
    have hgeB : 0 ≤ dirVal u v sF.1 sF.2 := by
      have ha1le := (maxExpK_mem_max hsD).2 a1 ha1
      have hb1le := pbracket_dirVal_le huv hsF hsP hb1
      have hsum : dirVal u v (expAdd a1.1 b1.1).1 (expAdd a1.1 b1.1).2 =
          dirVal u v a1.1.1 a1.1.2 + dirVal u v b1.1.1 b1.1.2 :=
        dirVal_expAdd_gen u v a1.1 b1.1
      have hsum2 : dirVal u v (expAdd sD sP).1 (expAdd sD sP).2 =
          dirVal u v sD.1 sD.2 + dirVal u v sP.1 sP.2 :=
        dirVal_expAdd_gen u v sD sP
      have hbrk : dirVal u v (brkExp sF sP).1 (brkExp sF sP).2 =
          dirVal u v sF.1 sF.2 + dirVal u v sP.1 sP.2 :=
        dirVal_brkExp_gen huv sF sP
      rw [hpair1] at hsum
      omega
    have hzero : dirVal u v sF.1 sF.2 = 0 := le_antisymm hleA hgeB
    have hfst : sF.1 = sF.2 := by
      have hv' : v = -u := by omega
      have h : u * (sF.1 - sF.2) = 0 := by
        have hdv : dirVal u v sF.1 sF.2 = u * (sF.1 - sF.2) := by
          rw [hv']; simp only [dirVal]; ring
        rw [← hdv, hzero]
      exact sub_eq_zero.mp (mul_eq_zero.mp h |>.resolve_left hu)
    have hvalF : dirVal ρ σ sF.1 sF.2 = ρ + σ := by
      have h := hhomF mF hmF (hredF mF hmF)
      rw [hmF1] at h
      rw [← hvF]
      exact h
    have hsF1 : sF.1 = 1 := by
      have h2 : dirVal ρ σ sF.1 sF.2 = (ρ + σ) * sF.1 := by
        rw [hfst]; simp only [dirVal]; ring
      rw [h2] at hvalF
      have h3 : (ρ + σ) * sF.1 = (ρ + σ) * 1 := by rw [hvalF]; ring
      exact mul_left_cancel₀ hne h3
    have hsF2 : sF.2 = 1 := by rw [← hfst]; exact hsF1
    exact Prod.ext hsF1 hsF2

/-- If sF.1 = sF.2 and its (ρ,σ)-valuation is ρ + σ ≠ 0, then sF = (1,1). -/
theorem eq_one_one_of_dirVal {ρ σ : Int} (hne : ρ + σ ≠ 0)
    {sF : Int × Int} (hfst : sF.1 = sF.2) (hvalF : dirVal ρ σ sF.1 sF.2 = ρ + σ) :
    sF = (1, 1) := by
  have hsF1 : sF.1 = 1 := by
    have h2 : dirVal ρ σ sF.1 sF.2 = (ρ + σ) * sF.1 := by
      rw [hfst]; simp only [dirVal]; ring
    rw [h2] at hvalF
    have h3 : (ρ + σ) * sF.1 = (ρ + σ) * 1 := by rw [hvalF]; ring
    exact mul_left_cancel₀ hne h3
  have hsF2 : sF.2 = 1 := by rw [← hfst]; exact hsF1
  exact Prod.ext hsF1 hsF2

/-- Central item (4), general direction (u,v) with u + v = 0, u ≠ 0:
    st(P) ≁ (1,1) (and the en-analogue). By contradiction: assume
    sP.1 = sP.2. The dichotomy gives crossProd sP sF = 0 ∨ sF = (1,1);
    in the first case sP.1 ≠ 0 (else vP = 0) forces sF.1 = sF.2, hence
    sF = (1,1) by the valuation argument. Then coeffAt sP [F,P] = 0
    (the bracket top vanishes since crossProd (1,1) sP = 0), so gen2
    gives coeffAt e1 (D·[F,P]) = 0, contradicting the endnote and the
    nonzero top coefficient of D·P. -/
theorem central_four_gen {K : Type*} [Field K] [CharZero K]
    {ρ σ u v : Int} (hne : ρ + σ ≠ 0) (huv : u + v = 0) (hu : u ≠ 0)
    {faceD faceF faceG0 faceP : List (KTerm K)}
    {vD vF vG0 vP : Int}
    (hhomD : IsHomog ρ σ vD faceD) (hhomF : IsHomog ρ σ vF faceF)
    (hhomG0 : IsHomog ρ σ vG0 faceG0) (hhomP : IsHomog ρ σ vP faceP)
    (hredD : ∀ m ∈ faceD, m.2 ≠ 0) (hredF : ∀ m ∈ faceF, m.2 ≠ 0)
    (hredP : ∀ m ∈ faceP, m.2 ≠ 0)
    (hndD : (faceD.map (·.1)).Nodup) (hndF : (faceF.map (·.1)).Nodup)
    (hndP : (faceP.map (·.1)).Nodup)
    (hneD : faceD ≠ []) (hneF : faceF ≠ [])
    (hDdef : faceD = pbracket faceG0 faceP)
    (hdef : ∀ e, coeffAt e (pmul faceD faceF) = coeffAt e (pmul faceG0 faceP))
    (hDD : ∀ e, coeffAt e (pbracket faceD faceP) = 0)
    (hvD : vD = vG0 + vP - (ρ + σ))
    (hvP : 0 < vP)
    {sD sF sP : Int × Int}
    (hsD : maxExpK u v faceD = some sD) (hsF : maxExpK u v faceF = some sF)
    (hsP : maxExpK u v faceP = some sP) :
    crossProd sP (1, 1) ≠ 0 := by
  intro hcontra
  have hdet : u * σ - v * ρ ≠ 0 := by
    have hv' : v = -u := by omega
    have h : u * σ - v * ρ = u * (ρ + σ) := by rw [hv']; ring
    rw [h]
    exact mul_ne_zero hu hne
  obtain ⟨mD, hmD, hmD1⟩ := (maxExpK_mem_max hsD).1
  obtain ⟨mF, hmF, hmF1⟩ := (maxExpK_mem_max hsF).1
  obtain ⟨mP, hmP, hmP1⟩ := (maxExpK_mem_max hsP).1
  have hcD : coeffAt sD faceD ≠ 0 := by
    rw [← hmD1, coeffAt_eq_of_nodup hndD hmD]
    exact hredD mD hmD
  have hcP : coeffAt sP faceP ≠ 0 := by
    rw [← hmP1, coeffAt_eq_of_nodup hndP hmP]
    exact hredP mP hmP
  have hPtop : coeffAt (expAdd sD sP) (pmul faceD faceP) ≠ 0 := by
    rw [coeffAt_pmul_top_gen hdet hhomD hhomP hredD hredP hsD hsP]
    exact mul_ne_zero hcD hcP
  have hend1 := endnote_D_mul hDdef hdef hDD (expAdd sD sP)
  have hcr11 : crossProd sP (1, 1) = sP.1 - sP.2 := by
    show sP.1 * 1 - sP.2 * 1 = sP.1 - sP.2
    ring
  have hsPeq : sP.1 = sP.2 := by
    rw [hcr11] at hcontra
    omega
  -- In either dichotomy case, sF = (1,1).
  have hsF11 : sF = (1, 1) := by
    rcases central_dichotomy_gen hne huv hu hhomD hhomF hhomG0 hhomP hredD hredF hredP
        hndD hndF hndP hneD hneF hDdef hdef hDD hvD hsD hsF hsP with hcross | h11
    · have hsP1 : sP.1 ≠ 0 := by
        intro h1
        have hsP0 : sP = (0, 0) := by
          apply Prod.ext
          · exact h1
          · rw [← hsPeq]; exact h1
        have hv := hhomP mP hmP (hredP mP hmP)
        rw [hmP1] at hv
        rw [hsP0] at hv
        have hv0 : dirVal ρ σ (0, 0).1 (0, 0).2 = 0 := by
          show ρ * 0 + σ * 0 = 0
          ring
        rw [hv0] at hv
        omega
      have hsFeq : sF.1 = sF.2 := by
        have h2 : crossProd sP sF = sP.1 * (sF.2 - sF.1) := by
          show sP.1 * sF.2 - sP.2 * sF.1 = sP.1 * (sF.2 - sF.1)
          rw [hsPeq]; ring
        rw [h2] at hcross
        have h0 : sF.2 - sF.1 = 0 := (mul_eq_zero.mp hcross).resolve_left hsP1
        omega
      have hvF : vF = ρ + σ :=
        valF_from_def hne hhomD hhomF hhomG0 hhomP hredD hredF hndD hndF hneD hneF hdef hvD
      have hvalF : dirVal ρ σ sF.1 sF.2 = ρ + σ := by
        have h := hhomF mF hmF (hredF mF hmF)
        rw [hmF1] at h
        rw [← hvF]
        exact h
      exact eq_one_one_of_dirVal hne hsFeq hvalF
    · exact h11
  -- With sF = (1,1), the bracket's top coefficient at sP vanishes.
  have hBsp : coeffAt sP (pbracket faceF faceP) = 0 := by
    have htop := coeffAt_pbracket_top_gen hdet huv hhomF hhomP hredF hredP hsF hsP
    rw [hsF11] at htop
    have hbrk : brkExp (1, 1) sP = sP := by
      show (1 + sP.1 - 1, 1 + sP.2 - 1) = sP
      exact Prod.ext (by omega) (by omega)
    have hcr : crossProd (1, 1) sP = 0 := by
      show 1 * sP.2 - 1 * sP.1 = 0
      omega
    rw [hbrk, hcr, Int.cast_zero, mul_zero] at htop
    exact htop
  have hYle : ∀ n ∈ pbracket faceF faceP, dirVal u v n.1.1 n.1.2 ≤ dirVal u v sP.1 sP.2 := by
    intro n hn
    have h1 := pbracket_dirVal_le huv hsF hsP hn
    rw [hsF11] at h1
    have h2 : dirVal u v (brkExp (1, 1) sP).1 (brkExp (1, 1) sP).2 = dirVal u v sP.1 sP.2 := by
      rw [dirVal_brkExp_gen huv (1, 1) sP]
      have h11 : dirVal u v (1, 1).1 (1, 1).2 = 0 := by
        show u * 1 + v * 1 = 0
        omega
      rw [h11, zero_add]
    rw [h2] at h1
    exact h1
  have hgen : coeffAt (expAdd sD sP) (pmul faceD (pbracket faceF faceP)) =
      coeffAt sD faceD * coeffAt sP (pbracket faceF faceP) :=
    coeffAt_pmul_top_gen2 hdet hhomD hredD hndD hsD hYle
  rw [hBsp, mul_zero] at hgen
  rw [hend1] at hgen
  exact hPtop hgen

/-- The face chain G_i := [G_{i-1}, P] at the face level: g 0 = faceG0,
    g (n+1) = pbracket (g n) faceP. -/
def gChain {K : Type*} [Field K] (faceG0 faceP : List (KTerm K)) : ℕ → List (KTerm K)
  | 0 => faceG0
  | n + 1 => pbracket (gChain faceG0 faceP n) faceP

/-- Central assembly, conditional on the two carried premises.
    CARRIED (explicit hypotheses, not axioms):
    * Joseph Lemma 2.2, in the exact form [GGV1] uses it (TeX 860–867):
      the defining equation hdef (D·F = G₀·P coefficientwise, where
      D = [ℓ(G₀),ℓ(P)]) with hvD (vD = vG0 + vP − (ρ+σ)), plus the
      (1)-clause hJL (nonneg second coordinates are preserved).
    * Lema Joseph (TeX 620), in face form: hneD ([ℓ(G₀),ℓ(P)] ≠ 0),
      hDD ([[ℓ(G₀),ℓ(P)],ℓ(P)] = 0), hGchain (the moreover clause
      [ℓ(G_i),ℓ(P)] = 0 for i ≥ 1, in the face-chain form).
    The G₀ ≠ 0 part of Lema Joseph is not needed for any conclusion
    below and is not a hypothesis here.
    NEW PROOFS in this theorem: vF = ρ+σ (via valF_from_def), items
    (2) and (3) (via central_dichotomy_gen at (1,−1) and (−1,1)),
    item (4) st and en (via central_four_gen). Items (5) and (1) are
    exactly the carried hGchain and hJL. The standalone identity
    [F,ℓ(P)] = ℓ(P) is NOT proved here (it would need a general
    cancellation lemma for D); vF is derived from hdef instead. -/
theorem central_conditional {K : Type*} [Field K] [CharZero K]
    {ρ σ : Int} (hne : ρ + σ ≠ 0)
    {faceD faceF faceG0 faceP : List (KTerm K)}
    {vD vF vG0 vP : Int}
    (hhomD : IsHomog ρ σ vD faceD) (hhomF : IsHomog ρ σ vF faceF)
    (hhomG0 : IsHomog ρ σ vG0 faceG0) (hhomP : IsHomog ρ σ vP faceP)
    (hredD : ∀ m ∈ faceD, m.2 ≠ 0) (hredF : ∀ m ∈ faceF, m.2 ≠ 0)
    (hredP : ∀ m ∈ faceP, m.2 ≠ 0)
    (hndD : (faceD.map (·.1)).Nodup) (hndF : (faceF.map (·.1)).Nodup)
    (hndP : (faceP.map (·.1)).Nodup)
    (hneD : faceD ≠ []) (hneF : faceF ≠ [])
    (hDdef : faceD = pbracket faceG0 faceP)
    (hdef : ∀ e, coeffAt e (pmul faceD faceF) = coeffAt e (pmul faceG0 faceP))
    (hDD : ∀ e, coeffAt e (pbracket faceD faceP) = 0)
    (hvD : vD = vG0 + vP - (ρ + σ))
    (hvP : 0 < vP)
    (hGchain : ∀ i, ∀ e, coeffAt e (pbracket (gChain faceG0 faceP (i + 1)) faceP) = 0)
    (hJL : (∀ m ∈ faceG0, 0 ≤ m.1.2) → (∀ m ∈ faceP, 0 ≤ m.1.2) →
      ∀ m ∈ faceF, 0 ≤ m.1.2)
    {sDst sFst sPst sDen sFen sPen : Int × Int}
    (hsDst : stExpK faceD = some sDst) (hsFst : stExpK faceF = some sFst)
    (hsPst : stExpK faceP = some sPst)
    (hsDen : enExpK faceD = some sDen) (hsFen : enExpK faceF = some sFen)
    (hsPen : enExpK faceP = some sPen) :
    vF = ρ + σ ∧
      (crossProd sPst sFst = 0 ∨ sFst = (1, 1)) ∧
      (crossProd sPen sFen = 0 ∨ sFen = (1, 1)) ∧
      crossProd sPst (1, 1) ≠ 0 ∧ crossProd sPen (1, 1) ≠ 0 ∧
      (∀ i, ∀ e, coeffAt e (pbracket (gChain faceG0 faceP (i + 1)) faceP) = 0) ∧
      ((∀ m ∈ faceG0, 0 ≤ m.1.2) → (∀ m ∈ faceP, 0 ≤ m.1.2) →
        ∀ m ∈ faceF, 0 ≤ m.1.2) := by
  have hvF : vF = ρ + σ :=
    valF_from_def hne hhomD hhomF hhomG0 hhomP hredD hredF hndD hndF hneD hneF hdef hvD
  have h2 := central_dichotomy_gen (u := 1) (v := -1) hne (by norm_num) (by norm_num)
    hhomD hhomF hhomG0 hhomP hredD hredF hredP hndD hndF hndP hneD hneF hDdef hdef hDD hvD
    hsDst hsFst hsPst
  have h3 := central_dichotomy_gen (u := -1) (v := 1) hne (by norm_num) (by norm_num)
    hhomD hhomF hhomG0 hhomP hredD hredF hredP hndD hndF hndP hneD hneF hDdef hdef hDD hvD
    hsDen hsFen hsPen
  have h4st := central_four_gen (u := 1) (v := -1) hne (by norm_num) (by norm_num)
    hhomD hhomF hhomG0 hhomP hredD hredF hredP hndD hndF hndP hneD hneF hDdef hdef hDD hvD hvP
    hsDst hsFst hsPst
  have h4en := central_four_gen (u := -1) (v := 1) hne (by norm_num) (by norm_num)
    hhomD hhomF hhomG0 hhomP hredD hredF hredP hndD hndF hndP hneD hneF hDdef hdef hDD hvD hvP
    hsDen hsFen hsPen
  exact ⟨hvF, h2, h3, h4st, h4en, hGchain, hJL⟩

/- ### Axioms audit for the central layer -/
#print axioms central_conditional
#print axioms central_dichotomy_gen
#print axioms central_four_gen
#print axioms valF_from_def
#print axioms endnote_D_mul
#print axioms coeffAt_pmul_top_gen2
#print axioms eq_one_one_of_dirVal
