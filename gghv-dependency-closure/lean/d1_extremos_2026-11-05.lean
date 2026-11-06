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
