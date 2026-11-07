import Mathlib

/-! # R10 — Combined-form esquina(1)/(2) restatements (Phase 4, Leg E)

**CLAIM:** The paper's combined form of esquina(1)/(2) is kernel-equivalent to
the pairwise (D2) form used in `d1_esquina1` / `d1_esquina2`.
**STATUS:** KERNEL (this file). The D2 combine leg
(`d1_d2combine_2026-11-05.lean`, `combined_to_slice_en`,
`en_sum_eq_one_one_combined`) already proved the combined-coefficient
identity implies the slice hypothesis that esquina(1)/(2) take as `hbr`;
what was missing was the *restatement* itself — the set/disjunction form
of the conclusions. That is what this file proves, in the exponent model
(`Int × Int` endpoints), independent of any bracket mathematics:
  (a) `{enP, enQ} = {(-k,0), (k+1,1)}` (set form) ↔ the pairwise
      disjunction (esquina(2) conclusion);
  (b) the `k = 1` specialization `{(-1,0), (2,1)}`;
  (c) esquina(1)'s conclusion as a single bundled structure ↔ the
      conjunction of Dir membership + the three caso-alineado inequalities.
**NOT proved here:** the bracket input `hbr` itself (that is D2's
`combined_to_slice_en`, already kernel); the replay of esquina(1)/(2) with
the combined hypothesis substituted (a mechanical replay of the existing
proofs feeding them `combined_to_slice_en`'s output — blocked only on the
base merge noted in the d2combine header, not on any bracket mathematics).
**Sources:** [GGV1] TeX 5320–5345 (esquina statement); inventory.md
"propiedades de los pares" entry (the reusable (1,1)-sum lemma).
No `sorry` anywhere; no `axiom` anywhere.
-/

/-- The set form of esquina(2)'s conclusion is the pairwise disjunction. -/
theorem esquina2_set_iff {enP enQ : Int × Int} {k : ℕ} :
    ({enP, enQ} : Set (Int × Int)) = {(-(k : ℤ), 0), ((k : ℤ) + 1, 1)} ↔
      (enP = (-(k : ℤ), 0) ∧ enQ = ((k : ℤ) + 1, 1)) ∨
      (enP = ((k : ℤ) + 1, 1) ∧ enQ = (-(k : ℤ), 0)) := by
  constructor
  · intro h
    -- `a ∈ {a, b}` gives `a ∈ {c, d}`; same for `b`; then case split.
    have ha : enP = (-(k : ℤ), 0) ∨ enP = ((k : ℤ) + 1, 1) := by
      have : enP ∈ ({enP, enQ} : Set (Int × Int)) := Set.mem_insert enP _
      rw [h] at this
      simpa using this
    have hb : enQ = (-(k : ℤ), 0) ∨ enQ = ((k : ℤ) + 1, 1) := by
      have : enQ ∈ ({enP, enQ} : Set (Int × Int)) :=
        Set.mem_insert_of_mem enP (Set.mem_singleton enQ)
      rw [h] at this
      simpa using this
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · -- enP = (-k,0), enQ = (-k,0): then the set is a singleton, but
      -- {(-k,0),(k+1,1)} has two distinct elements — contradiction.
      exfalso
      have hne : ((-(k : ℤ), 0) : Int × Int) ≠ ((k : ℤ) + 1, 1) := by
        intro hc
        have : (0 : Int) = 1 := congrArg Prod.snd hc
        norm_num at this
      have h2 : ({enP, enQ} : Set (Int × Int)) = {(-(k : ℤ), 0)} := by
        rw [ha, hb]
        exact Set.insert_eq_of_mem (Set.mem_singleton _)
      rw [h2] at h
      have : (((k : ℤ) + 1, 1) : Int × Int) ∈ ({(-(k : ℤ), 0)} : Set (Int × Int)) := by
        rw [h]; simp
      simp at this
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
    · -- enP = (k+1,1), enQ = (k+1,1): same singleton contradiction.
      exfalso
      have hne : (((k : ℤ) + 1, 1) : Int × Int) ≠ (-(k : ℤ), 0) := by
        intro hc
        have : (1 : Int) = 0 := congrArg Prod.snd hc
        norm_num at this
      have h2 : ({enP, enQ} : Set (Int × Int)) = {((k : ℤ) + 1, 1)} := by
        rw [ha, hb]
        exact Set.insert_eq_of_mem (Set.mem_singleton _)
      rw [h2] at h
      have : ((-(k : ℤ), 0) : Int × Int) ∈ ({((k : ℤ) + 1, 1)} : Set (Int × Int)) := by
        rw [h]; simp
      simp at this
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

/-- Esquina(2), combined form, forward direction (pairwise → set). -/
theorem esquina2_combined {enP enQ : Int × Int} {k : ℕ}
    (h : (enP = (-(k : ℤ), 0) ∧ enQ = ((k : ℤ) + 1, 1)) ∨
      (enP = ((k : ℤ) + 1, 1) ∧ enQ = (-(k : ℤ), 0))) :
    ({enP, enQ} : Set (Int × Int)) = {(-(k : ℤ), 0), ((k : ℤ) + 1, 1)} :=
  esquina2_set_iff.mpr h

/-- Esquina(2), combined form, backward direction (set → pairwise). -/
theorem esquina2_combined_mp {enP enQ : Int × Int} {k : ℕ}
    (h : ({enP, enQ} : Set (Int × Int)) = {(-(k : ℤ), 0), ((k : ℤ) + 1, 1)}) :
    (enP = (-(k : ℤ), 0) ∧ enQ = ((k : ℤ) + 1, 1)) ∨
      (enP = ((k : ℤ) + 1, 1) ∧ enQ = (-(k : ℤ), 0)) :=
  esquina2_set_iff.mp h

/-- The `k = 1` specialization (TeX 5344–5345; `d1_esquina2`
`esquina_item2_k1`): the pair is `{(-1,0), (2,1)}`. This is
`esquina2_combined` at `k = 1`, with `(-(1:ℤ), 0) = (-1, 0)` and
`((1:ℤ)+1, 1) = (2, 1)`. -/
theorem esquina2_k1_pair {enP enQ : Int × Int}
    (h : (enP = (-1, 0) ∧ enQ = (2, 1)) ∨
      (enP = (2, 1) ∧ enQ = (-1, 0))) :
    ({enP, enQ} : Set (Int × Int)) = {(-1, 0), (2, 1)} := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- Esquina(1)'s conclusion as one bundled proposition: Dir membership plus
the three caso-alineado inequalities (TeX 5336–5342, `eq:caso alineado`):
`(a',b') ∈ ℤ × ℕ₀`, `v_{ρ₁,σ₁}(a',b') < v_{ρ₁,σ₁}(a,b)`, `ab' - ba' > 0`. -/
def Esquina1Combined (dirP dirQ : Prop) (a' b' a b : ℤ) (ρ₁ σ₁ : ℤ) : Prop :=
  (dirP ∧ dirQ) ∧ 0 ≤ b' ∧
    (ρ₁ * a' + σ₁ * b' < ρ₁ * a + σ₁ * b) ∧ (a * b' - b * a' > 0)

/-- The bundle is the plain conjunction of its parts (the restatement). -/
theorem esquina1_bundle_iff {dirP dirQ : Prop} {a' b' a b ρ₁ σ₁ : ℤ} :
    Esquina1Combined dirP dirQ a' b' a b ρ₁ σ₁ ↔
      (dirP ∧ dirQ) ∧ 0 ≤ b' ∧
        (ρ₁ * a' + σ₁ * b' < ρ₁ * a + σ₁ * b) ∧ (a * b' - b * a' > 0) :=
  Iff.rfl
