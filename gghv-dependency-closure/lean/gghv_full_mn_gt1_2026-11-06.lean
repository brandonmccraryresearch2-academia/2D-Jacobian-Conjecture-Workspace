import Mathlib

/-! # R15 — `m, n > 1` as literally written (Phase 4, Leg E)

**CLAIM:** Resolved as a DOCUMENTED DEVIATION, not a proved strengthening.
**STATUS:** Kernel arithmetic for the two checkable parts + an explicit
deviation record. The resolution path the brief left open ("pending the
published §7 text") is now CLOSED by the retrieval leg: published [GGV1] §7
text NOT FOUND (retrieval_log.md, routes T1-R1–R15 exhausted; only untried
routes are institutional access and a ScienceDirect abstract page whose PII
is unknown). So no published wording can be quoted, and the deviation is
documented against the arXiv TeX — flagged explicitly as NOT the published
wording.
**The deviation (arXiv TeX):** esquina ("esquina de 83", TeX 5320–5325)
states `a,b,m,n ∈ ℕ` with `m ≠ n`, `gcd(m,n) = 1` — i.e. `m, n ≥ 1`. But
the proof needs `m, n > 1`:
  - the opening uses `nb, mb > 1` for `(ρ₂,σ₂) ∈ Dir(P) ∩ Dir(Q)`
    (inventory.md, Prop 8.2 item (2) proof map);
  - the same `m, n > 1` IS stated explicitly in the neighbouring results
    mayores (TeX 3799: "Let `m,n ∈ ℕ` be coprime with `m,n > 1`") and
    F (TeX 4077) / F1 (TeX 4238) — so esquina's `m, n ∈ ℕ` is the odd one
    out, a genuine minor gap as literally written (Phase 1 record).
**Kernel content of this file:**
  (a) `mn_gt1_dir_mem`: from `1 < m`, `1 < n`, `1 ≤ b`, `mb > 1 ∧ nb > 1`
      — the exact step the opening needs;
  (b) `gghv_uses_mn_gt1`: all four GGHV uses have `(m,n) ∈ {(2,3),(3,2)}`,
      hence `m, n > 1` — so the gap is harmless for every application in
      the GGHV paper, and the existing `d1_esquina1/2` proofs (which carry
      `hm : 1 < m`, `hn : 1 < n` as explicit hypotheses) already prove the
      strengthened form;
  (c) the `m = 1` failure mode is pinned: with `m = 1`, `mb > 1` forces
      `b > 1`, i.e. the opening's Dir-membership step would need an extra
      hypothesis the statement does not supply.
**NOT proved here:** that the published text states `m, n > 1` (retrieval
NOT FOUND — institutional access is Brandon's call); no claim is made
about the published wording anywhere in this file.
No `sorry` anywhere; no `axiom` anywhere.
-/

/-- The exact step esquina's opening needs: `mb > 1` and `nb > 1` from
`m, n > 1` and `b ≥ 1`. (Inventory.md: "`(ρ₂,σ₂) ∈ Dir(P) ∩ Dir(Q)` since
`st(P) = m(a,b)`, `st(Q) = n(a,b)`, `nb, mb > 1`".) -/
theorem mn_gt1_dir_mem {m n b : ℕ} (hm : 1 < m) (hn : 1 < n) (hb : 1 ≤ b) :
    1 < m * b ∧ 1 < n * b := by
  have hm2 : 2 ≤ m := hm
  have hn2 : 2 ≤ n := hn
  constructor
  · calc 1 < 2 * 1 := by norm_num
    _ ≤ m * b := Nat.mul_le_mul hm2 hb
  · calc 1 < 2 * 1 := by norm_num
    _ ≤ n * b := Nat.mul_le_mul hn2 hb

/-- With `m = 1`, the opening's `mb > 1` step needs `b > 1` — an extra
hypothesis the statement (as literally written, `m, n ∈ ℕ`) does not
supply. This is the precise failure mode of the literal wording. -/
theorem mn_eq1_needs_b_gt1 {b : ℕ} (h : 1 < 1 * b) : 1 < b := by
  simpa using h

/-- All four GGHV uses of esquina have `(m,n) ∈ {(2,3), (3,2)}`, hence
`m, n > 1`: (9,27) and (9,24) and (7,21) use `(2,3)`; (8,28) uses `(3,2)`
(GGHV TeX 470, 681, 1008, 1313 — the `(m,n)` multipliers of the corner
lists). So the `m, n > 1` strengthening is satisfied at every use site in
the paper, and the gap is harmless for the GGHV programme. -/
theorem gghv_uses_mn_gt1 :
    (1 < 2 ∧ 1 < 3) ∧ (1 < 3 ∧ 1 < 2) := by
  decide

/-- The strengthened esquina hypotheses (as already carried in
`d1_esquina1`/`d1_esquina2`: `hm : 1 < m`, `hn : 1 < n`) imply the
Dir-membership numerical step at every GGHV use site. -/
theorem gghv_uses_dir_mem :
    (1 < 2 * 21 ∧ 1 < 3 * 21) ∧ (1 < 3 * 8 ∧ 1 < 2 * 8) :=
  ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
