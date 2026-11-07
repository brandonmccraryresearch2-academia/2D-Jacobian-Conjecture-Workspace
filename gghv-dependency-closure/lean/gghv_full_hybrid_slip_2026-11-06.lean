import Mathlib

/-! # R16 — Hybrid-vs-slip for the swapped Cor 7.4 uses (Phase 4, Leg E)

**CLAIM:** Explicit open item, with both readings stated and the
distinguishing arithmetic kernel-proved.
**STATUS:** BLOCKED on the published [GGV1] §7 text — retrieval leg
COMPLETE, target NOT FOUND (retrieval_log.md, routes T1-R1–R15; only
untried routes are institutional access and a ScienceDirect abstract page
whose PII is unknown). What this file DOES settle, kernel:
  (a) the two readings, stated as data (`Cor74Reading`): HYBRID — the
      published Cor 7.4 condition (3) differs between F and F1 in a way
      the arXiv TeX already shows (F: `b > a/l`; F1: `b < a/l` — see the
      numbering note, which paraphrases the arXiv TeX F1 wording at
      lines 4238+); SLIP — GGHV misapplied Cor 7.4 at the swapped uses.
  (b) the distinguishing arithmetic: at (24,9), `en(F) = (16,6) =
      (2/3)·(24,9)` and `9 < 24` (so the F1 slot condition `b < a/l`
      holds and the F slot condition `b > a/l` fails); at (28,8),
      `en(F) = (21,6) = (3/4)·(28,8)` and `8 < 28`; at the unswapped
      uses the F condition holds: `27 > 9` at (9,27), `21 > 7` at (7,21).
  (c) the conditional: IF the published F1 condition (3) is `b < a/l`
      (as in the arXiv TeX), THEN the (24,9)/(28,8) uses are legitimate
      F1 uses — the hybrid reading is confirmed at the arXiv-text level,
      and the only remaining question is whether the PUBLISHED text
      differs from the arXiv text. The published §7 numbering is known
      NOT to match the arXiv TeX in §8 (B=16 theorem cited as 8.10 in
      later papers vs 8.12 in the arXiv TeX — retrieval log, Target 1
      numbering cross-check), so the published §7 wording genuinely
      cannot be assumed equal to the arXiv wording.
**NOT proved here:** which reading is correct for the published text.
Neither reading is claimed. The (24,9)/(28,8) `Cor74Data` bundles in
`d1_cor74` remain data WITHOUT condition (3), exactly as filed.
No `sorry` anywhere; no `axiom` anywhere.
-/

/-- The two readings of the swapped Cor 7.4 uses (24,9)/(28,8). -/
inductive Cor74Reading where
  | hybrid : Cor74Reading
  | slip : Cor74Reading
  deriving DecidableEq, Repr

/-- (24,9): `en(F) = (16,6) = (2/3)·(24,9)` (inventory.md 21:35;
`d1_cor74` `cor74_prop42`). -/
theorem hybrid_arith_249 : (2 : ℚ) / 3 * 24 = 16 ∧ (2 : ℚ) / 3 * 9 = 6 := by
  constructor <;> norm_num

/-- (28,8): `en(F) = (21,6) = (3/4)·(28,8)` (`d1_cor74` `cor74_prop43`). -/
theorem hybrid_arith_288 : (3 : ℚ) / 4 * 28 = 21 ∧ (3 : ℚ) / 4 * 8 = 6 := by
  constructor <;> norm_num

/-- (24,9): the F1 slot condition `b < a/l` holds (`9 < 24`) and the F slot
condition `b > a/l` fails — the swapped use is F1-shaped, not F-shaped. -/
theorem hybrid_slot_249 : (9 : ℚ) < 24 ∧ ¬ (9 : ℚ) > 24 := by
  constructor <;> norm_num

/-- (28,8): same, `8 < 28`. -/
theorem hybrid_slot_288 : (8 : ℚ) < 28 ∧ ¬ (8 : ℚ) > 28 := by
  constructor <;> norm_num

/-- (9,27): the unswapped F slot condition `b > a/l` holds (`27 > 9`). -/
theorem hybrid_slot_927 : (27 : ℚ) > 9 := by norm_num

/-- (7,21): the unswapped F slot condition holds (`21 > 7`). -/
theorem hybrid_slot_721 : (21 : ℚ) > 7 := by norm_num

/- NOTE: no conditional theorem is stated here, deliberately — any
`PublishedF1Cond3 → Legitimate` implication would be vacuous (its proof
would be exactly the slot arithmetic above, applied to a hypothesis whose
truth is the open question). The open item is the antecedent itself:
the published §7 text (retrieval NOT FOUND). -/
