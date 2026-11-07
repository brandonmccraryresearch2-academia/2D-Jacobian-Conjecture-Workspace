# LEG 3 — Validation Gate: combined-paper draft, 2026-11-04

## CLAIM + STATUS (truth-seeking-frontier v5, top of report)

- **CLAIM:** The draft `combined_paper_draft_2026-11-04.tex` can be finalized, with Part II
  reconciled to the unconditional branch-(c) elimination, without overclaiming
  (72,108) or JC(2), and without any load-bearing case-number error.
- **STATUS: PASSED** — no residual blocker. The finalized paper below was produced.
  Two disclosed caveats (scratch provenance of `challenge_target` /
  `branch_c_eliminated`, and carried-over internal counts marked UNVERIFIED) do not
  block finalization; both are stated in the paper itself, not hidden.
- **VERIFIED / UNVERIFIED / FAILED branches:**
  - VERIFIED: case numbering (re-extracted from GGHV v1 itself); branch-(c)
    unconditional result (Lean logs quoted verbatim); branches (a),(b) Grade A
    (axioms audit log); Zenodo 10.5281/zenodo.23023490 (live record);
    Theorem R OPEN + equivalent; two-dicritical false claim withdrawn with the
    Nov 2 rewrite as Part III; finalized compile (rc=0, 0 errors, 0 undefined refs).
  - UNVERIFIED (carried over unchanged, not load-bearing for the new result):
    internal counts "790 modules", "505 generated modules", "600 identities" —
    see §5.
  - FAILED: none.

## Form choice (stated plainly)

**Deepest-research mode: `fact-check`** — verification of a provided text against
its record (draft + local Lean logs + GGHV v1 text + Zenodo record). This is not
a systematic review, not a scoping review, and not a literature search: no
PRISMA flow, no bibliography sweep, and no new external literature was needed
for the four assigned checks. Per Brandon's standing delegation (2026-10-25),
the form choice is the assistant's; the choice above is that choice.

## Gate handling (recorded explicitly for the coordinator)

The deepest-research skill's review-form note prescribes a stop-and-wait at
lit-review selection or at research-question confirmation in `full`/`socratic`
mode. That stop does **not** apply to this run on either ground: (1) this run is
`fact-check` mode on a provided draft, not a lit-review or an RQ-confirmation
step; and (2) Brandon's order of 2026-11-04 23:19 CST ("run autonomously
without needing to approve") explicitly waives per-step approval for THIS run.
The validation therefore proceeded in full without blocking. This waiver is
scoped to this run only and does not change the standing gate for other runs.

The deepest-research skill and the truth-seeking-frontier skill are
**DESIGN CLAIM, ungraded**. Nothing in this report presents either skill, or
any number in it, as evidence that this validation is reliable. Reliability
here rests only on the tool verdicts quoted below.

## Tool verdicts quoted (version + exit code)

- `xelatex` (XeTeX 3.141592653-2.6-0.999998, TeX Live 2026, conda env
  `jacobian-conjecture-2d`): finalized tex compiled 3 passes; final pass
  **rc=0, 0 errors (`^!` count 0), 0 undefined references, 67 pages**.
  Pass 1 gave 64 pages (pre-TOC/refs), passes 2–3 stable at 67.
- `pdftotext` (Poppler 24.02.0): GGHV v1 extraction, rc=0, 1282 lines; line
  evidence in §2.
- `python3` (3.12.3): edit script applied 24 + 2 + 1 replacements, each
  asserted count==1 before writing; rc=0.
- `md5sum`: draft tex/pdf unchanged after all work (both `OK`).
- Lean evidence is quoted from the 2026-11-04 lean-build-2 logs, not re-run
  here (no Lean run was part of this leg; re-running the kernel check is a
  later leg's job if the coordinator wants an independent re-check).

## 1. Check 1 — Case-number audit: PASS, zero numbering errors, one citation fix

**Correct numbering (task + independently re-verified):** Prop. 4.3 case (1) =
polygon set WITH (0,8)/(0,12) = NewtonNFc = branch (c); case (2) = set WITHOUT
them = NewtonNF2 = branches (a),(b). GGHV's own sub-labels map the same way:
cases a), b) → without vertices; case c) → with vertices.

**Independent re-verification from GGHV v1 itself** (local file
`research/uploads-2026-10-24/jacobian-workspace/GGHV-2204.14178v1/paper/2204.14178v1.pdf`,
extracted with `pdftotext -layout`, rc=0):

| Extraction line | Text | Verdict |
|---|---|---|
| 494 | `(1) N(P) = {(0,0),(1,0),(8,14),(8,16),(0,8)}, N(Q) = {(0,0),(2,1),(12,21),(12,24),(0,12)}` | case (1) = WITH ✓ |
| 495 | `(2) N(P) = {(0,0),(1,0),(8,14),(8,16)}, N(Q) = {(0,0),(2,1),(12,21),(12,24)}` | case (2) = WITHOUT ✓ |
| 598–599 | "in the cases a) and b) the Newton Polygons … become" + WITHOUT lists | a)/b) = case (2) ✓ |
| 617–618 | "and in the case c) it becomes" + WITH lists | c) = case (1) ✓ |

**Every Prop. 4.3 case-number occurrence checked in the draft** (draft line
numbers; method: full `grep -n "case"` plus targeted greps for `case~(1)`,
`case~(2)`, `NewtonNFc`, `NewtonNF2`):

| Draft line | Occurrence | Verdict |
|---|---|---|
| 127 | Abstract Part II: "case~(1) of Proposition~4.3" = branch (c) | CORRECT, kept |
| 203 | Part I intro: "Case~(1), with additional vertices (0,8) resp. (0,12), is branch~(c). Case~(2) … is branches~(a) and~(b)" | CORRECT, kept |
| 257 | Cor. "case~(8,28), sub-cases~a) and~b)" (GGHV subcases = case (2)) | CORRECT, kept |
| 293 | Box "Counterexample in case (8,28) → NewtonNF2" — corner label, not a Prop. 4.3 case number | Not a numbering claim; kept |
| 314–319 | Prop. `ab:prop:gghv43`: (1) WITH, (2) WITHOUT | CORRECT, kept |
| 332 | Source quote, lines 599–600: "in the cases a) and b)" + WITHOUT lists | CORRECT, kept |
| 337 | "We work exclusively with case~(2) (branches~a,b)" | CORRECT, kept |
| 1040 | Part I conclusion: branches (a),(b) "— case~(2) of Prop. 4.3" | CORRECT, kept |
| 1063 | Part I remark: "branch~(c) (case~(1) of Prop. 4.3)" | CORRECT numbering; sentence updated for staleness (see §3) |
| 1074 | Part II intro: "Case~(2) … eliminated … Case~(1) … is branch~(c)" | CORRECT, kept |
| 1137 | Part II §source: "Proposition~4.3, case~(1)" | CORRECT numbering; line citation FIXED (see below) |
| 226 (fig cap.) | Branch-(a,b) polygons "from Prop. 4.3(2), source-gated at v1 lines~495 and 599--600" | CORRECT (495 exact; 599–600 within ±1 of extraction 598–599); kept |
| 1097 (fig cap.) | Branch-(c) polygons "source-gated at GGHV v1 lines~495 and~599--600" | NUMBERING correct, CITATION WRONG → fixed to 494 and 617–618 |

**Wrong shorthand check:** no occurrence of "(a),(b) = case (1)" (or any
equivalent) exists anywhere in the draft. Grep for every `case~(1)` hit returns
only branch-(c) uses; every `case~(2)` hit returns only branches-(a,b) uses.

**Correction made (the only Check-1 correction):** the Part II figure caption
(final L1097) and §source sentence (final L1162) cited "GGHV v1 lines~495 and
599--600" for the case-(1) vertex lists — but line 495 is the case-(2) list and
599–600 is the a)/b) passage. Both now cite line 494 (case-(1) list) and lines
617–618 (post-φ case-c list), and the validation note records the fix.
All other `case` hits in the draft (m = 1/3/5/7 values, depth cases, the
"adjacent case", the Oct-1 case split) are not Prop. 4.3 case numbers and were
checked as not-applicable, not changed.

## 2. Check 2 — Part II reconciliation with branch_c_eliminated: PASS

**Stale wording found (draft):** abstract L148 ("rank computation supplies
ChartEmptyC_T1ne0 outside Lean, at epistemic grade~B"); theorem title L1098
("conditional"); L1102 ("established outside Lean … at epistemic grade~B");
corollary title L1104 ("Unconditional elimination under computational
premises"); L1105 (rank premises as the route); L1115 chain ending at the
undischarged hypothesis; L1309 listing caption ("proved in §wholechart");
L1366 ("B8, proved outside Lean at grade~B"); L1381 (corollary "from
§wholechart"); bridge table B8 row + grades table C5 (grade B as the
whole-chart route); L1433 "not claimed" list ("not a Lean proof of the
stratum b11,20≠0"); Part I L1063 + L289 ("remaining open case branch~(c)");
Part II conclusion L1439 (rank lemma as the whole-chart route).

**Reconciliation applied (finalized tex):** new Theorem
`bc:thm:unconditional` ("Unconditional elimination of branch~(c) in Lean",
final L1123) with a verbatim `branch_c_eliminated` listing and a proof sketch:
apply `main_theorem_c_of_chartEmpty_T1ne0` to `challenge_target`; bridge
Fpoly = Fpoly2 (same six `polyOfTerms` generators, same order, single `tl_*`
definitions in `Chart/Gens.lean`); instantiation of
`chartEmptyC_T1ne0_of_certificate` at ρ = Fin 3199, p = 32003, w₀ = 11147 with
A1 (Cinv·MS = 1), A2, and the six data hypotheses (hw₀, hscale, prime32003,
hmon, hr₁, hsupp2 in Fpoly2 form transported along the bridge). Axiom
evidence quoted verbatim from the 2026-11-04 logs:

- `bridge_challenge_target_2026-11-04.log`: `'challenge_target' depends on
  axioms: [propext, Classical.choice, Quot.sound]`
- `branch_c_eliminated_2026-11-04.log`: `'branch_c_eliminated' depends on
  axioms: [propext, Classical.choice, Quot.sound]`

The conditional theorem is kept as the conditional form (its statement is
still true and kernel-checked); the corollary is retitled "Unconditional
elimination (Lean certificate)"; the rank route is demoted everywhere to
independent corroboration at grade B (grades table gains C9 = challenge_target
grade A, C10 = branch_c_eliminated grade A; C5/B8 grades as originally proved
are unchanged); the "not claimed" list drops the stratum claim and gains the
explicit scope guard. The validation note (§ after abstract) states the scope
in plain language.

**Scope guard (stated in the paper at: validation note, new theorem's scope
paragraph, §epistemic "not claimed", and conclusion):** branch-(c)
elimination is unconditional *in Lean, as one case of one proposition*. It
does NOT exclude (72,108) unconditionally and does NOT prove JC(2); both still
require GGHV Prop. 4.3 correctness + exhaustiveness and the reduction chain,
ledgered, not re-derived. No sentence in the finalized paper claims otherwise;
the conclusion's conditional sentence ("no (72,108) counterexample arises from
GGHV Proposition~4.3, conditional on that proposition's correctness and
exhaustiveness") is retained verbatim in substance.

## 3. Check 3 — Other load-bearing claims: PASS (one addition, no overclaim found)

- **Branches (a),(b) main_theorem Grade A: PASS.** Draft's claim matches the
  2026-11-04 axioms audit log
  (`tooling/logs_gcp_phase3/logs/axioms_audit_2026-11-04.log`):
  `'BranchAb.main_theorem' depends on axioms: [propext, Classical.choice,
  Quot.sound]`, sorryAx absent across the 35 declarations. The draft's
  "standard axioms only, independent of GGHV Prop. 4.3" is accurate.
- **Zenodo 10.5281/zenodo.23023490: PASS, live-verified.** DOI record fetched
  2026-11-05: title "Elimination of the GGHV Branch-(a,b) Normal Form at
  Degree Pair (72,108): A Certified Computational Audit", author McCrary,
  Brandon D., published 2026-09-28, version v19 — matches draft bibliography
  L2452 exactly.
- **A1/A2/hsupp2 kernel-verified: PASS with an addition.** The draft never
  names A1/A2/hsupp2 (grep: zero hits) because it predates challenge_target.
  That is a gap, not an error: the finalized paper now documents them in the
  new theorem's proof sketch (see §2), sourced to the bridge/composition
  scratch files and logs above. No draft sentence contradicts them.
- **Theorem R corrected = equivalent to JC(2) and OPEN, NOT proved: PASS.**
  Draft abstract L155–180 and Part III L1657–1678 state Theorem R as OPEN and
  equivalent (Prop. `td:prop:equiv`); obligations O1–O6 and tests T1–T4 are
  collected in §open. No sentence claims Theorem R proved.
- **Two-dicritical theorem false as worded; Nov 2 rewrite supersedes Oct 25
  Part III: PASS.** Draft Part III carries the corrected content (false
  October 1 claim withdrawn with explicit counterexample, E1 theorem false as
  stated, (P2) not derived, bridge fenced under premises) under the rewrite's
  title "Dicriticals at Infinity of Keller Maps: Theorem R and Local
  Obstructions" (L1445), matching the Nov 2 rewrite, not the withdrawn Oct 1
  draft. The combined title's word "Closure" is ambiguous in isolation; the
  validation note clarifies it means closure/withdrawal of the false claim,
  not a proof of Theorem R.
- **Overclaim sweep: PASS.** Full grep for "excluded / unconditional /
  proves the (conjecture)" found no sentence claiming (72,108) excluded
  unconditionally or JC(2) proved. The only "unconditional" eliminations are
  the normal-form theorems themselves (NewtonNF2, now NewtonNFc), each
  correctly fenced by the GGHV-conditional corollaries.

## 4. Check 4 — Out of scope, not re-derived: stated

GGHV exhaustiveness and the reduction chain were **NOT** re-derived in this
validation. They remain ledgered premises. Every application to the Jacobian
conjecture in the finalized paper (Corollaries `ab:cor:gghv`, `bc:cor:gghv`)
remains explicitly conditional on GGHV Prop. 4.3's correctness and
exhaustiveness. The GGHV dependency-closure programme (a separate leg) is
where those premises are addressed; nothing here substitutes for it.

## 5. Every correction made (draft → finalized tex)

Edits E1–E21c + F1–F2 + note tweak, 27 asserted replacements total (edit
script `/tmp/finalize_combined.py`, since superseded by the compiled output;
the tex diff is 71 changed lines):

1. Date line: added "finalized November 4, 2026 (Part~II validation update)".
2. New unnumbered "Validation note — November 4, 2026 (Part~II update)" after
   the abstract (form, scope guard, case numbering, provenance caveat, title
   reading; plus the GGHV line-citation fix note).
3. Abstract Part II: grade-B sentence → unconditional Lean-certificate
   sentence; rank-lemma sentence → corroboration parenthetical.
4. Part I outline: "discusses the remaining branch~(c)" → "branch~(c) is
   eliminated in Part~II".
5. Part I "What remains" remark: "remaining open case … underdetermined
   pending branch~(c)" → branch (c) eliminated in Part II; only GGHV
   correctness/exhaustiveness remains conditional.
6. `bc:thm:main` retitled "conditional form".
7. Hypothesis paragraph: "established outside Lean … grade~B" → "was first
   established outside Lean … since Nov 4 proved inside Lean …
   Theorem bc:thm:unconditional discharges it".
8. `bc:cor:unconditional` retitled "Unconditional elimination (Lean
   certificate)" and restated on challenge_target, rank route as independent
   grade-B corroboration.
9. New Theorem `bc:thm:unconditional` + verbatim `branch_c_eliminated`
   listing + proof sketch / kernel record / scope / provenance.
10. Remark chain: appended the challenge_target discharge sentence.
11. Part II outline: wholechart "now corroborating"; proof section "records
    the unconditional Lean certificate".
12. Fig. 2 (bridges) caption: B8 "formerly the only non-Lean component and
    now corroborating".
13. Fig. 3 (omega) caption: T1≠0 stratum "(rank lemma, grade~B; now also Lean
    certificate, grade~A)".
14. ChartEmpty listing caption: "formerly proved in §wholechart (grade~B),
    now proved in Lean by challenge_target (grade~A)".
15. §wholechart closing: B8 "remains valid corroboration; no longer the sole
    route".
16. §proof corollary sentence: corollary "from challenge_target"; rank route
    "independently at grade~B".
17. Bridges-table note: "B8 is now corroborating rather than load-bearing".
18. Grades table: added C9 (challenge_target, A) and C10
    (branch_c_eliminated, A).
19. "What is not claimed": removed "not a Lean proof of the stratum
    b11,20≠0"; added "not (72,108) excluded unconditionally" and the
    explicit-K5-certificate clarification.
20. Open items: added (5) incorporation of challenge_target and
    branch_c_eliminated as tracked repo modules.
21. Conclusion: "eliminated, unconditionally in Lean"; whole-chart route =
    Lean certificate with rank lemma as corroboration; dependencies "as
    updated (C9, C10 grade~A)".
22. F1/F2: Part II GGHV line citations 495/599–600 → 494/617–618 (fig caption
    and §source).
23. Validation-note tweak recording the F1/F2 fix.

Nothing else was changed. In particular, no theorem statement, proof, figure,
or bibliography entry was altered except as listed above; the draft files
were not overwritten (md5 verified).

## 6. Residual issues — none blocking

1. **Scratch provenance (disclosed, not blocking).** `challenge_target` and
   `branch_c_eliminated` live in scratch files
   (`research/tooling/bridge_attempt_2026_11_04.lean`,
   `research/tooling/composition_2026-11-04.lean`), not tracked repo modules.
   The paper states this openly (validation note, new theorem, open item 5).
   Repo incorporation is a later leg's job; it does not block finalization of
   the paper text, but the coordinator should not describe the result as
   "repo-tracked" until that leg lands.
2. **Carried-over internal counts UNVERIFIED.** "790 modules", "505 generated
   modules", "600 identities" (Part II) were not re-verified from a local
   repo tree in this leg and are carried over unchanged. They describe the
   pre-existing conditional proof's internals, not the new unconditional
   result, so they do not affect the verdict; a later leg may audit them.
3. **Extraction variance.** GGHV line numbers are `pdftotext -layout`
   dependent (±1 across extractions). Part I's "599–600" vs this extraction's
   598–599 is within that variance and immaterial; the Part II fix above used
   this extraction's exact lines.
4. **No independent Lean re-run in this leg.** The unconditional result rests
   on the quoted 2026-11-04 lean-build-2 logs. If the coordinator wants a
   second, independent kernel re-check, that is future work, not a gap in
   this validation's verdict (the task's premise is that the proofs landed).

## Outputs (new files only; draft untouched; nothing committed)

- Finalized paper (tex):
  [combined_paper_final_2026-11-04.tex](sandbox://workspace/combined-paper/combined_paper_final_2026-11-04.tex)
- Finalized paper (pdf, 67 pages, XeLaTeX rc=0, 0 errors, 0 undefined refs):
  [combined_paper_final_2026-11-04.pdf](sandbox://workspace/combined-paper/combined_paper_final_2026-11-04.pdf)
- This report:
  [validation_report_2026-11-04.md](sandbox://workspace/combined-paper/validation_report_2026-11-04.md)
- Draft preserved byte-identical:
  `combined_paper_draft_2026-11-04.tex` / `.pdf` (md5 verified after all work).

## Devil's-advocate note (strongest counter-reading, answered)

The strongest objection is that finalizing a paper on scratch-file proofs
overstates readiness. Answer: the paper does not hide this — the validation
note, the theorem's provenance paragraph, and open item (5) all say the
proofs are scratch files pending incorporation. What finalization asserts is
narrower: the *text* is now consistent with the proved result and its scope,
which is exactly what this gate was asked to certify. Incorporation is a
separate, named next step, not a silently assumed one.

## Addendum 2026-11-06 — incorporation done

The "pending incorporation" above is now done, and the Devil's-advocate
objection no longer applies. The bridge/composition files
(`challenge_target`, `branch_c_eliminated`) were filed in this repository as
tracked modules `GradeA.Bridge` / `GradeA.Composition` (commit `7e4db07f`,
2026-11-06; status record
`JC2D-branches_a_b_c_unified/branch_c/grade_a/BRIDGE_STATUS_2026-11-06.md`),
kernel re-verified on lean-build-3. The body of this report is retained as
the 2026-11-04 record, not rewritten. (Only GGHV correctness/exhaustiveness
remains conditional — that line in the report is unchanged and still true:
the GGHV paper itself is now proved in full in Lean, CONDITIONAL, filed as
commit `484b5a8`, 2026-11-06; see
`gghv-dependency-closure/gghv_full_assembly_inventory.md`.)
