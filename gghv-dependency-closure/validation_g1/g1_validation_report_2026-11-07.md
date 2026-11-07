# Validation Gate G1 — deepest-research fact-check of the GGHV full-proof assembly inventory

**CLAIM:** The inventory
`~/workspace/goals/gghv-dependency-closure/hidden_files/phase4/gghv_full_assembly_inventory.md`
(1,112 lines) is accurate as the definitive per-item verdict record for the
Phase 4 full-proof programme, and the proposed filing set claims no more
than the verified verdicts.
**STATUS:** **CONDITIONAL GO** for filing — see §5 for the exact conditions.
No claim FAILED outright; three claims need REVISE corrections (one
axiom-list correction, one E11 wording correction, one citation-line
correction) and the filing plan needs a per-file manifest condition.

**Mode (stated plainly):** deepest-research **fact-check mode** — targeted
claim verification against the programme's own primary sources (leg files +
logs on disk, GGHV TeX, [GGV5] TeX + arXiv v1 PDF) — plus the skill's
devil's-advocate checkpoint and an editor GO / CONDITIONAL GO / NO-GO
verdict. No literature review, no new mathematics, no held-off
deep-research task. Truth-seeking-frontier v5 throughout: CLAIM+STATUS at
top, quoted tool verdicts with versions and exit codes, ABSTAIN rather than
guess, no result stated beyond its HLRE v5 grade.
**Method:** No subagents were spawned (this agent runs at depth 2/2,
`can_spawn=no`); all 15 claims were checked directly by this agent against
the cited files/logs. No VM was started and no Lean spot re-runs were run:
every verdict rests on log/file evidence already on disk (exit codes,
`#print axioms` output, md5s, line numbers). At check time both VMs were
TERMINATED (`gcloud compute instances list`, project
gen-lang-client-0391037020: lean-build-3 TERMINATED, lean-build-2
TERMINATED). Lean version throughout the cited logs: 4.34.0.
**Running log:** `validation_g1_log.md` in this directory (append mode).

## §1. Per-claim verdict table

| # | Claim | Verdict | Evidence in one line |
|---|---|---|---|
| 1 | Honest headline: paper NOT proved unconditionally; Thm 2.1 CONDITIONAL (20-field MinimalPremises2); no numbered environment unconditional | PASS | No `*_unconditional` theorem in any leg/assembly/laurent file (grep); `theorem21_minimal_v2` assembly l.3108, [triple] in `assembly_axioms.log` |
| 2 | Fields 9–10 refined: `link_924/927_derived` [triple] by kernel composition; assembly FULL_EXIT=0 135 s, AXIOMS_EXIT=0 50 s, 0 errors, no sorryAx | PASS | `assembly_axioms.log`: both [triple]; `assembly_full.log` grep error = 0, sorryAx = 0; timings/exit codes recorded in `assembly_log.md` only (see note) |
| 3 | R8 axiom lists (b2/b1/b0 [], lo/hi [propext], Q [propext, Quot.sound]) | PASS | `r8_axioms.log` matches the inventory table exactly |
| 4 | Prop 3.12 CONDITIONAL (`finitas_of_data` [triple], FinitasData premises named) | PASS | File 1 l.5469 / l.5293; round-5 axioms [triple]; §N header maps fields to the five paper lemmas |
| 5 | Prop 2.1(2a)→(2b) BLOCKED (common-power lemma + z-form reduction) | PASS | Blocker stated precisely in File 2a §R header; `prop21_two_a_of_b` l.5065 [triple]; no (2a)→(2b) theorem exists |
| 6 | [GGV5] completeness BLOCKED (`enum_complete_of_links`, hchain/hattrib) | PASS | File 2b l.5529; both links open hypotheses; [triple] round-5 |
| 7 | [GGV6] Thm 7.3 NOT PROVED as a theorem (combination proved in base only) | PASS | `ggv6_thm73_stmt` l.4664 is a `def` (pinned statement); `ggv6_combine` proved; `ggv6_discard84_from_thm73` l.5458 [triple] conditional on h73 |
| 8 | Four red rows CONDITIONAL; Remark 3.31 CONDITIONAL ((10,25)/(14,35) forcing carried) | PASS | Red rows ll.5591/5603/5616/5640, all [triple] round-5; `remark331_of_data` l.5625 [triple] via `prop329_of_data` |
| 9 | D2 power laws PROVED (coeffAt_pmul_assoc l.4939, ppow_add_kt l.5020, ppow_mul_kt l.5050) | **REVISE** | Lines present, but `coeffAt_pmul_assoc` is **[propext, Quot.sound]**, not [triple]; the other two are [triple] |
| 10 | Laurent fold-in (1,705 lines; FINAL_FULL_RC=0, AX_FULL_RC=0, 87 theorems, sorryAx 0); E11/E19/E20/E23 as stated | **REVISE** (E11 sub-item) | Fragment/log figures confirmed; E19/E20/E23 confirmed; E11 C-existence is generic-lemma KERNEL only — no §5 instance applied in the fragment |
| 11 | ValAxioms diagnosis: Leg D's structure uninstantiable (unconditional mul forces w ≡ 0) | PASS | Verified by direct reading: Leg D fields verbatim = `ValAxiomsOrig`; `forces_zero` proof valid; `nonneg` second obstruction valid |
| 12 | [GGV5] discrepancy: Leg A §6 label wrong; Prop 6.1 verified for arXiv v1 (TeX l.1874); numbering-UNVERIFIED for published | **REVISE** (minor) | TeX/PDF determination confirmed; inventory §8 cites PDF "pdftotext l.1533" — correct line is **2927** |
| 13 | Paper slips §9, highest-stakes five, spot-checked against TeX | PASS | (a)–(e) all confirmed; TeX lines quoted in §3 |
| 14 | Filing set (phase4_map.md §11): every filed file claims no more than its verified verdict | **CONDITIONAL** | The plan itself overclaims nothing, but it contains no per-file grade/axiom/premises mapping — filing conditioned on producing one |
| 15 | Scope guards: "(72,108) excluded unconditionally" / "JC(2) proved" NOT claimed; Theorem R excluded | PASS | All three present in inventory §5 (ll.814–817) and respected throughout |

No FAILs. Three REVISEs (one substantive wording, one axiom list, one
citation line) and one CONDITIONAL (filing manifest).

## §2. Per-claim evidence

### 1. Honest headline — PASS
- `grep` over all `phase4_leg*/`, `phase4_assembly/`, `phase4_laurent/*.lean`
  for `theorem.*_unconditional`: zero theorem declarations; the only hits
  are comments stating "NO `theorem21_unconditional` is claimed."
- Assembly file (3,165 lines): `MinimalPremises2` l.3044 (20 fields),
  `theorem21_minimal_v2` l.3108; `assembly_axioms.log`:
  `'theorem21_minimal_v2' depends on axioms: [propext, Classical.choice,
  Quot.sound]`.

### 2. Fields 9–10 refined — PASS (with a record-keeping note)
- `assembly_axioms.log`: `'link_924_derived' depends on axioms: [propext,
  Classical.choice, Quot.sound]`, same for `link_927_derived`; plus
  `prop41_conditional` [propext, Quot.sound], `prop42_conditional`
  [triple], `prop43_conditional` [propext, Quot.sound],
  `prop44_conditional` [triple], `thm51_conditional` [triple],
  `cor52_conditional` does not depend on any axioms (l.593),
  `prop42_shape_of` [triple], `prop41_shape_of` [propext, Quot.sound] —
  all matching the legs' own lists (re-verified, not just re-quoted).
- `assembly_full.log` (36,472 bytes): `grep -ci error` = 0, sorryAx count
  0; 98 Lean warnings (99 case-insensitive "warning" matches minus the 1
  SSH-tunnel banner line) — the inventory's "98 warnings" is correct.
- `assembly_full.log` and `assembly_axioms.log` have identical md5
  (`2f880597c1be19a257f8837aba237e4d`): consistent, not suspicious — the
  same file (including its `#print axioms` block) was compiled twice.
  **Note:** the exit codes and timings (FULL_EXIT=0 135 s, AXIOMS_EXIT=0
  50 s) are recorded only in `assembly_log.md`, not inside the log files
  themselves. Future runs should echo `rc=`/timing into the log file.
  This does not change the verdict: the logs themselves show a clean
  compile with the expected axiom output.

### 3. R8 axiom lists — PASS
`r8_axioms.log` (rc=0, 15 s per `assembly_log.md`) prints exactly:
`esq3_dir_b2/b1/b0` do not depend on any axioms;
`esq3_lform_endpoint_lo/hi` depend on `[propext]`;
`esq3_lform_Q` depends on `[propext, Quot.sound]`. Matches inventory §2
R8. `esq3_lform_from_cube` (r8 file ll.122–133) is conditional on its
named premises `hcommon` (ℓ(P) = λ_P R^m) and `hxcube` (x·R =
c·(z−μ)³), as the inventory states.

### 4. Prop 3.12 CONDITIONAL — PASS
- `gghv_full_ggvstar_2026-11-06.lean` (5,686 lines, md5
  `5db7b34420dcf8d111223e79aaed3f44` — matches inventory): `structure
  FinitasData` l.5293, `theorem finitas_of_data` l.5469.
- Round-5 axioms file: `'finitas_of_data' depends on axioms: [propext,
  Classical.choice, Quot.sound]`; round-5 log: all three files
  LEAN_EXIT=0, 0 error lines, NO sorryAx (`legF_log.md` round-5 section,
  2026-11-07 ~01:39–01:41 UTC).
- The §N header maps the fields to the paper's lemmas exactly as the
  inventory states: `hmult` — Lemma `factores en jacobiano` eq2; `hdg` —
  Lemma `maximo grado`; `hval` — [GGV1] Prop 1.13; `hgap` — Remark `gap`;
  `hsupp` — single-factor support/en facts; `hst0` — [GGV1] Prop 2.4(1)
  dichotomy. The premises are named, not proved — the inventory says so.

### 5. Prop 2.1(2a)→(2b) BLOCKED — PASS
File 2a §R header (ll.4862–4870): "The reverse direction (2a) ⇒ (2b) is
BLOCKED with a precise blocker: it needs (i) the univariate common-power
lemma — if fⁿ = α·gᵐ with gcd(m,n) = 1 then f, g are powers of a common
polynomial … (ii) the z-form reduction P = x^{r/l}y^s f(z), which is not
in the KTerm layer." No theorem proving (2a)→(2b) exists in the file.
The forward direction `prop21_two_a_of_b` l.5065 is [triple] (round-5).

### 6. [GGV5] completeness BLOCKED — PASS
File 2b l.5529 `theorem enum_complete_of_links` takes `hchain` (every
pair yields a PLLC with the right degree formulas) and `hattrib` (every
such PLLC's degree pair is in the table) as hypotheses; [triple]
round-5. Neither link is proved anywhere in the leg files.

### 7. [GGV6] Thm 7.3 NOT PROVED — PASS
File 2b l.4664 `def ggv6_thm73_stmt` — a pinned *statement* (major
equality + minor inequality), with the header comment stating the proof
"is CARRIED" (resultant computation + [X] Thm 4.7 over the π-root
existence theory). `ggv6_combine` proves only the combination
I_m ≤ I_M from the statement. `ggv6_discard84_from_thm73` l.5458 is
[triple] round-5, conditional on `h73 : ggv6_thm73_stmt …`.

### 8. Red rows + Remark 3.31 — PASS
File 2b §U: `redrow_412_34_conditional` l.5591,
`redrow_412_57_conditional` l.5603, `redrow_520_23_conditional` l.5616,
`redrow_520_32_conditional` l.5640 — all [triple] in round-5 axioms;
`redrow_520_32_of_23` zero axioms. `prop329_of_data` File 1 l.5593
[triple]; `remark331_of_data` l.5625 [triple], proved from
`prop329_of_data` with the (10,25)/(14,35) forcing carried as the
`hSE` hypothesis — exactly as the inventory states.

### 9. D2 power laws — REVISE (axiom list)
Lines confirmed: `coeffAt_pmul_assoc` l.4939, `ppow_add_kt` l.5020,
`ppow_mul_kt` l.5050 in
`gghv_full_ggvstar_ggv1_2026-11-06.lean` (5,119 lines, md5
`2e61236431142905b92d09252d1251f9` — matches inventory).
Round-5 axioms file:
- `'coeffAt_pmul_assoc' depends on axioms: [propext, Quot.sound]` —
  **not** [triple] as the inventory states in §2 R18, §6, and the
  headline ("all [triple]").
- `'ppow_add_kt'` / `'ppow_mul_kt'` depend on `[propext, Classical.choice,
  Quot.sound]` — confirmed [triple].
All three are still kernel-proved (a [propext, Quot.sound] list is a
subset of the permitted triple); the correction is to the quoted list
only. **Exact correction:** wherever the inventory says the three power
laws are "all [triple]", replace with "`coeffAt_pmul_assoc` [propext,
Quot.sound]; `ppow_add_kt`, `ppow_mul_kt` [triple]".

### 10. Laurent fold-in — REVISE (E11 sub-item only)
- Fragment `gghv_full_laurent_2026-11-06.lean`: 1,705 lines — confirmed.
  The two "sorry" grep hits are header-comment words only (ll.11–12).
- `laurent_log.md`: final full-file run FINAL_FULL_RC=0, 0 errors, 1,705
  lines; full-file axioms audit AX_FULL_RC=0, 87 theorems (86 "depends on
  axioms" lines + `pow_ne_zero_of_ne` []), sorryAx count 0. **Note for
  the record:** the log records a first AX_FULL attempt at RC=1 with 7
  errors (generated `#print axioms` names in the wrong namespaces),
  fixed and re-run clean. The inventory omits this first-attempt failure;
  it does not affect the verdict (final run clean), but the filing
  manifest should record final-run-only.
- E19 PARTIAL — confirmed: `laurent_series_discharge_s6` l.1541
  (existence + bounds, repackaging `e19_existence_bounds_s6` with
  `valcore_finite_bounds` at the two LP valuations); `f_discharge_lp_s6`
  l.1681 conditional on `GGV1InputsLp` + unit (`exists_F_lp` l.1650).
- E20 — confirmed: `exists_tilde` l.1466, `tilde_discharge` l.1591
  (KERNEL modulo Ptcoef input data, as stated).
- E23 — confirmed: `bracket_reduction_discharge` l.1612 conditional on
  `hdeg` (the Leibniz-rule hypothesis), as stated.
- **E11 — REVISE:** `exists_sqrt_series` l.868 is a *generic* theorem
  (any CommRing with explicit `inv2u0`). The only applications in the
  fragment are the §6 instance `e19_sqrt_s6` (l.940, u0 = T 1) and the
  tilde instance (l.1482). **No §5-named instance is applied** (no
  application with A := RatFunc K, u0 := C₃ = y⁸(y+1)). The inventory's
  E11 detail entry does disclose this ("no separate §5-named existence
  theorem was written; the generic theorem is the discharge"), but the
  §1 table headline "C-existence KERNEL (`exists_sqrt_series`,
  fragment)" overstates the §5 discharge. **Exact correction:** file E11
  C-existence as "generic sqrt-series lemma KERNEL (`exists_sqrt_series`
  [triple]); §5 instance (RatFunc K, C₃ = y⁸(y+1)) NOT separately
  applied — instance application remains open". The F-CONDITIONAL
  (`f_discharge` l.1623 on `GGV1Inputs`) and "§5 bounds NOT discharged"
  parts of E11 are confirmed as stated.

### 11. ValAxioms diagnosis — PASS (confirmed by direct reading)
Leg D `gghv_full_s6_2026-11-06.lean` ll.110–116, `structure ValAxioms`:
fields `mul : ∀ a b, w (a * b) = w a + w b`, `add`, `neg`, `one`, `two`
— verbatim identical to the fragment's `ValAxiomsOrig` (ll.104–109).
The fragment's `forces_zero` (l.116) is valid: `hw.mul 0 a` gives
`w (0 * a) = w 0 + w a`, i.e. `w 0 = w 0 + w a`, hence `w a = 0` for
every `a`. The `nonneg` second obstruction is also valid (`add` with
`a + (−a) = 0` forces `0 = w 0 ≤ max (w a) (w (−a)) = w a`). So Leg D's
`e19_bound_step_21` (l.171), `e19_bound_step_1m1` (l.206),
`e19_finite_bounds` (l.268) are kernel-proved implications that can
never be instantiated with v_{2,1}/v_{1,−1}, exactly as the inventory
states. The usable replacements are the fragment's `ValCore` versions,
instantiated at `valCore_lpMaxDeg` / `valCore_lpMinDeg` (§6).

### 12. [GGV5] discrepancy — REVISE (citation line only)
On-disk TeX `~/workspace/research/guccione-papers/tex/1708.07936/main.tex`
(only [GGV5] TeX on disk): numbered sections §1 Restrictions (l.265),
§2 Construction (l.390), §3 Generation of (m,n)-families (l.1376),
**§4 "Program and graphic display" (l.1638)**, §5 Admissible complete
chains (l.1669), §6 "Possible counterexamples" (l.1792);
`\begin{proposition}\label{caso antisimetrico}` l.1874, inside §6.
Fresh `pdftotext` of `arxiv_1708.07936.pdf` (this run): TOC "4 Program
and graphic display" (l.31), "6 Possible counterexamples …" (l.33),
"Proposition 6.1. The example corresponding to F22 with (m, n) = (2, 3)
can not be obtained" at **l.2927**. So: Leg A's §6 label is WRONG;
Prop 6.1 is VERIFIED for arXiv v1; numbering-UNVERIFIED for any published
version (none found) — all confirmed.
**Correction:** inventory §8 item 3 cites "pdftotext l.1533". That line
number is wrong; the correct line is **2927** (my fresh pdftotext run;
`phase4_map.md:334` also records 2927). Fix inventory §8 to l.2927.
(Likely cause: a different pdftotext invocation/version in the assembly
run; the proposition text itself is undisputed.)

### 13. Paper slips — PASS (all five spot-checked against the TeX)
TeX: `~/workspace/research/rss-monitor/tex/2204.14178/main.tex` (2,262 lines).
- **(a) φ-shift:** l.1663: "Consider the automorphism φ of K[y]((x⁻¹))
  given by φ(y)=y, φ(x)=x−D₂ (and so φ(x⁻¹)=x⁻¹+x⁻²D₂+…)"; l.1668:
  "… for some d_i ∈ K[y] (note that d₂=0)". Same pair recurs §6 at
  ll.2025/2030. The paper asserts d₂=0 for the stated shift; the
  x²-coefficient of φ(D) is D₂−3t, so t=D₂ gives −2D₂ ≠ 0 and the
  consistent shift is t=D₂/3. Confirmed as stated.
- **(b) §5 recursion sign:** ll.1462–1465: "2C₃C_{3−k} = −P_{6−k} −
  Σ_{j=1}^{k−1} C_{3−j}C_{3−k+j}" and "C_{3−k} := −(1/(2C₃))(P_{6−k} +
  Σ …)". The expansion gives 2C₃C_{3−k} = P_{6−k} − Σ; both signs
  flipped. Confirmed as stated.
- **(c) 1/2 omission:** l.1625 (§5): "D_k = … = (1/2)P_{k+3}C₃^{4−2k} −
  Σ_{j=k+1}^{2} D_j D_{k+3−j}" — the 1/2 present on the first term is
  dropped on the sum (the correct expansion needs −(1/2)Σ D_j D… since
  D_j D_{k+3−j} = C_j C_{k+3−j} C₃^{4−2k}). Same at l.1987 (§6).
  Confirmed as stated.
- **(d) §6 polygon transposition:** ll.1817–1823 (Thm 6.1): "N(P) =
  {(0,0),(4,0),(2,6),(0,14)}, N(Q) = {(0,0),(6,0),(3,9),(0,21)}".
  Prop 4.4 (ll.1313–1319) gives the scaled form "N(P) =
  {(0,0),2(2,0),2(3,1),2(0,7)}, N(Q) = {(0,0),3(2,0),3(3,1),3(0,7)}",
  i.e. {(0,0),(4,0),(6,2),(0,14)} / {(0,0),(6,0),(9,3),(0,21)} — the
  middle vertex is transposed in the §6 statement. The §6 proof's own
  "ℓ_{1,0}(P)=x⁶y², ℓ_{1,0}(Q)=x⁹y³" (l.1826) agrees with Prop 4.4, not
  with the printed §6 list (max x-exponent 4 < 6). Confirmed as stated.
- **(e) (b₀) v=7 not 6:** l.~1855: "(b₀) v_{2,1}(x³y) = v_{2,1}(3,1) = 6".
  v_{2,1}(3,1) = 2·3 + 1·1 = 7. The "6" is arithmetically wrong;
  harmless (the bound used is ≤ 7). Confirmed as stated.

### 14. Filing set — CONDITIONAL
`phase4_map.md` §11 (Filing plan) proposes: new Lean modules
`gghv-dependency-closure/lean/gghv_full_<section>_2026-11-06.lean`,
manifest/log updates (`lean/MANIFEST.md`, `singular/MANIFEST.md`,
`CORRESPONDENCE.md` per module with its grade), commit/push via the Git
Database API only, and explicit non-filing of scratch/probe files and the
79 MB `INVERSE.pkl`. The plan itself asserts no grade and therefore
overclaims nothing — but it contains **no per-file grade / axiom-list /
carried-premises mapping**, so the check "every file proposed for filing
claims no more than its verified verdict" cannot be discharged from the
plan as written. See condition C1 in §5. (Spot-checks supporting the
underlying verdicts: Leg B theorems at the stated lines — prop41 l.407,
prop42 l.753, prop43 l.1088, prop44 l.1315, psp_183 l.494 — with axiom
lists matching `legB_log.md`; Leg C thm51 l.793, cor52 l.831,
e11_recursion_sign_slip l.564, e16_principal l.324, e13_f_separable
l.262, and `s5_axioms.log` counts 30 [triple] + 5 [propext, Quot.sound] +
2 [propext] + 2 [] = 39, sorryAx 0, matching inventory §10; Leg D
`s6_axioms3.log` counts 64 [triple] + 8 [propext, Quot.sound] + 8 [] =
80, sorryAx 0, matching inventory §10; Leg A `legA_axioms.log` 10 [] +
4 [propext] + 5 [triple] + 2 [propext, Quot.sound] = 21, sorryAx 0,
matching inventory §10.)

### 15. Scope guards — PASS
Inventory §5 (ll.814–817): '"JC(2) proved" is never claimed by this
programme — the full GGHV proof does not prove JC(2). "Theorem R" is
excluded from this programme everywhere. "(72,108) excluded
unconditionally" is NOT claimed — it rests on GGHV exhaustiveness + the
reduction chain, ledgered not re-derived.' All three guards are present
and respected throughout the inventory and the filing plan. No filing
file asserts any of them.

## §3. Devil's-advocate checkpoint

Strongest counter-argument attempted: *where could the inventory be
overstating a KERNEL or understating a blocker?*
- **Overstatement found (×2):** the `coeffAt_pmul_assoc` axiom list
  (§2.9) and the E11 §5 C-existence headline (§2.10). Both are now
  corrected above; neither changes any kernel status (the first is a
  subset-of-triple list; the second is a generic lemma whose §5 instance
  is genuinely still open).
- **Citation precision found (×1):** the GGV5 PDF line number (§2.12).
- **Checked and cleared:** (i) assembly FULL/AXIOMS logs byte-identical
  md5 — explained by the same file compiled twice with the same `#print`
  block; exit codes/timings live only in `assembly_log.md`, a
  record-keeping gap, not evidence of a problem. (ii) Laurent first
  AX_FULL attempt RC=1 — failed on generated `#print` names, fixed,
  final run clean; the inventory's omission is a manifest-completeness
  gap, not a verdict error. (iii) E13 SymPy defects (2× gcd Poly-domain
  artifacts, 1× bracket script error with factor 2, 3× dsolve
  limitations) and Leg G's two Singular script bugs (§5 D-scaling
  two-symbol C₃; 32-bit `int` overflow of 13!/14!) — the inventory
  discloses all of these rather than hiding them; the mathematics is
  decided by the correct runs. (iv) No `sorryAx` in any round-5 Leg F
  axioms file, any assembly log, any Leg A/C/D axioms log, or the
  Laurent final audit. (v) All md5s and line counts re-checked match the
  inventory (Leg F 5,686/5,119/5,700; assembly 3,165; Laurent 1,705).
- **Understated blockers?** None found. The BLOCKED items (Prop
  2.1(2a)→(2b), [GGV5] completeness, [GGV6] Thm 7.3 proof, §5/§6
  9-equation derivations, §5 min-degree ValCore, Leibniz rule for
  `LaurentSeries.derivative`) are each named with a precise blocker, and
  the CONDITIONAL items name their premises. The E7 eliminations (the
  only fully-kernel claims) rest on the previously verified GradeA
  modules (commit 7e4db07f), carried from the prior record and not
  re-verified in this gate — flagged here so the filing manifest says so
  explicitly rather than implying this gate re-checked them.
- **Residual risk for filing:** the filing plan's lack of a per-file
  manifest (§2.14) is the main avenue by which a correct inventory
  could become an overstating repo. Condition C1 closes it.

## §4. Findings list (every REVISE / CONDITIONAL, with exact correction)

| # | Location | Correction needed |
|---|---|---|
| F1 | Inventory §2 R18, §6, headline ("D2 power laws … all [triple]") | Replace with: "`coeffAt_pmul_assoc` [propext, Quot.sound]; `ppow_add_kt`, `ppow_mul_kt` [triple]" (round-5 axioms file). Kernel status unchanged. |
| F2 | Inventory §1 E11 table row + §0 headline ("C-existence KERNEL") | Replace with: "generic sqrt-series lemma KERNEL (`exists_sqrt_series` [triple]); §5 instance (RatFunc K, C₃ = y⁸(y+1)) NOT separately applied — instance application remains open". Keep F-CONDITIONAL and "§5 bounds NOT discharged" as stated. |
| F3 | Inventory §8 item 3 ("pdftotext l.1533") | Replace with "pdftotext l.2927" (verified by fresh pdftotext run; `phase4_map.md:334` agrees). |
| F4 | Filing plan (`phase4_map.md` §11) — condition, not a text error | Before filing, produce a per-file manifest mapping each filed module to its inventory verdict + axiom list + carried premises (see §5 C1). |

## §5. Overall verdict: CONDITIONAL GO

**CONDITIONAL GO for filing**, subject to all four conditions below. No
claim failed; the paper is honestly recorded as NOT proved
unconditionally, every blocker is named precisely, and the kernel claims
that were checked against their logs hold (with the two corrections in
F1/F2).

- **C1 — Filing manifest (from F4):** before any commit, produce a
  per-file manifest (in `lean/MANIFEST.md` + `CORRESPONDENCE.md`) mapping
  each filed module to its inventory verdict, its `#print axioms` list,
  and its carried premises. In it: (a) Leg D's `e19_bound_step_21`,
  `e19_bound_step_1m1`, `e19_finite_bounds` must be labelled
  "kernel-proved implication, NEVER instantiable with v_{2,1}/v_{1,−1}
  (ValAxioms uninstantiable — see §7) — do not cite as instantiated";
  (b) Leg H's minor must be filed as PARTIAL/narrowed (indices +
  modular determinants only; K₅ determinant value NOT done; §6.3(a)
  satisfaction is Brandon's judgement call; outside-project rebuild NOT
  DONE); (c) the E7 eliminations must be noted as carried from the prior
  GradeA verification (commit 7e4db07f), not re-verified by this gate;
  (d) the Laurent first-attempt AX_FULL failure (RC=1, fixed names)
  must be recorded with the final clean run.
- **C2 — Apply F1:** correct the `coeffAt_pmul_assoc` axiom list
  wherever the inventory / filing docs say the three power laws are
  "all [triple]".
- **C3 — Apply F2:** correct the E11 C-existence wording to
  generic-lemma KERNEL with the §5 instance open, in the inventory
  table row and in any filing document that repeats it.
- **C4 — Apply F3:** correct the [GGV5] PDF citation line to 2927 in
  inventory §8 (and anywhere else it is repeated); also correct Leg A's
  header claim wherever it is repeated in filing docs (the comb leg's
  job — the inventory correctly notes the dated inventory file itself
  is NOT rewritten).

If C1–C4 are met, filing may proceed; if any is skipped, the verdict
reverts to NO-GO for the affected files. No repo commits were made by
this gate. The held-off final deep-research task remains held off; the
validation gate stays in force for any later revision.

## §6. Limitations of this gate
- Verification is log/file-based: no Lean re-runs were executed (both
  VMs were TERMINATED and no spot re-run was judged necessary). A
  re-compile would strengthen, not change, these verdicts.
- The E7 eliminations and the Leg G second-tool runs were checked
  against their recorded logs/values, not re-executed.
- The published [GGV1] §7 text and Joseph Lemma 2.2 remain NOT FOUND
  (retrieval leg); this gate confirms the inventory says so, it does not
  close those gaps.
- ABSTAIN: whether the delivered Leg H minor form satisfies §6.3(a) as
  literally worded is Brandon's judgement call, per the inventory — this
  gate does not decide it.
