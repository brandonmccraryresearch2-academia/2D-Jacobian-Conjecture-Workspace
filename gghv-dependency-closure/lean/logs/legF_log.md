# Leg F log — [GGV*] remainder (R18–R20)
## Programme: GGHV full proof, Phase 4. Leg F = [GGV2]/[GGV6]/[GGV5]/[GGV1]-cited remainder + red rows.
## Rules: truth-seeking-frontier v5; CLAIM+STATUS at top of final report; quoted tool
## verdicts with version + exit code; second independent tool above CLAIMED; sorryAx NOWHERE;
## exact axiom list per theorem from #print axioms; ALL computation via lean-build-3
## (vm_lock.sh; do NOT stop the VM on release); NO repo commits.

## 2026-11-06 ~15:45 CST — Leg F started; sources read
- Read: phase4_map.md (§5/§6/§8/§9), inventory.md (§B/§F + 21:50/21:55/22:00 entries),
  gghv_statement_inventory.md (full, incl. §3c), d1_ggvstar_2026-11-05.lean (full, 5,409 lines),
  verification logs (lean/logs/d1_ggvstar_*_parent_recheck.log + _parent_axioms.log;
  check7/check8 logs in tooling/).
- Exact Lean invocation (from dated log 2026-11-05, line 361; Phase 1 pattern):
  on lean-build-3, `cd ~/repo/JC2D-branches_a_b_c_unified/branches_a_b/lean &&
  lake env lean --root=/tmp /tmp/<file>.lean`, Lean 4.34.0, toolchain ~/toolchain/bin.
  Second run with appended #print axioms; verdict = log's own rc, not the ssh wrapper's.
- Base status (d1_ggvstar header, re-verified by reading the file): Prop 3.12 STATEMENT PINNED
  (finitas_stmt, l=1, lambda-form), proof CARRIED; Prop 3.29 PROVED CONDITIONAL on hfin
  (Prop 3.12) + hSE (starting-vs-end instance); Remark 3.31 exclusions CONDITIONAL on Prop 3.29;
  Def 3.21 PINNED as AdmChain/PLLC; cota CONDITIONAL on para_la_cota; [GGV6] Thm 7.3
  combination + F9 instances PROVED, inequality itself CARRIED; Props 6.4/6.6/Ex 6.7
  statements pinned + instances; Prop 2.5 statement pinned (q-arith only); [GGV1] Thm 7.6
  divisibilidad_stmt pinned with numbering UNRESOLVED; Prop 2.11 pavadass pinned;
  Prop 2.1(2b) pinned as def prop21_two; Prop 6.1 tail arithmetic PROVED; enumeration
  statement pinned, completeness CARRIED; (8,24) red row CONDITIONAL on Prop 6.1.
- VM lock: HELD by legC since before leg start (age 235s at first check, 432s at second).
  Doing local (non-VM) writing first; will acquire when free. Never forcing a run.

## Source-text findings (all verified from the TeX/PDF on disk this session)
- [GGV2] = arXiv:1605.09430. TeX numbering differs from the arXiv PDF (v2) numbering.
  PDF Prop 3.12 = TeX Proposition `finitas direcciones` (l.720); PDF Prop 3.29 = TeX
  Proposition `casos imposibles` (l.1009); PDF Remark 3.31 = unnumbered remark after it
  (l.1049: "Propositions cota and casos imposibles give nice conditions..."; l.1053: the
  (2,1),(3,2),(6,3),(8,4) exclusions + (10,25)/(14,35) forcing "without a formal proof").
  Prop 3.12 proof read in full (TeX 747-853): case analysis from Lemma `factores en
  jacobiano` (eq2: t=s(i-1)+1 or ut=vs) + Lemma `maximo grado` (deg g <= (i-1)deg r + 1)
  + [GGV1] Prop 1.13 (v = u(i-1)+rho+sigma) + Remark `gap` (s <= N1) + [GGV1] Prop 2.4(1)
  (st-similarity dichotomy, lambda=0 case).
- [GGV2] Def 3.21 RESOLVED (pdftotext of arxiv_1605.09430.pdf): PDF Def 3.21 is the LAST
  LOWER CORNER (llc, TeX Definition `llc` l.927): a point (a,b) is a last lower corner if
  there is an admissible chain, obtained as in Remark 3.20 from a standard (m,n)-pair,
  with C_fin=(a,b) and m(a,b) the last corner of H(P) below the diagonal. PDF Def 3.17 is
  the POSSIBLE last lower corner (PLLC, TeX `Definicion pllc` l.911). The base's
  identification "Def 3.21 = AdmChain + PLLC" is therefore imprecise: Def 3.21 = LLC =
  PLLC + the pair-origin condition. GGHV's "last possible corner" (Def 3.21) is loose
  phrasing for the LLC; the exclusion (8,4) runs through LLC => PLLC + Prop 3.29.
- [GGV1] Thm 7.6(5) RESOLVED (TeX 1401.1784, theorem `divisibilidad`, l.4288): the
  theorem has items (1)-(6) + resumed (7)-(8); item (5) IS "q_j | d_i for all i>j>0".
  GGHV's use "q_1 = 4 | d_0" instantiates it with j=1 (the (4,-1) corner) and i = the
  index of the (1,0) corner; GGHV's d_0 is locally defined (the (1,0)-corner's d), not
  the TeX's d_0. The base's note ("no item giving q_1 | d_0") expected a literal match;
  the resolution is the index identification, recorded in File 2a.
- [GGV1] Prop 2.11 (pavadass, TeX l.962): items (1)-(5) read in full. Item (3) is a
  DESCENT: if p(z)=pbar(z^k), f(z)=fbar(z^k), then fbar separable and every irreducible
  factor of pbar divides fbar. The base's pavadass_conclusion pins the ASCENT form
  (Separable (comp f (X^k))) — the opposite direction; corrected in File 2a.
- [GGV6] = arXiv:1708.09367 (TeX §§1-3) vs published Pro Mathematica 30(60) (2019).
  Published numbering (Thm 7.3, Props 6.4/6.6, Ex 6.7, Prop 2.5) is NOT the arXiv
  numbering (arXiv: Thm 3.15 I_M = I(P,Q); Thm 3.25 I_m <= I(P,Q); Prop 3.18 top roots;
  Prop 3.13 traduccion; Example 16). Content mapping by statement comparison:
  Thm 7.3 = arXiv Thms 3.15+3.25 combined; Prop 6.4 = arXiv Prop 3.18; Prop 6.6 =
  arXiv Prop 3.13; Ex 6.7 = arXiv Example 16. Published-number alignment UNVERIFIED
  (published text not on disk; web search found only the arXiv + the [GGV4] PUCP page).
  Prop 2.5: NO TeX analogue located in arXiv §1 (props there: jacobiano se anula,
  direcciones positivas, b igual a 2) — stays CARRIED.
- Red rows: [GGV4] = "A differential equation for polynomials..." (arXiv:1310.8249).
  Its arXiv §3.5 ("Low-degree cases and the conjecture") contains NO (4,12) discard;
  the GGHV citation "[GGV4] §3.5" must refer to the PUBLISHED version's §3.5
  (Pro Mathematica 27 (2013) 83-98) — numbering/content gap flagged, rows stay
  CONDITIONAL on the cited external results. [GGV3] §5 treats (50,75) only (per the
  [GGV3] note), resting on [GGV1] Remark 7.10 + computations as in [GGV1] Prop 8.3;
  (75,50) follows by P/Q swap (swap-closure as explicit hypothesis).

## Plan
- File 1 (main): gghv_full_ggvstar_2026-11-06.lean — [GGV2]: Prop 3.12 CONDITIONAL proof
  (from named paper-lemma premises: eq2, max-degree, valuation identity, gap bound,
  support/en facts, st-dichotomy) + one-factor counting lemma + Prop 3.29 / Remark 3.31
  with reduced premises (hfin discharged to FinitasData) + Def 3.21 LLC pin + LLC=>PLLC
  + (8,4) LLC exclusion. Base slice copied verbatim by assembler (gen_legF1.py).
- File 2a: gghv_full_ggvstar_ggv1_2026-11-06.lean — [GGV1]: Thm 7.6(5) resolution +
  corrected divisibilidad statement + conditional use; Prop 2.11(3) descent (separable
  half attempted as kernel probe; divisibility half delimited); Prop 2.1(2b) (2a)
  consequence from ppow laws (probe; delimit if it resists).
- File 2b: gghv_full_ggvstar_ggv6_ggv5_2026-11-06.lean — [GGV6] Thm 7.3/6.4/6.6/Ex 6.7
  (arXiv-numbered pins + F9 conditional chain + Prop 2.5 carried); [GGV5] enumeration
  finiteness corollary from cota + completeness BLOCKED with precise blocker; 4 red-row
  conditional theorems.

## 2026-11-06 ~21:43-21:54 CST -- all three files assembled (verification pending, lock held by legC)

### File 1: gghv_full_ggvstar_2026-11-06.lean (5,668 lines, 43 base items, 9 new theorems)
- Assembled by gen_legF1.py (doc_start fixed: at most one doc comment; the
  MnPair anchor is preceded by two comment blocks, the upper starting with
  plain `/-`, which broke the old loop).
- New: FinitasData, lambda_eq_of_val_zero, finitas_case_of_tprime,
  finitas_one_factor, finitas_of_data (Prop 3.12 CONDITIONAL on the named
  univariate premises), prop329_of_data, prop329_84_of_data,
  remark331_of_data, LLC (Def 3.21 origin part; maximality clause CARRIED),
  llc_imp_pllc, llc_84_excluded_of_data.
- No `sorry`/axiom-token hits except the header comment's prose ("sorryAx").

### File 2a: gghv_full_ggvstar_ggv1_2026-11-06.lean (5,080 lines, 39 base items, 23 new theorems)
- Assembled by gen_legF2a.py.
- Section P (Thm 7.6(5)): numbering RESOLVED from TeX 1401.1784 l.4288 --
  items (1)-(6) + resumed (7)-(8); item (5) IS "q_j | d_i for all i>j>0".
  GGHV main.tex 379 verified verbatim: "q_1 = 4 | d_0, where d_0 = max{d :
  l_{1,0}(P) = R^{md}}" with the [GGV5]-order note. Corrected 8-item def
  divisibilidad8 (base's divisibilidad_stmt is a 4-item conflation: drops
  the j>0 restriction, states q_i ∤ d_i for ALL i, states the q_0 clauses
  unconditionally -- all three corrected). divisibilidad_item5_of_base,
  divisibilidad_gghv_use8 (conditional on the index identification
  1 < i0, GGHV's d_0 = d i0; corner order is the remaining §5 gap).
- Section Q (Prop 2.11(3)): TeX l.962-1005 read; item (3) is a DESCENT
  (base's pavadass_conclusion pins the ASCENT form -- corrected as
  pavadass3_stmt). Chain-rule lemma comp_X_pow_deriv_mul + descended
  equation pavadass_descended_eq (paper: eqq1 descends via
  z p'(z) = k t pbar'(t)); full (3) CONDITIONAL on the multiplicity
  procedure premise hproc (linear-factor argument over an algebraic
  closure, not formalized).
- Section R (Prop 2.1(2b)): TeX l.514 read; (2a) is Joseph Prop 2.1(2),
  cited; (2b) derives from it. PROVED here: expAdd_assoc,
  coeffAt_pmul_assoc (triple-sum argument), ppow_add, pscale_ppow,
  ppow_mul (the three D2 power laws cor74_assembly carries as hypotheses
  -- now KERNEL, which also discharges the Cor 7.4 leg's power-law
  premises), plus congruence lemmas and prop21_two_a_of_b ((2b) => (2a),
  KERNEL modulo prop21_two's hypotheses). (2a) => (2b) BLOCKED with a
  precise blocker: univariate common-power lemma + z-form reduction
  (rational exponents, not in the KTerm layer).

### File 2b: gghv_full_ggvstar_ggv6_ggv5_2026-11-06.lean (1,095 lines, 52 base items, 10 new theorems)
- Assembled by gen_legF2b.py (anchor fix: `theorem redrow_824_conditional`
  has no trailing space -- args start on the next line).
- Section S ([GGV6]): Thm 7.3 = arXiv Thms 3.15+3.25; Prop 6.4 = arXiv
  Prop 3.18; Prop 6.6 = arXiv Prop 3.13; Ex 6.7 = arXiv Example 16
  (content mapping by statement comparison; published-number alignment
  UNVERIFIED). ggv6_discard84_from_thm73 (max=84 from the full Thm 7.3
  statement for F9); ex16_major_roots + ex16_IM (I_M = 3m, PROVED).
  Prop 2.5: NO TeX analogue (arXiv props are named, not numbered);
  published text not on disk; use already proved (prop25_q). CARRIED.
  Thm 7.3 itself (resultant + [X] Thm 4.7) NOT proved: needs the §7
  argument over the pi-root existence theory.
- Section T ([GGV5]): pllc_finite_of_cota (CONDITIONAL on para_la_cota:
  fixed g => finitely many PLLCs with a-b = g). Completeness BLOCKED
  with a precise blocker: (1) pair-to-chain construction (Remark
  `parte inferior`, vdE 10.2.6 + [GGV1] Def 4.3 + Prop 3.12 setup) not
  formalized; (2) PLLC-to-table attribution ([GGV5] §§5-6) not
  re-derived. enum_complete_of_links names exactly these two links.
  NOTE: para_la_cota's own proof uses Prop 3.12 cases (2)/(3), which
  File 1 now discharges one level down (finitas_of_data) -- para_la_cota
  is the next attackable premise (flagged to the parent as follow-up,
  not in this leg's item list).
- Section U (red rows): GGHV §2 citations verified from main.tex 308-313
  + l.295 ([M] only case 64 complete). [GGV4] arXiv §3.5 contains NO
  (4,12) discard -- citation must be the PUBLISHED §3.5 (gap flagged).
  [GGV3] §5 treats (50,75) only; (75,50) by P/Q swap (explicit
  hypothesis). redrow_external + redrow_discard_conditional schema +
  four conditional theorems (412_34, 412_57, 520_23, 520_32 via swap).

### Verification status
- VM lock: legC has held it since before 15:45 CST (age 1521s at 21:54).
  My `vm_lock.sh acquire legF` call is BLOCKED waiting (backgrounded,
  session proc_a295efa22b13); never forced. NO Lean verification has run
  yet on any of the three files. Next: when the lock is acquired, wake
  lean-build-3, wait 60-90 s, scp each file to /tmp, foreground run with
  the exact invocation, fix errors in rounds, axioms audit, record.

## 2026-11-06 ~16:36 CST (22:36 UTC): VM lock acquire #1 TIMED OUT after 3600 s; holder legC
- Acquire started ~15:36 CST (21:36 UTC), default timeout 3600 s, never forced.
- Lock history during the wait: legC held continuously except one release/re-acquire cycle
  (~22:11 UTC, age reset to ~6 min; legC's own `acquire legC 600` loop won the race back).
- Waiters observed: legH, legD, legG, legE, legB, legA (legA itself timed out once at 1800 s
  and re-acquired at 3600 s), legF (this leg). 7-way mkdir race on each release; each
  holder keeps the lock 30+ min (legC's holds: ~42 min, then ~27 min and counting).
- Local work complete before the timeout: all three files assembled, self-reviewed,
  structurally validated (no duplicate decls, all #print axioms names resolve),
  assembler prime-regex bug fixed and files regenerated, verification script
  `run_legF_verify.sh` written (wake + scp + 2 fresh runs per file + log pull).
- Action: re-acquiring once with 3600 s (programme precedent: legA did the same after
  its 1800 s timeout). If acquire #2 also times out, file the interim report to the
  parent (files + UNVERIFIED + blocker + run script) rather than loop indefinitely.

## 2026-11-06 ~17:07 CST (23:07 UTC): Coordinator notice — retrieval update + lock time-slicing
### (1) Retrieval leg COMPLETE; Thm 7.6(5) numbering CORRECTED
- Published [GGV1] §7 text NOT FOUND (15 routes exhausted; hidden_files/phase4/
  retrieval/retrieval_log.md). arXiv v3 TeX (30 May 2016) predates the 19 Sep 2016
  online publication: pre-publication text.
- Numbering: published numbering CANNOT be assumed equal to arXiv TeX numbering.
  Evidence (hidden_files/phase4/retrieval/arxiv_tex_numbering_note.md): the B=16
  theorem is 8.12 in the TeX but cited as "Theorem 8.10" in Valqui/Guccione/
  Guccione, Pro Mathematica 27 (2013) 83-98 and in Valqui & Ramirez, Pro
  Mathematica 33, 65 (2024) 50-67 (2013 citation predates arXiv v1, so it cites
  a 2013 draft; 2024 citation's [1] ambiguous). Retrieval log line 31: the
  published preview matches TeX Theorem 2.6 / §6 topics, but contains NO §7
  content. One further web search by this leg for a citing paper quoting
  "Theorem 7.6" of [GGV1] by number returned nothing.
- CORRECTION: the earlier "Thm 7.6(5) NUMBERING RESOLVED" claim is WITHDRAWN.
  What is pinned is the ARXIV v3 item (5) ("q_j | d_i for i>j>0"). The
  identification "published Thm 7.6(5) = arXiv v3 item (5)" is now CARRIED as
  an explicit premise, not asserted. Section P amended (legF2a_section_P_
  divisibilidad.lean): divisibilidad_gghv_use8 now takes the published content
  as hypothesis h76_5; new companion divisibilidad_gghv_use8_of_arxiv
  instantiates h76_5 with the arXiv item (5) (valid as a statement about the
  arXiv text; its use as the published theorem depends on the carried,
  UNVERIFIED numbering identification). File 2a regenerated: 234,473 bytes,
  24 new theorems (was 23), 55 audit lines, 0 duplicate decls, 0 missing audit
  names, no sorry/axiom. Item 4 verdict is now CONDITIONAL on (a) the numbering
  identification and (b) the corner-index identification (1 < i0, GGHV d_0 =
  d i0) -- the §5 corner theory, still not proved here.
- TITLE CORRECTION (coordinator): Joseph's paper is "The Weyl algebra --
  semisimple and nilpotent elements", Amer. J. Math. 97 (1975), 597-615.
  VERIFIED: the base d1 file already cites it correctly (l.1548) and the wrong
  shorthand "The Jacobian conjecture in dimension 2" appears NOWHERE in this
  leg's files or the base slice. No edit needed.
### (2) VM lock time-slicing (new rule, effective now)
- Leg C has held the lock continuously since 22:11:17Z; Legs A, G, H timed out
  waiting. New rule: acquire PER verification run only, RELEASE immediately
  after that run completes; never hold while writing proofs; max continuous
  hold ~30 min.
- Compliance: this leg holds no lock while writing (acquire #1 timed out at
  3600 s without ever holding; acquire #2 pending since ~22:37 UTC). When
  acquire #2 lands, verification will run ONE pass (run_legF_verify.sh now
  takes a pass argument: `bash run_legF_verify.sh 1`), then the lock is
  released immediately; pass 2 under a fresh acquire, then release. Each file
  already contains its own #print axioms lines, so one pass gives both the
  compile verdict and the axioms audit.

## 2026-11-06 ~17:30 CST (23:30 UTC): Coordinator notice — [GGV5] Prop 6.1 numbering CHECKED (arXiv version)
- Leg A finding (relayed): local [GGV5] TeX §6 is "Program and graphic
  display", NO Proposition 6.1 under that number. CHECKED against the ONLY
  [GGV5] TeX on disk, arXiv:1708.07936 (tex/1708.07936/main.tex, 2045 lines;
  .tar .tex byte-identical; compiled PDF arxiv_1708.07936.pdf agrees):
  §1 Restrictions (l.265); §2 Construction (l.390); §3 Generation (l.1376);
  §4 Program and graphic display (l.1638); §5 Admissible chains v11<=35
  (l.1669); §6 Possible counterexamples max<=150 (l.1792). Preamble
  l.92-94: \newtheorem{theorem}{Theorem}[section], proposition etc. share
  the counter => PER-SECTION numbering. Proposition `caso antisimetrico'
  (l.1874, F_22/(2,3) non-obtainability) is the FIRST and only theorem-like
  environment in §6 => Proposition 6.1 in this TeX's own numbering;
  compiled PDF renders "Proposition 6.1" (pdftotext lines 2810, 2927);
  l.1818: "In Proposition \ref{caso antisimetrico} we show that we can
  discard it." Content matches GGHV's (8,24)/(2,3) citation exactly, and
  the base's prop61_stmt pin (stFace 16 -9, (11/16,1)) is consistent with
  the proof (l_{16,-9}(P_1), l.1880-1892).
- RESULT: [GGV5] Prop 6.1 numbering RESOLVED in the arXiv version
  (Prop 6.1 = caso antisimetrico). DISCREPANCY FLAGGED: Leg A's §6
  identification does not match this file (Program is §4 here); it may
  rest on a different [GGV5] source (e.g. the published version, whose
  section order/numbering is NOT on file). Published-version numbering
  remains UNVERIFIED (same arXiv-vs-published caveat as [GGV1] Thm 7.6);
  the (8,24) discard rests on Prop 6.1 as identified here in the arXiv
  version. Recorded as a comment note in File 2b Section U (U-note);
  File 2b regenerated (see verification below). No new theorems; the four
  red-row discards in Section U do not themselves cite Prop 6.1 (only the
  base's (8,24) row does).

## 2026-11-06 ~17:40 CST (23:40 UTC): VM lock acquire #2 TIMED OUT after 3600 s; holder legE
- Acquire #2 started ~16:38 CST (22:38 UTC), timeout 3600 s, never forced.
- Lock history during the wait: legC held from 22:11:17Z until ~23:08 UTC (then
  released); legB won the race and held ~23:08-~23:25 UTC; legE holds since
  ~23:25 UTC. Time-slicing rule (coordinator, ~17:07 CST) is visibly working:
  holds now cycle at ~20 min instead of legC's ~57-min hold.
- Action: re-acquiring (#3, 3600 s). If #3 also times out, file the interim
  report to the parent (files + UNVERIFIED + blocker + run script) rather
  than loop indefinitely.

## 2026-11-06 ~17:54 CST (23:54 UTC): VM lock acquire #3 LOST WITHOUT RESULT (session dropped)
- Acquire #3 started ~17:40 CST (23:40 UTC), timeout 3600 s. At ~23:53 UTC
  its background session (proc_b6649e343726) vanished: process.poll returned
  "unknown session", process.list no longer shows it, and NO legF acquire
  process survives (ps confirms). The lock still shows legE (acquired
  23:20:33Z, age ~33 min -- past the ~30-min guideline). No acquire/timeout
  output was ever delivered. Likely cause: a runtime/service disruption
  ~23:53 UTC (new legH and legG-runner acquire processes also started at
  23:53, suggesting other legs re-acquired then). I do NOT hold the lock.
- Action: re-acquiring (#4, 3600 s). If #4 also fails to land, file the
  interim report to the parent rather than loop indefinitely.

## 2026-11-07 ~00:08-00:12 UTC: VERIFICATION ROUND 1 (pass 1) — all three files LEAN_EXIT=1
- Lock: acquired by legF 00:08:18 UTC (acquire #4, ~14 min wait), released
  00:11:39 UTC after pass 1 (hold ~3.3 min, within the time-slicing rule).
  Driver: run_legF_verify.sh 1 (wake + scp + one fresh run per file).
  Logs: logs/legF_*_run1.log + *_run1.axioms.txt. Lean 4.34.0,
  `cd ~/repo/JC2D-branches_a_b_c_unified/branches_a_b/lean &&
  lake env lean --root=/tmp /tmp/<file>.lean`. Base slices compiled with
  only warnings (same linter/deprecation warnings as d1); ALL errors are
  in the new sections or the 2b slice boundary.
- File 1 (gghv_full_ggvstar_2026-11-06, 25 s, 16 error lines): ROOT CAUSE
  `λ` used as a binder identifier (47 occurrences in Section N) -- `λ` is
  the lambda token in Lean 4, not a valid identifier. It killed the
  `FinitasData` structure itself, cascading sorryAx into finitas_of_data,
  prop329_of_data, remark331_of_data, llc_84_excluded_of_data (all show
  sorryAx in the axioms audit). `llc_imp_pllc` CLEAN on the permitted
  triple. Independent errors in `lambda_eq_of_val_zero`: (a) the rewrite
  chain `rw [hlam, neg_div, ...]` -- neg_div does not match, since hlam's
  RHS parses as (-X)/σ, not -(X/σ); (b) `exact_mod_cast h` for h11 --
  the cast does not reduce `1 * x + Int.negSucc 0 * y` to `x - y`.
- File 2a (gghv_full_ggvstar_ggv1_2026-11-06, 17 s, 12 error lines):
  CLEAN on the permitted triple/subsets: divisibilidad_gghv_use8,
  divisibilidad_gghv_use8_of_arxiv, expAdd_assoc, expAdd_zero_left,
  sum_map_mul_left', pmul_pscale, pscale_pscale, pscale_congr,
  pmul_congr_left/right, pmul_comm, ppow_congr, ppow_add_kt (renamed,
  see below), pscale_ppow, ppow_mul_kt (renamed). FAILURES: (a)
  comp_X_pow_deriv_mul -- "typeclass instance problem is stuck,
  Semiring ?m" at the `have hXk : Polynomial.X ^ k = ...` TYPE (bare X
  with undetermined ring in a standalone have); (b) coeffAt_pmul_one_left
  -- the `show` jumped past the unreduced singleton outer map
  (List.map ... [((0,0),1)]); (c) coeffAt_pmul_pmul / pmul' -- the proof
  ends after `rw [List.map_map]` with the `∘` unreduced; (d) ppow_add /
  ppow_mul "has already been declared" -- the names clash with an
  IMPORTED declaration (not in the base slice: no ppow_add/ppow_mul
  declaration exists in d1; the clash source is to be identified by
  grepping Mathlib on the VM in round 2); (e) prop21_two_a_of_b --
  "don't know how to synthesize implicit argument σ/ρ": prop21_two's
  ρ σ are implicit and uninferable from hb's bare type; the 5076/5079
  application mismatches cascade from (d).
- File 2b (gghv_full_ggvstar_ggv6_ggv5_2026-11-06, 21 s, 78 error lines):
  ROOT CAUSE (assembler): the base slice started at PiRoot, but the
  PiRoot..end range depends on early definitions (dirVal, Term, stFace,
  enFace, KTerm, coeffAt, StdMnPair, ...) -- "Unknown identifier dirVal"
  (l.197), "Unknown identifier AdmChain" (l.299), cascading sorryAx into
  pllc_finite_of_cota, enum_complete_of_links, redrow_discard_conditional
  and all five red-row theorems. ggv6_discard84_from_thm73 and ex16_IM
  CLEAN on the permitted triple despite the slice failure.
  NOTE: `redrow_520_32_of_23` produced NO axioms line (its declaration
  failed, so #print axioms found no such constant).
### Fixes applied (all local, 2026-11-07 ~00:20 UTC; files regenerated)
- File 1, Section N: `λ` -> `r`, `λ0` -> `r0` (47 occurrences, incl.
  hλ->hr, hλ0mem->hr0mem, etc.); lambda_eq_of_val_zero: rewrite chain
  is now `rw [hlam, div_mul_eq_mul_div, neg_mul]`; h11 now goes through
  an integer `have h2 : (0:ℤ) < Cprev.1 - Cprev.2` proved by omega after
  `simp only [dirVal]`, then `exact_mod_cast h2`.
- File 2a, Section Q: hXk now `(Polynomial.X : Polynomial K) ^ k =
  (Polynomial.X : Polynomial K) * (Polynomial.X : Polynomial K) ^ (k-1)`.
  Section R: coeffAt_pmul_one_left inserts
  `simp only [List.map_singleton, List.sum_singleton]` after
  `rw [coeffAt_pmul_exp]`; coeffAt_pmul_pmul/pmul' append
  `simp only [Function.comp_def]` after `rw [List.map_map]`;
  ppow_add -> ppow_add_kt, ppow_mul -> ppow_mul_kt (declarations +
  references in ppow_mul_kt's proof and prop21_two_a_of_b + header
  comment); prop21_two_a_of_b's hb now
  `prop21_two (ρ := ρ) (σ := σ) termsP termsQ τ μ m n`.
- File 2b assembler: ANCHORS now the full prefix dirVal..redrow_824_conditional
  (gen_legF1.py's 43 anchors + prop61_stmt..redrow_824_conditional); the
  slice-start bug is recorded in the assembler's HEADER. File 2b is now
  5,700 lines (was 1,095), 304 decls, 41 audit lines.
- Structural re-validation after regeneration: all three files 0 duplicate
  decls, 0 missing audit names, no sorry/axiom tokens (only the header
  prose "NO sorryAx"). Remaining λ chars in File 1 (28) are all in base-slice
  COMMENTS (prose λ_P, λ_τ, etc.), which compiled in d1; new sections have 0.
### Round-2 checklist (on the VM, next lock hold)
- Re-run pass 1 for all three files; then pass 2 (determinism repeat).
- Grep the VM Mathlib source for the ppow_add/ppow_mul clash source
  (`.lake/packages/mathlib`: `grep -rn "theorem ppow_add\|def ppow_add"`).
- Record exact axiom lists per new theorem; confirm no sorryAx anywhere.

## 2026-11-07 ~00:37-00:44 UTC: VERIFICATION ROUND 2 (pass 1) — File 2b PASSED, File 2a 1 error left, File 1 structure fix pending
- Lock: acquired by legF 00:37:06 UTC (acquire #5, ~20 min wait), released
  00:44:21 UTC after pass 1 (hold ~7 min). Driver: run_legF_verify.sh 1.
  Lean 4.34.0, same invocation. Logs: logs/legF_*_run1.log (round-2
  versions) + *_run1.axioms.txt.
- File 2b: LEAN_EXIT=0, 0 error lines. ALL new theorems CLEAN on the
  permitted triple: ggv6_discard84_from_thm73, ex16_IM,
  pllc_finite_of_cota, enum_complete_of_links, redrow_discard_conditional,
  redrow_412_34_conditional, redrow_412_57_conditional,
  redrow_520_23_conditional, redrow_520_32_conditional (all [propext,
  Classical.choice, Quot.sound]); redrow_520_32_of_23 on ZERO axioms
  ("does not depend on any axioms" -- the driver's grep pattern
  "depends on axioms" misses the zero-axiom phrasing; audit complete:
  38 depends-lines + 3 zero-axiom lines (dirLt_iff_cross,
  redrow_520_32_of_23, succ_pred5_iff) = 41 audit lines). File 2b DONE
  pending pass 2 (determinism repeat).
- File 2a: LEAN_EXIT=1, 1 error line. Everything CLEAN except the
  pavadass chain: comp_X_pow_deriv_mul fails at the `have hXk` proof --
  after `conv_lhs => rw [<- Nat.sub_add_cancel, pow_add, pow_one]` the
  goal `X^(k-1) * X = X * X^(k-1)` is left unsolved (conv does not close
  non-rfl goals); needs a `mul_comm` step. All other new theorems CLEAN:
  divisibilidad_gghv_use8/_of_arxiv, expAdd_assoc, expAdd_zero_left,
  coeffAt_pmul_one_left, coeffAt_pmul_pmul/pmul', coeffAt_pmul_assoc,
  sum_map_mul_left', pmul_pscale, pscale_pscale, pscale_congr,
  pmul_congr_left/right, pmul_comm, ppow_congr, ppow_add_kt,
  pscale_ppow, ppow_mul_kt, prop21_two_a_of_b.
  FIX: hXk proof now `conv_lhs => rw [...]; rw [mul_comm]`.
- File 1: LEAN_EXIT=1, 14 error lines. lambda_eq_of_val_zero now CLEAN
  ([propext, Classical.choice, Quot.sound]) -- the neg_div removal and
  the omega h11 fixes worked. Remaining failure is ONLY the FinitasData
  structure: `hgcd : Int.gcd ρ σ = 1` errors "argument ρ has type
  ?m.1 → ℤ" (Int.gcd : ℤ → ℤ → ℕ per #check). PROBES (lean-build-3,
  probe_gcd*.lean): a plain def with Int.gcd ρ σ works; a structure
  with `ρ σ : Int` on ONE line + Int.gcd fails; the same structure with
  ρ, σ on SEPARATE lines PASSES; a structure with separate lines and
  `a + b = 0` passes. Root cause: multi-name field lines in a structure
  + Int.gcd (mechanism not fully understood -- the combined-line fields
  elaborate fine for +/< but not for Int.gcd; separate lines work).
  FIX: all multi-name field lines in FinitasData split into separate
  lines (ρ/σ, u/v, Cprev/Cnew, N1/N2, s/t, dr/dg).
- Clash source identified (round-2 checklist): Mathlib
  Mathlib/Algebra/Group/PNatPowAssoc.lean -- `theorem ppow_add
  (k n : ℕ+) (x : M)` (l.57) and `theorem ppow_mul (x : M) (m n : ℕ+)`
  (l.71), about ℕ+-powers. The _kt renames avoid the clash.

## 2026-11-07 ~01:29-01:32 UTC: VERIFICATION ROUND 3 (pass 2) — File 2b CONFIRMED, File 2a CLEAN, File 1 structure fixed / 7 proof-body errors left
- Lock: acquire #6 started ~00:47 UTC (3600 s timeout), ACQUIRED 01:29:08
  UTC after a ~42 min wait (legD held continuously, ~48 min total, past
  the ~30-min rule; never forced/broken). Released 01:32:21 UTC after
  pass 2 (hold ~3.2 min). Driver: run_legF_verify.sh 2. Lean 4.34.0.
  Logs archived: logs/round3/ (round-2 logs in logs/round2/).
- File 2b: LEAN_EXIT=0, 0 error lines -- DETERMINISM REPEAT PASSED.
  All 9 new theorems on the permitted triple in run2, identical to run1.
  File 2b DONE.
- File 2a: LEAN_EXIT=0, 0 error lines -- the mul_comm fix worked.
  comp_X_pow_deriv_mul, pavadass_descended_eq, pavadass3_of_descended,
  prop21_two_a_of_b all [propext, Classical.choice, Quot.sound].
  File 2a DONE (first clean pass; a second clean pass would be ideal
  but is not required -- fold into round 4 if a hold is available).
- File 1: LEAN_EXIT=1, 7 error lines. The field-split fix WORKED: the
  FinitasData structure now elaborates (no more "Function expected at
  FinitasData" / hgcd errors). lambda_eq_of_val_zero CLEAN, llc_imp_pllc
  CLEAN. Remaining errors, all inside finitas_of_data /
  finitas_case_of_tprime / finitas_one_factor / prop329_of_data:
  (a) 5401 type mismatch: h2 stated `< (vartheta)*u` but the goal has
  `< u*(vartheta)` (mul_comm); (b) 5405 `Int.toNat_pos` is NOT a
  constant in this Mathlib; (c) 5456 omega fails on finitas_one_factor
  (nonlinear atom (i-1)*dr not shared between h4 and hdg); (d) 5474
  `Int.dvd_gcd` is the NAT-divisor version (its conclusion is
  `?k | Int.gcd (up k) ?n`, unusable for an Int divisor D.rho -- the
  produced type `?m.149 | (up ?m.149).gcd ?m.148` proves it); (e) 5478
  `Int.dvd_one` is NOT a constant; (f) 5593 prop329_of_data rewrites
  hCp/hCn before hN1/hN2, so `N1_of s.Cprev s.Cnew` is already gone
  (now `N1_of D.Cprev D.Cnew`) when `rw [<- hN1]` runs.
  FIXES APPLIED (local, regenerated File 1, 5686 lines): (a) h2 restated
  with `D.u * (vartheta:Int)` + `rw [mul_comm D.u (vartheta:Int)]`
  inside; (b) ht'Npos proved by casting through ht'N (no toNat lemma);
  (c) finitas_one_factor: explicit h5 (h4 rewritten into hdg) then
  omega; (d)+(e) case (1): natAbs route -- Nat.dvd_gcd +
  Int.natAbs_dvd_natAbs + rw [D.hgcd] + Nat.dvd_one +
  Int.natAbs_eq_natAbs_iff, giving D.rho = 1 directly (no Int.dvd_gcd,
  no Int.dvd_one); (f) prop329_of_data rewrite order fixed to
  [<- hrho, <- hsigma, <- hN1, <- hN2, <- hCp, <- hCn].
  NOTE on (d): the natAbs route relies on Int.gcd being definitionally
  Nat.gcd of natAbs (have hnat' : ... := hnat tests the defeq); if the
  round-4 log shows a mismatch there, probe #check @Int.dvd_gcd /
  @Int.gcd_dvd_left instead.

## 2026-11-07 ~01:33-01:38 UTC: VERIFICATION ROUND 4 (pass 1) — ALL THREE FILES PASS, 0 ERRORS
- Lock: acquire #7 ACQUIRED IMMEDIATELY ~01:33 UTC (no wait); released
  01:38:06 UTC (hold ~5 min). Driver: run_legF_verify.sh 1. Lean 4.34.0.
  Logs archived: logs/round4/.
- File 1: LEAN_EXIT=0, 0 error lines. ALL 9 new theorems CLEAN on the
  permitted triple [propext, Classical.choice, Quot.sound]:
  lambda_eq_of_val_zero, finitas_case_of_tprime, finitas_one_factor,
  finitas_of_data, prop329_of_data, prop329_84_of_data,
  remark331_of_data, llc_imp_pllc, llc_84_excluded_of_data. NO sorryAx
  anywhere in the round-4 run1 axioms (38 depends-lines + 2 zero-axiom
  base lines = 40 audit lines). The natAbs gcd route worked (Int.gcd
  is definitionally Nat.gcd of natAbs, as the `have hnat'` defeq test
  passed). File 1 md5 5db7b34420dcf8d111223e79aaed3f44, 5686 lines.
- File 2a: LEAN_EXIT=0, 0 error lines -- SECOND clean pass. 52
  depends-lines + 3 zero-axiom lines (incl. divisibilidad_item5_of_base
  on zero axioms) = 55 audits. File 2a md5
  2e61236431142905b92d09252d1251f9, 5119 lines.
- File 2b: LEAN_EXIT=0, 0 error lines, run1 wall 17 s -- THIRD clean
  pass. 38 depends-lines + 3 zero-axiom lines (incl.
  redrow_520_32_of_23 on zero axioms) = 41 audits. File 2b md5
  159527f8326bf32e87276651054c5fcf, 5700 lines.
- REMAINING: one determinism repeat (pass 2) for File 1, whose only
  clean pass so far is this round-4 run1. Round 5 will run pass 2 for
  all three files.

## 2026-11-07 ~01:39-01:41 UTC: VERIFICATION ROUND 5 (pass 2) — DETERMINISM REPEAT PASSED, ALL FILES DONE
- Lock: acquire #8 ACQUIRED IMMEDIATELY ~01:39 UTC; released 01:41:28
  UTC (hold ~2.5 min). Driver: run_legF_verify.sh 2. Lean 4.34.0.
  Logs archived: logs/round5/.
- ALL THREE FILES: LEAN_EXIT=0, 0 error lines. NO sorryAx in any
  round-5 run2 axioms file. Spot checks: finitas_of_data, prop329_of_data
  [propext, Classical.choice, Quot.sound]; comp_X_pow_deriv_mul,
  pavadass3_of_descended [propext, Classical.choice, Quot.sound];
  ggv6_discard84_from_thm73, redrow_412_34_conditional,
  redrow_412_57_conditional [propext, Classical.choice, Quot.sound].
- Clean-pass tally: File 1: 2 (round 4 run1, round 5 run2). File 2a: 3
  (round 3 run2, round 4 run1, round 5 run2). File 2b: 4 (round 2 run1,
  round 3 run2, round 4 run1, round 5 run2).
- LEG F COMPLETE. Final files: gghv_full_ggvstar_2026-11-06.lean
  (5686 lines, md5 5db7b34420dcf8d111223e79aaed3f44), gghv_full_ggvstar_ggv1_2026-11-06.lean
  (5119 lines, md5 2e61236431142905b92d09252d1251f9), gghv_full_ggvstar_ggv6_ggv5_2026-11-06.lean
  (5700 lines, md5 159527f8326bf32e87276651054c5fcf). NO repo commits
  (per brief; incorporation only after the validation gate).
