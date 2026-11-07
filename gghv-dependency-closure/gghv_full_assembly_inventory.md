# GGHV full-proof assembly inventory — definitive per-item verdict record

**CLAIM:** This file is the definitive per-item verdict record for the
Phase 4 full-proof programme (prove the GGHV paper, arXiv:2204.14178v1, in
full in Lean 4), assembled from the nine completed proof legs (A–H +
retrieval) plus the assembly-stage Lean work. Every verdict below is
grounded in a leg file + log read on disk by the assembly agent (not from
the map alone); where an axiom list is quoted, the source log is named.
**STATUS:** Written 2026-11-06/07 by the assembly agent. Assembly Lean
run + R8 axiom print: DONE 2026-11-07 ~02:08 UTC (lean-build-3, Lean
4.34.0): assembly FULL_EXIT=0 (135 s, 0 errors), AXIOMS_EXIT=0 (50 s,
0 errors, repeat run byte-identical log), R8 print rc=0 (15 s, 0 errors);
all axiom lists recorded in §0/§2 and §10; no sorryAx. Laurent fold-in
pass DONE 2026-11-07 ~03:37 UTC (successor coordinator): fragment
`~/workspace/research/tooling/phase4_laurent/gghv_full_laurent_2026-11-06.lean`
(1,705 lines) verified FINAL_FULL_RC=0, 0 errors, ~10 s, Lean 4.34.0;
full-file axioms audit AX_FULL_RC=0, 87 theorems, sorryAx 0 (log
`laurent_log.md`). E11/E19/E20/E23 updated in §1/§7 with the fragment's
verdicts; see §7 for the fold-in record and the ValAxioms diagnosis.

## Honest headline

**The paper is NOT proved unconditionally.** No numbered environment
(theorem / proposition / corollary) is fully proved unconditionally, and
Theorem 2.1 is NOT unconditional. The programme's position after all nine
legs + assembly:

- **Theorem 2.1 — CONDITIONAL** (`theorem21_minimal_v2`, assembly file,
  [propext, Classical.choice, Quot.sound] — assembly run 2026-11-07,
  FULL_EXIT=0 135 s, AXIOMS_EXIT=0 50 s, 0 errors, no sorryAx) from the
  20-field `MinimalPremises2`. Leg A's fields 9–10 are REFINED into named
  chains (see §0), not unconditionally discharged.
- **Prop 3.12 ([GGV2]) — CONDITIONAL** (`finitas_of_data`, Leg F File 1,
  [triple]) on the named `FinitasData` premises (the paper's univariate
  lemmas). Leg B can consume it with those premises named.
- **Prop 2.1(2a)→(2b) — BLOCKED** (univariate common-power lemma +
  z-form reduction; Leg F).
- **[GGV5] enumeration completeness — BLOCKED** (pair-to-chain construction
  + PLLC-to-table attribution; Leg F `enum_complete_of_links` names the
  two open links `hchain`/`hattrib`).
- **[GGV6] Thm 7.3 — NOT PROVED as a theorem** (combination proved in the
  base; the theorem needs the §7 argument over the π-root existence
  theory; Leg F). The max=84 discard from the full Thm 7.3 statement is
  CONDITIONAL (`ggv6_discard84_from_thm73`, [triple]).
- **Four red rows — CONDITIONAL** (Leg F, all four [triple], each on its
  named external discard + connection hypothesis).
- **Remark 3.31 — CONDITIONAL** (`remark331_of_data`, [triple]); the
  (10,25)/(14,35) forcing is CARRIED (paper: "without a formal proof").
- **E11/E19/E20/E23 — Laurent fold-in DONE** (see §7): E11 PARTIAL
  (generic sqrt-series lemma KERNEL; §5 instance NOT separately applied
  — instance application remains open (G1 correction F2); F CONDITIONAL
  on `GGV1Inputs`; §5 (b_k)/(c_k) bounds NOT discharged — min-degree
  ValCore on RatFunc K missing); E19 PARTIAL (§6 existence + (b_k)/(c_k) bounds
  KERNEL via `laurent_series_discharge_s6`; F CONDITIONAL on
  `GGV1InputsLp` + unit); E20 KERNEL modulo Ptcoef input data
  (`exists_tilde` / `tilde_discharge`); E23 PARTIAL (monomial bracket +
  ODE uniqueness KERNEL; series-bracket reduction CONDITIONAL on `hdeg`).
  **ValAxioms diagnosis (KERNEL):** Leg D's `ValAxioms` structure is
  uninstantiable — unconditional `mul` forces w ≡ 0
  (`ValAxiomsOrig.forces_zero`, [propext, Quot.sound]) — so Leg D's
  `e19_bound_step_21/_1m1/finite_bounds` can never be instantiated with
  v_{2,1}/v_{1,−1}; the usable bound steps are the fragment's `valcore_*`
  versions (KERNEL from `ValCore`).
- **Discharged in this programme:** the D2 power laws are now PROVED
  (Leg F File 2a §R: `coeffAt_pmul_assoc` [propext, Quot.sound];
  `ppow_add_kt`, `ppow_mul_kt` [triple] — verified present at lines
  4939/5020/5050 of `gghv_full_ggvstar_ggv1_2026-11-06.lean`),
  discharging the Cor 7.4 leg's power-law premises. `para_la_cota` is the next attackable premise
  (it would discharge `cota_of_chain`'s premise and hence the finiteness
  corollary's premise; its proof uses Prop 3.12 cases (2)/(3), which
  File 1 now discharges one level down).
- **Fully proved (kernel, narrow claims only):** the three elimination
  sub-cases inside E7 (Prop 4.3) — (a)/(b) by branches-(a),(b)
  `main_theorem`, (c) by `branch_c_eliminated` (both kernel, permitted
  triple, filed as tracked GradeA modules, commit 7e4db07f) — plus the
  kernel arithmetic / elimination / separability pieces listed per item
  below. These do not make any numbered environment unconditional.

## Verdict vocabulary (as used below)

- **KERNEL** — proved by the Lean kernel; axiom list quoted (a subset of
  the permitted triple [propext, Classical.choice, Quot.sound], or zero)
  with file + line; `sorryAx` absent (grep-verified per leg).
- **CONDITIONAL** — proved from explicit named premises; the premises are
  named in the entry and are part of the theorem statement.
- **BLOCKED** — not formalized; the precise blocker is named.
- **I1** — independently recomputed by a second tool (Singular/SymPy/
  python-flint); NOT a kernel proof.
- **PARTIAL** — some named part KERNEL/CONDITIONAL, some named part
  BLOCKED/CONDITIONAL; the split is stated exactly.

Permitted triple throughout: [propext, Classical.choice, Quot.sound].
`[triple]` below abbreviates it. Zero-axiom is written `[]`.

## §0. The assembly result — fields 9–10 refined

Assembly file:
`~/workspace/research/tooling/phase4_assembly/gghv_full_assembly_2026-11-06.lean`
(3,165 lines = header + Leg A body + Leg B body + Leg C body + 256-line
assembly section; `import Mathlib` only; self-contained; no leg file
imported; no `sorry`, no `axiom` declarations, no `admit` — grep-verified
locally).

- `MinimalPremises2` (20 fields): Leg A's fields 1–8 and 11 unchanged;
  fields 9–10 replaced by the refined chains below.
- `link_924_derived` / `link_927_derived`: Leg A's opaque links PROVED
  from the refined chains by kernel composition (bridge + link + kernel
  B/C theorems + ex falso). Axiom lists from the assembly run
  (2026-11-07, lean-build-3): both [propext, Classical.choice,
  Quot.sound]. `prop42_shape_of` [triple], `prop41_shape_of` [propext,
  Quot.sound]. Re-verified in the same run: `prop41_conditional`
  [propext, Quot.sound], `prop42_conditional` [triple],
  `prop43_conditional` [propext, Quot.sound], `prop44_conditional`
  [triple], `thm51_conditional` [triple], `cor52_conditional` [] —
  all matching the legs' own reported lists.
- `theorem21_minimal_v2` / `theorem21_conditional_minimal_v2`: Theorem 2.1
  from `MinimalPremises2`. Axiom list from the assembly run:
  [propext, Classical.choice, Quot.sound].
- What the refinement discharged: the §4 vertex-level reductions are now
  KERNEL given their premise structures (Leg B), and the §5 endgame is
  now KERNEL given the §5 data link (Leg C). What remains carried, now
  with precise names (see the per-field table):

| Leg A field | Assembly status | Carried now (named) |
|---|---|---|
| 1–5 red rows | CARRIED, unchanged | [GGV4] §3.5, [M], [H], [GGV3] §5, [GGV5] Prop 6.1 — Leg F R20 CONDITIONAL (§3) |
| 6 link_84 | CARRIED, unchanged | [GGV6] Thm 7.3 + π-root machinery — Leg F: NOT PROVED as a theorem |
| 7 prop329 | CARRIED, unchanged | [GGV2] Prop 3.29 — Leg F: CONDITIONAL on FinitasData premises |
| 8 link_120 | CARRIED, unchanged | last-possible-corner computation + Thm 7.6(5) numbering — Leg F CONDITIONAL |
| 9 link_924 | REFINED | `prem42` (Prop42Premises: HybridSlip924, pred_sound [Prop 3.12], pred_ne_25 [[vdE] 10.2.6], h312_2 [Prop 3.12(2)]); `bridge924` (polynomial lift, Laurent layer R14); `link51_924` (§5 data link) |
| 10 link_927 | REFINED | `prem41` (Prop41Premises); `bridge927` (Cor 5.7 Succ/ψ step + polynomial lift); `link52_927` (Cor 7.2 / Thm 2.6 / Def 4.3 / ψ); `link51_927` (§5 data link) |
| 11 enum_complete | CARRIED, unchanged | [GGV5] enumeration completeness — Leg F: BLOCKED |

Why fields 9–10 could NOT be unconditionally discharged: Leg B's
conditionals are vertex-list level only (Leg B verdict table: "the
polynomial-level statement is NOT claimed (Laurent layer, R14)"), so the
step from a row counterexample to a Thm-5.1-shaped polynomial
counterexample — the bridge — is proved by no leg and stays carried.
Leg C's `thm51_conditional` is kernel only given its link hypothesis; the
link (the §5 data derivation: rescaling inputs, coefficient-system
derivation, 9-equation derivation, [GGV1] Props 1.13/2.1) is the open
part and stays carried. The assembly therefore refines the opaque links
into named sub-premises + kernel composition; it does not eliminate them.

## §1. Per-item verdicts E1–E23 (paper order)

| Item | Verdict | Key theorem(s) / file |
|---|---|---|
| E1 Thm 2.1 | CONDITIONAL | `theorem21_minimal_v2` [triple] (assembly run 2026-11-07: FULL_EXIT=0, 135 s) |
| E2 §2 table | KERNEL (table) / CONDITIONAL (red rows) / BLOCKED (completeness) | `gghv_table_full` [] (Leg A); red rows §3; completeness Leg F BLOCKED |
| E3 §3 max=120 | KERNEL arithmetic + CONDITIONAL discard | `discard_120_kernel_data`, `discard_120_row` [] (Leg A); `prop329_of_data` [triple] (Leg F) |
| E4 §3 max=84 | KERNEL arithmetic + CONDITIONAL discard | `discard_84_kernel_data`, `discard_84_row` [] (Leg A); `ggv6_discard84_from_thm73` [triple] (Leg F) |
| E5 Prop 4.1 (9,27) | CONDITIONAL | `prop41_conditional` [propext, Quot.sound] (Leg B l.407) |
| E6 Prop 4.2 (9,24) | CONDITIONAL | `prop42_conditional` [triple] (Leg B l.753) |
| E7 Prop 4.3 (8,28) | CONDITIONAL (reduction); KERNEL (eliminations) | `prop43_conditional` [propext, Quot.sound] (Leg B l.1088); eliminations kernel (branches a/b + branch_c) |
| E8 Prop 4.4 (7,21) | CONDITIONAL | `prop44_conditional` [triple] (Leg B l.1315) |
| E9 Algorithm PSP | KERNEL (implementation + output); correctness CONDITIONAL | `psp_183` [propext] (Leg B l.494); correctness = [GGV2] Prop 3.12 (Leg F CONDITIONAL) |
| E10 Thm 5.1 | CONDITIONAL | `thm51_conditional` [triple] (Leg C l.793) |
| E11 calculo de C (§5) | PARTIAL (fold-in §7) | Generic sqrt-series lemma KERNEL (`exists_sqrt_series`, fragment); §5 instance NOT separately applied; F CONDITIONAL (`f_discharge` on `GGV1Inputs`); §5 bounds NOT discharged |
| E12 Remark (§5) | PARTIAL | `e12_remark_conditional` [triple] (Leg C l.500); "still satisfy Thm 5.1" conditional on hJac/hFace |
| E13 f separable | KERNEL | `e13_f_separable`, `e13_bezout` [triple] (Leg C); I1 second-tool (see §1 detail) |
| E14 D_k ∈ K[y] (§5) | CONDITIONAL | `e14_d_mem` [triple] (Leg C l.357); convolution identity carried |
| E15 valuations −39/51 | KERNEL arithmetic + CONDITIONAL bounds | `e15_bound_neg13`/`e15_bound_17` [propext, Quot.sound] (Leg C) |
| E16 9-eq system (§5) | KERNEL (elimination only); derivation OPEN | `e16_principal` [triple], `e16_cert` [propext, Quot.sound] (Leg C); I1 Gröbner/resultant |
| E17 Cor 5.2 | CONDITIONAL | `cor52_conditional` [] (Leg C l.831) |
| E18 Thm 6.1 | CONDITIONAL | `s6_theorem61` [triple] (Leg D l.1577) |
| E19 calculo de C para 7 | PARTIAL (fold-in §7) | §6 existence + bounds KERNEL (`laurent_series_discharge_s6`, fragment); F CONDITIONAL (`f_discharge_lp_s6` on `GGV1InputsLp` + unit) |
| E20 Remark (§6) | KERNEL modulo Ptcoef input data (fold-in §7) | `exists_tilde` / `tilde_discharge` (fragment); `e20_assembly` [propext, Quot.sound] (Leg D l.498) |
| E21 D_k ∈ K[y] (§6) | CONDITIONAL (kernel modulo named inputs) | `e21_membership` [triple] (Leg D l.1455) |
| E22 9-eq system (§6) | KERNEL (elimination/displays only); derivation OPEN | `s6_principal_eq` [triple] (Leg D l.954); k=2 + non-square KERNEL |
| E23 F_{−4} = (1/2)y^{−1} | PARTIAL (fold-in §7) | `e23_ode_unique` [triple] (Leg D l.383); series-bracket reduction CONDITIONAL on `hdeg` (`bracket_reduction_discharge`, fragment) |

### E1 — Theorem 2.1 (§2). CONDITIONAL.
`theorem21_minimal_v2` [propext, Classical.choice, Quot.sound]
(assembly file; assembly run 2026-11-07 ~02:08 UTC: FULL_EXIT=0, 135 s,
0 errors; AXIOMS_EXIT=0, 50 s, 0 errors) from the 20-field
`MinimalPremises2` (§0). The (7,21) row is eliminated
via §3 (`discard_721_via_sec3`, [] in Leg A), so the §6 route is not on
the minimal list. No `theorem21_unconditional` exists. The row-vs-degree-
pair correction stands: eliminating the (9,27) ROW does not eliminate the
degree PAIR (72,108) — the (8,28) row gives (72,108) only after the P↔Q
swap (`pair_72_108_from_828_swapped`, Leg A).

### E2 — §2 table of 10 cases. KERNEL (table) / CONDITIONAL (red rows) / BLOCKED (completeness).
- Table arithmetic KERNEL: `gghv_table_full` [] — 10 rows, degree pairs,
  max degrees, bound <125, pairMax = maxDeg (Leg A;
  `legA_axioms.log`). `survivors_exact` [propext]; `pair_72_108_unique`
  []; `pair_108_72_unique` (Leg A). I1: Singular table recompute
  (Leg G runner, R21 I1 PASS: BAD_ROWS = 0; survivors (108,72),(66,99),
  (72,108); GCD_72_108 = 36).
- Red rows CONDITIONAL — see §3 (Leg F, all four [triple]).
- Table completeness BLOCKED — [GGV5] enumeration completeness, Leg F
  `enum_complete_of_links` [triple] on the two OPEN links `hchain`
  (pair-to-chain construction) and `hattrib` (PLLC-to-table attribution).

### E3 — §3 discard of max=120. KERNEL arithmetic + CONDITIONAL discard.
Kernel (Leg A): `v_120_direction`, `v_120_en_unique`, `d0_bound`,
`d0_forced_4`, `corner_120_exponents`, packaged in
`discard_120_kernel_data`; `discard_120_row` [] (conditional on
`prop329` + `link_120`). Leg F: `prop329_of_data` [triple]
(`gghv_full_ggvstar_2026-11-06.lean` l.5593) — [GGV2] Prop 3.29
CONDITIONAL on FinitasData-existence per AdmStep + hSE (starting-vs-end
instance); `llc_imp_pllc` [triple] (l.5658) — LLC = PLLC + pair-origin
condition (base's "Def 3.21 = AdmChain + PLLC" CORRECTED; maximality
clause CARRIED, named explicitly); `llc_84_excluded_of_data` [triple].
Carried: [GGV1] Thm 7.6(5) — CONDITIONAL (`divisibilidad_gghv_use8`
[triple], File 2a l.4714) on (a) the numbering identification `h76_5`
(published numbering UNVERIFIED — published §7 text NOT FOUND,
retrieval leg; §8 precedent shows numbering can shift, so arXiv ≠
published is not assumed) and (b) the corner-index identification;
[GGV2] Remark 3.31 — CONDITIONAL (`remark331_of_data` [triple],
l.5625), (10,25)/(14,35) forcing CARRIED; the last-possible-corner
computation itself (Leg F).

### E4 — §3 discard of max=84. KERNEL arithmetic + CONDITIONAL discard.
Kernel (Leg A): `im_84_general` (I_M(j)=2(j+2) for every j),
`im_84_at_j0` (=4), `im_minor_84_rat` (=5), `minor_delta_step`,
`factor_count_84`, packaged in `discard_84_kernel_data`;
`discard_84_row` [] (conditional on `link_84`). Leg F:
`ggv6_discard84_from_thm73` [triple]
(`gghv_full_ggvstar_ggv6_ggv5_2026-11-06.lean` l.5458) — the max=84
discard from the full Thm 7.3 statement (F₉ family), CONDITIONAL on
Thm 7.3 itself; `ex16_IM` [triple] KERNEL-clean (I_M = 3m, Example 16).
[GGV6] Thm 7.3 itself: NOT PROVED as a theorem — the combination is
proved in the base; the theorem needs the [GGV6] §7 argument over the
π-root existence theory (resultant computation for the major equality;
minor inequality via [X] Thm 4.7). Carried: [GGV1] Prop 2.11(3) —
CONDITIONAL (`pavadass3_of_descended` [triple], File 2a l.4832, modulo
hproc multiplicity-procedure premise; direction CORRECTED: item (3) is a
DESCENT, not the ascent the base pinned); [GGV6] Props 6.4/6.6, Ex 6.7
(instances proved in base; proofs carried); π-root machinery.
Second proof of the same elimination: Theorem 6.1 / E18.

### E5 — Proposition 4.1, Case (9,27). CONDITIONAL.
`prop41_conditional` [propext, Quot.sound] (Leg B,
`gghv_full_s4_2026-11-06.lean` l.407). Carried premises
(`Prop41Premises`, l.360): Cor 7.4 edge step, φ₃ edge step, Prop 8.2
applied instance (afterPhi2/afterPhi3 lists, k-inequalities, en/st/dir
fields). Kernel inside: sieve (`sieve_table_927` [propext] =
[(1,1),(5,2),(13,5)]; (1,1) PASSES the divisibility and is excluded by
the diagonal argument, not the sieve), k=1 (`esquina_k1_927`), φ-maps
(`phi3_927P/Q`), Jacobian-factor pair (`phiJacPair_3` [] = (−1,1)).
Polynomial-level statement NOT claimed (Laurent layer R14).

### E6 — Proposition 4.2, Case (9,24). CONDITIONAL.
`prop42_conditional` [triple] (Leg B l.753). Carried premises
(`Prop42Premises`, l.676, parameter `HybridSlip924`): [GGV2] Prop 3.12
soundness (`pred_sound`), [vdE] Prop 10.2.6 (`pred_ne_25`), Prop 3.12(2)
(`h312_2`: 6 ∈ r3mults), hybrid-vs-slip (`hybrid_slip`), φ₂ corners,
edge transform, (a′,b′) dichotomy. Prop 3.12 itself: CONDITIONAL
(`finitas_of_data` [triple], Leg F File 1 l.5469) on the named
`FinitasData` premises (Lemma `factores en jacobiano` eq2, Lemma
`maximo grado`, [GGV1] Prop 1.13, Remark `gap`, [GGV1] Prop 2.4(1)
dichotomy) — Leg B can consume `finitas_of_data` with those premises
named; the FinitasData premises themselves are carried, not proved.
Kernel inside: PSP algorithm output, three-sub-case φ-maps, Jacobian
factor (`phiJacPair_3` []). Polynomial-level statement NOT claimed
(Laurent layer R14). Hybrid-vs-slip: OPEN (published §7 NOT FOUND;
Leg E R16 kernel arithmetic only — `hybrid_slot_249/288/927/721`
[triple] — both readings stated, question stays open).

### E7 — Proposition 4.3, Case (8,28). CONDITIONAL (reduction); KERNEL (eliminations).
Reduction: `prop43_conditional` [propext, Quot.sound] (Leg B l.1088).
Carried premises (`Prop43Premises`, l.982, parameters `HybridSlip828`,
`Prop312_828`): [GGV6] Prop 2.5 (`pred_mem`), [GGV2] Prop 3.12 setting
(`prop312_holds`), hybrid-vs-slip (`HybridSlip828`), k=2 exclusion
(`k_ne2`), lower-side shapes, Succ determination
(`succP`/`succQ` = (−2,7)). [GGV6] Prop 2.5: CARRIED (no TeX analogue
in arXiv §1; use proved as `prop25_q`). Finding (Leg B, verified
against the φ-images): E7's end assignment is SWAPPED relative to E5 —
the paper sets (en(Q),en(P)) = ((2,1),(−1,0)).
Eliminations — KERNEL (the only fully-covered claims in the paper):
item (2) (cases (a),(b)) by branches-(a),(b) `main_theorem` (permitted
triple); item (1) (case (c)) by `branch_c_eliminated` (no hypotheses,
permitted triple) via `challenge_target` + `bridge_Fpoly`, filed as
tracked GradeA modules (commit 7e4db07f, fork main, re-verified on
lean-build-3). Explicit maximal minor for the branch-(c) matrix: see §4.

### E8 — Proposition 4.4, Case (7,21). CONDITIONAL.
`prop44_conditional` [triple] (Leg B l.1315). Carried premises
(`Prop44Premises`, l.1296): Cor 7.4 (q=7) φ₂-cut link only
(afterPhi1 list + phi2cut). Kernel inside: ℓ-normalisation re-pinned
with attribution from d1_cor74 (`ell721_normalization` [propext,
Quot.sound]); φ₃ map + scaling (`phi3_721`, `scale2_721`/`scale3_721`).
INVENTORY CORRECTION (coordinator-verified by grep): the statement
inventory said the (7,21) F-side instance is "not yet a `Cor74Data`
bundle" — WRONG as of the filed Phase 1 record: `d1_cor74_2026-11-05.lean`
ALREADY defines `cor74_721` (line 3627: dir (7,−2), ab (7,21), p 5,
q 7, enF (5,15)) with `cor74_721_cond3`, `cor74_721_exp_P/Q`, and proves
`ell721_normalization`. E8's uncovered part is therefore only the
φ-chain, not the bundle. The (7,21) row's elimination runs through E18
(§6) — and, independently, through §3 (E4).

### E9 — Algorithm PossibleStartingPoints. KERNEL (implementation + output); correctness CONDITIONAL.
`psp_183` [propext] (Leg B l.494): output [(2,0),(3,1),(4,1),(6,2)];
`psp_183_dirs` — output directions {(1,−2),(2,−5)}. `dir` is the
primitive PERPENDICULAR direction (v/g, −u/g), verified against the
paper's conclusion. Correctness (the output directions contain
Pred_P(1,0)) is [GGV2] Prop 3.12 — CONDITIONAL via `finitas_of_data`
(Leg F), NOT claimed by Leg B.

### E10 — Theorem 5.1 (`teorema impossible`, §5). CONDITIONAL.
`thm51_conditional` [triple] (Leg C,
`gghv_full_s5_2026-11-06.lean` l.793). Carried: the link hypothesis —
§5 rescaling inputs, coefficient-system derivation, 9-equation
derivation, [GGV1] Props 1.13/2.1 (Prop 1.13 both directions and
Prop 2.1(1) are kernel/conditional layers in Leg F File 2a; Prop 2.1(2b)
is carried — see R18 below). Kernel inside: `e10_clearing` [propext],
`e10_rescaling` [triple], `e10_endgame` [triple] (the nueva ecuacion
principal + degree endgame, k≥8 vs k≤7). I1: §5 elimination by
resultants + Gröbner (Phase 1, re-run by Leg G runner — see R23).
Covers BOTH the (9,24) and the (9,27) shapes in one statement.

### E11 — Proposition `calculo de C` (§5). PARTIAL (Laurent fold-in DONE 2026-11-07).
C-existence: generic sqrt-series lemma KERNEL — `exists_sqrt_series`
[triple] (fragment l.868; over any CommRing with explicit `inv2u0`).
Its only applications in the fragment are the §6 instance (l.940) and
the tilde instance (l.1482); the §5 instance (A := RatFunc K, u0 := C₃
= y⁸(y+1)) is NOT separately applied — instance application remains
open. (G1 correction F2.) F CONDITIONAL via `f_discharge`
(fragment l.1623) on the named bundle `GGV1Inputs` (cancel + leading at
coefficient level = the [GGV3] §1 α-choice + [GGV1] Prop 1.13/2.1
content). §5 (b_k)/(c_k) bounds NOT discharged — precise remainder:
the fragment has no min-degree ValCore on RatFunc K
(RatFunc.intDegree is max-degree only; `−intDegree(r⁻¹) =
intDegree(r)` does not give min-degree), so `valcore_finite_bounds`
cannot be instantiated for the §5 (1,−1) side. Kernel pieces proved
(Leg C): `e11_recursion_step` [triple] (corrected sign: C_{3−k} :=
(1/(2C₃))(P_{6−k} − Σ)); `e11_recursion_sign_slip` [triple] (the
paper's as-printed recursion ⇒ −P_{6−k}). Paper slip: §5 recursion
sign error (TeX ~1462–1465) — see §9. Feeds E14/E15/E10 (their
conditional bounds carry E11(3)/(4) + the x-monomial valuations as
hypotheses; E15's bounds stand — see E15).

### E12 — Remark (§5). PARTIAL.
Kernel identities: `e12_Qtilde`, `e12_Ctilde_sq` (Leg C); conditional
assembly `e12_remark_conditional` [triple] (Leg C l.500). "Still satisfy
Thm 5.1" is CONDITIONAL on bracket/face preservation (`hJac`/`hFace`).
Full tilde-series existence is KERNEL modulo Ptcoef input data
(fragment `exists_tilde`, fold-in §7).

### E13 — Proposition `f` separable (§5). KERNEL.
`e13_f_separable` [triple], `e13_bezout` [triple] (U·f+V·f′=1), plus
`e13_ode` (differential equation), `e13_f_factor` (f = y(y+1)g),
`e13_f_natDegree` (=6), `e13_g_natDegree` (=4), `e13_g_ne_zero_at_zero`
/`_neg_one` (Leg C, `gghv_full_s5_2026-11-06.lean` ll.143–262).
Second tool (Leg G runner, lean-build-3): Singular 4.3.1 rc=0 —
ODE_DIFF = 0 both forms, DEG_F1 = 15, DEG_F = 6, DEG_G = 4, GCD_F_FP = 1,
GCD_G_GP = 1, bracket identities 0 — I1 PASS on the mathematical content.
Caveats (logged, not hidden): the filed SymPy script exits rc=1 with
defects DECOMPOSED (21/27 PASS) — 2× gcd FAILs are Poly-domain artifacts
(value is 1); 1× bracket FAIL is a script error in BOTH scripts (factor
2 — they compare [x³C₃, x⁵f₁] to x⁷(6C₃f₁′−10C₃′f₁), but the paper's
identity is x⁷C₃² = 2[x³C₃, x⁵f₁]; the correct identities PASS in both
tools — the paper is right, the check is wrong); 3× dsolve FAILs are a
SymPy 1.14.0 limitation (Piecewise/zoo/nan mess) — ODE uniqueness among
polynomials via dsolve is NOT ESTABLISHED (not refuted). Script
corrections needed (not done by the runner).

### E14 — Proposition `D_k ∈ K[y]` (§5). CONDITIONAL.
`e14_d_mem` [triple] (Leg C l.357) — strong induction in a subring,
kernel modulo the carried convolution identity. Paper slip (found by
Leg D, applies to §5 too): the printed D_k formula OMITS the 1/2 on the
sum in both §5 (E14) and §6 (E21); harmless for membership; Leg D's
`e21` identity uses the CORRECTED factor 1/2 (see §9). Also: E21's proof
writes `C_3` in the `D_j D_{k+3−j}` identity where `y` is meant (§9).

### E15 — Proposition valuations of D (§5). KERNEL arithmetic + CONDITIONAL bounds.
Kernel arithmetic: `e15_arith_neg13`, `e15_arith_17` (both by `ring`,
Leg C ll.430–433). Conditional bounds: `e15_bound_neg13` /
`e15_bound_17` [propext, Quot.sound] (Leg C ll.439/458) — from E11(3)/(4)
+ x-monomial valuations carried as hypotheses. Full valuations depend
on E11: the §5 (b_k)/(c_k) bounds are NOT discharged (min-degree
ValCore on RatFunc K missing — fold-in §7), so the conditional bounds
stand as stated.

### E16 — §5 system of 9 equations + principal equation. KERNEL (elimination only); derivation OPEN.
Kernel (Leg C): `e16_cert` [propext, Quot.sound] (certificate identity
by `ring`), `e16_principal` [triple] (9 equations + dm1≠0 ⇒
principal=0; `gghv_full_s5_2026-11-06.lean` ll.277–324). The
9-equation DERIVATION from the C/F/D expansions remains OPEN (now also
needing the corrected φ-shift t=D₂/3 — see §9). I1: Phase 1 resultants +
Gröbner (ELIM_IDEAL_SIZE 1, generator exactly the target), re-run by
the Leg G runner (R23 I1 PASS on the computational steps; see §2 R23).
φ-shift: the 9 equations are the d₂=0 normal form, i.e. for the corrected
shift t=D₂/3, never the paper's shift (Leg C SymPy + Leg G both tools).

### E17 — Corollary 5.2 (§5). CONDITIONAL.
`cor52_conditional` [] (Leg C l.831) — two-line application of Thm 5.1
via `link52` (Cor 7.2 + Thm 2.6 + Def 4.3 + ψ sixth-power step + φ-shift
bracket, all carried inside `link52`). No axioms.

### E18 — Theorem 6.1 (`teorema impossible para 7`, §6). CONDITIONAL.
`s6_theorem61` [triple] (Leg D, `gghv_full_s6_2026-11-06.lean` l.1577;
80 theorems in the file: 64 [triple], 8 [propext, Quot.sound],
8 zero-axiom (`decide`); FULL EXIT 0, ~14 s; AXIOMS EXIT 0; no sorryAx).
Wrapper discharges hdm1mono (`s6_dm1_dvd` + `s6_dm1_monomial`,
[triple]) and hprin (`s6_principal_eq` [triple]); remaining premises:
9 equations + degrees (hd0deg: deg d₀ = 9, hd1deg: deg d₁ = 6) + dm1≠0
+ hsq (the non-square premise — Singular-supported: `member_s6_square.sing`
reduce(y⁹T,GJ) = 0, so T follows up to the nonzero factor y⁹, but no
explicit lift coefficients, so hsq stays a named premise). Prop 4.4
reduction belongs to Leg B (E8), carried as a named premise. k=2
(`s6_k2` [triple]) and the non-square contradiction (`s6_nonsquare`
[triple], `e18_final_combination` [triple]) are KERNEL from the degree
data and d_{−1} = αy^k. NEW SLIP (Leg D): §6 printed polygon lists
N(P) = {(0,0),(4,0),(2,6),(0,14)}, N(Q) = {(0,0),(6,0),(3,9),(0,21)}
have the middle vertex TRANSPOSED against Prop 4.4's {(0,0),(4,0),(6,2),
(0,14)} / {(0,0),(6,0),(9,3),(0,21)} AND against the §6 proof's own
ℓ_{1,0}(P) = x⁶y², ℓ_{1,0}(Q) = x⁹y³ (max x-exponent 4 < 6 in the
printed list). Assembly stated for the Prop 4.4 lists; printed lists
recorded as differing (kernel `decide`:
`e18_polygon_discrepancy_P/Q` []). The (7,21) row is already eliminated
via §3 (E4); the §6 route is the paper's second proof of the same
elimination, not on the minimal premise list for Theorem 2.1.

### E19 — Proposition `calculo de C para 7` (§6). PARTIAL (Laurent fold-in DONE 2026-11-07).
Kernel (Leg D): valuation arithmetic (`v_{2,1}(3,1) = 7`, NOT the paper's
(b₀) value 6); recursion identity `e19_recursion` [triple]
(`gghv_full_s6_2026-11-06.lean` l.247; matches TeX ~1877 exactly — §6
recursion is CLEAN, unlike §5). §6 existence + (b_k)/(c_k) bounds
KERNEL via the fragment's `laurent_series_discharge_s6` [triple]
(fragment l.1541): C with C² = P, C.coeff(−3) = T 1, bounds lpMaxDeg ≤
1+2n and lpMinDeg ≤ n−1, no coefficients below −3, v10 C = 3. F
CONDITIONAL via `exists_F_lp` / `f_discharge_lp_s6` (fragment l.1681)
on `GGV1InputsLp` + the unit u with ↑u = C (unit supplied KERNEL by
`isUnit_of_coeff`). **ValAxioms diagnosis (KERNEL, fragment
`ValAxiomsOrig.forces_zero/nonneg/no_nontrivial`, [propext,
Quot.sound]):** Leg D's `ValAxioms` structure is uninstantiable —
unconditional `mul` (w(a·b) = w a + w b for ALL a, b, including a = 0)
forces w ≡ 0, and `add` forces w ≥ 0, inconsistent with any valuation
taking a negative value (e.g. v_{2,1}(y⁻¹) = −1). Hence Leg D's
`e19_bound_step_21`, `e19_bound_step_1m1`, `e19_finite_bounds` are
kernel-proved as implications but can NEVER be instantiated with
v_{2,1}/v_{1,−1} — do NOT cite them as instantiated. The usable bound
steps are the fragment's `valcore_bound_step_21/_1m1/finite_bounds`
(KERNEL from `ValCore`: nonzero guards on mul, sum≠0 guard on add),
instantiated at `valCore_lpMaxDeg` / `valCore_lpMinDeg` for §6. Paper
slip: (b₀) v=6, correct 7 (§9); valuation product-vs-sum typo PRESENT
in §6 too (§9).

### E20 — Remark (§6). KERNEL modulo Ptcoef input data (Laurent fold-in DONE 2026-11-07).
Kernel (Leg D): Q̃ identity + truncated C̃², C̃³ expansions
(`e20_assembly` [propext, Quot.sound], l.498). Tilde-series existence
KERNEL modulo Ptcoef input data via the fragment's `exists_tilde`
(Ct² = Pt, Ct·Cti = 1, Qtilde = Ct³ + lam'·Cti + Ft, Ct.coeff(−3) =
C3) and `tilde_discharge` (Ptcoef n = Pcoef n + (2/3)α₁ at n = 0;
fragment l.1591). The paper's sharper claim (Ft has v10 = −4, lam' =
lam − α₁²/3 + …) is NOT proved — Ft is defined as the difference. Read
with the §6 labels (Theorem 6.1 / `calculo de C para 7`), NOT the
printed §5 labels (§9: the §6 remark repeats the §5 remark verbatim
including its labels — a cross-reference slip).

### E21 — Proposition `D_k ∈ K[y]` for (7,21) (§6). CONDITIONAL (kernel modulo named inputs).
`e21_membership` [triple] (Leg D l.1455) — membership induction in
`RatFunc K` (IsPoly closure lemmas, all [triple]), conditional on the
E19 recursion data and on `y ∣ P₅` (the D₂ base case). Kernel:
`D_j D_{k+3−j}` identity with the CORRECTED factor 1/2 on the sum (Leg D
found the paper OMITS the 1/2 in both §5 and §6; harmless for
membership — §9). Depends on E19 for its inputs: the §6 existence is
now KERNEL (`laurent_series_discharge_s6`, fold-in §7); `y ∣ P₅` (the
D₂ base case) is still carried.

### E22 — §6 system of 9 equations + principal equation para 7. KERNEL (elimination/displays only); derivation OPEN.
Kernel (Leg D): `(D̃²)_{-k}` and `(Q̃)_{-j}` displays (given d₃=1, d₂=0,
dᵢ=0 for i≥4); principal equation `s6_principal_eq` [triple] (l.954)
from the 9 equations via the Part-11/12 certificate identity
(transcribed from the Singular `cert_s6` script and re-verified there);
k=2 and the non-square contradiction KERNEL (see E18). The 9-equation
DERIVATION from the C/F/D expansions remains OPEN (as in §5, E16).
I1: elim/cert/groebner re-runs exit 0 (Leg D, Singular 4.3.1: Res =
(−19683/64)·target·dm1³, reduce = 0 at k=0; CERT_DIFF = 0, CERT_IS_ZERO
= 1; Gröbner reduce(dm1·target, E) = 0). `lift_s6_extra.sing` TIMEOUT
600 s (exit 124) — inconclusive (reduce against the RAW ideal, not a GB;
its Q4x2 carried a 6/6 transcription error — display `d3cu_neg4` itself
was correct at 6/6; fixed to 12/12). `member_s6_extra.sing` (0.37 s, GB
size 200): both extra identities ARE in the 9-equation ideal. Explicit
lift() coefficients still NOT obtained (lift is the slow step).

### E23 — In-text computation `F_{−4} = (1/2)y^{−1}` (§6). PARTIAL (Laurent fold-in DONE 2026-11-07).
Kernel (Leg D): monomial bracket computation + monomial uniqueness;
polynomial-ODE uniqueness lemma `e23_ode_unique` [triple] (l.383).
Kernel (fragment): `bracket_mono` ([xⁿyʲ, xᶜyᵈ] =
(nd−jc)xⁿ⁺ᶜ⁻¹yʲ⁺ᵈ⁻¹), `e23_instance` ([x⁶y², (1/2)y⁻¹x⁻⁴] = x),
bracket additivity, `lpDeriv` / `derivX` / `derivY` on monomials.
Series-bracket reduction CONDITIONAL on `hdeg`
(`bracket_reduction_discharge` / `e23_series_reduction`, fragment
l.1612) — `hdeg` needs the Leibniz rule for
`LaurentSeries.derivative`, absent from Mathlib 4.34.0; the bracket step
`[C^k, C²] = 0` is a named hypothesis `bracket_pow_C` for the same
reason. I1 support (Leg G runner, R23): Laurent bracket
[x⁶y², (1/2)y⁻¹x⁻⁴] = x (SymPy rc=0 OVERALL ALL PASS).

## §2. The [GGV1]/[GGV*] remainder — R8–R23

### R8 — Esquina (3) ℓ-form. KERNEL (assembly theorem CONDITIONAL on its named premises).
File: `~/workspace/research/tooling/phase4_legE/gghv_full_esquina3l_2026-11-06.lean`
(10 item files + index in `phase4_legE/`; 87 declarations; FULL runs
7–14 s per file, Lean 4.34.0, exit 0; second tool Python 3.11.2 ALL PASS
exit 0, 19 checks; Singular 4.3.1 `jacobi_check.sing` JACOBI = 0,
BRACKET_AB = −x²−1, exit 0).
Axiom lists (from `logs_vm/gghv_full_esquina3l_2026-11-06_axioms.log`,
verified on disk):

| Theorem | Axioms |
|---|---|
| `esq3_val_8_3` | [] |
| `esq3_mn_sum` | [propext, Quot.sound] |
| `esq3_dir_determination` | [triple] |
| `esq3_phi_aligned_impossible` | [propext, Quot.sound] |
| `esq3_phi_nonaligned_impossible` | [propext, Quot.sound] |
| `esq3_lform_term_val` | [propext] |
| `esq3_lform_from_cube` | [propext, Quot.sound] |
| `esq3_dir_b2` | [] |
| `esq3_dir_b1` | [] |
| `esq3_dir_b0` | [] |
| `esq3_lform_endpoint_lo` | [propext] |
| `esq3_lform_endpoint_hi` | [propext] |
| `esq3_lform_Q` | [propext, Quot.sound] |

The six theorems were printed by the assembly R8 run
(`~/workspace/research/tooling/phase4_assembly/r8_axioms_2026-11-06.lean`,
rc=0, 15 s, 0 errors, 2026-11-07 ~02:08 UTC; log
`r8_axioms.log`). All six are kernel `decide`/`ring` facts as expected
(the endpoints are `ring` identities over ℤ; `esq3_lform_Q` is
`esq3_lform_from_cube` applied) — and the run's output above is the
record, not the expectation.
`esq3_lform_from_cube` is CONDITIONAL on its named premises: the
common-power premise `ℓ(P) = λ_P R^m` (Remark "a remark", R12
conditional) and the cube premise `x·R = c·(z−μ)³` (the "𝔯 has no simple
linear factor" step, carried as the cube hypothesis, not proved).
NOT proved: the cube premise itself (φ-argument); the identification of
`ℓ_{−1,3}(P)` with the face polynomial in the KTerm list model (needs
the D2 bridge — the statement is in an abstract commutative ring).

### R9 — Central's gaps. KERNEL + CONDITIONAL.
File `gghv_full_central_gaps_2026-11-06.lean` (Leg E). KERNEL:
`central_cancellation` [propext], `central_item5` [propext],
`joseph_counting_contradiction` [propext, Quot.sound] +
`int_interval_card` [triple] (Lema Joseph dimension-counting arithmetic).
CONDITIONAL: `central_eq_central_from_joseph22` [propext] on the named
`Joseph22HomogForm` premise (homogeneous form only; exact wording NOT
retrieved — inference only, never presented as Joseph's wording; the
naive un-homogeneous form is FALSE — counterexample in the dated log).
Central item (1) (`F ∈ L`) is the `sub F` component of that conditional
theorem. Joseph Lemma 2.2 itself: NOT FOUND (retrieval leg, 12 routes;
Joseph's paper is "The Weyl algebra — semisimple and nilpotent
elements", *Amer. J. Math.* 97 (1975), 597–615 — the shorthand "The
Jacobian conjecture in dimension 2" is WRONG, confirmed three ways).

### R10 — Combined-form esquina(1)/(2). KERNEL.
File `gghv_full_esquina_combined_2026-11-06.lean` (Leg E).
`esquina2_set_iff`, `esquina2_combined`, `esquina2_k1_pair` [triple]
each; `esquina1_bundle_iff` [].

### R11 — The (7,21) coefficient identity. KERNEL.
File `gghv_full_721_coeff_2026-11-06.lean` (Leg E). `face721_*` (base
identity, coeffs, monic, natDegree, leading coeff, remainder degree)
[triple] each; `face721_factor_count` [propext].

### R12 — Remark "a remark"'s face laws + alineados(2a). KERNEL.
File `gghv_full_remark_facelaws_2026-11-06.lean` (Leg E).
`alineados_2a_from_2b`, `remark_ratio`, `remark_st_scaling`,
`remark_en_scaling` [triple] each; `tpow_exp_smul` [propext, Quot.sound].

### R13 — D1 full theory. KERNEL.
File `gghv_full_d1_theory_2026-11-06.lean` (Leg E).
`dirLt_trans_halfplane` [triple] (transitivity on an interval),
`dirLt_irrefl'` [propext], `dirLt_asymm'` [propext, Quot.sound],
`succ_set_consecutive` [], `succOp_eq_of_isSuccFrom` + `succOp_spec`
[triple] (Succ as operator), `cross_dot_identity` [propext, Quot.sound].

### R14 — D2 polynomial versions. KERNEL.
File `gghv_full_d2_poly_2026-11-06.lean` (Leg E). `pderiv_comm`,
`pbracket_antisymm/add_left/add_right/smul/leibniz/jacobi/translate`,
`joseph_counterexample_bracket`, all [triple]. Second tool: Singular
JACOBI = 0 (see R8).

### R15 — m,n > 1 as literally written. KERNEL as documented deviation.
File `gghv_full_mn_gt1_2026-11-06.lean` (Leg E). `mn_gt1_dir_mem`
[triple], `mn_eq1_needs_b_gt1` [], `gghv_uses_mn_gt1` [],
`gghv_uses_dir_mem` [triple]. The paper states m,n ∈ ℕ but esquina(2)'s
proof needs m,n > 1 — a genuine minor gap as literally written;
arXiv-TeX wording flagged as NOT the published wording (published §7
text NOT FOUND).

### R16 — Hybrid-vs-slip. KERNEL arithmetic; question OPEN.
File `gghv_full_hybrid_slip_2026-11-06.lean` (Leg E).
`hybrid_arith_249/288`, `hybrid_slot_249/288/927/721` [triple] each.
Both readings stated explicitly; the hybrid-vs-slip question itself
stays OPEN (published §7 NOT FOUND).

### R17 — Mayores full statement. KERNEL/CONDITIONAL.
File `gghv_full_mayores_2026-11-06.lean` (Leg E).
`mayores_termination_descent` [propext],
`mayores_chain_terminates` [propext, Quot.sound],
`mayores_cocientes_ratio` [triple], `mayores_cocientes_conditional` +
`mayores_full_conditional` [triple].

### R18 — Thm 7.6(5), Prop 2.11(3), Prop 2.1(2b), Prop 3.12. CONDITIONAL (Prop 3.12) / BLOCKED ((2a)→(2b)).
Leg F, three files (5,686 / 5,119 / 5,700 lines; round-5 logs: all three
LEAN_EXIT=0, 0 error lines, NO sorryAx; md5s recomputed and matching:
5db7b34420dcf8d111223e79aaed3f44 / 2e61236431142905b92d09252d1251f9 /
159527f8326bf32e87276651054c5fcf).
- [GGV2] Prop 3.12: CONDITIONAL — `finitas_of_data` [triple] (File 1,
  l.5469) from the `FinitasData` structure (File 1, l.5293), which
  carries the paper's cited lemmas as named premises (Lemma `factores en
  jacobiano` eq2, Lemma `maximo grado`, [GGV1] Prop 1.13, Remark `gap`,
  [GGV1] Prop 2.4(1) dichotomy). The three cases (1)/(2)/(3) plus the
  ℓ=1 + v_{1,−2} clause are proved from it. Leg B can consume
  `finitas_of_data` with those premises named.
- [GGV1] Thm 7.6(5): CONDITIONAL — `divisibilidad_gghv_use8` and
  `divisibilidad_gghv_use8_of_arxiv` [triple] (File 2a, ll.4714/4725).
  Premises: (a) the numbering identification, carried as explicit
  hypothesis `h76_5` — published numbering UNVERIFIED (published §7
  text not found; §8 precedent shows numbering can shift, so arXiv ≠
  published is not assumed); (b) the corner-index identification
  (1 < i₀, GGHV d₀ = d i₀). The base's `divisibilidad_stmt` pin was
  CORRECTED (it dropped the j>0 restriction, overstated the q_i ∤ d_i
  clause, and stated the q₀ clauses unconditionally).
- [GGV1] Prop 2.11(3): CONDITIONAL — `pavadass3_of_descended` [triple]
  (File 2a, l.4832) modulo hproc (multiplicity-procedure premise).
  Direction CORRECTED: the base pinned the ASCENT form; item (3) is a
  DESCENT.
- [GGV1] Prop 2.1(2b): (2b)→(2a) KERNEL-clean (`prop21_two_a_of_b`
  [triple], File 2a l.5065, modulo `prop21_two`'s own hypotheses).
  (2a)→(2b) BLOCKED — blocker: univariate common-power lemma
  (fⁿ = α·gᵐ, gcd(m,n)=1 ⇒ f,g powers of a common polynomial, via
  factorization/multiplicity over an algebraic closure) + z-form
  reduction (P = x^{r/l}y^s f(z), rational exponents, not in the KTerm
  layer).
- D2 power laws now PROVED (File 2a §R): `coeffAt_pmul_assoc` (l.4939)
  [propext, Quot.sound], `ppow_add_kt` (l.5020), `ppow_mul_kt` (l.5050)
  [triple] — this discharges the Cor 7.4 leg's power-law premises (see §6).

### R19 — [GGV5] enumeration COMPLETENESS. BLOCKED.
Leg F File 2b §T: `enum_complete_of_links` [triple] (l.5529)
CONDITIONAL on two OPEN links: (1) pair-to-chain construction (Remark
`parte inferior`, vdE Prop 10.2.6 + [GGV1] Def 4.3 + Prop 3.12 setup)
not formalized — `hchain`; (2) PLLC-to-table attribution ([GGV5] §§5–6)
not re-derived — `hattrib`. Finiteness corollary `pllc_finite_of_cota`
[triple] (l.5510) CONDITIONAL on `para_la_cota`. `para_la_cota` is the
next attackable premise: its proof uses Prop 3.12 cases (2)/(3), which
File 1 now discharges one level down — it would discharge
`cota_of_chain`'s premise and hence the finiteness corollary's premise
(see §6). The first-stage PLLC filter is recomputed (Phase 1, I1);
completeness is NOT. Leg G delimitation stands: the generative step
(families from a given final corner) and arithmetic attribution ARE
recomputable in Singular (R22 I1 PASS); the Main-algorithm chain
enumeration and the completeness claim (listed families/chains are ALL)
are NOT computable in Singular — they rest on the [GGV5] C++ program +
SQL database, which are not available as a Singular computation.

### R20 — [GGV2] Props 3.29/3.12, Def 3.21, Remark 3.31; [GGV6] Props 6.4/6.6, Ex 6.7, Prop 2.5; four red rows. CONDITIONAL (red rows + 3.29/3.31/Def 3.21); NOT PROVED (Thm 7.3); CARRIED (Prop 2.5).
- Prop 3.29 / Remark 3.31 / Def 3.21: see E3 (§2 above).
- [GGV6] Thm 7.3 / Props 6.4/6.6 / Ex 6.7: see E4.
- [GGV6] Prop 2.5: CARRIED (no TeX analogue in arXiv §1; use proved as
  `prop25_q`).
- Four red rows: CONDITIONAL — `redrow_412_34_conditional`,
  `redrow_412_57_conditional`, `redrow_520_23_conditional`,
  `redrow_520_32_conditional` (File 2b §U, ll.5591/5603/5616/5640),
  all [triple] (round-5 axioms logs, verified on disk), modulo the
  named external discard + connection hypothesis ([GGV4] §3.5 published
  / [M] case 64 / [H] / [GGV3] §5; (5,20)/(3,2) via P/Q swap,
  swap-closure as explicit hypothesis). `redrow_520_32_of_23` on ZERO
  axioms. (8,24) row: `redrow_824_conditional` (File 2b, l.5419),
  conditional on [GGV5] Prop 6.1 — see §8 for the numbering
  determination. [GGV4] §3.5 flag: the arXiv version (arXiv:1310.8249)
  contains NO (4,12) discard — the citation must refer to the
  PUBLISHED version's §3.5 (Pro Mathematica 27 (2013) 83–98), flagged as
  a numbering/content gap; the (4,12) rows stay CONDITIONAL on the cited
  external discards.

### R21 — §2 table + §3 numerics in Singular. I1 PASS.
Leg G runner (lean-build-3): Singular 4.3.1 rc=0 (BAD_ROWS = 0; all 10
rows' maxima [64,112,75,75,84,96,108,120,99,108]; survivors
(108,72),(66,99),(72,108); GCD_72_108 = 36, ratio (2,3); §3 numerics as
expected); filed re-run `d1_singular_table_enum_2026-11-05.py` rc=0
OVERALL: ALL PASS. Logs: `phase4_legG/logs/table_s5_singular.log`,
`table_filed_py.log`, `versions.log` (Singular 4.3.1 Debian
1:4.3.1-p3+ds-2, Python 3.11.2, SymPy 1.14.0, python-flint 0.9.0).

### R22 — [GGV5] enumeration recompute. I1 PASS (generative step + attribution; completeness NOT recomputed).
Leg G runner: Singular `GetmnFamilies` rc=0 (all 7 family checks = 1;
sizes exact); Python/flint cross-check rc=0 OVERALL: ALL PASS. Logs:
`phase4_legG/logs/ggv5_families_singular.log`,
`ggv5_families_py.log`. Delimitation (see R19): Main-algorithm chain
enumeration + completeness need the [GGV5] program/database or a Lean
proof, not a Singular run.

### R23 — The 9 equations' derivation. I1 PASS on the computational steps (two tools jointly); Lean-only parts delimited.
Leg G runner: SymPy rc=0 OVERALL: ALL PASS (§5+§6 D-scaling all 24
identities = 0; (D̃²)/(D̃³) displays all = 0 except k=7; inverse
coefficients as expected; Laurent bracket [x⁶y², (1/2)y⁻¹x⁻⁴] = x);
Singular rc=0 (§6 scaling all 0; (D̃²) k=1..6, (D̃³) j=1..3 = 0;
inverse coeffs PASS; (E) bracket = 0). Logs:
`phase4_legG/logs/nine_eq_singular.log`, `nine_eq_sympy.log`.
Delimitation: checked = D-scaling identities, displayed (D̃²)/(D̃³)
expansions, inverse coefficients, φ-shift coefficient; Lean-only =
E11/E14/E19/E21 themselves and the "φ(P̂),φ(Q̂) ∈ K[x,y] ⇒ negative
coefficients vanish" implication. Two Singular script bugs REPORTED, not
fixed: (a) §5 D-scaling nonzero because the script uses two symbols for
C₃ (`c3x` in the C-list, `c3` as scaling base) — SymPy (single C₃)
gives 0 for all 12, mathematics decided; (b) (D̃²)_{−7}/_{−8} and
(D̃³)_{−4} outputs corrupted by 32-bit `int` overflow of 13!/14! in
`coeffU`'s `fact` (13! = 6227020800 → 1932053504; 14! → 1278945280) —
use a bigint/exact division. Corrections needed (not done by the runner).
Runner's driver-1 invocation bug (logged verbatim): `Singular < script <
/dev/null` makes the second redirect win, so Singular read empty stdin —
all four first Singular runs were banner-only and VOID; re-ran correctly
as `timeout 600 Singular < script`; the reported verdicts are from the
correct re-runs. (D̃²)_{−7} display facts CONFIRMED: TRUE − DISPLAY =
2d_{−10} exactly (SymPy); TRUE − (DISPLAY + 2d_{−10}) = 0; the literal
"2 d_{−1} 0" term is identically zero. The filed Gröbner script's
corrected form (with 2·dm10) is the true expansion.
φ-shift CONFIRMED BY BOTH TOOLS (independent of Leg C's confirmation):
x²-coefficient of φ(D) is D₂−3t; at t=D₂ it is −2D₂ (not 0); at t=D₂/3
it is 0. The paper's stated shift is a genuine slip confined to the
shift formula; the 9 equations are the d₂=0 normal form, i.e. for the
corrected shift. See §9.

## §3. The four red rows (detail)

All four CONDITIONAL (Leg F File 2b §U, all [triple], round-5 axioms
logs verified on disk). Each is conditional on (i) the cited external
discard, stated over standard pairs with the row's (m,n), A₀ and degree
pair, and (ii) a connection hypothesis. The (8,24) row is conditional on
[GGV5] Prop 6.1 — see §8.

| Row (A₀, (m,n), max) | Cited discard | Theorem | Axioms |
|---|---|---|---|
| (4,12), (3,4), 64 | [GGV4] §3.5 + [M] + [H] | `redrow_412_34_conditional` (l.5591) | [triple] |
| (4,12), (5,7), 112 | [GGV4] §3.5 | `redrow_412_57_conditional` (l.5603) | [triple] |
| (5,20), (2,3), 75 | [GGV3] §5 | `redrow_520_23_conditional` (l.5616) | [triple] |
| (5,20), (3,2), 75 | [GGV3] §5 (via P/Q swap) | `redrow_520_32_conditional` (l.5640); `redrow_520_32_of_23` | [triple]; [] |
| (8,24), (2,3), 96 | [GGV5] Prop 6.1 | `redrow_824_conditional` (l.5419) | (conditional on Prop 6.1; see §8) |

Flags: [GGV4] §3.5 in the arXiv (arXiv:1310.8249) contains NO (4,12)
discard — the citation must refer to the published version's §3.5 (Pro
Mathematica 27 (2013) 83–98), a numbering/content gap; the (4,12) rows
stay CONDITIONAL on the cited external discards. [GGV3] §5 treats
(50,75) only (per the [GGV3] note), resting on [GGV1] Remark 7.10 +
computations as in [GGV1] Prop 8.3; (75,50) follows by P/Q swap
(swap-closure as an explicit hypothesis). [M] considered max ∈
{64,75,84,99} but only case 64 has a complete proof (GGHV main.tex
295), so the (5,20) discards rest on [GGV3] §5, not on [M].

## §4. The explicit maximal minor (Step 3 — Leg H)

**PARTIAL, narrowed.** Leg H deliverable:
`~/workspace/research/tooling/phase4_legH/minor_spec_2026-11-06.md` +
`extract_minor.py` + `det_minor.py` + `vm_out/out/` (rows.json, piv.json,
pivcols.json, colv.json, det_p32003.json, det_p1000003.json, det logs,
globals.txt, summary.json). Verified on disk by the assembly agent:
det jsons read — p=32003 det_flint = det_numpy = 29127, routes_agree
true, detC_flint = 9069, detC×det ≡ 1 (mod 32003); p=1000003 det_flint =
det_numpy = 262898, routes_agree true; timings 4.6 s / 193.4 s and
4.8 s / 201.4 s as reported.

- Matrix: M₂₄, weighted Macaulay matrix of the six chart generators
  (Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃) at weight W = 24 — 3199 rows × 6054 columns,
  239,154 nonzeros; entries in K₅ = ℚ[w]/(R), R = w⁵ − w⁴ + 3w³ + 3w² + 26.
- Row set (maximal, all rows): indices 0–3198 in filed order, labelled by
  monomial 5-tuples in (t,s,r,u,q); matches the matrix pkl rows (sha16
  `80fed24d2a885918`) and the filed Lean `A2Data.lean rowsList`.
- Column set: the 3199 FLINT-RREF pivot columns, strictly increasing
  ordinals 0–5307. By generator: Psi 1308/1308 (all Psi columns are
  pivots), Phi1 731/1071, Phi2 522/1071, Theta1 306/868, Theta2 210/868,
  Theta3 122/868. Verified `pivcols[jj] == cols[piv[jj]]` against
  `inv_work_M.pkl` and against a freshly rebuilt p = 1000003 matrix.
- Determinants (nonzero, two independent routes each): p = 32003, w₀ =
  11147 → 29127; p = 1000003, w₀ = 806739 → 262898. Over K₅, det(M_S) ≠ 0
  follows by the rank lemma's own proof (Lemma `bc:lem:rank`):
  det φ(M_S) = φ(det M_S) ≠ 0 ⟹ det M_S ≠ 0 in A ⊂ K₅.
- §6.3(a) check: "explicit nonzero maximal minor, with row and column
  indices, of the branch-(c) Macaulay matrix over K₅" — DONE for indices
  + modular determinant values. NOT DONE: the determinant value as an
  explicit element of K₅ (5 rational coefficients) — no feasible route
  exists (would need the 3199×3199 determinant over ℚ[w]/(R), i.e.
  multimodular reconstruction over ~10⁴ primes). So §6.3(a) as literally
  worded is PARTIAL → narrowed, and whether the delivered form satisfies
  §6.3(a) is BRANDON'S JUDGEMENT CALL. If the K₅ value is required, that
  is a separate resourced job (~10⁴-prime multimodular reconstruction),
  not a quick follow-on. Outside-project rebuild (§6.3b) also NOT DONE —
  not this leg. A Lean formalization of this minor (`RingHom.map_det`
  instance) is un-ordered.
- Filed form: `branch_c/rank_lemma_check/INVERSE.pkl`, 82,788,865 bytes,
  file sha256
  `1af9b3c8a4d32a2a611b6b3958c6e3770e282d5d351b423af45ea304a44189fe`
  (verified locally and on VM; never copied into any repo). NOTE
  (resolves a record ambiguity): the Phase 3 "sha256 `00e40995b010f30a`"
  is the hash of the pivot LIST, not the file — it matches the extracted
  `sha256(repr(piv))[:16]` exactly, as does the C hash `6cffa0100555b7b8`.
  Extraction used a restricted unpickler (builtins + numpy ndarray/dtype
  only); exit 0. VM: lean-build-3, Python 3.11.2, python-flint 0.9.0,
  numpy 2.4.6. Both determinant scripts exit 0; scripts assert route
  agreement and abort on disagreement. This leg produces an
  identification (I1 on the shared matrix construction), not a kernel
  proof; it does not change any Lean grade.

## §5. Theorem 2.1 — consolidated

CONDITIONAL (`theorem21_minimal_v2`, assembly file, [propext,
Classical.choice, Quot.sound]; assembly run 2026-11-07 ~02:08 UTC:
FULL_EXIT=0, 135 s, 0 errors; AXIOMS_EXIT=0, 50 s, 0 errors; no
sorryAx) from the 20-field `MinimalPremises2` (§0). The honest
headline (§0) stands: the paper is NOT proved unconditionally, and
Theorem 2.1 is NOT unconditional. The remaining premises, in dependency
order of depth: (i) [GGV5] enumeration completeness (BLOCKED — the
deepest external blocker, with Joseph Lemma 2.2 the other; both stay
CONDITIONAL/BLOCKED explicitly, never papered over); (ii) the §5 data
links + bridges for fields 9–10 (Laurent layer R14 + §5 derivation);
(iii) [GGV6] Thm 7.3 + π-root machinery; (iv) [GGV2] Prop 3.29 /
Remark 3.31 / Thm 7.6(5) numbering (all CONDITIONAL on named premises);
(v) the four red rows (CONDITIONAL on cited external discards). The §6
route for the (7,21) row is not on the minimal list. "JC(2) proved" is
never claimed by this programme — the full GGHV proof does not prove
JC(2). "Theorem R" is excluded from this programme everywhere. "(72,108)
excluded unconditionally" is NOT claimed — it rests on GGHV
exhaustiveness + the reduction chain, ledgered not re-derived.

## §6. Discharged items (what this programme closed)

- **D2 power laws — PROVED** (Leg F File 2a §R —
  `coeffAt_pmul_assoc` [propext, Quot.sound]; `ppow_add_kt`,
  `ppow_mul_kt` [triple] — verified present at the stated lines):
  `coeffAt_pmul_assoc` (l.4939), `ppow_add_kt` (l.5020), `ppow_mul_kt`
  (l.5050). This discharges the Cor 7.4 leg's power-law premises (which
  the base's `cor74_assembly` carried as hypotheses).
- **Next attackable premise: `para_la_cota`.** Its proof uses Prop 3.12
  cases (2)/(3), which File 1 now discharges one level down
  (`finitas_of_data`); discharging `para_la_cota` would discharge
  `cota_of_chain`'s premise and hence `pllc_finite_of_cota`'s premise.
- **E9 algorithm output — KERNEL** (`psp_183` [propext]); **E13 — KERNEL**
  (`e13_f_separable` [triple]); **E16/E22 eliminations — KERNEL**
  (`e16_principal`, `s6_principal_eq` [triple]); **§2 table — KERNEL**
  (`gghv_table_full` []); **§3 arithmetic — KERNEL**
  (`discard_84/120_kernel_data`); **E7 eliminations — KERNEL**
  (branches (a)/(b)/(c)); **R8–R17 kernel pieces** as listed in §2.
- **Prop 3.12 — CONDITIONAL, one level discharged:** `finitas_of_data`
  proves the three cases + the ℓ=1 clause from `FinitasData`; the
  remaining carried premises are the paper's univariate lemmas (named
  in `FinitasData`), not the whole proposition.
- **Prop 2.1(2b)→(2a) — KERNEL-clean** (`prop21_two_a_of_b` [triple]).
- **(2a)→(2b) — BLOCKED** (see §1 R18; the univariate common-power lemma
  + z-form reduction are the precise blockers, not a vague "open").

## §7. Laurent fold-in — DONE 2026-11-07 ~03:37 UTC

Fragment: `~/workspace/research/tooling/phase4_laurent/gghv_full_laurent_2026-11-06.lean`
(1,705 lines, `import Mathlib` only, no `sorry`, no `axiom` declarations).
Verified by the coordinator on disk (file + `laurent_log.md`): final
full-file run FINAL_FULL_RC=0, 0 errors, ~10 s, Lean 4.34.0 / Lake 5.0.0
on lean-build-3; full-file axioms audit AX_FULL_RC=0, 87 theorems,
`sorryAx` count 0 (86 "depends on axioms" lines + `pow_ne_zero_of_ne`
[]); non-triple lists are all subsets (`ValAxiomsOrig.*` [propext,
Quot.sound], `ValCore.inv_unit` [propext, Quot.sound], `ValCore.pow`
[propext], `valcore_b0_21` [propext]). Second-tool check: Python/Fractions
`recursion_check.py` — convolution identity (u*u)_n = q_n for n = 0..5:
PASS. (The two "sorry" grep hits in the file are header-comment words.)

Per-item verdicts (see the §1 detail entries for the full statements):
- **E11** (§5): generic sqrt-series lemma KERNEL
  (`exists_sqrt_series`); §5 instance NOT separately applied —
  instance application remains open (G1 correction F2); F CONDITIONAL
  (`f_discharge` on `GGV1Inputs`); §5 (b_k)/(c_k) bounds
  NOT discharged (min-degree ValCore on RatFunc K missing).
- **E19** (§6): existence + (b_k)/(c_k) bounds KERNEL
  (`laurent_series_discharge_s6`); F CONDITIONAL (`exists_F_lp` /
  `f_discharge_lp_s6` on `GGV1InputsLp` + unit).
- **E20** (§6): tilde-series existence KERNEL modulo Ptcoef input data
  (`exists_tilde` / `tilde_discharge`).
- **E23** (§6): monomial bracket + ODE uniqueness KERNEL;
  series-bracket reduction CONDITIONAL on `hdeg`
  (`bracket_reduction_discharge`).

**ValAxioms diagnosis (KERNEL — acts on Leg D's framework):** Leg D's
`ValAxioms` structure is uninstantiable. The fragment proves
(`ValAxiomsOrig.forces_zero`, [propext, Quot.sound], fragment l.116)
that unconditional `mul` — w(a·b) = w a + w b for ALL a, b, including
a = 0 — forces w ≡ 0 (w(0) = w(0) + w(b) for every b), and `nonneg` /
`no_nontrivial` that no valuation taking a negative value can satisfy
it. Hence Leg D's `e19_bound_step_21`, `e19_bound_step_1m1`,
`e19_finite_bounds` are kernel-proved as implications but can NEVER be
instantiated with v_{2,1}/v_{1,−1} — they must NOT be cited as
instantiated. The usable bound steps are the fragment's `ValCore`
versions (`valcore_bound_step_21/_1m1/finite_bounds`, KERNEL from
`ValCore`: nonzero guards on mul, sum≠0 guard on add), instantiated at
`valCore_lpMaxDeg` / `valCore_lpMinDeg` (§6) and
`valCore_ratFunc_intDegree` / `valCore_v10`. (Coordinator-checked the
reasoning: from `mul` with a = 0, w(0·b) = w(0) + w(b), i.e. w(b) = 0
for every b. The diagnosis is correct.)

Premises that FALL (named individually — no bulk-flipping):
- `C7AssemblyPremises.laurent_series` (E19 §6 existence) — discharged
  by `laurent_series_discharge_s6` (KERNEL).
- E20 tilde-series existence — discharged by `exists_tilde` /
  `tilde_discharge` (KERNEL modulo Ptcoef input data).
- E21's E19-input dependence — discharged (the §6 existence is now
  KERNEL); `y ∣ P₅` (the D₂ base case) is still carried.
- E12's tilde-existence sub-premise — discharged (KERNEL modulo Ptcoef
  input data); E12 stays CONDITIONAL on hJac/hFace.

Premises that do NOT fall (named individually):
- `bridge924` / `bridge927` polynomial lifts (Laurent layer R14) — the
  fragment proves series-level results, not the polynomial lift from a
  row counterexample to a Thm-5.1-shaped polynomial counterexample.
  They stay carried.
- `link51_924` / `link51_927` (§5 data links) — the C-existence part is
  now KERNEL, but the F part is CONDITIONAL on `GGV1Inputs` and the §5
  bounds are NOT discharged, so the links stay carried (now with the
  F/bounds parts named precisely instead of the unformalized existence).
- E14's convolution identity — NOT literally discharged. E14's induction
  is in a subring S of K with the convolution identity as a hypothesis;
  the fragment proves the series-level counterpart (C² = P at
  coefficient level over LaurentSeries (RatFunc K)), a different ambient
  type. E14 stays CONDITIONAL.
- E15's bounds — NOT discharged (§5 (b_k)/(c_k) bounds missing).
  E15 stays CONDITIONAL as stated.
- E10's premises — NOT discharged (F part now CONDITIONAL on
  `GGV1Inputs`; the 9-equation derivation is still OPEN).
- E23's `hdeg` — stays carried (needs the Leibniz rule for
  `LaurentSeries.derivative`, absent from Mathlib 4.34.0).

Precise remainders after the fold-in (not discharged):
- §5 (b_k)/(c_k) bounds — needs a min-degree ValCore on RatFunc K
  (RatFunc.intDegree is max-degree only).
- Leibniz rule for `LaurentSeries.derivative` — needed for the bracket
  step `[C^k, C²] = 0` (named hypothesis `bracket_pow_C`) and for `hdeg`
  in the series-bracket reduction. Mathlib 4.34.0 has no such rule; it
  must be proved by hand or the derivative avoided.
- The paper's sharper Ft claim (Ft has v10 = −4, lam' = lam − α₁²/3 +
  …) — NOT proved; Ft is defined as the difference.

## §8. [GGV5] discrepancy — determination (assembly task 3)

**Question:** Leg A reported "the local [GGV5] TeX §6 is 'Program and
graphic display'" and contains no Proposition 6.1 under that number.
The on-disk TeX has §4 "Program and graphic display" (l.1638) and §6
"Possible counterexamples" (l.1792, `caso antisimetrico` = Prop 6.1 at
l.1874). Which [GGV5] source did Leg A use?

**Determination: Leg A's §6 label is WRONG for the only [GGV5] source on
disk and for arXiv v1; no alternative source was found to attribute it
to. Most likely a miscount/misread by Leg A.**

Evidence (each item checked by the assembly agent on 2026-11-06/07):

1. **Leg A's source:** Leg A's file header is the ONLY place the claim
   appears ("The local [GGV5] TeX (1708.07936, §6 = 'Program and graphic
   display') does not contain a Proposition 6.1 under that number").
   `legA_log.md` contains NO mention of 1708, GGV5, or 6.1 at all (grep
   empty) — the log gives no source, route, or line number for the claim,
   so Leg A's actual reading cannot be reconstructed from its log.
2. **On-disk TeX** (`~/workspace/research/guccione-papers/tex/1708.07936/main.tex`,
   the only [GGV5] TeX copy on disk — `find` over `~/workspace` returns
   no other 1708.07936 TeX): numbered sections are §1 Restrictions
   (l.265), §2 Construction (l.390), §3 Generation of (m,n)-families
   (l.1376), **§4 "Program and graphic display" (l.1638)**, §5 Admissible
   complete chains (l.1669), §6 "Possible counterexamples" (l.1792).
   `caso antisimetrico` (`\begin{proposition}`, l.1874) sits inside §6.
   The paper's text at l.1818 refers to "Proposition~\ref{caso
   antisimetrico}" for the F₂₂ discard.
3. **arXiv v1 PDF** (`~/workspace/research/guccione-papers/arxiv_1708.07936.pdf`,
   arXiv-rendered, CreationDate 2021-07-10): pdftotext TOC — "4 Program
   and graphic display ... 23" (l.28), "6 Possible counterexamples with
   max(deg(P), deg(Q)) ≤ 150 ... 27" (l.30); "Proposition 6.1. The
   example corresponding to F22 with (m, n) = (2, 3) can not be obtained
   ..." at pdftotext l.2927. The PDF and the TeX agree.
4. **arXiv listing** (arxiv.org/abs/1708.07936, crawled 2026-11-07 01:51
   UTC): "Some algorithms related to the Jacobian Conjecture", Jorge A.
   Guccione, Juan J. Guccione, Rodrigo Horruitiner, Christian Valqui,
   submitted 26 Aug 2017, single submission (v1). NO "Journal ref" field
   — arXiv lists no journal version.
5. **Journal version:** none found. Web search finds [GGV5] cited in a
   2018 paper's bibliography as "available at arXiv:1708.07936" — still
   arXiv-only as of Aug 2018. No journal, volume, pages, or DOI for this
   paper surfaced in the search. (The companion arXiv:1708.09367 is a
   different paper, "The Jacobian conjecture: approximate roots and
   intersection numbers", not [GGV5].)
6. **Possible miscounts considered and rejected as explanations:** counting
   the unnumbered `\section*{Introduction}` (l.248) as §1 would shift
   "Program" to §5, not §6. No numbering convention found in the TeX or
   PDF makes "Program and graphic display" §6. No v2 of the arXiv paper
   exists (single submission). The claim therefore cannot be attributed
   to a different arXiv version or to a journal version; it is a misread
   by Leg A of the source it cited.

**Consequences for the record:**
- [GGV5] Prop 6.1 citation: VERIFIED for the arXiv version — Proposition
  6.1 (`caso antisimetrico`) is in §6 of arXiv:1708.07936v1, TeX l.1874,
  PDF pdftotext l.2927. Leg F's resolution in its favour is confirmed.
- [GGV5] Prop 6.1 citation: numbering-UNVERIFIED for any published
  version, because no published version was found to exist. If a journal
  version is ever located, its numbering must be checked before citing
  Prop 6.1 against it (cf. the [GGV1] §7 numbering precedent: two later
  papers cite the B=16 theorem as "Theorem 8.10" while the local TeX has
  it as 8.12).
- Leg A's red-row premise for (8,24) is unaffected in substance: it
  carries "[GGV5] Prop 6.1" as an external theorem, and that proposition
  exists under that number in the arXiv version. Only Leg A's stated
  reason for not formalising it ("the local TeX §6 ... contains no
  Proposition 6.1 under that number") is wrong and must not be repeated.
  The real reason the red-row discard is carried is that formalising it
  needs the cited papers' Newton-polygon machinery (Leg F R20), as Leg A
  also stated.
- The comb leg must correct Leg A's header claim wherever it is repeated;
  the inventory file (`gghv_statement_inventory.md`) is a dated record
  and is NOT rewritten — this determination is recorded here.

## §9. Paper slips found by the legs (table, with Lean status)

| # | Slip | Where | Lean status |
|---|---|---|---|
| 1 | φ-shift t=D₂/3, not t=D₂: with φ(x)=x−t, the x²-coefficient of φ(D) is D₂−3t; the paper's stated shift t=D₂ (TeX 1663) gives d₂=−2D₂, NOT 0 as claimed (TeX 1668); the consistent shift is t=D₂/3. Same shift + assertion recur at TeX 2025/2030 (§6). | GGHV §5 (TeX 1663/1668), §6 (2025/2030) | CONFIRMED by three independent tools: Leg C SymPy 1.14.0 (ALL_PASS); Leg G runner SymPy + Singular (both tools); Leg D Lean kernel `phi_shift_x2_paper` [propext, Quot.sound] / `phi_shift_x2_corrected` [triple]. The 9 equations are the d₂=0 normal form for the corrected shift. Does NOT touch the kernel E16 elimination. |
| 2 | §5 recursion sign error: paper writes 2C₃C_{3−k} = −P_{6−k} − Σ and C_{3−k} := −(1/(2C₃))(P+Σ); the expansion gives 2C₃C_{3−k} = P_{6−k} − Σ. Both signs flipped. | GGHV §5 (TeX ~1462–1465) | KERNEL: `e11_recursion_sign_slip` [triple] (Leg C) shows the as-printed recursion ⇒ −P_{6−k}; `e11_recursion_step` [triple] is the corrected form. §6 recursion is CLEAN (TeX ~1877, matches kernel `e19_recursion` exactly). |
| 3 | 1/2 omission in the D_k formula: the printed D_k identity OMITS the 1/2 on the sum, in both §5 (E14) and §6 (E21). Harmless for membership. | GGHV §5 (E14), §6 (E21) | KERNEL with the corrected factor: Leg D's `e21_membership` [triple] uses 1/2; Leg C's `e14_d_mem` [triple] is the §5 induction. |
| 4 | §6 polygon transposition: printed N(P) = {(0,0),(4,0),(2,6),(0,14)}, N(Q) = {(0,0),(6,0),(3,9),(0,21)} have the middle vertex TRANSPOSED against Prop 4.4's {(0,0),(4,0),(6,2),(0,14)} / {(0,0),(6,0),(9,3),(0,21)} AND against the §6 proof's own ℓ_{1,0}(P) = x⁶y², ℓ_{1,0}(Q) = x⁹y³ (max x-exponent 4 < 6 in the printed list). | GGHV §6 Thm 6.1 statement (TeX 1817–1823) vs Prop 4.4 (TeX 1313–1319) | KERNEL (`decide`): `e18_polygon_discrepancy_P/Q` [] (Leg D). Assembly stated for the Prop 4.4 lists. |
| 5 | (b₀) v=7 not 6: item (3) states v_{2,1}(C) = v_{2,1}(3,1) = 7, but the proof's base case (b₀) states v_{2,1}(x³y) = v_{2,1}(3,1) = 6. Since v_{2,1}(3,1) = 2·3+1·1 = 7, the "6" is arithmetically wrong; the bound actually used is ≤ 7, so harmless. | GGHV §6 E19 (TeX ~1839–1850) | KERNEL: valuation arithmetic in Leg D (v_{2,1}(3,1) = 7). Do not copy the "6". |
| 6 | (D̃²)_{−7} literal term: the display contains a literal `2 d_{−1} 0` term, in both §5 and §6. | GGHV §5 (TeX ~1680), §6 (TeX ~2040s) | CONFIRMED: TRUE − DISPLAY = 2d_{−10} exactly (Leg G SymPy); the literal term is identically zero; the filed Gröbner script's corrected form (with 2·dm10) is the true expansion. §5 displays no (D̃²)_{−6} equation; §6 displays (D̃²)_{−6} and (D̃²)_{−8} but excludes them from the 9-equation system. |
| 7 | §6 Remark cites Theorem 5.1 / `calculo de C` where Theorem 6.1 / `calculo de C para 7` are meant (the §6 remark repeats the §5 remark verbatim, including its labels). | GGHV §6 E20 (TeX 1934–1952) | Read with the §6 labels (Leg D `e20_assembly`). Intended reading unambiguous from context. |
| 8 | E21's proof writes `C_3` in the `D_j D_{k+3−j}` identity where `y` is meant; E6's proof writes "`P ∈ kK[x,y]`" (as printed) where `K[x,y]` is meant. | GGHV §6 E21 (TeX 1977–1994); §4 E6 (TeX ~681–997) | Flagged in the statement inventory; not copied literally. Leg D's E21 identity uses `y`. |
| 9 | (7,21) ℓ-formula strips an x¹⁴ factor: the text's `ℓ_{1,0}(P) = x^{28} λ_p (y − λ x^{−2})^{14}` (equivalently R = x²y − λ lacking an x factor) equals the face polynomial divided by x¹⁴; the correct face is λ_p·x¹⁴·R¹⁴ with R = x²y − λ. The (24,9) and (28,8) conclusions are literal; (7,21) is the odd one out. | GGHV §4 E8 (TeX 1313–1396) | KERNEL: `ell721_normalization` [propext, Quot.sound] (Phase 1 d1_cor74, re-pinned in Leg B). Prove the normalisation relation; do NOT copy the formula literally. |
| 10 | Valuation product-vs-sum typo: the paper writes v(C_{3−j}C_{3−k+j}) ≤ v(C_{3−j})·v(C_{3−k+j}) (product of valuations); it should be the sum. The bounds that follow are the sum, so harmless. | GGHV §5 E11 (TeX 1477, 1493); §6 E19 too | Lean proves the additive version from the valuation axioms (Leg D verified for §6; Leg C flagged for §5). |
| 11 | E5/E7 end-assignment swap: E7 sets (en(Q),en(P)) = ((2,1),(−1,0)), i.e. en(P) = (−k,0), en(Q) = (k+1,1), opposite to E5's assignment. (Not a slip in the paper's mathematics — a verified reading note.) | GGHV §4 E7 vs E5 | Verified against the φ-images by Leg B (both give the paper's finals). |
| 12 | (8,28) exponents: Part 19's (8,28) exponents 4·2=8 WRONG — (m,n)=(3,2), so 4·3=12. (Phase 1 record, carried forward.) | Phase 1 Part 19 | Do not use 4·2=8 anywhere. |

## §10. Files index + verification record

### Leg files (all scratch under `~/workspace/research/tooling/`)
- Leg A: `phase4_legA/gghv_full_s2s3_2026-11-06.lean` (645 lines) +
  `legA_full.log` (FULL_EXIT=0, 6 s) + `legA_axioms.log` (AXIOMS_EXIT=0,
  6 s, 21 theorems: 10 [] + 4 [propext] + 5 [triple] + 2 [propext,
  Quot.sound]) + `check_legA_2026-11-06.py` (28 checks ALL PASS, exit 0)
  + `legA_log.md`.
- Leg B: `phase4_legB/gghv_full_s4_2026-11-06.lean` (1,378 lines;
  FULL_EXIT=0, 7–8 s; second-tool Python 20/20 ALL PASS, PY_EXIT=0) +
  `legB_log.md`.
- Leg C: `phase4_legC/gghv_full_s5_2026-11-06.lean` (836 lines;
  FULL LEAN_RC=0, 42 s; AXIOMS LEAN_RC=0; 30 [triple] + 5 [propext,
  Quot.sound] + 2 [propext] + remainder []) + `gghv_full_s5_axioms_2026-11-06.lean`
  + `s5_axioms.log` + `legC_log.md` + `legG_phi_shift_check.log`
  (SymPy ALL_PASS=True).
- Leg D: `phase4_legD/gghv_full_s6_2026-11-06.lean` (1,613 lines;
  FINAL FULL EXIT 0, ~14 s; FINAL axioms EXIT 0; 80 theorems: 64
  [triple], 8 [propext, Quot.sound], 8 []) + `s6_axioms3.log` +
  `legD.log` + Singular re-run logs (elim/cert/groebner exit 0).
- Leg E: `phase4_legE/` (10 item files + index, 87 declarations;
  per-file FULL 7–14 s exit 0; `legE_log.md` axiom lists; `logs_vm/`)
  + second-tool Python ALL PASS exit 0 (19 checks) + Singular
  `jacobi_check.sing` JACOBI = 0 exit 0.
- Leg F: `phase4_legF/` (3 files, 5,686/5,119/5,700 lines; round-5
  logs: all three LEAN_EXIT=0, 0 error lines, NO sorryAx; md5s
  5db7b34420dcf8d111223e79aaed3f44 / 2e61236431142905b92d09252d1251f9 /
  159527f8326bf32e87276651054c5fcf) + `legF_log.md`. Assembly-agent
  re-verification (local, 2026-11-06/07): md5s and line counts recomputed
  — ALL MATCH the map exactly. `sorry` grep: 1 hit per file, each a
  header comment stating "NO sorryAx anywhere in this file (the assembler
  forbids `sorry`...)" (lines 32/43/55) — comment mentions only, no `sorry`
  in code. Axiom-distribution counts re-verified locally: Leg A 10 [] +
  4 [propext] + 5 [triple] + 2 [propext, Quot.sound] (21 total, matches);
  Leg C 30 [triple] + 5 [propext, Quot.sound] + 2 [propext] + 2 [] (39
  total, matches the map's "39 declarations"); Leg D 64 [triple] + 8
  [propext, Quot.sound] + 8 [] (80 total, matches).
- Leg G: `phase4_legG/` (7 scripts + `logs/` 9 files; all 7 scripts run
  on lean-build-3) + `legG_log.md`.
- Leg H: `phase4_legH/minor_spec_2026-11-06.md` + `extract_minor.py` +
  `det_minor.py` + `leg_log_2026-11-06.md` + `vm_out/out/` (det jsons).
- Retrieval: `hidden_files/phase4/retrieval/retrieval_log.md` (both
  targets NOT FOUND) + `arxiv_tex_numbering_note.md`.

### Assembly files
- `~/workspace/research/tooling/phase4_assembly/gghv_full_assembly_2026-11-06.lean`
  (3,165 lines) — FULL run 2026-11-07 ~02:07 UTC: FULL_EXIT=0, 135 s,
  0 errors (log `assembly_full.log`, 36,472 bytes; 98 warnings, all
  linter/deprecation noise — unused simp args/tactics, `if_pos`/`if_neg`
  deprecations already known from Leg B, unused variable names,
  mathlib/batteries local-changes notices; no errors, no sorryAx).
  AXIOMS run (repeat of the same file — the #print block for 11 theorems
  is in the file): AXIOMS_EXIT=0, 50 s, 0 errors (log
  `assembly_axioms.log`, 36,472 bytes — byte-identical size to the FULL
  log, determinism repeat). Per-theorem axiom lists:
  `prop41_conditional` [propext, Quot.sound], `prop42_conditional`
  [triple], `prop43_conditional` [propext, Quot.sound],
  `prop44_conditional` [triple], `thm51_conditional` [triple],
  `cor52_conditional` [], `prop42_shape_of` [triple],
  `prop41_shape_of` [propext, Quot.sound], `link_924_derived` [triple],
  `link_927_derived` [triple], `theorem21_minimal_v2` [triple] — all
  matching the legs' own reported lists (the B/C conditionals are
  re-verified by this run, not just re-quoted). The .lean file is
  byte-identical to the copy compiled on the VM (no post-run edits).
- `~/workspace/research/tooling/phase4_assembly/r8_axioms_2026-11-06.lean`
  (146 lines) — R8 six-theorem print 2026-11-07 ~02:08 UTC: rc=0, 15 s,
  0 errors (log `r8_axioms.log`, 1,088 bytes). Results in §2 R8 table:
  `esq3_dir_b2/b1/b0` [], `esq3_lform_endpoint_lo/hi` [propext],
  `esq3_lform_Q` [propext, Quot.sound].
- `~/workspace/research/tooling/phase4_assembly/assembly_log.md` —
  running log (append mode).

### What remains open (for the parent)
1. Laurent fold-in pass (E11/E19/E20/E23 — §7) — DONE 2026-11-07
   ~03:37 UTC (successor coordinator). Fragment verified on disk;
   inventory updated; ValAxioms diagnosis recorded.
2. Validation gate (G1) before any filing; then filing (Step 3), comb
   (Step 4), push-all (Step 5), §15/HLRE v5 filing (Step 6), finalization
   (whole-tree refresh, "Cite this repo" blocks, `branch_two_dicritical`
   rename — name still awaiting Brandon's choice).
3. Next attackable premises (not ordered — for the parent's call):
   `para_la_cota` (Leg F); the FinitasData univariate premises (Leg F);
   the (2a)→(2b) univariate common-power lemma + z-form reduction
   (Leg F); the §5/§6 9-equation derivations (Legs C/D, OPEN); the
   [GGV6] §7 argument over the π-root existence theory (Leg F);
   published [GGV1] §7 text + Joseph Lemma 2.2 (retrieval NOT FOUND —
   institutional access needs Brandon); the §5 min-degree ValCore on
   RatFunc K (Laurent fold-in remainder — the §5 (b_k)/(c_k) bounds);
   a Leibniz rule for `LaurentSeries.derivative` (Laurent fold-in
   remainder — `bracket_pow_C` + `hdeg`).
