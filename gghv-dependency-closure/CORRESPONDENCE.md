# Correspondence — GGHV dependency closure

This guide maps each filed Lean module and each Singular script in
`gghv-dependency-closure/` to the statement of the GGHV paper (Guccione et
al., 2022) or its cited [GGV*] machinery that it proves or recomputes, with
its HLRE v5 grade. The full per-file record — byte sizes, SHA-256 prefixes,
axiom counts, verification logs, carried premises, and exclusions — is in
`lean/MANIFEST.md` and `singular/MANIFEST.md`; this guide is the map, those
manifests are the record. Nothing here is truncated: every filed leg appears
below.

## Grade vocabulary (used throughout)

- **Kernel-verified** — the Lean kernel accepted the proof of that narrow
  claim, with the axiom list printed by `#print axioms`. A kernel-verified
  claim proved from carried premises is kernel-verified *conditionally on
  those premises*, and the premises are named.
- **Conditional** — proved from explicit unproved premises carried as
  hypotheses. The premises are part of the theorem statement.
- **I1** — independent recomputation (Singular / SymPy / python-flint),
  **not** kernel proof.
- **Permitted axiom triple** — `[propext, Classical.choice, Quot.sound]`.
  Every axiom list below is this triple, a subset of it, or zero axioms.
  `sorryAx` occurs nowhere.
- **Theorem R is excluded everywhere in this programme.** Nothing below
  proves JC(2) or excludes (72, 108) unconditionally.

## Sources

- [GGV1] Guccione, Guccione, & Valqui (2017), *J. Algebra* 471, 13–74, DOI
  10.1016/j.jalgebra.2016.08.039, arXiv:1401.1784v3. The paper's internal
  names (`le basico`, `le bbasico`, `extremos`, `esquina(1)–(3)`, `central`,
  `Cor. 7.4`, `Theorem 2.1`) are the [GGV1] section/lemma names.
- GGHV (Guccione et al., 2022), Proposition 4.3 and its §2 table, §3, §5,
  §6, Parts 11–12.
- [GGV5] the enumeration the §2 table rests on; [GGV6] Theorem 7.3;
  [GGV3] §5; [M] case 64; Joseph (1975), *Amer. J. Math.* 97, 597–615,
  Lemma 2.2 and `Lema Joseph`.

## Lean modules → paper statements

| File (`lean/`) | Paper statement | Headline theorem(s) | Grade and axioms |
|---|---|---|---|
| `d1_lebasico_full_2026-11-05.lean` | [GGV1] `le basico` (paper gives no proof) | `endpoint_slice_max` (closes the vertex-incidence gap); `breakpoint_between` (replaces the refuted chord-normal route) | Kernel-verified; `le_basico_full` on the permitted triple. Build round 1 `LEAN_EXIT=1` (superseded), round 2 `LEAN_EXIT=0`. |
| `d1_lebbasico_2026-11-05.lean` | [GGV1] `le bbasico` | `le_bbasico`: consecutive directions hold iff they share a vertex | Kernel-verified; `le_bbasico` on the permitted triple. |
| `d1_extremos_2026-11-05.lean` | [GGV1] `extremos` (480 inequality; 694 aligned; 721 non-aligned) + commutator valuation | `extremos_alineados` (694), `extremos_noalineados_st`, `extremos_noalineados_en` (721), `en_sum_eq_one_one`, `bracket_val_le` (480) | Kernel-verified; 4 lines on the permitted triple, `bracket_val_le` on `[propext, Quot.sound]`. |
| `d1_esquina1_2026-11-05.lean` | [GGV1] `esquina(1)` | `esquina_item1`: `Dir` membership + all three caso-alineado inequalities; `(a', b')` via Bézout from `gcd(m, n) = 1` | Kernel-verified; 3 lines on the permitted triple. Finding: `hmn` (`m ≠ n`) is unused by the proof. |
| `d1_esquina2_2026-11-05.lean` | [GGV1] `esquina(2)` | `esquina_item2`; `esquina_item2_k1` (`k = 1` gives `{(−1, 0), (2, 1)}`, Part 18's form derived) | Kernel-verified; 3 lines on the permitted triple, `succMin_eq` on zero axioms. Gap: the paper states `m, n ∈ ℕ` but the proof needs `m, n > 1`. |
| `d1_esquina3_2026-11-05.lean` | [GGV1] `esquina(3)`, direction half | `esquina_item3_dir`, `esquina_item3_dir_cases`, `minkPow_complete`: `(ρ₂, σ₂) = (−1, 3)`; `b' ∈ {0, 1, 2}` | Kernel-verified conditionally on `hdir`, `hcent`, `hprim`; 3 lines on the permitted triple. The `ℓ`-form is **not** proved. |
| `d1_central_2026-11-05.lean` | [GGV1] Theorem `central` | `central_conditional`: `vF = ρ + σ` with items (2), (3), (4); key lemma `coeffAt_pmul_top_gen2` | Kernel-verified conditionally; 10 lines on the permitted triple, 1 on `[propext]`. Carried: Joseph 2.2 (not located; naive un-homogeneous form is false), `Lema Joseph` (not proved), `[F, ℓ(P)] = ℓ(P)` (not proved). Items (5) and (1) carried. |
| `d1_cor74_2026-11-05.lean` | [GGV1] Corollary 7.4 (F/F1 twins) | `cor74_F_conditional`, `cor74_F1_conditional`; `cor74_exponent` on `[propext]`; `cor74_assembly` on `[propext, Quot.sound]`; `ell721_normalization` proved | Kernel-verified conditionally (condition (3) + carried central premises); 35 axiom lines: 14 triple, 6 `[propext, Quot.sound]`, 13 `[propext]`, 2 zero. Corrections: text's `R = x²y − λ` lacks an `x` factor (correct face `λ_p · x¹⁴ · R¹⁴`); Part 19's `4·2 = 8` is wrong, `4·3 = 12`. |
| `d1_assembly_2026-11-05.lean` | [GGV1] Theorem 2.1 (from the §3, §5, §6 routes + [GGV5] enumeration) | `theorem21_minimal` (11-field premise list); `discard_84_row`; `table_cases` | Kernel-verified conditionally on the 11-field list; `theorem21_minimal` on `[propext]` only, `discard_84_row` on zero axioms, `table_cases` on `[propext]`. Finding: the (7, 21) row **is** the `max = 84` row. No unconditional theorem. |
| `d1_ggvstar_2026-11-05.lean` | [GGV*] machinery: [GGV6] Thm 7.3; Prop 3.29, 1.13, 2.1, 2.11, 6.1; Cor 7.2; Thm 7.6 | Thm 7.3 combination + `F₉` arithmetic; Prop 3.29 (conditional); Prop 1.13 both directions; Prop 2.1(1); (8, 24) row conditional on [GGV5] Prop 6.1 | Kernel-verified conditionally; 71 axiom lines: 37 triple, 12 `[propext, Quot.sound]`, 14 `[propext]`, 8 zero. Correction: `N₁ = 6`, `N₂ = 3` (integers), not `5/3`, `3/2`. Carried: Thm 7.6(5) (numbering unresolved), Prop 2.11(3), Prop 2.1(2b), Prop 3.12, enumeration, 4 of 5 red rows. |
| `d1_d2combine_2026-11-05.lean` | [GGV1] D2 combine (pairwise → combined bracket) + dependents | Bridge lemma (combined top coefficient = endpoint coefficients × cross product, `k = 1` reduced/`Nodup`); combined-form `extremos`; D2 power laws (`pscale`/`pbracket`); `common_power_coprime`; Remark conditionally on `alineados(2a)`; `mayores` T-termination (Stage D); `lema_geometrico_1`, `lema_geometrico_2` | Kernel-verified (Remark only conditionally); 72 axiom lines: 39 triple, 11 `[propext, Quot.sound]`, 14 `[propext]`, 8 zero. |
| `d1_d2combine_axioms_2026-11-05.lean` | Same as `d1_d2combine` | The D2 combine development with a 127-line `#print axioms` block appended (126 distinct names; `stFace_swap` printed twice) | Kernel-verified; run log 126 verdict lines: 67 triple, 30 `[propext, Quot.sound]`, 20 `[propext]`, 9 zero; 0 errors. File header text is stale (describes the extremos base). |
| `bridge_attempt_2026_11_04.lean` | GGHV Prop. 4.3 case (1) — the certificate interface | `bridge_Fpoly` (`Fpoly = Fpoly2`, six generators in order 0–5); `hsupp_chart`; `hA2_chart`; `challenge_target : ChartEmptyC_T1ne0 L` at `ρ = Fin 3199`, `p = 32003`, `w₀ = 11147` | Kernel-verified, **no hypotheses**; `challenge_target` on the permitted triple. R109Data/K5 not needed. Filed as tracked module `GradeA.Bridge` (`branch_c/grade_a/lean/GradeA/Bridge.lean`, `build_bridge.sh`) 2026-11-06; re-verified on lean-build-3. |
| `composition_2026-11-04.lean` | GGHV Prop. 4.3 case (1) — elimination | `branch_c_eliminated`: `¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNFc P Q ∧ jac P Q = C lam * X 0 ^ 2`, over any field of characteristic 0 | Kernel-verified, **no hypotheses**; on the permitted triple. With the branches (a),(b) `main_theorem` (case (2)), the Prop. 4.3 split is fully eliminated in Lean. Does **not** claim (72, 108) excluded unconditionally or JC(2). Filed as tracked module `GradeA.Composition` (`branch_c/grade_a/lean/GradeA/Composition.lean`, `build_bridge.sh`) 2026-11-06; re-verified on lean-build-3. |

## Singular scripts → recomputations

| Script (`singular/`) | What it recomputes | Verdict (log) |
|---|---|---|
| `extract_cert_2026-11-05.py` | Extracts the Parts 11–12 certificate identities verbatim from the Lean files (independent of `ring`) | The extracted identities are the ones the `cert` scripts check. |
| `d1_singular_cert_s5_2026-11-05.sing` | §5 (Part 11) D3 certificate identities | `CERT_DIFF = 0`, `CERT_IS_ZERO = 1`. |
| `d1_singular_cert_s6_2026-11-05.sing` | §6 (Part 12) D3 certificate identities | `CERT_DIFF = 0`, `CERT_IS_ZERO = 1`. |
| `d1_singular_elim_s5_2026-11-05.sing` | §5 principal-equation elimination, Route A' (resultants) | `Res = (−19683/64) · target · dm1³`; `reduce = 0` at `k = 0`. SymPy re-run agrees (quotient `−27/(64·dm1³)`). |
| `d1_singular_elim_s6_2026-11-05.sing` | §6 principal-equation elimination, Route A' (resultants) | Same as §5: `Res = (−19683/64) · target · dm1³`; `reduce = 0` at `k = 0`. SymPy agrees. |
| `d1_singular_groebner_s5_2026-11-05.sing` | §5 elimination, Route B (Gröbner `eliminate` of the full 9-equation ideal) | Ideal is principal, generator exactly the target: `ELIM_IDEAL_SIZE 1`, `reduce(target, E) = 0`. |
| `d1_singular_groebner_s6_2026-11-05.sing` | §6 elimination, Route B | Same as §5: `ELIM_IDEAL_SIZE 1`, `reduce(target, E) = 0`. |
| `d1_singular_numerics_2026-11-05.sing` | §3 numerics; §4 degree/gcd arithmetic | `I_M = 4`, `I_m = 5`; `4 + gcd(8, 4) = 8` (since `gcd(8, 4) = 4`, `4 + 4 = 8`); Part 4 bounds 75, 76, 78; degrees 27, 27; `gcd(72, 108) = 36` (since `72 = 36 × 2`, `108 = 36 × 3`); ratio `(2, 3)`. Flint cross-check passes. |
| `d1_singular_pllc_2026-11-05.sing` | [GGV5] enumeration first stage (piecewise-linear-candidate filter) | `pllcFilter(8, 3) = 1`, `pllcFilter(8, 4) = 0`; 18 candidates with `a ≤ 9`; Python agrees. |
| `d1_singular_pllc_fix_2026-11-05.sing` | Fix to the `pllc` script (Singular has no `list == list`; membership re-checked component-wise) | Component-wise check agrees with Python. One fix, not a second computation. |
| `d1_singular_table_enum_2026-11-05.py` | §2 table, all 10 rows (Python exact integers + python-flint primary) | OVERALL ALL PASS. Max degrees `[64, 112, 75, 75, 84, 96, 108, 120, 99, 108]`; 5 red rows; survivors `[(108, 72), (66, 99), (72, 108)]`. |

All Singular verdicts are status **I1** (independent recomputation, not kernel
proof). Tools: Singular 4.3.1, SymPy 1.14.0, python-flint 0.9.0, on
lean-build-3. Not recomputed: [GGV5] enumeration completeness, the PFL
generative use, the family-to-row attribution, and the derivation of the 9
equations from the C/F/D expansions (the elimination shows only that *if* the
9 equations hold, *then* the principal equation holds).

## Relation to the branch packages

- **Branch (c).** The frozen v3.1 bundle
  (`JC2D-branches_a_b_c_unified/branch_c/bundle_v3_1/`) holds the branch-(c)
  elimination under its §10 computational premises (grade B outside Lean).
  The two files `lean/bridge_attempt_2026_11_04.lean` and
  `lean/composition_2026-11-04.lean` sit **outside** that bundle: they close
  branch (c) unconditionally in Lean (see the `branch_c_eliminated` row
  above) by instantiating the bundle's certificate interface at the concrete
  data. Since 2026-11-06 they are also filed as tracked modules alongside
  grade A — `grade_a/lean/GradeA/Bridge.lean` (`GradeA.Bridge`,
  `challenge_target`) and `grade_a/lean/GradeA/Composition.lean`
  (`GradeA.Composition`, `branch_c_eliminated`), compiled and audited by
  `grade_a/build_bridge.sh` (status: `grade_a/BRIDGE_STATUS_2026-11-06.md`);
  the `lean/` copies stay as the filed leg record. The branch-(c)
  correspondence guide
  (`JC2D-branches_a_b_c_unified/branch_c/correspondence_guide/CORRESPONDENCE_GUIDE.md`)
  records this in its §1 addenda; the guide's source freeze is unchanged.
- **Branches (a),(b).** The (a),(b) elimination is recorded in the
  branch-(a,b) correspondence guides and is not repeated here; the
  dependency-closure legs above use its results only where stated (the
  `le basico`/`le bbasico` layer and the top-layer classification).
- **Grade-A package.** The grade-A modules (A1, A2, `hsupp2`, R67Data,
  R109Data, IrreducibleR, IrreducibleR109, K5Field, Transfer, Macaulay,
  Axioms) live at `JC2D-branches_a_b_c_unified/branch_c/grade_a/` and are
  referenced, not duplicated, by the files in `lean/` (see
  `lean/MANIFEST.md`).
- **Two dicritical divisors.** The two-dicritical paper is filed at
  `branch_two_dicritical/paper/` and at the repository root as
  `combined_paper_final_2026-11-04.tex` / `.pdf` (67 pages, canonical
  latest; the branch copy is archival). The two-dicritical claim itself is
  **not** part of the dependency-closure programme and is not graded here;
  see `branch_two_dicritical/CORRESPONDENCE.md` and the README status
  section.

## Still open — updated to the Phase 4 verdicts (2026-11-07)

The full still-open list is in the README ("GGHV dependency closure" section)
and in `lean/MANIFEST.md` / `singular/MANIFEST.md` per file. Most Phase 1
items are now closed — in one line each: combined-form esquina(1)/(2)
restatements — **KERNEL** (R10); the (7, 21) coefficient identity —
**KERNEL** (R11); the Remark's two face laws + `alineados(2a)` — **KERNEL**
(R12); esquina(3)'s `ℓ`-form — **CONDITIONAL** (R8); central's
`[F, ℓ(P)] = ℓ(P)` cancellation gap — **KERNEL + CONDITIONAL** (R9); `m, n >
1` — **KERNEL as a documented deviation** (R15); hybrid-vs-slip — kernel
arithmetic done, question **OPEN** (R16); the §6 `k = 2` derivation +
non-square contradiction — **KERNEL**, E18 as a whole **CONDITIONAL**; §5
rescaling + the degree-78 endgame — kernel theorems, E10 as a whole
**CONDITIONAL**; the 9 equations' D2 derivation — **I1** on the computational
steps, Lean-only parts delimited, not a Lean proof (R23). Still **BLOCKED**:
[GGV5] completeness; Prop 2.1(2a)→(2b); [GGV6] Thm 7.3 NOT PROVED. Still
open: Joseph Lemma 2.2 (not located); `Lema Joseph` (not proved); the
published [GGV1] §7 text (missing).

---

## Phase 4 — the GGHV paper proved in full (filed 2026-11-07)

**Honest headline: the paper is NOT proved unconditionally.** No
numbered environment is fully proved unconditionally; Theorem 2.1 is
CONDITIONAL from the 20-field `MinimalPremises2`. Nothing here proves
JC(2), proves Theorem R, or excludes (72, 108) unconditionally. The
definitive per-item verdict record is
`gghv_full_assembly_inventory.md`; the independent validation is
`validation_g1/g1_validation_report_2026-11-07.md` (CONDITIONAL GO).
The per-file record — byte sizes, SHA-256, axiom lists, verification
logs, carried premises, exclusions — is in `lean/MANIFEST.md` (§ Phase
4) and `singular/MANIFEST.md` (§ Phase 4); this section is the map.

| File (`lean/`) | Paper statement | Headline theorem(s) | Grade and axioms |
|---|---|---|---|
| `gghv_full_s2s3_2026-11-06.lean` | GGHV §2 table + §3 discards | `gghv_table_full` []; `discard_84_row` / `discard_120_row` [] | KERNEL table arithmetic; red rows CONDITIONAL (carried to Leg F); completeness BLOCKED. 21 theorems: 10 [] + 4 [propext] + 5 [triple] + 2 [propext, Quot.sound]. Leg A's header claim about the [GGV5] TeX §6 was WRONG (inventory §8) and was corrected comment-only 2026-11-07 per inventory §8's directive (new sha256 in `lean/MANIFEST.md`); the inventory §8 determination stands as the record of the original error. |
| `gghv_full_s4_2026-11-06.lean` | GGHV §4, Props 4.1–4.4 + PSP algorithm (E5–E9) | `prop41_conditional`; `prop42_conditional`; `prop43_conditional`; `prop44_conditional`; `psp_183` | E5–E8 CONDITIONAL on named `Prop4xPremises`; E9 KERNEL output, correctness CONDITIONAL. `prop41`/`prop43` [propext, Quot.sound]; `prop42`/`prop44` [triple]; `psp_183` [propext]. Second tool 20/20 ALL PASS. |
| `gghv_full_s5_2026-11-06.lean` | GGHV §5, Thm 5.1 + `calculo de C` (E10–E17) | `thm51_conditional`; `cor52_conditional`; `e13_f_separable`; `e16_principal` | E10 CONDITIONAL; E11 PARTIAL; E12 PARTIAL; E13 KERNEL; E14 CONDITIONAL; E15 KERNEL arithmetic + CONDITIONAL bounds; E16 KERNEL (elimination only), derivation OPEN; E17 CONDITIONAL. 39 decls: 30 [triple] + 5 [propext, Quot.sound] + 2 [propext] + 2 []. |
| `gghv_full_s5_axioms_2026-11-06.lean` | (axioms-print companion to the §5 file) | 39 `#print axioms` lines | No new theorems. Log `s5_axioms.log`. |
| `gghv_full_s6_2026-11-06.lean` | GGHV §6, Thm 6.1 + `calculo de C para 7` (E18–E23) | `s6_theorem61`; `s6_principal_eq`; `e23_ode_unique`; `e20_assembly` | E18 CONDITIONAL; E19 PARTIAL; E20 KERNEL modulo Ptcoef input data; E21 CONDITIONAL; E22 KERNEL (elimination/displays only), derivation OPEN; E23 PARTIAL. 80 theorems: 64 [triple], 8 [propext, Quot.sound], 8 []. **C1(a): `e19_bound_step_21/_1m1/finite_bounds` are kernel-proved implications, NEVER instantiable with v_{2,1}/v_{1,−1} (ValAxioms uninstantiable) — do not cite as instantiated.** |
| `gghv_full_s6_2026-11-06_axioms.lean` | (axioms-print companion to the §6 file) | 80 `#print axioms` lines | No new theorems. Log `s6_axioms3.log`. |
| `gghv_full_esquina3l_2026-11-06.lean` | [GGV1] esquina(3), ℓ-form (R8) | `esq3_dir_determination`; `esq3_lform_from_cube`; `esq3_lform_Q` | KERNEL arithmetic + CONDITIONAL ℓ-form assembly. Endpoint/Q theorems re-printed by the assembly R8 run with identical lists. `esq3_lform_from_cube` CONDITIONAL on the common-power + cube premises (carried). |
| `gghv_full_central_gaps_2026-11-06.lean` | [GGV1] `central` gaps (R9) | `central_cancellation`; `joseph_counting_contradiction` | KERNEL + CONDITIONAL. `central_eq_central_from_joseph22` [propext] on the named `Joseph22HomogForm` premise. Joseph Lemma 2.2 itself NOT FOUND. |
| `gghv_full_esquina_combined_2026-11-06.lean` | Combined-form esquina(1)/(2) (R10) | `esquina2_combined`; `esquina1_bundle_iff` | KERNEL. `esquina2_*` [triple]; `esquina1_bundle_iff` []. |
| `gghv_full_721_coeff_2026-11-06.lean` | The (7,21) coefficient identity (R11) | `face721_*`; `face721_factor_count` | KERNEL. `face721_*` [triple]; `face721_factor_count` [propext]. |
| `gghv_full_remark_facelaws_2026-11-06.lean` | Remark "a remark" face laws + alineados(2a) (R12) | `alineados_2a_from_2b`; `remark_ratio` | KERNEL. Mostly [triple]; `tpow_exp_smul` [propext, Quot.sound]. |
| `gghv_full_d1_theory_2026-11-06.lean` | D1 full theory (R13) | `dirLt_trans_halfplane`; `succOp_spec` | KERNEL. `stFace`/`enFace` ↔ CCW bridge still open. |
| `gghv_full_d2_poly_2026-11-06.lean` | D2 polynomial bracket (R14) | `pderiv_comm`; `pbracket_jacobi` | KERNEL, all [triple]. Translation chain rule CONDITIONAL on the `pderiv`/`aeval` commutation. |
| `gghv_full_mn_gt1_2026-11-06.lean` | m,n > 1 as literally written (R15) | `mn_gt1_dir_mem` | KERNEL as documented deviation: the paper states m,n ∈ ℕ but esquina(2)'s proof needs m,n > 1 — a genuine minor gap as literally written. |
| `gghv_full_hybrid_slip_2026-11-06.lean` | Hybrid-vs-slip (R16) | `hybrid_slot_249/288/927/721` | KERNEL arithmetic [triple]; the hybrid-vs-slip question itself stays OPEN (published §7 NOT FOUND). |
| `gghv_full_mayores_2026-11-06.lean` | `mayores` full statement (R17) | `mayores_chain_terminates`; `mayores_full_conditional` | KERNEL / CONDITIONAL. |
| `gghv_full_ggv1_2026-11-06.lean` | (Leg E index — comment-only header) | — | No theorems, no axioms log. Filed as the leg's index. |
| `gghv_full_ggvstar_2026-11-06.lean` | [GGV2] Prop 3.12 / 3.29 / Remark 3.31 / Def 3.21 (R18/R20) | `finitas_of_data`; `prop329_of_data`; `remark331_of_data` | CONDITIONAL on named `FinitasData` premises. All [triple]. Round-5 clean pass. |
| `gghv_full_ggvstar_ggv1_2026-11-06.lean` | [GGV1] Thm 7.6(5), Prop 2.11(3), Prop 2.1, D2 power laws (R18) | `divisibilidad_gghv_use8`; `pavadass3_of_descended`; `prop21_two_a_of_b`; `coeffAt_pmul_assoc`; `ppow_add_kt`; `ppow_mul_kt` | Thm 7.6(5) / Prop 2.11(3) CONDITIONAL; (2b)→(2a) KERNEL-clean; (2a)→(2b) BLOCKED; power laws PROVED — `coeffAt_pmul_assoc` **[propext, Quot.sound]** (G1 F1, not [triple]); `ppow_add_kt`, `ppow_mul_kt` [triple]. Round-5 clean pass. |
| `gghv_full_ggvstar_ggv6_ggv5_2026-11-06.lean` | [GGV6] Thm 7.3, [GGV5] completeness, four red rows (R19/R20) | `ggv6_discard84_from_thm73`; `enum_complete_of_links`; `redrow_*_conditional` | Thm 7.3 NOT PROVED as a theorem; completeness BLOCKED (open links `hchain`/`hattrib`); red rows CONDITIONAL. All [triple] except `redrow_520_32_of_23` []. Round-5 clean pass. |
| `gghv_full_laurent_2026-11-06.lean` | Laurent fragment: E11/E19/E20/E23 fold-in | `exists_sqrt_series`; `laurent_series_discharge_s6`; `exists_tilde`; `bracket_reduction_discharge` | E11 PARTIAL (generic sqrt-series lemma KERNEL; §5 instance NOT separately applied — G1 F2); E19 PARTIAL (existence + bounds KERNEL, F CONDITIONAL); E20 KERNEL modulo Ptcoef input data; E23 PARTIAL (`hdeg` carried). 87 theorems, AX_FULL_RC=0, sorryAx 0. First AX_FULL attempt failed RC=1 (wrong `#print` namespaces), fixed, final clean (C1(d)). |
| `gghv_full_assembly_2026-11-06.lean` | Assembly: Theorem 2.1 from `MinimalPremises2` | `theorem21_minimal_v2`; `link_924_derived`; `link_927_derived` | CONDITIONAL (20-field premises; fields 9–10 refined, not discharged). All [triple] except `prop41_shape_of` / `prop41_conditional` / `prop43_conditional` [propext, Quot.sound] and `cor52_conditional` []. FULL_EXIT=0 (135 s), AXIOMS_EXIT=0 (50 s). |
| `r8_axioms_2026-11-06.lean` | (R8 axioms-print companion) | `esq3_dir_b2/b1/b0`; `esq3_lform_endpoint_lo/hi`; `esq3_lform_Q` | [] / [propext] / [propext, Quot.sound]. rc=0, 15 s. |

**Leg H — explicit maximal minor (PARTIAL, narrowed):** filed at
`JC2D-branches_a_b_c_unified/branch_c/rank_lemma_check/` —
`minor_spec_2026-11-06.md` + `extract_minor.py` + `det_minor.py` +
det jsons (`rows.json`, `piv.json`, `pivcols.json`, `colv.json`,
`det_p32003.json`, `det_p1000003.json`) + `summary.json` /
`globals.txt`. Indices + modular determinants DONE (p=32003 →
29127; p=1000003 → 262898; both routes agree); the K₅ determinant
value is NOT done; §6.3(a) satisfaction is Brandon's judgement call;
outside-project rebuild NOT DONE. I1 identification, not a kernel
proof. The 79 MB `INVERSE.pkl` is already tracked in the repo and is
referenced by path + sha256 only, never re-filed.

**C1(c):** the E7 eliminations (branches (a)/(b)/(c)) are carried from
the prior GradeA verification (commit 7e4db07f), NOT re-verified by
gate G1.

**HLRE v5 §15 amendment (filed 2026-11-07):** `HLRE-v5-section15-AMENDMENT-2026-11-06.md` amends the §15 closing paragraph and reference [9] of HLRE v5 (McCrary & Muse, 24 Sep 2026; approved as written 2026-11-06; grade A retained; [9] is the combined paper). The filed v5 PDF itself is untouched.

## Singular scripts → recomputations (Phase 4)

| File (`singular/`) | Recomputation | Result |
|---|---|---|
| `gghv_full_singular_table_s5_2026-11-06.sing` (+ `table_filed_py` cross-check) | §2 table + §3 numerics (R21) | I1 PASS (BAD_ROWS = 0) |
| `gghv_full_singular_ggv5_families_2026-11-06.sing` + `_py_2026-11-06.py` | [GGV5] generative step + attribution (R22) | I1 PASS (all 7 family checks = 1; cross-check ALL PASS) |
| `gghv_full_singular_e13_ode_2026-11-06.sing` + `_sympy_2026-11-06.py` | E13 ODE / separability | I1 PASS (Singular rc=0; SymPy script rc=1 with logged DECOMPOSED defects — see `lean/MANIFEST.md` §4.3) |
| `gghv_full_singular_nine_eq_2026-11-06.sing` + `_sympy_2026-11-06.py` | 9-equation D-scaling / displays (R23) | I1 PASS on the computational steps (both tools); two Singular script bugs REPORTED, not fixed (two-symbol C₃; 32-bit `int` overflow of 13!/14!) |
| `e13_singular_check.sing` / `e13_sympy_check.py` | Leg C E13 second-tool check | See `singular/logs/e13_*` |
| `legG_phi_shift_check.py` | φ-shift: x²-coefficient D₂−3t | CONFIRMED by both tools (t=D₂ → −2D₂; t=D₂/3 → 0) |
| `lift_s6_extra.sing` / `lift_s6_square.sing` | Leg D §6 lift attempts | TIMEOUT 600 s (inconclusive) / explicit lift coefficients NOT obtained |
| `member_s6_extra.sing` / `member_s6_square.sing` | Leg D §6 membership | Extra identities ARE in the 9-equation ideal; square identity follows up to the nonzero factor y⁹ (no explicit lift, hsq stays a premise) |
| `jacobi_check.sing` | Leg E Jacobi identity | JACOBI = 0, BRACKET_AB = −x²−1, exit 0 |
