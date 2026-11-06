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
| `bridge_attempt_2026_11_04.lean` | GGHV Prop. 4.3 case (1) — the certificate interface | `bridge_Fpoly` (`Fpoly = Fpoly2`, six generators in order 0–5); `hsupp_chart`; `hA2_chart`; `challenge_target : ChartEmptyC_T1ne0 L` at `ρ = Fin 3199`, `p = 32003`, `w₀ = 11147` | Kernel-verified, **no hypotheses**; `challenge_target` on the permitted triple. R109Data/K5 not needed. |
| `composition_2026-11-04.lean` | GGHV Prop. 4.3 case (1) — elimination | `branch_c_eliminated`: `¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNFc P Q ∧ jac P Q = C lam * X 0 ^ 2`, over any field of characteristic 0 | Kernel-verified, **no hypotheses**; on the permitted triple. With the branches (a),(b) `main_theorem` (case (2)), the Prop. 4.3 split is fully eliminated in Lean. Does **not** claim (72, 108) excluded unconditionally or JC(2). |

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
  data. The branch-(c) correspondence guide
  (`JC2D-branches_a_b_c_unified/branch_c/correspondence_guide/CORRESPONDENCE_GUIDE.md`)
  records this in its §1 addendum; the guide's source freeze is unchanged.
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

## Still open

The full still-open list is in the README ("GGHV dependency closure" section)
and in `lean/MANIFEST.md` / `singular/MANIFEST.md` per file. In one line each:
combined-form esquina(1)/(2) restatements; the (7, 21) coefficient identity;
the Remark's two face laws + `alineados(2a)`; esquina(3)'s `ℓ`-form;
central's `[F, ℓ(P)] = ℓ(P)` cancellation gap; `m, n > 1`; hybrid-vs-slip;
the §6 `k = 2` derivation + non-square contradiction; §5 rescaling + the
degree-78 endgame as Lean proofs; the 9 equations' D2 derivation; [GGV5]
completeness; Joseph Lemma 2.2 (not located); `Lema Joseph` (not proved);
the published [GGV1] §7 text (missing).
