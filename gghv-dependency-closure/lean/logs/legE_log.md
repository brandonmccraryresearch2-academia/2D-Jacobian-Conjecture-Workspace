# Leg E log — [GGV1] remainder (R8–R17), Phase 4

**CLAIM:** Scratch proofs + verdicts for the [GGV1] machinery remainder.
**STATUS:** In progress, 2026-11-06. Retrieval leg COMPLETE before this log's
first entry: BOTH targets NOT FOUND (see
`hidden_files/phase4/retrieval/retrieval_log.md`). Joseph's paper title is
"The Weyl algebra — semisimple and nilpotent elements", Amer. J. Math. 97
(1975), 597–615 — the shorthand "The Jacobian conjecture in dimension 2" is
WRONG (confirmed three ways in the log) and is never used in this leg.
Published [GGV1] §7 text NOT FOUND: R15 is resolved as a documented deviation
(arXiv-TeX wording flagged as NOT the published wording); R16 stays an
explicit open item with both readings stated; Joseph Lemma 2.2 is carried as
an explicit named premise in the HOMOGENEOUS form only (naive form FALSE).

## 2026-11-06 ~15:29 CST — Leg E started
- Read phase4_map.md §5/§6/§8/§9, inventory.md (full, incl. all 2026-11-04
  addenda), gghv_statement_inventory.md §3c, Phase 1 files
  (d1_esquina3, d1_central, d1_cor74, d1_d2combine, d1_esquina1/2 headers +
  theorem lists), verification logs (exact invocation: `lake env printenv
  LEAN_PATH` in the branches_a_b/lean project, then
  `LEAN_PATH="$LP" lean --root=/tmp -o /tmp/x.olean /tmp/x.lean`; axioms run
  = second run with appended `#print axioms`), lean_large_build_chunking
  skill, and the [GGV1] TeX at the cited lines (le basico 1351, Lema Joseph
  620, central 826–900, alineados 514–559, Remark "a remark" 1197–1240,
  lema geometrico 1535/1551, mayores 3799–3838, F 4077–4110, F1 4238,
  esquina 5320–5585) via a latin-1 decode.
- VM lock held by legC at first check (age 89s) — writing files first,
  verifying when the lock frees. No repo commits (validation gate).
- R11 pinned: the (7,21) coefficient identity = the coefficient-level bridge
  at the (7,−2) face with the ppow expansion (binomial coefficients of
  ((z^7−α₁)²(z^7−α₂))ᵐ); see d1_d2combine header + memory 2026-11-05.

## 2026-11-06 ~16:00 CST — VM lock wait
- All 10 split files + probe + index written (see dir listing). No `sorry`/
  `axiom` in any file (grep-checked; only header mentions of the words).
- First `vm_lock.sh acquire legE 1800` TIMED OUT (1800 s): legC still
  holds the lock (age 2368 s at check; lock dated 2026-11-06T21:29:00Z).
  Lock is NOT stale (< 3 h) — not broken, per the lock rules.
  Re-acquiring with a 3600 s timeout in the background.

## 2026-11-06 ~16:30 CST — VM lock wait (continued)
- Second `vm_lock.sh acquire legE 3600` process was lost without a
  delivered result (session dropped during runtime MEMORY.md watcher
  events). Lock state at re-check: legC holds a FRESH lock dated
  2026-11-06T22:11:17Z (pid 22986; the earlier 21:29 lock is gone, so
  legC released and re-acquired). Age 1608 s at check. NOT stale.
  Re-acquiring with a fresh 3600 s timeout.

## 2026-11-06 ~17:20 CST — VM lock ACQUIRED
- Third acquire succeeded after 2541 s (legC released between checks).
  Lock held by legE (pid 1830). Running verification now: probe first,
  then all files (FULL + AXIOMS), then second-tool checks.

## 2026-11-06 ~18:00 CST — Round 1 results (Lean 4.34.0 / Mathlib, lean-build-3)
FULL+AXIOMS exit 0: R9 (central gaps), R15 (m,n>1), R17 (mayores),
INDEX. FAIL: R8 (1 err), R10 (28), R11 (3), R12 (6), R13 (Decidable
succOp), R14 (pbracket/translate noncomputable + name clash), R16
(trailing doc-comment). Probe file fails by design (unknown API
constants). Probe2 (pderiv API) PASSED exit 0: map_add/map_sub work
on the Derivation; smul via smul_eq_C_mul + pderiv_C_mul; pderiv_comm
proved via induction_on' (monomial/add). Probe3 PASSED exit 0: R11
base identity via map_add/map_mul/map_pow/map_ofNat + ring; coeffs via
controlled simp only + norm_num; remainder degree via natDegree
bounds; R12 remark_ratio via field_simp alone, st-scaling via
smul_eq_mul + div_mul_cancel₀.
Round-1 fixes applied: R8 drop stray `ring`; R10 ℤ casts for (-k,0)/
(k+1,1); R11 probe3 proofs; R12 Nat.cast_ne_zero + smul_eq_mul +
drop ring after field_simp; R13 `open Classical in` on succOp; R14
`noncomputable def pbracket`, `translate` renamed `phiTranslate`
(root-level name clash), drop unused simp args; R16 trailing comment
to plain block comment. Round 2 running.

## 2026-11-06 ~18:35 CST — Round 2 results (Lean 4.34.0 / Mathlib, lean-build-3)
Round 2 FULL+AXIOMS exit 0: R8, R9, R11, R12, R14, R15, R16, R17, INDEX.
Round 2 FULL exit 1: R10 (tuple-ascription syntax `(a, b : T)` invalid;
fixed to `((a, b) : T)`), R13 (`open Classical in` after a doc comment
invalid — moved above it; `choose_spec` needed a named `hex` existence
proof). Round 3 (R10+R13 only): FULL exit 0 both; AXIOMS R10 exit 0;
AXIOMS R13 exit 1 ONLY because the ad-hoc inline invocation stripped
the `'` from `dirLt_irrefl'`/`dirLt_asymm'` (shell quoting) — rerun via
script file `rerun_r13_axioms.sh`: AXIOMS R13 exit 0, 11 s.
Per-file FULL timings (round 2): R8 12 s, R9 11 s, R11 12 s, R12 11 s,
R14 12 s, R15 11 s, R16 10 s, R17 10 s, INDEX 7 s; R10 11 s, R13 10 s
(round 3). AXIOMS runs 10–14 s each. No `sorry`/`sorryAx` anywhere
(grep-checked); no `axiom` declarations in code.

## Exact axiom lists (from `#print axioms` runs, round 2 + R13 rerun)
Permitted triple: [propext, Classical.choice, Quot.sound]. Every list
below is a subset of it, or empty. No other axiom appears anywhere.
- R8: esq3_val_8_3: [] | esq3_mn_sum: [propext, Quot.sound] |
  esq3_dir_determination: [propext, Classical.choice, Quot.sound] |
  esq3_phi_aligned_impossible: [propext, Quot.sound] |
  esq3_phi_nonaligned_impossible: [propext, Quot.sound] |
  esq3_lform_term_val: [propext] |
  esq3_lform_from_cube: [propext, Quot.sound]
  (esq3_dir_b2/b1/b0, esq3_lform_endpoint_lo/hi, esq3_lform_Q compiled
  in the FULL run; not separately axiom-printed.)
- R9: central_cancellation: [propext] | central_item5: [propext] |
  joseph_counting_contradiction: [propext, Quot.sound] |
  int_interval_card: [propext, Classical.choice, Quot.sound] |
  central_eq_central_from_joseph22: [propext]
  (conditional on the named Joseph22HomogForm premise — a hypothesis,
  not an axiom.)
- R10: esquina2_set_iff, esquina2_combined, esquina2_k1_pair:
  [propext, Classical.choice, Quot.sound] each |
  esquina1_bundle_iff: []
- R11: face721_base_identity, face721_coeffs, face721_monic,
  face721_natDegree_pow, face721_leading_coeff,
  face721_remainder_degree: [propext, Classical.choice, Quot.sound]
  each | face721_factor_count: [propext]
- R12: alineados_2a_from_2b, remark_ratio, remark_st_scaling,
  remark_en_scaling: [propext, Classical.choice, Quot.sound] each |
  tpow_exp_smul: [propext, Quot.sound]
- R13: cross_dot_identity: [propext, Quot.sound] |
  dirLt_trans_halfplane: [propext, Classical.choice, Quot.sound] |
  dirLt_irrefl': [propext] | dirLt_asymm': [propext, Quot.sound] |
  succ_set_consecutive: [] |
  succOp_eq_of_isSuccFrom: [propext, Classical.choice, Quot.sound] |
  succOp_spec: [propext, Classical.choice, Quot.sound]
- R14: pderiv_comm, pderiv_comm01, pbracket_antisymm, pbracket_add_left,
  pbracket_add_right, pbracket_smul, pbracket_leibniz, pbracket_jacobi,
  pbracket_translate, joseph_counterexample_bracket: all
  [propext, Classical.choice, Quot.sound]
- R15: mn_gt1_dir_mem: [propext, Classical.choice, Quot.sound] |
  mn_eq1_needs_b_gt1: [] | gghv_uses_mn_gt1: [] |
  gghv_uses_dir_mem: [propext, Classical.choice, Quot.sound]
- R16: hybrid_arith_249, hybrid_arith_288, hybrid_slot_249,
  hybrid_slot_288, hybrid_slot_927, hybrid_slot_721: all
  [propext, Classical.choice, Quot.sound]
- R17: dirValQ_rat_smul: [propext, Classical.choice, Quot.sound] |
  mayores_termination_descent: [propext] |
  mayores_chain_terminates: [propext, Quot.sound] |
  mayores_cocientes_ratio: [propext, Classical.choice, Quot.sound] |
  mayores_cocientes_conditional: [propext, Classical.choice, Quot.sound] |
  mayores_full_conditional: [propext, Classical.choice, Quot.sound]

## Second-tool checks (lean-build-3, 2026-11-06 ~18:40 CST)
- Python 3.11.2, `second_tool_checks.py`: ALL PASS, exit 0 (19 checks:
  R11 base identity + 4 coefficients + factor count; R8 b'-cases,
  direction, phi impossibilities, term valuation; R16 slot fractions
  and orderings; R15 GGHV uses; R17 descent + counting). Log:
  logs_vm/second_tool.log.
- Singular 4.3.1 (`Singular --version < /dev/null`), `jacobi_check.sing`:
  JACOBI = 0; BRACKET_AB = -x2-1; BRACKET_AB + (x^2+1) = 0; exit 0.

## Lock
Lock still held by legE (pid 1830, acquired ~17:20 CST after 2541 s
wait). To be released after this log entry; VM NOT stopped on release.

## 2026-11-06 ~18:45 CST — Final re-check + lock release
- Comment-only header edits (R14 Jacobi bullet KERNEL; index R14 line):
  R14 FULL re-run exit 0, INDEX FULL re-run exit 0 (warnings only:
  unused simp args in pderiv_comm/joseph_counterexample_bracket).
- VM lock RELEASED by legE (held ~17:20–18:45 CST). VM NOT stopped.
- Leg E complete: all 10 item files + index compile exit 0 on
  lean-build-3 (Lean 4.34.0 / Mathlib); all axiom lists ⊆ permitted
  triple or empty; no sorry/sorryAx; second-tool checks pass
  (Python 3.11.2 ALL PASS exit 0; Singular 4.3.1 JACOBI = 0, exit 0).
