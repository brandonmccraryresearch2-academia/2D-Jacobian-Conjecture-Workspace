/-! # GGHV full proof — [GGV1] remainder (Phase 4, Leg E)

Main index file for Leg E. Per the `lean_large_build_chunking` skill the
leg is SPLIT, one file per sub-item (each self-contained, `import Mathlib`
only, no cross-file imports, no `sorry`, no `axiom`):

  - `gghv_full_esquina3l_2026-11-06.lean` — R8: esquina(3) ℓ-form
    (kernel arithmetic + conditional ℓ-form assembly).
  - `gghv_full_central_gaps_2026-11-06.lean` — R9: central's gaps
    (cancellation + item (5) kernel; Lema Joseph counting kernel;
    Joseph 2.2 carried as an explicit homogeneous premise).
  - `gghv_full_esquina_combined_2026-11-06.lean` — R10: combined-form
    esquina(1)/(2) restatements (kernel).
  - `gghv_full_721_coeff_2026-11-06.lean` — R11: the (7,21) coefficient
    identity (base identity + degree + factor count kernel; general-`m`
    second coefficient open with its step-1 bound kernel).
  - `gghv_full_remark_facelaws_2026-11-06.lean` — R12: Remark "a remark"
    face laws (alineados(2a) kernel from (2b); consequences (1)(2)(3)
    kernel conditional on the power-law premises; monomial face law
    kernel; general face law carried).
  - `gghv_full_d1_theory_2026-11-06.lean` — R13: D1 theory (`dirLt`
    transitivity on a half-plane kernel; set-level consecutiveness +
    Succ as an operator kernel modulo explicit premises; the
    `stFace`/`enFace` ↔ CCW bridge still open).
  - `gghv_full_d2_poly_2026-11-06.lean` — R14: D2 polynomial bracket
    (bilinearity / antisymmetry / Leibniz kernel; Jacobi KERNEL via
    in-file `pderiv_comm`; translation chain rule conditional on the
    `pderiv`/`aeval` commutation).
  - `gghv_full_mn_gt1_2026-11-06.lean` — R15: `m, n > 1` as a
    documented deviation (published §7 text NOT FOUND by the retrieval
    leg; arXiv-TeX wording flagged as NOT the published wording).
  - `gghv_full_hybrid_slip_2026-11-06.lean` — R16: hybrid-vs-slip
    (BLOCKED on published §7 text; distinguishing arithmetic kernel).
  - `gghv_full_mayores_2026-11-06.lean` — R17: mayores full statement
    (T-termination kernel; cocientes ratio kernel; full theorem
    CONDITIONAL on condind).

Per-item verdicts, compile timings, and the exact axiom lists are in
`legE_log.md` in this directory. Verification pattern (Phase 4 map §9):
wake lean-build-3, wait 60–90 s, scp to /tmp, foreground run, second run
with appended `#print axioms`, verify axioms ⊆ permitted triple
[propext, Classical.choice, Quot.sound] and `sorryAx` absent.
-/
