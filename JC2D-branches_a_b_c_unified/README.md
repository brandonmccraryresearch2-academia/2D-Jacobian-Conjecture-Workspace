# JC2D Branches (a), (b), (c) — Unified

Elimination of the degree-(72,108) candidate of GGHV Proposition 4.3, case (1),
for the two-dimensional Jacobian conjecture: branches (a), (b) and (c), organized
in one directory.

| Directory | Branch | Elimination paper package |
|---|---|---|
| `branches_a_b/` | (a), (b) — GGHV normal form (2), degree-(8,28) case | The v19 package, revised 2026-10-05 to 2026-10-07; the identical copy `branch_ab_v19/` at the repository root is the path the Zenodo record cites. Contents: a 34-page paper, a Lean 4 machine-checked m = 7 chart classification (Prop. 6.1), Lean m = 3, 5 classifications, the Lean proof of Corollary 1.2 (a₈,₁₆ = 0, lower-edge rigidity), four certificates, the explicit a₈,₁₆ certificate, audits, logs, `verify_v19.sh` |
| `branch_c/` | (c) — GGHV normal form (1), degree-(72,108) case | v3.1 bundle in the branch-(a,b) paper format: symbolic elimination in Lean 4 (`Descent2R`, `T1Zero`, `Bridge`, `Combine`) + numerical elimination (exact/modular certificates, rank lemma), `verify_branch_c.sh` |

## Reading order

1. `TECHNICAL_MAP.md` — the exhaustive technical map: the mathematics, every
   component, the symbolic and numerical eliminations branch by branch, the trust
   base, and how to reproduce everything.
2. `branches_a_b/README.md` — the branch-(a,b) elimination (v19).
3. `branch_c/README.md` then `branch_c/GUIDE.md` — the branch-(c) elimination (v3.1).

## Status

- Branches (a,b): eliminated. Lean proves `main_theorem` (no remaining hypothesis)
  on the standard axioms; the paper is finalized through v19 (Zenodo 10.5281/zenodo.23023490).
- Branch (c): **eliminated in Lean** (2026-11-04). `branch_c_eliminated`
  (`GradeA.Composition`, no hypotheses, standard axioms only) states that no
  Keller pair with Newton normal form (c) exists over any field of
  characteristic 0; it is `main_theorem_c_of_chartEmpty_T1ne0` applied to
  `challenge_target` (`GradeA.Bridge`), the certificate interface instantiated
  at the concrete data ρ = Fin 3199, p = 32003, w₀ = 11147, via the bridge
  `Fpoly = Fpoly2` and the A1, A2, and six data hypotheses. The rank lemma +
  finite-field ranks at two primes now stand as independent corroboration
  (I1), not the sole support. Together with the branches (a),(b)
  `main_theorem`, the GGHV Prop. 4.3 case (8,28) split is fully eliminated in
  Lean. This does not claim (72,108) excluded unconditionally or JC(2).
- Neither branch resolves the Jacobian conjecture; GGHV Prop. 4.3's other cases and the
  reduction to it are outside scope.

## Deferred

- `TODO_correspondence_guide.md` — the branch-(c) correspondence guide: **done** 2026-10-07 (PR #13),
  `branch_c/correspondence_guide/CORRESPONDENCE_GUIDE.md`; section mapping corrected 2026-10-12.
- Branch (c), grade A for `ChartEmptyC_T1ne0` (plan A1–A5): **done
  2026-10-31–11-04** (A1 compiled 2026-10-31, A2 2026-11-01, `hsupp2`
  2026-11-02, `challenge_target` + `branch_c_eliminated` proved 2026-11-04)
  and filed as tracked modules `GradeA.Bridge` / `GradeA.Composition`
  (commit `7e4db07f`, 2026-11-06; status record
  `branch_c/grade_a/BRIDGE_STATUS_2026-11-06.md`). The outside replication
  (I3) is specified in `branch_c/rank_lemma_check/I3_REPLICATION_SPEC.md` and is still open;
  for a blind replication use `replication/INDEPENDENT_REPLICATION_GUIDE.md` (2026-10-12), because the specification
  states its expected values.
  See `TECHNICAL_MAP.md` §9.
- Closed on 2026-10-06:
  - the p-adic argument (not needed);
  - the Muse `char0_cert` bundle (withdrawn, superseded by v3; `branch_c/muse_refutation/`).
