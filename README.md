# 2D Jacobian Conjecture Workspace

Research workspace for the two-dimensional Jacobian conjecture, organized around
the elimination of the surviving degree-$(72,108)$ candidate configurations of
Guccione–Guccione–Horruitiner–Valqui (GGHV) Proposition 4.3, cases (1) and (2)
of the $(8,28)$ split, plus a
claimed theorem on dicritical divisors of Keller maps (false as worded, and its proof is incomplete; see below)
and an independent blind
verification of GGHV Proposition 4.3, normal form (2).

**Author:** Brandon D. McCrary (ORCID: 0009-0008-2804-7165)

## Scope

GGHV Proposition 4.3 (case (8,28)) lists the surviving configurations for a
counterexample pair to the planar Jacobian conjecture at degree pair
$(72,108)$. In this repository's formalization they are organized as
**branches**:

| Branch | GGHV normal form | Case | Status |
|---|---|---|---|
| (a), (b) | form (2) | degree-$(8,28)$ | **Eliminated** — Lean 4 `main_theorem`, no remaining hypothesis |
| (c) | form (1) | degree-$(72,108)$ | **Eliminated** — Lean 4 `branch_c_eliminated`, proved 2026-11-04 with no hypotheses on the permitted axiom triple (see below) |

Case (1) of the $(8,28)$ split carries the $(0,8)$/$(0,12)$ vertices
(`NewtonNFc`); case (2) lacks them (`NewtonNF2`).

All branches work over $K_5 = \mathbb{Q}[w]/(R)$ with
$R(w) = w^5 - w^4 + 3w^3 + 3w^2 + 26$ irreducible over $\mathbb{Q}$ (it is irreducible mod 67 and mod 109;
irreducibility over $\mathbb{Q}$ is kernel-checked since 2026-10-12, `branch_c/grade_a/`).
The Jacobian condition is $[P,Q] = \lambda x^2$ with $\lambda \neq 0$.

**What this is not.** This workspace eliminates the $(8,28)$ split of one
proposition (GGHV Prop. 4.3): case (2) by branches (a),(b) and case (1) by
branch (c), both in Lean. It is not a proof of the two-dimensional Jacobian
conjecture, and it does not claim "$(72,108)$ excluded unconditionally":
those conclusions still rest on GGHV Proposition 4.3's exhaustiveness and on
the reduction chain from the conjecture to Prop. 4.3, which are ledgered, not
re-derived, here. GGHV Proposition 4.3's other cases and the reduction from the
conjecture to Prop. 4.3 are outside scope.

## Repository layout

| Path | Contents |
|---|---|
| `JC2D-branches_a_b_c_unified/` | The unified branch-elimination workspace (branches (a), (b), (c)) |
| `JC2D-branches_a_b_c_unified/branches_a_b/` | Branch (a),(b) elimination package (v19, revised 2026-10-05 to 2026-10-07). Contents: a 34-page paper, a Lean 4 machine-checked $m=7$ chart classification (Prop. 6.1), Lean $m=3,5$ classifications, the Lean proof of Corollary 1.2 ($a_{8,16}=0$, lower-edge rigidity), four certificates, the explicit $a_{8,16}$ certificate, audits, logs, `verify_v19.sh`. Published on Zenodo: 10.5281/zenodo.23023490 |
| `branch_ab_v19/` | Byte-identical copy of `JC2D-branches_a_b_c_unified/branches_a_b/`, at the path cited by the Zenodo record. The two copies are updated together. |
| `JC2D-branches_a_b_c_unified/branch_c/` | Branch (c) elimination package: v3.1 bundle (byte-for-byte reviewer bundle) with Lean 4 symbolic elimination (`Descent2R`, `T1Zero`, `Bridge`, `Combine`) + numerical elimination (exact/modular certificates, Macaulay rank lemma at two primes), 18-page paper, `verify_branch_c.sh` |
| `JC2D-branches_a_b_c_unified/TECHNICAL_MAP.md` | Exhaustive technical map: the mathematics, every component, the symbolic and numerical eliminations branch by branch, the trust base, and how to reproduce everything |
| `JC2D-branches_a_b_c_unified/TODO_correspondence_guide.md` | The original to-do for the branch-(c) correspondence guide: done 2026-10-07 (`branch_c/correspondence_guide/`), corrected 2026-10-12 |
| `JC2D-branches_a_b_c_unified/replication/` | Blind replication guide for an outside party, with a separate answer key recomputed in fresh code (2026-10-12) |
| `JC2D-branches_a_b_c_unified/reviews/` | Reviews of the work, with their evidence (the review of 2026-10-12 covers PRs #12–#15 and the A1–A5 and two-dicritical drafts) |
| `REPRODUCTION_GUIDE.md`, `REPRODUCTION_ANSWER_KEY.md`, `reproduction_key_checks.py` | Protocol for re-running the project's own scripts on another machine (reproducibility, I1), with its answer key and comparator |
| `branch_two_dicritical/` | **Claimed** theorem: no Keller map admits two dicritical divisors. As worded the statement is false, and the proof is incomplete (see the status section below). 6-page paper, 18 executed SymPy scripts with outputs, `verify_all.sh`, `CORRESPONDENCE.md` mapping each script to its paper statement |
| `tier1_blind_gghv43_nf2/` | Independent blind verification of GGHV Proposition 4.3, normal form (2): verdict DO NOT EXIST (run 2026-09-25, logged in `LOG.md`) |
| `gghv-dependency-closure/` | GGHV dependency-closure programme, Phase 2: the scoping + integrative synthesis report and annotated bibliography (2026-11-05) — see "GGHV dependency closure" below |
| `environment.yml`, `lean.toml`, `setup.sh` | Compute environment setup (conda environment, Lean 4 toolchain) |

## Status of each line of work

### Branches (a), (b) — eliminated

For polynomials $P, Q \in L[x,y]$ over a field $L$ of characteristic $0$ in GGHV
normal form (2) with $[P,Q] = \lambda x^2$, $\lambda \neq 0$, there is **no
solution**. The Lean 4 formalization proves, independently of GGHV Proposition
4.3:

- `chartClassification_holds`: every solution of the 17-equation normalized
  chart is one of the five $K_5$-conjugate points ($m=7$ case of Prop. 6.1),
  kernel-checked on the standard axioms only.
- `main_theorem`: the NewtonNF2 form of Theorem 1.1 with no remaining
  hypothesis, kernel-checked on the standard axioms only.

Conditional on GGHV Proposition 4.3, this eliminates branches (a),(b). The
paper went through an independent final blind review (2026-09-28, no fatal
flaw found) and was published on Zenodo as v19 (10.5281/zenodo.23023490).

### Branch (c) — eliminated in Lean (2026-11-04)

**Status (proved 2026-11-04 on lean-build-2).** `challenge_target` is **proved**
in Lean 4 with **no hypotheses** and axioms exactly
`[propext, Classical.choice, Quot.sound]` (the permitted triple), and
`branch_c_eliminated` is **proved** the same day on the same permitted triple.
The proof of `challenge_target` goes through the `Fpoly = Fpoly2` bridge plus
instantiation of the interface theorem
`chartEmptyC_T1ne0_of_certificate` at the concrete data $\rho = \mathrm{Fin}\ 3199$,
$p = 32003$, $w_0 = 11147$, supplied with A1, A2, and the six data hypotheses.
`R109Data` / `K5` were **not** needed for this step. The earlier grade-B status
of this branch is therefore superseded: the chart-emptiness premise that Lean
previously did not check is now discharged inside Lean by the certificate
instantiation. Together with the branches (a),(b) `main_theorem`, the GGHV
Proposition 4.3 case $(8,28)$ split is now **fully eliminated in Lean**:
case (2) by branches (a),(b), case (1) by `branch_c_eliminated`.

In Lean 4 (no `sorry`, only `propext`, `Classical.choice`, `Quot.sound`):

$$\text{ChartEmptyC\_T1ne0} \to \text{ChartEmptyC} \to \text{DescentClaimC} \to \neg\exists\, P\, Q\, \lambda,\ \lambda \neq 0 \wedge \text{NewtonNFc}\, P\, Q \wedge [P,Q] = \lambda x^2.$$

The stratum $b_{11,20} = 0$ is kernel-checked (`T1Zero`); `Combine` isolates
exactly what Lean does not check. Before 2026-11-04, `ChartEmptyC` was
established outside Lean (grade B): it followed from the fixed-degree Macaulay
rank lemma plus full row rank of the Macaulay matrix at two primes
($p = 1000003$ and $p = 32003$), with two independent implementations and
planted-zero controls. That grade-B account is retained here as history; the
premise it supplied is now proved in Lean as described above. The 18-page paper
(`branch_c/paper/branch_c_elimination.pdf`) carries the full account and four finished figures. Its §6
paragraph "Formalization seam" (degree-19 rigidity not in Lean) is out of date: `degree19_rigidity`,
`vertex_12_24_forces_t2` and the branch-(a,b) classification are kernel-checked and used by
`main_theorem_c_of_claim` (`branch_c/correspondence_guide/CORRESPONDENCE_GUIDE.md`, §6).

Since 2026-10-12, `branch_c/grade_a/` proves the generic half of `ChartEmptyC_T1ne0` in Lean: $R$ is irreducible
over $\mathbb{Q}$; a polynomial in $\mathbb{Z}[X]$ that vanishes at a root of $R$ in characteristic $0$ vanishes at
every root of $R$ in every ring; and a modular left inverse of a Macaulay block at one prime excludes common zeros in
characteristic $0$ (`no_common_zero_of_certificate`). The chart reduction is kernel-checked too: a chart point is a
common zero of the six chart generators, with $b_{11,20}$ free (`chart_gens_vanish`). The interface theorem
`chartEmptyC_T1ne0_of_certificate` then gives the premise from the Macaulay data (rows, pivot columns, support) and
two finite deliverables: A1, the packed kernel check read as $C\cdot M_S = I$ modulo 32003; and A2, $M_S$ is the
evaluated Macaulay block of the generators, up to one nonzero scale per generator. Both deliverables are now
supplied and kernel-verified (`branch_c/grade_a/README.md`):

- **A1 — compiled 2026-10-31.** Theorem `A1 : Cinv * MS = 1` at $\rho = \mathrm{Fin}\ 3199$,
  $p = 32003$, from regenerated manifest-verified rank-check data, kernel-verified with
  `#print axioms A1 = [propext, Classical.choice, Quot.sound]` (the permitted triple).
- **A2 — complete 2026-11-01** (`A2Assembly` v3, `Fpoly2` form).
- **hsupp2 — compiled 2026-11-02** (same permitted axioms, `Fpoly2` form).
- All six data hypotheses are complete: `hw₀`, `hscale`, `prime32003`, `hmon`, `hr₁`, and `hsupp2`.
  The `Fpoly = Fpoly2` bridge plus instantiation is what proves `challenge_target` above.

**Scope guard.** Branch-(c) elimination is a kernel-verified elimination of
one case of one proposition. It does **not** claim "$(72,108)$ excluded
unconditionally" and does **not** prove JC(2): those still rest on GGHV
exhaustiveness and the reduction chain, ledgered not re-derived.
**Repository note.** The bridge/composition files (`challenge_target`,
`branch_c_eliminated`) were proved in scratch on lean-build-2 and remain
scratch, not repo-tracked modules; their incorporation into this repository as
tracked modules is still pending (see `JC2D-branches_a_b_c_unified/branch_c/grade_a/GRADE_A_STATUS_2026-11-05.md`,
scope guard).

### Two dicritical divisors — claimed; false as worded, and the proof is incomplete

The claim: let $K$ be a field of characteristic $0$ and $P, Q \in K[x,y]$ with
$[P,Q] = c \in K^\times$ (a Keller map). Then the resolution of the pencil
$\lambda P + \mu Q$ contains no two distinct dicritical divisors. The proposed proof:
$m \geq 2$ is impossible (constant-leading-form on $E_k$, $k \geq 2$; $E_1$
degree obstruction), and the $m = 1$ bridge is empty for every $d \geq 2$
(descending induction on $W = 2J+K$; diagonal blocks reduce to scaled
Vandermonde, full rank; nullspace $= \mathrm{span}\{1,y\}$, $J = 0$).

Status (review of 2026-10-12, corrected 2026-10-13; `JC2D-branches_a_b_c_unified/reviews/REVIEW_2026-10-12_handoff.md`
§5 and §9, and `branch_two_dicritical/lean/README.md`):
- **as worded, the statement is false for every Keller map of degree $\geq 2$.** Its pencil has a base point at
  infinity and, once the target is translated so that $0$ is a value, an affine one; every base point carries a
  dicritical (`JC2D-branches_a_b_c_unified/reviews/two_dicritical/base_point_at_infinity_check.py`;
  `main_statement_check.py` there works out $(x-y^2,\ y)$ and $(x,\ y+x^2)$). Read literally, the statement would
  imply the Jacobian conjecture outright, and every non-affine automorphism refutes it. The intended statement, at
  most one dicritical at infinity, is written down in `branch_two_dicritical/RESTATEMENT.md` (2026-10-13). It is
  equivalent to the plane Jacobian conjecture;
- **Theorem `thm:e1` (the $E_1$ obstruction) is false as stated.** Its proof reads $\nu_{E_1}\geq -2$ as "total
  degree $\geq 2$" instead of "$x$-degree $\leq 2$", and $P=(x+y^2)^2+y$, $Q=P+x+y^2$ is a Keller pair in its open
  subset. The intended conclusion holds for every $m$: $E_1$ is never dicritical for a Keller map. Its algebraic step
  is now proved in Lean (`E1Keller.lean`); the chart step is executed only;
- the adjacent $m = 1$ case is computed at $d = 3$ only, while the theorem is stated for every degree;
- the constant-leading-form proposition, which carries $m \geq 2$, has a proof sketch only;
- the Lean drafts of 2026-10-12 rested their bridge induction on two axioms that are false as stated. Since
  2026-10-12, `branch_two_dicritical/lean/` proves the bridge collapse from the paper's explicit equations with no
  axioms, together with the block-rank lemma. That proof also closes a gap at weight $W = 2$. Read geometrically, the
  bridge assumes two dicriticals over **free** points of the second exceptional curve $E_2$, with pole order at most
  1 for every member of the pencil. The second premise is asserted, not derived. Under these premises one such
  dicritical already forces degree $\leq 2$. Dicriticals over the satellite points of $E_2$ are not treated. The
  hypothesis "both centers nonzero" marks where the formula applies: the formal witness $(x-a_4y^2,\ y)$ with a center
  at $a = 0$ is not a geometric bridge (`branch_two_dicritical/lean/check_satellite.py`).

So the theorem is open, and its statement must first be corrected.

## Grade-A package — all modules green (2026-11-05)

The grade-A package lives in
`JC2D-branches_a_b_c_unified/branch_c/grade_a/` (status file
`GRADE_A_STATUS_2026-11-05.md`, which supersedes the 2026-11-04 note).
**Full `gradea_build` PASSED on lean-build-3 (Lean 4.34.0 / Mathlib v4.34.0)
on 2026-11-05: all 8 modules exit 0** — `R67Data` (12 s), `R109Data` (295 s),
`IrreducibleR` (5 s), `IrreducibleR109` (6 s), `K5Field` (4 s), `Transfer`
(4 s), `Macaulay` (5 s), `Axioms` (3 s) — plus the `#print axioms` check:
**22 of 22 theorems on the standard axioms (or a subset)**, `sorryAx` absent.
"All grade-A modules green" is true for the first time. The package is
incorporated in this repository as commit `03f242f` (current HEAD,
"Grade-A green: full gradea_build passes on lean-build-3").

What was repaired to get there (vs the first full-build attempt, which failed
at `IrreducibleR109`): all 13 Mathlib v4.34.0 API-drift errors in
`IrreducibleR109.lean` (e.g. `Polynomial.mod_add_div` →
`EuclideanDomain.div_add_mod'`, `hr.of_dvd` → `isRoot_of_dvd`,
`reduceMod109` marked `noncomputable`, `Ideal.Quotient.lift` given a genuine
ring hom); latent errors in `K5Field.lean` (`example : Field K5` marked
`noncomputable`, ambiguous `gcd` qualified to `EuclideanDomain.gcd`); and the
renamed `R109Data` port (`Rint109` internal; downstream statements
`bezout_lin`, `bezout_quad_small`, `quad_mod` unchanged). No public theorem
statement changed. The package was validated by deepest-research fact-check
on 2026-11-05 (verdict GO; validation record
`~/workspace/research/tooling/gradea_validation_2026-11-05.md`).

The underlying field is $K_5 = \mathbb{Q}[w]/(R)$ with
$R(w) = w^5 - w^4 + 3w^3 + 3w^2 + 26$ — note $R$ has **no $X$ term** (the
$w^1$ coefficient is $0$). Green means the eight grade-A modules compile and
their 22 audited theorems sit on the standard axioms (or a subset). It does
NOT claim "$(72,108)$ excluded unconditionally" and does NOT prove JC(2):
those still rest on GGHV exhaustiveness and the reduction chain, ledgered not
re-derived.

## GGHV dependency closure — Phase 1 complete

The dependency-closure programme proves in Lean, and recomputes in Singular,
everything this work depends on in the GGHV paper (Guccione et al., 2022) and
its cited [GGV*] machinery, principally Guccione, Guccione, & Valqui (2017)
[GGV1], *J. Algebra* 471 (2017), 13–74, DOI 10.1016/j.jalgebra.2016.08.039,
arXiv:1401.1784v3. **Phase 1 is complete.** Every claim below carries its
HLRE v5 grade; "conditional" means proved from explicit unproved premises,
"kernel-verified" means proved by the Lean kernel for that narrow claim only,
"I1" means independent recomputation, not kernel proof. **Theorem R is
excluded everywhere in this programme** — it is not a goal, a premise, or a
conclusion of any leg.

- **[GGV1] leg.** Proposition 8.2(2) proved **conditionally**; Corollary 7.4
  proved **conditionally**; Theorem 2.1 proved from a minimal 11-field
  premise list (`theorem21_minimal`, on `[propext]` only) — **not
  unconditionally**. Key finding: the $(7,21)$ row **is** the $\max = 84$ row —
  `discard_84` and `discard_721` are two arguments for the **same** row, not
  two rows. The published [GGV1] §7 text is still missing (see Phase 2).
- **[GGV*] machinery leg.** Theorem 7.3 combination + $F_9$ arithmetic
  proved, $I_M = 4$, $I_m = 5$; Proposition 3.29 **conditional**;
  Proposition 1.13 both directions proved; Proposition 2.1(1) proved;
  the $(8,24)$ row **conditional**. Fields are discharged one level down;
  none is unconditional.
- **D2 combine — proved (round-12).** Bridge lemma: the combined top
  coefficient equals the endpoint coefficients times the cross product, with
  $k = 1$ in the reduced / `Nodup` case; `extremos` in combined form;
  D2 power laws proved; the Remark conditional on `alineados(2a)`; `mayores`
  T-termination proved; `lema geometrico` 1 + 2 proved.
- **Singular leg — COMPLETE 2026-11-05, all five items agree (status I1
  recomputation, NOT kernel proof).** Parts 11–12 certificate identities
  (`CERT_DIFF = 0`, `CERT_IS_ZERO = 1`); §5/§6 eliminations by three routes,
  including Gröbner `eliminate` of the full 9-equation ideal, which is
  PRINCIPAL with generator exactly the target; §3 numerics; the §2 table;
  [GGV5] enumeration arithmetic.

**Still open** (as Lean proofs or as settled text): combined-form
`esquina(1)`/`(2)` restatements (base merge); the $(7,21)$ coefficient
identity; the Remark's two face laws + `alineados(2a)`; `esquina(3)`'s
$\ell$-form; central's $[F,\ell(P)] = \ell(P)$ cancellation gap; $m, n > 1$;
hybrid-vs-slip; the §6 $k = 2$ derivation + non-square contradiction;
§5 rescaling + the degree-78 endgame as Lean proofs; the 9 equations' D2
derivation; [GGV5] completeness.

## Phase 2 synthesis — scoping + integrative review (2026-11-05)

Phase 2 asks what the whole Phase 1 body of work points to, and which
non-intuitive assumptions, viewed from another domain, would alter the
problem. Filed in this repository at
`gghv-dependency-closure/phase2_synthesis_report_2026-11-05.md` (12,878 words)
with the companion
`gghv-dependency-closure/phase2_annotated_bibliography_2026-11-05.md`
(60 sources × themes T1–T5, scope-qualified). **Form:** scoping + integrative
literature review, deepest-research full mode. The form was chosen by the
assistant under Brandon's standing deep-research delegation (2026-10-25) and
confirmed by Brandon 2026-11-05 ~10:42 CST. Academic-research-skills (ARS)
has no separate scoping mode, so the scoping protocol and the PRISMA-ScR
reporting checklist stay with the author; this report is **not** a systematic
review and does **not** claim PRISMA compliance. (Word-count note: 12,878
words against a 3,000–8,000-word specification — the overrun was flagged in
the record.) Evidence base: Phase 1 as given, not re-derived; all Phase 1
grades preserved as recorded. Analogies across domains are hypotheses, never
proofs. **Evidence base: 60 verified sources — 42 Tier 1 (peer-reviewed
journal/monograph), 12 Tier 2 (preprint), 6 Tier 3 (gray literature)** —
confirmed against journal/publisher pages, arXiv abstract pages, MathSciNet,
repository records, and citing sources; 0 dropped. Review: devil's advocate
REVISE ×2 (checkpoint 2: 0 critical, 10 major, 12 minor; checkpoint 3:
0 critical, 7 major, 18 minor), editor MINOR REVISION (0 critical, 4 major,
13 minor), ethics CLEARED (2 minor advisories). **17 MATERIAL GAPs** are
carried forward (listed at the end of this section).

The headline findings, in full:

- **SQ1 — Control at infinity: the real crux only in a narrowed sense.**
  The Jelonek set gives the obstruction a proved shape: for a Keller map,
  the obstruction to properness — hence, for Keller maps, to being an
  automorphism (the properness ⟺ automorphism step is not cited from
  Jelonek (1993) / Jelonek & Lasoń (2019) as a single theorem) — is exactly
  the Jelonek set $S_f$, empty or a uniruled hypersurface with an explicit
  degree bound (Jelonek, 1993; Jelonek & Lasoń, 2019). In Keller scope, ten
  sources converge on T1 (Jelonek 1993; Jelonek & Lasoń 2019; Favre &
  Jonsson 2011; El Hilany & Tsigaridas 2023; Moh 1983; Cossart & Matusinski
  2011; Campbell 1998; van den Essen 2000; Gwoździewicz 1993; Valette &
  Valette 2010); El Hilany (2022) and El Hilany (2019) converge only for
  generic (T-BG) families, Bajbar & Stein (2018) only in the real case for a
  sufficient class, Favre & Jonsson (2004) only locally. The valuative-tree
  half is a **hypothesis**: GGHV's $(\rho,\sigma)$-directions are
  *conjectured* points or ends of the canonical tree $V_0$ of valuations
  centred at infinity, pending the unwritten dictionary between the
  valuative tree and Newton polygons at infinity *for a map* [MATERIAL GAP
  5]. The topological half is a **preprint claim**: in dimension 2, for a
  map with nonvanishing Jacobian, non-properness is equivalent to
  $H_2(N_F) \neq 0$ (Valette & Valette, 2010, preprint). The control-theory
  bridge is **reader-constructed, not a literature finding**: "observability
  at infinity" in control denotes time-infinity or infinite-frequency /
  impulsive modes, never spatial infinity of a static map; the three bridge
  hypotheses (H-B1 properness as observability, H-B2 dicriticals as
  unobservable modes, H-B3 the valuative tree as an observability
  codistribution) are hypotheses, not correspondences. The Jelonek memo
  formula $\sum_j t_j \cdot \chi(S_j) = d-1$ was **NOT found in the
  literature** and remains an unverified hypothesis [MATERIAL GAP 1].
- **SQ2 — The literal-text gaps: untested as symptoms, not refuted.** The
  four gaps rest on the Phase 1 record alone; the corpus was never searched
  for textual-error analogues, so "no literature analogue found" is absence
  of evidence, not evidence of absence. Three read most parsimoniously as
  local textual errors: the $(7,21)$ face missing its $x$ factor (the text's
  $\ell_{1,-2}(P)$ is the face divided by $x^{14}$; harmless — the
  $\varphi_2$ step uses the root $\lambda$ and the edge direction, both
  correct); Part 19's $4\cdot 2 = 8$ error (with $(m,n) = (3,2)$,
  $4\cdot 3 = 12$); `hmn` ($m \neq n$) unused by `esquina(1)`'s proof
  (confirmed in the paper's own proof — a redundancy, not a gap). The
  fourth, $m, n > 1$ needed but unstated in `esquina(2)`, is a **genuine
  minor gap as literally written** (the paper states only $m, n \in
  \mathbb{N}$, but the (2) proof needs $nb, mb > 1$); it is repaired by
  adding the hypothesis. The decisive text, published [GGV1] §7, is missing
  and could rescue $m, n > 1$ or change the slip verdicts, so the "no
  rescue" claim is itself conditional on that missing text [MATERIAL GAPs
  11, 14].
- **SQ3 — The carried premises: three different failure modes, not one
  boundary.** All four are load-bearing imports across a boundary, and each
  failure breaks a distinct, named downstream result. **Joseph Lemma 2.2**
  — unlocated (citation verified: *Amer. J. Math.* 97 (1975), 597–615; no
  open text located), homogeneity load-bearing, the naive un-homogeneous
  form **false** by explicit counterexample in the Phase 1 record
  ($B = x$, $A = y(x^2+1)+x$ gives $AB/[A,B] \notin K[x,y]$); possibly a
  mis-citation, not merely an import. It carries the central assembly
  (`central_conditional`, conditional on Joseph Lemma 2.2 + Lema Joseph),
  hence `esquina(3)`'s direction argument [MATERIAL GAP 12]. **Lema
  Joseph** — unproved, with three precise sub-gaps: (i) algebraic
  independence of $P, Q$ giving $\dim M(t) = (t+1)^2$; (ii) valuation
  bounds for $M(t)$ forcing the $H_j$ recursion (needs the Remark's
  common-power form, proved by the D2 combine only conditionally on
  `alineados(2a)`); (iii) termination of the $H_j$ recursion — discharged
  by the D2 combine as `mayores` T-termination. The independence sub-gap
  and the maximal-$j$ step (via unproved Remark 453(3)) remain.
  **[GGV5] enumeration completeness** — carried as field 11 of Theorem
  2.1's minimal premise list; a completeness claim about an enumeration,
  not a theorem. If the [GGV5] §§5–6 enumeration is incomplete, the
  survivor list $[(108,72), (66,99), (72,108)]$ and the 125 ceiling itself
  are unreliable. The Singular leg recomputed the filter/direction/
  candidates arithmetic, not completeness [MATERIAL GAP 13]. Unlike the
  other three premises this one is a **chain through the table** rather
  than a fan leaf, which makes it the most damaging failure mode.
  **Published [GGV1] §7 text missing** — a missing text, not a premise at
  all: the two swapped Corollary 7.4 uses ($(24,9)$ and $(28,8)$) have a
  mixed slot pattern neither TeX twin covers as literally stated, while the
  two unswapped uses ($(9,27)$ and $(7,21)$) are clean F-fits; until the
  published wording is seen, hybrid-vs-slip cannot be settled [MATERIAL
  GAP 14].
- **SQ4 — Both theses stay hypothesis / untested candidate.** **"Plane
  genuinely special" — HYPOTHESIS, unchanged.** Methodological specialness
  is proved (tame generation true in 2, false in 3 — the Nagata
  automorphism is wild (Shestakov & Umirbaev, 2003); all embeddings of the
  line in the plane are equivalent (Abhyankar & Moh, 1975); Markus–Yamabe
  true in 2, false in ≥ 3 (van den Essen, 1997)), but no dimension-2
  *mechanism* for JC(2) is established — the strongest candidates
  (Jung–van der Kulk amalgamated-product structure, Abhyankar–Moh
  degree-divisibility) have never been connected to JC(2) in a way that
  would fail in dimension 3 [MATERIAL GAP 15]. The Alpöge July 2026
  announcement of a 3-dimensional counterexample (degrees $(7,6,4)$,
  det $-2$) would, if correct, be the strongest possible evidence — but it
  is a Tier 3 social-media post, reported only, not verified; its reported
  corroborations (van den Essen, Gao, an Isabelle/HOL AFP formalisation)
  are not in the verified corpus and are not relied on. **"Selection by
  extremal/shell structure" — UNTESTED CANDIDATE, unchanged.** Extremal
  selection is real-but-narrow: in variational pattern formation near
  onset the selected pattern *is* the minimiser of a known free-energy
  functional within the critical wavenumber shell (Swift & Hohenberg, 1977);
  universal optimality is proved for $E_8$ and the Leech lattice, in
  dimensions 8 and 24 (Cohn et al., 2022; dimension 1 trivial); $D_4$ is a
  strict local minimum of Epstein zeta for every $s > 0$ (Sarnak &
  Strömbergsson, 2006). Against: Alexander–McTague's shell-counting
  prediction of the stable phase is wrong (fcc wins; every AM crystal
  unstable) (Alexander & McTague, 1978; Groh & Mulder, 1999; Klein, 2001);
  $D_4$ is not universally optimal as a spherical code (Cohn et al., 2007);
  the Maxwell point has "no bearing" once variational structure is broken
  (Raja et al., 2023); far from equilibrium there is in general no extremal
  principle at all (Cross & Hohenberg, 1993). No claim about $D_4$
  lattice-packing optimality is made: it is supported by neither
  Sarnak–Strömbergsson (2006) nor Cohn et al. (2007) [MATERIAL GAP 16].
  The $D_4$ ratio in IRH and the extremal valuations in the GGHV closure
  are two separate extremal facts in two separate domains with nothing in
  the corpus connecting them.
- **SQ5 — The 125 frontier + the supermindai claim: COMPARISON ONLY.**
  **125 is GGHV's enumeration ceiling, not a property of $(72,108)$.**
  GGHV list all degree pairs with max degree below 125 and discard them
  all except $(72,108)$ (and symmetric $(108,72)$); Theorem 2.1 is the
  disjunction "max degree ≥ 125 OR the pair is $(72,108)/(108,72)$". The
  title bound "108" is the max degree of the surviving pair; "125" is the
  first max degree NOT covered by the enumeration. Ladder, per-rung grades:
  2 (Wang, 1980, PROVED) → 100 (Moh, 1983, peer-reviewed with a reported
  reproducibility caveat, second-hand) → 104 (Nguyen, 2025, preprint only,
  journal claim unverified, abstract-only read) → 108 as the surviving
  pair's max degree / 125 as enumeration ceiling (Guccione et al., 2022,
  preprint) → 125 as claimed closed floor (SuperMind, 2026, as stated;
  Helali, 2026, as reported — neither evaluated here). If the [GGV5]
  enumeration is incomplete, 125 is not a ceiling at all but an artefact of
  an incomplete list. The next open cases live AT max degree 125 and above:
  the smallest such pair studied in the located literature is $(75,125)$
  (Hossain, 2026), which that paper explicitly does NOT exclude. The
  **supermindai manuscript** — "The degree of a possible counterexample to
  the plane Jacobian conjecture is at least 125" (SuperMind, 2026), Theorem
  1.1: every noninvertible plane Keller map over an algebraically closed
  field of characteristic zero has max degree ≥ 125; Corollary 1.2,
  verbatim: "No plane Keller counterexample has degree pair (72, 108) or
  (108, 72)" — is **COMPARED, not audited or graded**. AI-authorship is
  verified from the manuscript itself ("completed autonomously by
  GPT-5.6-Sol Max", title page; "Human involvement was limited to
  intermediate feedback", §7.3). Its §7.2 supplementary archive was NOT
  located or opened. What the claim would have to show to be NEW relative
  to the verified position: (1) both Proposition 4.3 configurations, end to
  end — closing both residual Laurent configurations AND carrying the
  reduction from an arbitrary polynomial Keller pair to them; (2) the bound
  assembled in one chain — the $(72,108)$ exclusion combined with GGHV's
  Theorem 2.1 disjunction to yield "max degree ≥ 125", in the same
  "unconditional once the cited reduction is accepted" sense the manuscript
  itself states; (3) an independently re-runnable exact-certificate package
  — the quintic first-layer classification, the Case-II Bézout identity,
  the Case-I square relation and two-chart certificate (including the
  mod-67 lucky-reduction step), together with the §7.2 supplementary
  archive (self-checking program, versions, SHA-256 checksums); (4) the
  symmetric pair handled explicitly — $(108,72)$ as well as $(72,108)$.
  What it would NOT newly show even if as stated: prove JC(2) or anything
  at degree ≥ 125; re-derive GGHV exhaustiveness, the §2 table, or the
  [GGV*] machinery (it imports them); discharge any of the 11 fields of
  the minimal premise list; reproduce the Lean kernel-verified eliminations
  in formalised form (its evidence kind — exact computer algebra +
  supplement — is different from, not a replacement for, a kernel check);
  or settle $(75,125)$. Venue and authorship status (self-published GitHub
  Pages PDF, AI-authored, unreviewed) describe provenance, not correctness.

The report's organising scheme, **VEE (Valuative, Enumerative,
Eliminative)**, is an organisational re-labelling of Phase 1's three legs,
not a finding of the literature; its layers are not independent (the
enumerative layer depends on valuative arguments, the eliminative layer on
the enumerative layer), with dependency arrows 1b → 2b, 2b → 2c, 3b → 3a.
The arrows locate the binding constraint: every downstream grade inherits
2b's enumeration conditionality. The conclusion the report ends on: the
closure is a chain of *conditional* results, with the enumeration premise at
the top, whose computations are strong and whose conditions are imported —
and the imports, not the computations, are now the binding constraint. The
assumption that would alter the problem is the one SQ3 makes visible: that
the imported premises hold in the form used. **CommutingDerivations
(OpenAI) is NEVER a kernel check or a premise here** (statement-audited +
source-complete, kernel INCOMPLETE-EVIDENCE; see the grade-A status file and
the Phase 2 report).

**17 MATERIAL GAPs carried forward:** (1) the Jelonek memo formula
$\sum_j t_j \cdot \chi(S_j) = d-1$ — no source states it; (2) the
control-theory bridge H-B1–H-B3 — reader-constructed; (3) a *verified*
spatial sense of "observability at infinity" in control theory; (4) a
systematic toric / weighted-projective compactification treatment of Keller
maps; (5) a dictionary between the valuative tree and Newton polygons at
infinity *for a map*; (6) which dicritical directions occur for Keller maps;
(7) a several-complex-variables obstruction (Hartogs/Remmert-type) for
Keller maps; (8) a topological interpretation of the computable Jelonek set
(bridging Valette's $H_2(N_F)$ and El Hilany–Tsigaridas's computation); (9)
effectivity of Jelonek-set computation at degree $(72,108)$ scale; (10)
whether the T-BG hypothesis holds for Keller maps or for the GGHV
$(72,108)$ candidate specifically; (11) any literature analogue of, or
explanation for, the four SQ2 literal-text gaps; (12) Joseph Lemma 2.2
itself — the text unlocated, the premise carried on a citation alone; (13)
[GGV5] enumeration completeness proved or independently verified anywhere;
(14) the published [GGV1] §7 text — missing; (15) a dimension-2 mechanism
for JC(2) proved to fail in dimension 3; (16) global $D_4$ optimality for
theta/Epstein zeta among all lattices; (17) certification of input ideals —
that a hand-derived system (here, the 9 equations from C/F/D expansions) is
the correct idealisation of a geometric problem, and likewise any bridge
from extremal selection to polynomial-system elimination.

**Progress deck.** A 12-slide progress deck for this programme, current
through Phase 1 complete, was re-rendered 2026-11-05: slide 7 records the
grade-A incorporation (commit `03f242f`), the D2 combine proved, and the
Singular leg complete, and the Phase 2 synthesis has landed. The deck lives
in the GGHV dependency-closure goal workspace, not in this repository:
`~/workspace/goals/gghv-dependency-closure/files/planar-jacobian-progress-deck/planar-jacobian-progress-deck.pptx`.

## Papers

All papers are typeset with Fira Sans (text), Fira Mono (code), and Fira Math
(mathematics) exclusively.

| Paper | Location | Pages |
|---|---|---|
| Branch (a),(b) elimination (v19, revised 2026-10-05 to 2026-10-07) | `JC2D-branches_a_b_c_unified/branches_a_b/paper/branch_ab_elimination_v3.pdf` (same file in `branch_ab_v19/paper/`) | 34 |
| Branch (c) elimination | `JC2D-branches_a_b_c_unified/branch_c/paper/branch_c_elimination.pdf` | 18 |
| No Keller map admits two dicritical divisors | `branch_two_dicritical/paper/two_dicritical_closure.pdf` | 6 |

Page counts verified 2026-11-05 with `pdfinfo` against the on-disk PDFs
listed above (34, 18, and 6 pages respectively).

## Reproducibility

Each package ships its own verification entry point:

```bash
# Branch (a),(b) (or branch_ab_v19/verify_v19.sh, the identical copy)
JC2D-branches_a_b_c_unified/branches_a_b/verify_v19.sh

# Branch (c)
JC2D-branches_a_b_c_unified/branch_c/verify_branch_c.sh

# Two dicritical divisors
branch_two_dicritical/verify_all.sh
```

Checksums (`CHECKSUMS.md5`, `CHECKSUMS.sha256`) and build records
(`BUILD_STATUS.md`) are kept in each package directory.

## Note on removed directories

The legacy top-level `branch_ab/` and `branch_c/` directories were removed;
their contents are superseded by `JC2D-branches_a_b_c_unified/branches_a_b/`
and `JC2D-branches_a_b_c_unified/branch_c/` respectively.

`branch_ab_v19/` was restored at the root on 2026-10-03 because the Zenodo
record cites that path. It is kept byte-identical to
`JC2D-branches_a_b_c_unified/branches_a_b/`; the last sync was 2026-11-05
(verified byte-identical by `diff -r` after the 2026-11-05 paper rebuilds).
To check that the two copies agree, run
`diff -r -x __pycache__ -x .lake branch_ab_v19 JC2D-branches_a_b_c_unified/branches_a_b`.
