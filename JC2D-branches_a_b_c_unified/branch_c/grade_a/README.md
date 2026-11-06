# Branch (c), toward grade A: `ChartEmptyC_T1ne0` in Lean, up to two finite deliverables

Started 2026-10-12. This folder follows the corrected architecture of
`../../reviews/REVIEW_2026-10-12_handoff.md` §4.3. It replaces the A1–A5 drafts of the unmerged branch
`caic/branch-c-cleanup` (see the review, §4.1, for why those drafts cannot reach grade A as written).

**Status (2026-10-12, evening).** `chartEmptyC_T1ne0_of_certificate` (`lean/GradeA/Chart/Assembly.lean`) proves
`ChartEmptyC_T1ne0 L` for every field `L` of characteristic 0 from hypotheses that are finite computations on concrete
data: the Macaulay data (rows, pivot columns, support), **A1** (`Cinv * MS = 1` modulo `p`) and **A2** (`MS` is the
evaluated Macaulay block, up to one nonzero scale per generator). The chart reduction, the bridge to the Macaulay
form and the transfer to characteristic 0 are kernel-checked. `ChartEmptyC_T1ne0` stays grade B until the data and
A1, A2 are supplied ("What remains").

## What is proved here (Lean 4.34.0, Mathlib v4.34.0; no `sorry`; standard axioms only)

| Module | Theorem | Statement |
|---|---|---|
| `R67Data` | `R_no_root_int`, `rem_not_both_zero` | R has no root mod 67; for each of the 4489 monic quadratics X² + aX + b over 𝔽₆₇ the remainder of R is nonzero (`decide` on integers, axioms `[propext]`) |
| `IrreducibleR` | `R67_irreducible` | R is irreducible over 𝔽₆₇ |
| | `Rint_irreducible`, `Rrat_irreducible` | R is irreducible over ℤ and over ℚ (Gauss's lemma) |
| | `minpoly_eq_Rrat`, `Rrat_dvd_of_aeval_eq_zero` | for a root w of R in any field of characteristic 0, `minpoly ℚ w = R`, so R divides every rational polynomial vanishing at w |
| `Transfer` | `eval_eq_zero_of_eval_root` | if D ∈ ℤ[X] vanishes at a root of R in a field of characteristic 0, then R ∣ D in ℤ[X], so D vanishes at every root of R in every commutative ring (in particular at w₀ in 𝔽_p) |
| | `no_left_kernel` | if a square matrix M over ℤ[X] has a left inverse at a root w₀ of R mod p, then M(w) has no nonzero left kernel vector at any root w of R in any field of characteristic 0 |
| `Macaulay` | `macaulay_vecMul_eq_zero` | at a common zero z of F₁ … F_k ∈ ℤ[X][z] (at X = w), the vector of row-monomial values is a left kernel vector of the Macaulay block `coeff_{mon r}(mult c · F_{gen c})` |
| | `no_common_zero_of_certificate` | **the assembly:** if the Macaulay block has a left inverse mod p at a root w₀ of R, the F_n have no common zero at any root of R in any field of characteristic 0 |
| `R109Data` | `bezout_lin`, `bezout_quad_small`, `quad_mod` | Bézout certificates for `gcd(R, X^109-X) = 1` and `gcd(R, X^(109²)-X) = 1` (via modular reduction); kernel-verified identities |
| `IrreducibleR109` | `R109_irreducible` | R is irreducible over 𝔽₁₀₉ (from the two Bézout certificates; no `decide` on 11881 pairs) |
| | `det_transfer_109` | determinant transfer through `ℤ[X]/(R) →+* 𝔽₁₀₉[X]/(R̄)` (`RingHom.map_det`); a nonzero minor mod 109 lifts |
| `K5Field` | `K5_gcd_isUnit`, `K5_bezout`, `K5_isUnit_mk` | K₅ = ℚ[w]/(R) is a field (`AdjoinRoot.instField`); explicit extended-GCD inversion via `EuclideanDomain.gcdA`/`gcdB` |

`build.sh` compiles the five modules in a temporary directory against any Lake project with Mathlib v4.34.0
(default `../../branches_a_b/lean`, after `lake exe cache get` there), scans for `sorry`/`admit`/`native_decide`/
`axiom` (the keyword anywhere on a line, since 2026-10-13), and checks the axioms of the 12 theorems listed in
`lean/GradeA/Axioms.lean`. If the project has no compiled
Mathlib, it stops with exit status 2 before calling `lake`, which would otherwise start cloning Mathlib.
`logs/build.log` (rerun 2026-10-13): all checks pass, about 2 min on 2 cores, from scratch.

**H3 is now grade A.** "R is irreducible over ℚ" (premise H3 of `../rank_lemma_check/README.md`), until now checked
by FLINT and in Python, is `Rrat_irreducible`.

**Why this is the right transfer.** The rank computation is in 𝔽₃₂₀₀₃ at w₀ = 11147, and the claim is over any
field L of characteristic 0 with a root w of R. There is no ring map between them, so the transfer must go through
a ring that maps to both, here ℤ[X] (X ↦ w and X ↦ w₀). The A3 draft of the cleanup branch used a ring map K₅ → 𝔽_p,
which does not exist.

## The chart reduction and the interface (2026-10-12, evening)

| Module | Theorem | Statement |
|---|---|---|
| `Chart/Terms` | `exprOfTerms`, `denote_exprOfTerms`, `chartCtx` | a generator as a list of integer terms, read back as a reflected expression (kernel-friendly: recursors only; `x^0` is written as `1`, since `toPolyK` keeps `x^0` as a monomial) |
| `Chart/Gens` (generated) | `tl_n`, `F_n` | the six chart generators F_n = D_k^d · D_n · cond_n on b₁₂,₂₂ = 1, b₁₂,₂₃ = κ(w), reduced mod R, with b₁₁,₂₀ free: 110, 175, 175, 260, 260, 260 integer terms (22, 35, 35, 52, 52, 52 terms over K₅) |
| `Chart/F_<n>` (generated) | `s_F_n` | ck_n, eT2, eX, eR vanish ⟹ F_n vanishes: `lc_zero2` with the identity checked by `decide +kernel`, in the form of the bundle's `T1Zero.s_f_n` without the stratum b₁₁,₂₀ = 0 |
| `Chart/Main` (generated) | `chart_gens_vanish` | **the chart reduction:** at a root w of R in a field of characteristic 0, a point with b₁₂,₂₂ = 1 at which Ω and the six conditions vanish is a common zero of the six F_n (Ω gives b₁₂,₂₃ = κ(w) through the bundle's `s_sq`, `s_X2`) |
| `Chart/Poly` | `polyOfTerms`, `denote_exprOfTerms_chartCtx` | the same term lists as `MvPolynomial (Fin 5) ℤ[X]`; at a chart point the reflected expression equals `evalAt w z` of the polynomial |
| `Chart/Assembly` | `Fpoly_vanish` | the chart reduction in `MvPolynomial` form |
| | `chartEmptyC_T1ne0_of_certificate` | **the interface:** the Macaulay data, A1 and A2 give `ChartEmptyC_T1ne0 L` for every field of characteristic 0 |

- **Generators.** `certgen/gen_chart.py` computes the six certificates from the bundle's own code (its
  `certgen_c/gen_t1zero_c.py`, imported read-only; `certgen/shim/make_cert_c.py` provides the two functions of
  `make_cert_c.py` it uses, verbatim). It checks every identity by exact integer arithmetic. It also checks that the
  generators are the rank check's, up to one constant per generator: F_n(w₀) = D_k^d D_n · G_n mod p at p = 32003 and
  1000003, with G_n from the bundle's `step3b_rank_lift.chart_modp_direct`. `certgen/gen_chart_lean.py` writes the
  generated modules.
- **Neither b₁₁,₂₀ ≠ 0 nor the five "pure" conditions are used.** The six generators have no common zero on the
  whole chart, which is what the rank check shows.
- **Build.** `build_chart.sh [BUNDLE_PROJECT]` regenerates the generated modules and compares them byte for byte,
  scans, compiles the 4 base and 12 chart modules, and checks the axioms of the 13 theorems in `Chart/Axioms.lean`.
  The chart modules import the bundle's `CondsC` and `T1Zero` modules (read-only), so the project must have the
  bundle built. `logs/build_chart.log` (rerun 2026-10-13): all checks pass, about 4.5 min on 2 cores, from scratch.

- **Bridge and branch-(c) elimination.** `build_bridge.sh [BUNDLE_PROJECT]`
  stages the filed oleans, fresh-compiles the eight chart modules, scans
  `lean/GradeA/Bridge.lean` and `lean/GradeA/Composition.lean`, compiles the
  tracked modules `GradeA.Bridge` (`bridge_Fpoly`, `hsupp_chart`, `hA2_chart`,
  `challenge_target`) and `GradeA.Composition` (`branch_c_eliminated`), and
  checks both theorems' axioms are the permitted triple. The modules are the
  2026-11-04 scratch proofs filed in the tree (theorems byte-identical; only
  the headers and one import line changed); the frozen bundle is not touched.
  See `BRIDGE_STATUS_2026-11-06.md`. Run 2026-11-06 on lean-build-3 against
  the overlay project: all checks passed.

## What remains for `ChartEmptyC_T1ne0` (grade B today)

The hypotheses of `chartEmptyC_T1ne0_of_certificate`, for p = 32003 and w₀ = 11147. Nothing else is missing.

1. **The generators and the chart reduction: done** (above).
2. **The rows, the pivot columns, the support condition.**
   - The 3199 row monomials (weighted degree ≤ 24, weights 1, 2, 3, 3, 4), injective, with the monomial 1 among them.
   - The 3199 pivot columns (generator, multiplier) of `branch_c/rank_lemma_check/`.
   - `hsupp`: every monomial of `mult c · F_{gen c}` is a row. This is decidable from a sparse representation of
     the F_n.
   - **The F_n must stay reduced modulo R** (an outside referee's caution, 2026-10-13). `hsupp` is about the
     ℤ[X]-support, while `build_matrix.py` builds the rows from K₅-supports. A coefficient that is a nonzero multiple
     of R would add a monomial that is not a row. The generators of `Chart/Gens.lean` have every w-exponent below 5,
     so the two supports agree; `gen_chart.py` checks this (check 5).
3. **The left inverse modulo 32003**, in two parts that meet at one matrix `MS`, the pivot block of the rank check
   as written in its data (unscaled generators G_n, the rank check's row order):
   - **(A1, CAIC)** `hA1 : Cinv * MS = 1` over `ZMod 32003`, with `Cinv k i` the k-th 40-bit digit of `Cpk_i`. The
     kernel already checks the packed identities (`../rank_lemma_check/`: 6,398 identities, axioms `[propext]`);
     the no-carry digit argument (B = 2⁴⁰, CAIC's draft `NoCarryBridge.lean`, 3 `sorry`s) turns them into this
     matrix identity, once linked to RCCommon's Boolean checks `slotOK`/`colOK`.
   - **(A2)** `hA2`: `macaulay Fpoly mon gen mult`, evaluated at w₀ mod p, equals `MS * diagonal (scale ∘ gen)` with
     `scale n = D_k^d D_n mod p` (nonzero: checked by `gen_chart.py`). Keeping the packed certificate unchanged costs
     only this diagonal. A route inside the kernel: compute each column from the sparse generators by a function on
     natural numbers; check the 3199 columns against the data by `decide` (about 10⁵ entries); and prove once,
     generically, that the computed column is the evaluated `macaulay` column (`MvPolynomial.coeff_monomial_mul'`
     and the sparse sum).
   - Small items: `hw₀` (R(11147) ≡ 0 mod 32003, via `eval₂_Rint`) and the primality of 32003.

Both A1 and A2 need the column data of M_S as a Lean definition; today it exists only inside the `col_j` statements
of the generated check modules. `../rank_lemma_check/gen_lean.py` will be extended to emit it.

## Files

| File | Contents |
|---|---|
| `lean/GradeA/R67Data.lean` | the two finite checks modulo 67 |
| `lean/GradeA/IrreducibleR.lean` | R irreducible over 𝔽₆₇, ℤ, ℚ; the minimal polynomial of a root |
| `lean/GradeA/Transfer.lean` | the transfer through ℤ[X]; `no_left_kernel` |
| `lean/GradeA/Macaulay.lean` | the Macaulay block; the left kernel at a common zero; the assembly theorem |
| `lean/GradeA/Axioms.lean` | `#print axioms` for the 12 theorems |
| `lean/GradeA/Chart/Terms.lean`, `Poly.lean`, `Assembly.lean` | the term lists and their read-back; the `MvPolynomial` form and the bridge; the interface theorem |
| `lean/GradeA/Chart/Gens.lean`, `F_*.lean`, `Main.lean` | generated by `certgen/gen_chart_lean.py`: the generators, the six certificates, the chart reduction |
| `lean/GradeA/Chart/Axioms.lean` | `#print axioms` for the 13 chart and interface theorems |
| `lean/GradeA/Bridge.lean`, `lean/GradeA/Composition.lean` | the tracked modules `GradeA.Bridge` (`challenge_target`) and `GradeA.Composition` (`branch_c_eliminated`); the 2026-11-04 proofs filed in the tree |
| `certgen/gen_chart.py`, `certgen/gen_chart_lean.py`, `certgen/shim/make_cert_c.py` | the certificate computation and checks; the Lean writer; the two functions of the bundle's `make_cert_c.py` it needs |
| `build.sh`, `build_chart.sh`, `build_bridge.sh` | build and audit (the base modules against any Mathlib project; the chart modules against the bundle's project; the bridge and composition modules against the bundle's project) |
| `BRIDGE_STATUS_2026-11-06.md` | status record for the bridge/composition incorporation (provenance, diffs, verification, validation) |
| `logs/build.log`, `logs/build_chart.log` | the runs of 2026-10-13 |

The frozen bundle `../bundle_v3_1/` is not touched: the base modules import Mathlib only, and the chart modules import
the bundle's `CondsC` and `T1Zero` modules and run its generator code read-only.
