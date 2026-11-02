# Comparator harness for branch (c) grade A — prototype (2026-10-21)

Modelled on the Comparator pattern of the openai/math release: a challenge
module pins the *statements*; solution modules must prove exactly those
statements; the only permitted axioms are `propext`, `Classical.choice`,
`Quot.sound`. This folder is a prototype: it pins the statements and provides
the textual pin check (`check.sh`). It does not change any existing module,
build script, or grade.

## What is pinned (`Challenge.lean`, config `comparator.json`)

| Pin | Kind | Status |
|---|---|---|
| `challenge_interface` | theorem, statement verbatim `chartEmptyC_T1ne0_of_certificate` (Assembly.lean) | **Solved** — Assembly.lean is the reference solution; `check.sh` verifies the statements still agree textually |
| `A1_statement` | `Prop` def, type verbatim the interface's `hA1` | **Open** — at the concrete data this is the packed kernel check `C · M_S = I` over `ZMod 32003` |
| `A2_statement` | `Prop` def, type verbatim the interface's `hA2` | **Open** — at the concrete data this identifies `MS` as the evaluated Macaulay block of `Fpoly`, up to a nonzero scale per generator |
| `challenge_target` | theorem: `ChartEmptyC_T1ne0 L` for every char-0 field `L`, no hypotheses | **Open** — follows from the interface + the concrete data + A1/A2 solutions |

## What a solution must supply (unchanged from `../README.md`, "What remains")

The concrete data of `branch_c/rank_lemma_check/` in Lean form: `ρ = Fin 3199`,
the 3199 row monomials (`mon`, injective, `1` among them), pivot columns
(`gen`, `mult`), the support condition `hsupp`, the prime `p = 32003` with
`w₀ = 11147` a root of `Rint`, and `MS`, `Cinv`, `scale` (nonzero) — then
proofs of `A1_statement` and `A2_statement` at that data. Nothing else is
missing, and nothing pinned here changes when the data lands.

## What this prototype does *not* do

- It is not compiled yet: `Challenge.lean` imports `Jacobian.BranchC.T1Zero.Combine`
  and the generated chart modules, which exist only once the branch-(c)
  overlay is built (see `../build_chart.sh`). `check.sh` therefore checks the
  pin *textually* for now; the kernel-level check (compile challenge +
  solution, compare exported statements, `#print axioms` against the
  permitted list) is the same shape as `../build.sh` steps 2–3 and should be
  wired once the overlay builds.
- `Fpoly` is copied verbatim into `Challenge.lean` (the openai/math
  self-contained-definitions pattern) because Assembly.lean both defines it
  and proves the interface. Factoring `Fpoly` into `GradeA/Chart/Poly.lean`
  would let the challenge import it instead; the pins would not change.

## Running the check

```sh
bash check.sh              # pin integrity + challenge hygiene
bash check.sh Solution.lean  # additionally scan a candidate solution file
```

Exit 0 iff the interface pin matches Assembly.lean (modulo whitespace and
the theorem name), the challenge contains exactly its two `sorry` closures
and no `axiom`/`admit`/`native_decide`, and any supplied solution file is
free of `sorry`/`admit`/`axiom`/`native_decide`.
