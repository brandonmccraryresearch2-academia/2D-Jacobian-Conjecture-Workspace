# Bridge + branch-(c) elimination as tracked modules — status 2026-11-06

Step 1 of the six-step programme approved 2026-11-06 ~14:37 CST.

## What was filed

| Module | File | Theorem(s) | Axioms |
|---|---|---|---|
| `GradeA.Bridge` | `lean/GradeA/Bridge.lean` (2,859 bytes, sha256 `96e992d6f4cf2bbfcac33c71e8393700bc2783fc3d6fb5b747a99fc40a1d5c16`) | `bridge_Fpoly`, `hsupp_chart`, `hA2_chart`, `challenge_target` | `[propext, Classical.choice, Quot.sound]` |
| `GradeA.Composition` | `lean/GradeA/Composition.lean` (1,254 bytes, sha256 `b21a892926dc8d936407c74f6d98bf8393787d3bc1ebd823a56e268bf8587faf`) | `branch_c_eliminated` | `[propext, Classical.choice, Quot.sound]` |

Build/audit script: `build_bridge.sh` (sha256 `59e91454413cbf677db684cae23609651f892029cadda4f68ecf0482ffd97822`),
following the `build.sh` / `build_chart.sh` pattern: stage the filed oleans,
fresh-compile the eight Chart modules, scan for `sorry`/`admit`/
`native_decide`/`axiom`, compile `GradeA.Bridge` then `GradeA.Composition`,
audit the `#print axioms` lines. Default bundle project
`../bundle_v3_1/jacobian_lean`; on lean-build-3 pass `~/tooling/work/overlay_c`.
(The version that ran on the VM was sha256 `32f2839f673770d5f220d31b63a2b1be5b0f65b356a3e00dc4c893718bbd4cd7`;
the only change since is a comment rewording required by validation — no
Lean re-run needed.)

## Provenance and diffs vs the validated scratch files

- Origin: scratch files `bridge_attempt_2026_11_04.lean` (2,507 bytes, sha256
  `b4b4c3985196f46283cbf22a993d04bb3baf07eda8db9bfa44d833f9815401c4`) and
  `composition_2026-11-04.lean` (811 bytes, sha256
  `59d78bcfc47350844a04665cd5bb06baf9854a66a494636feef6dd3be7ac6c4e`),
  both proved 2026-11-04 on lean-build-2, no hypotheses, permitted triple.
  Filed leg copies at `gghv-dependency-closure/lean/` are byte-identical to
  the scratch files and stay in place as the leg record.
- `GradeA.Bridge` differs from its scratch file by the header comment ONLY;
  all theorem statements and proofs are byte-identical.
- `GradeA.Composition` differs from its scratch file by the header comment
  plus one import line (`import bridge_attempt_2026_11_04` →
  `import GradeA.Bridge`); the theorem statement and proof are byte-identical.
- The frozen bundle `../bundle_v3_1/` was not touched: `Composition` imports
  its `Jacobian.BranchC.T1Zero.Combine` read-only, as before.

## Verification (lean-build-3, Lean 4.34.0, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b)

- Baseline parent re-check of the scratch-identical copies
  (`bridge_recheck_2026-11-06.sh` v2): all eight Chart modules exit 0;
  bridge run 1 exit 0 (6 s), composition run 1 exit 0 (5 s); run-2 AXIOMS
  fresh processes both exit 0; `challenge_target` and `branch_c_eliminated`
  each on `[propext, Classical.choice, Quot.sound]`; sorryAx absent.
  Log: `~/workspace/goals/gghv-dependency-closure/hidden_files/
  step1_bridge_incorporation/logs/bridge_recheck_2026-11-06.log`.
- `build_bridge.sh` run 2 against the actual module files (overlay_c):
  Chart F_Psi 4 s, F_Phi1 5 s, F_Phi2 6 s, F_Theta1 10 s, F_Theta2 10 s,
  F_Theta3 10 s, Main 52 s, Assembly 5 s — all exit 0; scan PASS;
  `GradeA.Bridge` exit 0 (5 s), `GradeA.Composition` exit 0 (6 s); axioms
  PASS 2/2 on the permitted triple; "ALL CHECKS PASSED".
  Log: `.../logs/build_bridge_2026-11-06.log`.
- Run 1 of `build_bridge.sh` failed on `lake: command not found`: the script
  had inherited `PATH="$HOME/.elan/bin:$PATH"` from `build.sh`, but on
  lean-build-3 `~/.elan/bin/lake` does not exist — lake/lean live in
  `~/toolchain/bin/`. Fixed (`PATH="$HOME/toolchain/bin:$HOME/.elan/bin:$PATH"`).
  Note: `build.sh` and `build_chart.sh` carry the same latent PATH issue when
  launched from a non-interactive shell; they passed 2026-11-05 from a shell
  that had `~/toolchain/bin` on PATH. Not changed here (out of scope).
- The re-check run 1 (script v1) failed with `unknown module prefix 'RCData00'`:
  `A1Data00–07` import top-level modules `RCData00–07`, whose oleans live only
  in `branch_c/rank_lemma_check/lean/` (also `RCCommon.olean` there). Fixed by
  staging those oleans and adding the directory to LEAN_PATH. Why the
  2026-11-04 run succeeded is unresolved from the record (possibly a different
  LEAN_PATH/tree state on lean-build-2); recorded, not guessed.
- One linter warning only, in both the 2026-11-04 scratch log and this run:
  `Bridge.lean:50:2` suggests `have` for `haveI`. Not changed: `haveI`
  registers `prime32003` as an instance for the `exact` below, and the
  suggestion is generic and untested here. Harmless.

## Validation

- Basis: the combined-paper deepest-research validation PASSED 2026-11-04 and
  covers this content.
- Focused deepest-research validation of this incorporation (content changed
  vs scratch: headers + one import line): GO — deepest-research `fact-check`
  mode, 2026-11-06 evening. All six checks PASS (byte-identity of the modules
  vs scratch confirmed by independent diff/SHA recomputation; kernel-evidence
  logs support the claims with no discrepancies; the import change cannot
  change the proved statement; headers claim nothing beyond the evidence;
  `build_bridge.sh` follows the repo pattern with a correct step-3 axioms
  check; nothing weakens or goes beyond the validated 2026-11-04 content).
  Two text-only corrections were required and applied before commit: this
  line replaces the PENDING marker, and the dependency-olean convention
  sentence below was reworded to its precise form. The validation was
  log-based (no Lean re-execution by the validator).

## What this claims and does not claim

- `challenge_target`: `ChartEmptyC_T1ne0 L` for every field of characteristic
  0, no hypotheses. `branch_c_eliminated`: no NewtonNFc Keller pair over any
  field of characteristic 0. Together with the branches (a),(b) `main_theorem`
  (case (2)), the GGHV Prop. 4.3 case split is fully eliminated in Lean.
- Does NOT claim (72, 108) excluded unconditionally, and does not prove JC(2):
  both still rest on GGHV exhaustiveness and the reduction chain, ledgered
  not re-derived.
- The dependency oleans staged by `build_bridge.sh` are the filed tree
  artifacts (built from the filed sources 2026-11-04/05; the eight grade-A
  modules were rebuilt from source by `build.sh` on 2026-11-05); only the
  Chart modules and the two new modules are compiled fresh here. Trusting
  prebuilt dependency oleans (Mathlib, the bundle) is the established
  convention; the filed GradeA oleans are additionally trusted here, having
  been rebuilt from source by `build.sh` on 2026-11-05. (`build.sh` itself
  rebuilds all eight grade-A modules from source and does not stage filed
  GradeA oleans.)
