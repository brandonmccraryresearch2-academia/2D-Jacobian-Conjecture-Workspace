# Leg B log — GGHV §4 Propositions 4.1–4.4 + Algorithm PossibleStartingPoints (E5–E9)

## 2026-11-06 ~15:35 CST — Leg started; sources read
- Read in full: `hidden_files/phase4/gghv_statement_inventory.md` (entries E5–E9),
  `hidden_files/phase4/phase4_map.md` (§5, §6, §8, §9), GGHV TeX §4 (lines 457–1398,
  all four propositions + algorithm, including figures' corner lists).
- Read Phase 1 baseline: `d1_cor74_2026-11-05.lean` (Cor74Data, cor74_927/721/prop42/prop43,
  ell721_normalization), `d1_esquina2` (`esquina_item2_k1`), `d1_assembly`
  (MinimalPremises pattern), `composition_2026-11-04.lean` (`branch_c_eliminated`),
  `bridge_attempt_2026_11_04.lean` (`challenge_target`).
- Read verification logs: `lean/logs/d1_cor74_2026-11-05_parent_recheck.log` /
  `..._parent_axioms.log` — exact invocation pattern: standalone file (`import Mathlib`),
  run from a Lean project dir with `LEAN_PATH="$(lake env printenv LEAN_PATH)" lean --root=/tmp
  -o /tmp/<file>.olean /tmp/<file>.lean`, twice (FULL + AXIOMS with appended `#print axioms`).
- Retrieval leg CLOSED (read `hidden_files/phase4/retrieval/retrieval_log.md` in full):
  published [GGV1] §7 NOT FOUND (T1-R1–R15 exhausted); Joseph Lemma 2.2 NOT FOUND
  (T2-R1–R12). Hybrid-vs-slip therefore stays a carried premise; [GGV2] Prop 3.12
  unlanded (Leg F running in parallel) — carried, not waited on.
- VM lock: held by legC when leg started (age 106s at first check, 684s at file completion).
  Acquire legB (timeout 1800s) started in background; local work (file writing) done meanwhile.
  No local Lean compilation (ALL computation through GCP per standing direction).

## 2026-11-06 ~15:50 CST — Main file written (scratch, no repo changes)
- File: `~/workspace/research/tooling/phase4_legB/gghv_full_s4_2026-11-06.lean`
  (1,354 lines, `import Mathlib` only, self-contained).
- Formalisation level (documented in the file header): vertex-list level (Phase 1 style).
  Newton polygon = `List (Int × Int)`; φ₁ = `swapPt`; final morphisms = `phiPow c`;
  shears = `cutPt` model. The identification model↔paper-automorphism is carried as
  named premise fields about opaque intermediate lists; all decidable arithmetic is
  kernel. No `sorry` / `sorryAx` / `native_decide` anywhere (grep-verified; the only
  match is the word "sorryAx" in a comment stating its absence).
- Contents: §0 point arithmetic; §E5 sieve + k=1 + φ-map + `prop41_conditional`;
  §E9 algorithm implementation + `psp_183` output; §E6 Cor74 (24,9) data + R³ count +
  three sub-case φ-maps + `prop42_conditional`; §E7 Cor74 (28,8) data + (1,−3)-face +
  (−2,7) checks + k∈{1,2} + `prop43_conditional`; §E8 Cor74 (7,21) bundle +
  ℓ-normalisation (copied with attribution from d1_cor74) + φ-chain + `prop44_conditional`;
  verdict table + `#print axioms` for the four conditional theorems and key kernel lemmas.

## Findings recorded while writing (for the parent / validation gate)
1. INVENTORY CORRECTION (stale claim): the inventory says the (7,21) F-side instance is
   "not yet a `Cor74Data` bundle" (inventory §B, "still to add (i)"). WRONG as of the
   filed Phase 1 record: `d1_cor74_2026-11-05.lean` ALREADY defines `cor74_721`
   (dir (7,−2), ab (7,21), p 5, q 7, enF (5,15)) with `cor74_721_cond3`,
   `cor74_721_exp_P/Q`, and proves `ell721_normalization`. Re-pinned here self-contained
   (`cor74_721_s4`); NOT claimed as new. The inventory's E8 "not covered" part is
   therefore only the φ₁/φ₂/φ₃ polygon chain (now conditional here), not the bundle.
2. E5 sieve: `(1,1)` PASSES the divisibility (`13 ∣ 13`) — the paper excludes it by the
   diagonal argument, not the sieve. Recorded as `sieve_diag_passes` + `sieve_diag_value`
   so the sieve verdict is not overstated; `sieve_table_927` returns `[(1,1),(5,2),(13,5)]`.
3. E7 end assignment is SWAPPED relative to E5: the paper sets
   `(en(Q),en(P)) = ((2,1),(−1,0))`, i.e. `en(P) = (−k,0)`, `en(Q) = (k+1,1)` —
   opposite to E5's `(2,1)`/`(−1,0)`. Verified against the φ-images (both give the
   paper's finals). Recorded in the file.
4. E6 sub-case arithmetic verified by hand before formalising: the `(a',b') = (9,3)`
   vertex scales to `(18,6) = 2·(9,3)` / `(27,9) = 3·(9,3)` (sub-case 2); the two-factor
   `(18,6)` corner scales to `(36,12)` / `(54,18)` (sub-case 1); `(0,0)` = no extra
   vertex (sub-case 3). All three φ-images proved kernel (`phi_924_sub*`).
5. E9 algorithm: `dir` is the primitive PERPENDICULAR direction `(v/g, −u/g)` — verified
   against the paper's conclusion (output directions `{(1,−2),(2,−5)}` in `psp_183_dirs`).
   Included points: `(2,0),(3,1),(4,1),(6,2)` with per-point `s`/`N₁`/`N₂` values
   documented in the comment above `psp_183`.
6. No repo commits made (validation gate). No VM work yet — pending lock.

## Verification — COMPLETE 2026-11-06 ~17:30 CST
- [x] VM lock acquired (legB), lean-build-3 woken. — 1st acquire TIMED OUT after 1800 s (legC, ~16:06 CST); 2nd TIMED OUT (~16:36 CST); 3rd TIMED OUT (~17:07 CST; legC held ONE continuous lock since 22:11:17Z, pid 22986, ~50+ min); 4th acquire LANDED ~17:08 CST (pid 9617, after ~20 s). VM was already RUNNING (legC left it warm); SSH via --tunnel-through-iap; user brandonmccrary_research2_gmail_c; toolchain ~/toolchain/bin (lean/lake); project dir ~/repo/JC2D-branches_a_b_c_unified/branches_a_b/lean/ (lake env printenv LEAN_PATH). Singular 4.3.1, Python 3.11.2 confirmed on VM.
- [x] Probe file compiled first. — probe_s4_2026-11-06.lean: FIRST run FAILED with a real bug (parse error `dirPerp` line 10:30 — Lean 4 parses `(e : T, ...)` as a parenthesised ascription, not a tuple; the trailing `: Int` on the first component made the parser expect `)` at the comma). Fixed by extra parens around the first component in BOTH probe and main file (same term, disambiguated parse). Re-run: PROBE_EXIT=0, 6 s, Lean 4.34.0; `probe_psp_183` [propext], `probe_sieve_table_927` [propext].
- [x] FULL run: `LEAN_PATH="$(lake env printenv LEAN_PATH)" lean --root=/tmp -o /tmp/gghv_full_s4_2026-11-06.olean /tmp/gghv_full_s4_2026-11-06.lean` — run 1 (7 s, exit 1): 6 errors — (a) `rw` leaves `(↑1+1,1)=(2,1)` / `(-↑1,0)=(-1,0)` unclosed in E5/E7 henP/henQ (rw's auto-rfl is reducible-transparency; fixed with `; decide`); (b) stray `/--` doc comment before the §E6 `/-!` header (→ plain `/-` comment); (c) `rw`/`simp ... at <field projection>` illegal (rform_ne3_924, k1_828 — fixed with local `have` copies); (d) `hab ▸ h.k_ineq` motive failure through pair projections (→ `rw [hab] at <copy>` + `dsimp only`); (e) membership simp left trailing `∈ []` (added `List.mem_nil_iff, or_false`). Run 2 (7 s, exit 1): 2 errors — ℕ vs ℤ mismatch: E7 `k_ineq` is an Int inequality (`↑k`), k-lemmas were ℕ (fixed by restating `esquina_k12_247` / `esquina_k1_31` over `ℤ` with `((k : Int) + 1)`). Run 3: FULL_EXIT=0, 7 s. Header/verdict-table comments then updated to record verification (comment-only); final run FULL5_EXIT=0, 8 s, 0 errors. Only warnings: 4× `if_neg`/`if_pos` deprecation (use ite_eq_right/left instead) — warnings only, left as-is.
- [x] AXIOMS (from the `#print axioms` block in the file, same runs): `prop41_conditional` [propext, Quot.sound]; `prop42_conditional` [propext, Classical.choice, Quot.sound]; `prop43_conditional` [propext, Quot.sound]; `prop44_conditional` [propext, Classical.choice, Quot.sound]; `psp_183` [propext]; `sieve_table_927` [propext]; `ell721_normalization` [propext, Quot.sound]; `phiJacPair_3` / `phiJacPair_4` no axioms. `sorryAx` NOWHERE (grep-verified; only match is the comment stating its absence). All lists are permitted-triple subsets.
- [x] Second tool (Python recomputation, run on lean-build-3, Python 3.11.2): FIRST run FAILED 2/20 — my Python script had the divisibility backwards (`s % n2`, i.e. N₂∣s); the Lean file (`s ∣ N₂`) and the paper were right — (5,1) with N₂=1 was wrongly included by the script. Fixed script (`n2 % s`), re-ran: SECOND-TOOL CHECK ALL PASS, PY_EXIT=0 (20/20: sieve survivors, (1,1) diag point, algorithm output + directions with per-candidate s/N₁/N₂, E5/E7 k-bounds, all 9 φ-maps, both Jacobian-factor pairs).
- [x] VM lock released (VM NOT stopped — coordinator stops at checkpoints). — "LOCK RELEASED by legB", status UNLOCKED, 2026-11-06 ~17:31 CST; lean-build-3 left RUNNING.

## 2026-11-06 ~17:18 CST — Coordinator notice (two items, acknowledged)
- (1) Retrieval COMPLETE — published [GGV1] §7 text NOT FOUND (15 routes exhausted; only untried route is institutional access, a Brandon decision). ALREADY HANDLED as briefed: hybrid-vs-slip is carried as explicit premises (`HybridSlip924` in `Prop42Premises`, `HybridSlip828` in `Prop43Premises`) and the NOT FOUND outcome is recorded in the file header + final report. No waiting, no change.
- (2) VM lock time-slicing (new rule): acquire PER verification run only, release immediately after, max continuous hold ~30 min, never hold while writing proofs. NOTED. Leg B's verification is complete and its lock was already released (~17:31 CST); confirmed the lock has since passed to legA (age 22 s at check). No further lock use needed from Leg B unless a re-verification is ordered — any such run would follow the per-run acquire/release rule.

## 2026-11-06 ~16:00–16:10 CST — review pass + hardening (pre-verification)
- Full re-read of gghv_full_s4_2026-11-06.lean (1,354 lines, all sections E5–E9 + verdict table + #print axioms block).
- Hardened E6: the four `unfold preP924_1` / `unfold preQ924_1` steps in `prop42_conditional` replaced by `show` (defeq unfolding of the if-then-else) + `rw [if_neg/if_pos]` — same proofs, no tactic dependency.
- Verified `decide_eq_true_eq` exists in Lean 4.34.0 core (`Init/SimpLemmas.lean:412`, `@[simp] theorem decide_eq_true_eq [Decidable p] : (decide p = true) = p`) — `sieveOkB_iff`'s `simp only [sieveOkB, decide_eq_true_eq]` is valid. (Read-only grep of local toolchain source; no local compilation.)
- MEMORY.md external edits noted (no impact on Leg B): Phase 3 bullet extended (Brandon's 15:58 finalization step — update all repo-1 docs, "Cite this repo" blocks, rename branch_two_dicritical — + gcloud answer + 64 GB RAM correction); replacement two-dicritical paper uploaded (19 pp., Nov 2 2026, supersedes Oct 1 draft; front matter still links old cloud GitHub URL — stale, fork is canonical; PDF not to be altered; rename still awaiting Brandon's name choice).
