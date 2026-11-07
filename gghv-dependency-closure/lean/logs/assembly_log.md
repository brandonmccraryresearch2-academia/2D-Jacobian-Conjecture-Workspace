# Assembly log — GGHV full-proof programme, assembly stage (2026-11-06/07)

## 2026-11-06 ~19:47 CST — Assembly started (subagent, parent brief)

- Read: `phase4_map.md` §18 (all leg results), `gghv_statement_inventory.md`
  (E1–E23, full), Leg A file (645 lines, full), Leg B `Prop41/42/43/44Premises`
  + conditional theorems, Leg C `thm51_conditional`/`cor52_conditional`,
  Leg E R8 file + `legE_log.md` axiom lists, Leg F key theorems (grep-verified
  present at stated lines), Leg D `s6_axioms3.log` tail, Leg H det jsons
  (recomputed values match: p=32003 det 29127, p=1000003 det 262898,
  routes_agree true), Leg G logs present (9 files), retrieval log
  (both targets NOT FOUND, lines 94/163).
- Verified on disk (not from the map alone): no duplicate top-level
  `theorem/def/structure` names across Leg A/B/C files; Leg A `variable`
  line 191 only; Leg C `open Polynomial`/`open Finset` lines 58–59 only;
  Leg B axioms from `legB_log.md` (prop41 [propext, Quot.sound], prop42
  [triple], prop43 [propext, Quot.sound], prop44 [triple], psp_183 [propext],
  sieve_table_927 [propext]); Leg C `thm51_conditional` [triple],
  `cor52_conditional` no axioms (from `s5_axioms.log`); Leg A FULL_EXIT=0
  6 s, AXIOMS_EXIT=0 6 s, second tool 28 checks ALL PASS exit 0
  (from `legA_log.md`).
- [GGV5] discrepancy: checked Leg A file header (only place the
  "§6 = Program and graphic display" claim appears; `legA_log.md` contains
  no mention of 1708/GGV5/6.1 — grep empty), on-disk TeX
  `tex/1708.07936/main.tex` (§1 l.265, §2 l.390, §3 l.1376, §4 "Program and
  graphic display" l.1638, §5 l.1669, §6 "Possible counterexamples" l.1792,
  `caso antisimetrico` l.1874), local arXiv v1 PDF
  (`arxiv_1708.07936.pdf`, pdftotext: TOC "4 Program and graphic display"
  p.23, "6 Possible counterexamples" p.27, "Proposition 6.1. The example
  corresponding to F22 with (m, n) = (2, 3)..." at pdftotext l.1533),
  arXiv abs page (crawled 2026-11-07 01:51 UTC: "Some algorithms related
  to the Jacobian Conjecture", submitted 26 Aug 2017, NO journal-ref field;
  single submission), web search (2018 paper cites [GGV5] as "available at
  arXiv:1708.07936" — still arXiv-only as of Aug 2018; no journal version
  found). Determination: Leg A's §6 label is WRONG for the only [GGV5]
  source on disk and for arXiv v1; no alternative version exists to
  attribute it to (no v2, no journal version found); most likely a
  miscount/misread by Leg A. [GGV5] Prop 6.1 VERIFIED for the arXiv
  version (§6, `caso antisimetrico`); numbering-UNVERIFIED for any
  published version (none found to exist). Full write-up in the inventory.

## Assembly file built (local, no VM)

- `gghv_full_assembly_2026-11-06.lean` (3,165 lines) =
  header + Leg A body (644 lines, `import Mathlib` stripped) +
  Leg B body (1,377 lines) + Leg C body (835 lines) +
  `assembly_section.lean` (256 lines: Prop42Shape/Prop41Shape,
  prop42_shape_of/prop41_shape_of, S5Link, MinimalPremises2 (20 fields),
  link_924_derived/link_927_derived, theorem21_minimal_v2,
  theorem21_conditional_minimal_v2, discharge audit, #print axioms block
  for 11 theorems).
- Design decision (recorded in the file header): fields 9–10 are REFINED,
  not unconditionally discharged. The old opaque links are replaced by
  named chains: prem42/prem41 (§4 structures, carried) → kernel B
  conditionals → bridge924/bridge927 (polynomial lift + Cor 5.7 step,
  carried — Leg B is vertex-list level only, Laurent layer R14) →
  link52_927 (carried) → link51_924/link51_927 (§5 data links, carried)
  → kernel C thm51_conditional → False → endgame data ex falso.
  Prop44 (E8) is in the file as part of Leg B but consumes no assembly
  premise: the (7,21) row is eliminated via §3, not §6.
- Pre-VM checks (local): single real `import Mathlib` (line 1; the other
  two grep hits are header-comment mentions); `sorry`/`^axiom `/`admit`
  grep: no hits outside comments stating their absence.
- `r8_axioms_2026-11-06.lean` (146 lines) = Leg E R8 file + appended
  `#print axioms` for esq3_dir_b2/b1/b0, esq3_lform_endpoint_lo/hi,
  esq3_lform_Q (the six theorems Leg E compiled but did not print).
  Leg E's own axioms run printed 7 other R8 theorems (verified in
  `logs_vm/gghv_full_esquina3l_2026-11-06_axioms.log`).

## VM work (pending — lock held by `laurent` at last check)

- Lock status at ~20:00 CST: LOCKED by laurent (age 109 s). Per the
  time-slicing rule: local work (inventory draft) first, acquire per
  verification run only, release immediately after.
- Runs to do, in order: (1) assembly FULL; (2) assembly AXIOMS
  (same file — the #print block is already in it; record per-theorem
  lists); (3) R8 axioms file (FULL + print in one run — the file has
  the #prints appended; record the six lists).
- VM stop: only if I hold the lock and no other agent is using it
  (check lock status first); otherwise leave running and say so.

## VM work — COMPLETE 2026-11-07 ~02:08 UTC

- Lock: acquired as `assembly` after the Laurent agent released (acquire
  waited ~8.7 min; pid 2175). VM lean-build-3 was already RUNNING.
- Runs (all via `gcloud compute scp/ssh --tunnel-through-iap`,
  `~/toolchain/bin/lake env lean --root=/tmp` from the
  `branches_a_b/lean` project dir — the established pattern):
  - scp assembly file (3,165 lines) + r8 file to /tmp: OK.
  - FULL assembly: `assembly_full.log` rc=0, 135 s, error count 0
    (grep -c 'error' = 0). 98 warnings, all linter/deprecation noise
    (57 unused simp args, unused `repeat rw` tactics, `if_pos`/`if_neg`
    deprecations already known from Leg B, unused variable names,
    mathlib/batteries local-changes notices). No errors, no sorryAx.
  - AXIOMS assembly (repeat of the same file; the #print block for 11
    theorems is in the file): `assembly_axioms.log` rc=0, 50 s, error
    count 0; log byte-identical in size to the FULL log (36,472 bytes) —
    determinism repeat.
  - R8 axioms: `r8_axioms.log` rc=0, 15 s, error count 0.
- Axiom lists (assembly run — B/C conditionals RE-VERIFIED here, not
  just re-quoted; all match the legs' own reported lists):
  prop41_conditional [propext, Quot.sound]; prop42_conditional [triple];
  prop43_conditional [propext, Quot.sound]; prop44_conditional [triple];
  thm51_conditional [triple]; cor52_conditional []; prop42_shape_of
  [triple]; prop41_shape_of [propext, Quot.sound]; link_924_derived
  [triple]; link_927_derived [triple]; theorem21_minimal_v2 [triple].
  (Leg B's own #print block in the file also re-printed psp_183
  [propext], sieve_table_927 [propext], ell721_normalization [propext,
  Quot.sound], phiJacPair_3/4 [].)
- R8 six (task 2 — DONE): esq3_dir_b2/b1/b0 [] (zero axioms);
  esq3_lform_endpoint_lo/hi [propext]; esq3_lform_Q [propext,
  Quot.sound]. Recorded in the inventory §2 R8 table.
- Lock RELEASED immediately after the runs (`LOCK RELEASED by assembly`;
  status UNLOCKED). VM left RUNNING (not stopped — coordinator stops at
  checkpoints; the Laurent agent may still need it). No repo commits.
- The .lean assembly file was NOT edited after verification — the local
  copy is byte-identical to the copy compiled on the VM.
- Inventory updated with the run results (STATUS, §0, E1, §2 R8, §5,
  §10, §10 "what remains open" renumbered). No PENDING markers remain
  except the Laurent fold-in (§7).

## Still open (assembly stage)
- Laurent fold-in pass (E11/E19/E20/E23) — awaits the parent forwarding
  the fragment's results. Do NOT start before then.
- Validation gate (G1) before any filing.
