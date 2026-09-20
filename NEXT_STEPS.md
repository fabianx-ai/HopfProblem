# Next steps (after the fresh-reviewer pass over rounds 7 and 8, 2026-09-21)

The reviewer pass (`Lib/reviews/REVIEW-7-8.md`, twenty-one Fable reviewers, one receipt each, reviews in
`Lib/reports/review-7-8/`) accepted all twenty-one receipts with findings and found nothing unsound: no
weakened statement, no added hypothesis, no lost content, merges replayed clean. What it found is in the
receipts, the docstrings and the citations. Open, in order:
(1) the fix list of `REVIEW-7-8.md` §3 (about forty docstring/citation/receipt corrections, the two
refuted "forced" claims of packet 02 to be lifted, the `Coproduct` biproduct pins, the `SphereTwo` probes
in a new `Hopf/Proof/AxiomAudit.lean`, the duplicate `import` lines, the twin-less deletions recorded),
one commit each, then the receipts' counts corrected in one commit; (2) the monolith wave,
`Lib/reports/round-7/judgement/monoliths.md` (25 files; `SurgeryCollapse`/`OrderedCancellation` first,
they hold the last Morse D material); (3) the owner decisions: chain-interface coefficients (the pins
reviewer confirms the `ULift ℤ` obstruction is real and a protocol obstruction; the clean route is a new
polymorphic `chains` beside the pinned one plus a `u = 0` comparison, i.e. an addition), the pre-PR chain
tower (dup-hom item 2, refusal judged right). The `Hopf`-side axiom probes are no longer a decision:
the reviewers' standing rule is that a move to `Hopf/Proof` carries its probes.
Also carried over from the receipts' "left" sections (dropped by the previous version of this file):
the 40 Jev two-letter disagreements and the auditors' ten low-confidence calls; the remaining project
namespaces (`nativeMorseIndex`, `NativeTransversality`, `ThreefoldGluing`, `SpecialPeriods.Threefold.Star`,
`MorseCancellation.`); dup-hom items 3–6 (the degree-one cochain lemmas are unblocked now that
`GlobalUnitH1Criterion.lean` is gone); dup-sheaf items 1–5; dfiles-c's `sheaf`/`unit` removal; moved's
`Matrix.Pivot`/`Module.Presentation`/`sheetSum` items; the ~17 unattributed remaining pins.
Two facts every later round must know: `autoImplicit` is on in 221 of 446 `Lib` files (no `leanOptions`
in `lakefile.toml`), and a statement can be pinned at universe 0 with no `.{0}` in its text (instance
arguments resolved at a universe metavariable; `#check` with `pp.universes` finds it).

Round 8 (`Lib/reviews/INTEGRATION-8.md`) did the judgement packets except the monoliths: universe pins
1,024 → 320 (the rest is the chain-interface decision, `ULift ℤ` vs literal `ℤ`), 280 duplicate
declarations gone with twins, the D files moved or split, project namespaces partly renamed.

Round 7 (`Lib/reviews/INTEGRATION-7.md`) did the scriptable and checklist blocks of the textbook audit with
Opus 5 agents: preamble gone, `_mo1973` names gone, `Lib.lean` complete, about 2,057 docstrings added,
about 467 universe pins lifted, manuscript citations replaced by textbook references in ~150 files. The
judgement round is prepared in `Lib/reports/round-7/judgement/`: `chokepoint-pins.md` (lift these first,
then re-run the checklist on the files they release), `monoliths.md` (25 files to split, with the
auditors' cut lists), `d-files.md` (21), `moved-verbatim.md` (7), `duplicates.md` (11 groups). Then the
fresh-reviewer pass over `Lib/reports/round-7/**/RECEIPT*.md`. The audit itself: `Lib/reports/textbook-audit/AUDIT.md`;
Jev calibration: `Lib/reports/textbook-audit/jev/JEV2.md`.

Integration 6 (`Lib/reviews/INTEGRATION-6.md`) replayed the 358 `Lib/` commits of `center-solution` onto
this branch; `Lib/` is byte-identical to `center-solution`'s (446 modules). Two small follow-ups from it:
(a) the 12 `Hopf/Proof` deletions of the mixed commits (`Lib/reports/integration-6/commit-classification.txt`,
the entries listing a `Hopf/` path): the material they delete now lives in `Lib`, take them over one commit
each (cherry-pick the `Hopf/` hunk only), then run the environment diff; (b) 13 `Lib` modules are not imported
by `Lib.lean` (list in INTEGRATION-6 §2): add the imports, in one commit, after checking with the owner that
`Lib.lean` need not stay identical to `center-solution`'s. The textbook audit below now covers all 446 files.

Owner decision 2026-09-14: the remainder is done by Claude agents; no seat assignment. Head:
`lib/textbook-extraction`, the commit the owner names (`git log -1`). Reviews: `Lib/reviews/INTEGRATION-5.md`
(the parallel round), `INTEGRATION-4.md`. Layout: `Hopf/<path>.lean` holds only the stock still to be
moved into `Lib/`; proof-specific declarations are under `Hopf/Proof/<path>.lean`; the `Mathoverflow1973`
wrapper survives only around the final theorem (`comparator/config.json` names
`Mathoverflow1973.mathoverflow_1973`). Census (`scripts/lib_stock_census.py --check`, counts outside
`Hopf/Proof/`): 123 against baseline 1648 — 1,516 declarations moved this round in 12 agent branches
(receipts in `Lib/reports/integration-4/*-moves.md`, `freed-*.md`, `import-all.md`).

## 1. Review pass (first)

No fresh-context reviewer looked at this round's moves. Run one reviewer per receipt
(`singhom-moves.md` 686 rows, `spheretop-moves.md` 331 + 231, `recognition-moves.md` 87 + 31,
`lcp-moves.md` 94, `freed-wang.md` 73, `freed-circle.md` 16, the E1 split, `import-all.md`): statements
verbatim modulo the disclosed retargets, nothing lost, every claim reproducible. Findings go into
`INTEGRATION-5.md` §5 (a new section, "Review findings") and are fixed before the next moves. Two points to judge explicitly: the second
SphereTopology pass moved the four `DiskOnePointCollapse.collapse*` rows after finding that their only
"SixSphere" mention is the `SixSphereCube` export alias of `OnePointCollapse` (retarget
`SixSphereCube.X -> OnePointCollapse.X`); and `lib/next-lcp` left a `namespace FirstHurewicz export
SingularChains (...)` alias block in `Hopf/LCP/CuspFilling.lean` for three `Hopf/Proof/` consumers.

## 2. Stock still under `Hopf/` (123 rows)

- `Hopf/Recognition.lean` 95: 34 CHARGED (`SixSphereCube.*` and 13 singletons) stay; 61 were blocked by
  `Hopf/SphereTopology.lean` rows that the second pass has since moved
  (`Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean`), so most are movable now — third pass, same
  method (`lean-agent-ide dump Hopf.Recognition`, receipts as before).
- `Hopf/SphereTopology.lean` 23, `Hopf/SingularHomology.lean` 2: CHARGED, stay; they are the file's residue
  and should move to `Hopf/Proof/<path>.lean` under the layout rule once nothing stock depends on them.
- `Hopf/Hurewicz.lean` 3: `SixSphereCube.{StandardSphere, euclideanOnePointSphereHomeomorph,
  sphereBasePoint}` are proof-specific but used by stock `Hopf/Recognition.lean`; move them to
  `Hopf/Proof/Hurewicz.lean` together with their Recognition consumers (item above).
- The 24 `PeriodTorusHigherHomology` rows of `FREED.md` left under `Hopf/Proof/LCP/Specialization.lean`
  (`freed-circle.md`, "blocked") were blocked by `Hopf/LCP/*` stock rows that `lib/next-lcp` moved
  (`TorusCoordinates.lean`); move them now.
- Then the stock files are empty or residue-only: say so per file, and retire the empty ones from the
  import chain (the consumers import `Hopf.LibShims` and their `Hopf/Proof/` twin).

## 3. Shims and module system

- De-shim pass, part 2: retire the `topSus` and `Hurewicz.DegreeTwo` aliases in `Hopf/LibShims.lean` and
  the `FirstHurewicz` alias block in `Hopf/LCP/CuspFilling.lean` by re-spelling their `Hopf/Proof/`
  consumers; give the remaining `*_mo1973_*` helpers in `Lib/` real names (`grep -rn '_mo1973_' Lib`).
- `import all` (owner: when convenient): 6 lines left — `RegularLevel.lean` (2; needs a Lib-side
  implicit-function datum with transparent `prodFun`), `SmoothFlow.lean` and `MorseLemma.lean` (mechanical
  switch to `Diffeomorph.toPartialDiffeomorphUniv` from `Lib/Geometry/Manifold/LocalDiffeomorph.lean`;
  MorseLemma is the root of the chain, full rebuild), `Morse/Cubic.lean`, `Morse/CubicFlow.lean` (inherited
  from the old Cancellation file). `Transversality/Basic.lean` can redirect its `toPartialDiffeomorph'`,
  `diffeomorph'` to the `LocalDiffeomorph.lean` versions (one line each).
- The 13 non-`module` Lib files created this round (and the 46 older ones) block `module` importers;
  conversion pass when the moves are done.

## 4. Records

- `Lib/reports/E1.md`, section "Layout split done": replace "still running at 8847/8858" by the final
  green line (8858 jobs). `Lib/reports/I.md` and `NEXT_STEPS.md` history still mention the old name
  `sum_range_shift_of_endpoints_mo1973_27356` (now `_eq`); fine as history.
- `Lib/reports/proof-split/FREED.md` header: the 40 `PeriodTorusHigherHomology` rows were under
  `Hopf/Proof/LCP/Specialization.lean`, not CuspFilling; the table was right.

## 5. Lanes and generalisations (after the above)

J-B/J-C/J-D/J-E certification per `Lib/docs/J.md`, then the product at `(1, n)`; E2 refactor at
`2k+1 ≤ n` per `E2.md`; B: the van Kampen extraction; the 300 demoted rows of `DEMOTED.md`
(after the correction): generalisation, not moves; last.

## Rules

`ps` before `lake build`; never `lake update`/`cache get`/`clean`; never push; Lake, not direct `lean`;
never kill a process by command-line pattern (use `/proc/<pid>/cwd`); reviewer ≠ author (a fresh-context
subagent is a reviewer); probes and evidence in the tree, no `/tmp`, `~`, `/home` citations; a lane report
says "landed" only for declarations that exist in `Lib/` at the head it names; nothing is "COMPLETE"
while its probe theorem is still under `Hopf/`; the Comparator stays deferred until publication.
