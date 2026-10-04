# Next steps (after the four-tree split, integration 7c and the facade dissolution, 2026-10-04)

State: all 24 monoliths split behind facades (`Lib/reports/wave-1/MERGE.md`, `wave-2/MERGE.md`); both waves
reviewed by Fable reviewers (`Lib/reviews/REVIEW-WAVES.md`: nothing unsound) and the findings fixed
(§5 there); `center-solution` replayed per commit up to `d4db0d1a` (`Lib/reviews/INTEGRATION-7.md`,
`Lib/reports/integration-7/REPLAY-7b.md`). Integration 7c replayed `center-solution` up to `91485e80`
(`Lib/reports/integration-7/REPLAY-7c.md`, three clean cherry-picks). The 24 facades are dissolved (`Lib/reports/facades/RECEIPT.md`: 205 consumers
rerouted to the pieces from the dump's `uses`, facade docstrings kept as directory `README.md`s, envdiff 0/0/0; reviewed:
`Lib/reports/facades/RECEIPT.md` §8 correction — the merge `b25f3507` is the verified unit, 12 of the 24 per-facade
commits do not build on their own). The Shared/Center split was reviewed
(`/home/goblin/.claude/jobs/06995e68/tmp/review-center/REVIEW.md`, findings fixed in merge of `fix/center-review`;
corrections section in the center-proof receipt). Chain green (9,465 jobs), 3,881 probes within the three standard
axioms (Lib 3,785, Shared 53, Center 9, Unused 34; the Hopf DegreeSix declarations are probed nowhere), census 123.
Known for the rebase: 21 `W4W1` files and `W4-W1-Solution.lean` import `Hopf.Proof.*` on `center-solution`
(receipt R1 note); `W4W1/CenterChargedAssembly.lean` needs an identifier edit (`Int.` → `ThreefoldHomology.`).
**Layout (owner decision 2026-10-03, receipt `Lib/reports/center-proof/RECEIPT.md`): four trees.** `Lib/` =
generic textbook (imports Mathlib and `Lib` only); `Shared/Proof/` = used by both proofs (imports `Lib` only);
`Hopf/Proof/` = the old proof, finished and frozen, nothing new goes there (imports `Lib`, `Shared`);
`Center/Proof/` = the center construction only (imports `Lib`, `Shared`; the construction itself is `W4W1/` on
`center-solution`). `Hopf` and `Center` never import each other. Classification is by git history (introducing
commit, moving commit), usage as a cross-check; a declaration used by the old proof on either branch and by
`W4W1` is "both". The receipt's import map lists, per moved declaration, its module on `center-solution` and
its module here, so that `center-solution` can be rebased onto this branch with import-line edits only.
`Hopf/Proof/AxiomAudit.lean` is gone; the audits are `Lib.AxiomAudit`, `Shared.Proof.AxiomAudit`,
`Center.Proof.AxiomAudit`, `Unused`. Isolation greps (all must be empty): `Lib` imports no `Shared`/`Hopf`/`Center`;
`Shared` imports no `Hopf`/`Center`; `Hopf`, `S6` and the root files import no `Center`; `Center` imports no `Hopf`.
Open, in order:
(1) **`Unused/`** exists (owner decision 2026-10-02; `Unused/README.md`, receipt `Lib/reports/unused/cube3.md`):
only what the owner names moves there, verbatim. No dead-code sweeps over `Lib`: what is part of the textbook
is not dead code, and explanation outweighs tidiness (owner, 2026-10-02);
(2) **replays** continue from `91485e80` of `center-solution` (`Models.lean` is now 8,428 lines; the source
worktree had two untracked `G07AngularOrigin_*Check.lean` files when 7c finished). Rule: a replayed commit whose material is not generic goes to `Center/Proof`
(or `Shared/Proof` if the old proof uses it too), never to `Hopf/Proof`;
(3) **owner's word needed** (INTEGRATION-7 §Left): split `Hyperbolic/Models.lean` (7,870 lines) and
`CurveTransport.lean`, sweep their manuscript labels, add the comparison with Mathlib's `UpperHalfPlane`
metric — now, or after the source branch stops appending to those files (recommended: after; replays stay
clean cherry-picks);
(4) facades done; next: the "better homes" of both MERGE receipts, then the `native*`/`Native*`/`MorseCancellation.*`/
`FlowConstruction` rename wave; the misnamed groups of REVIEW-WAVES §2 finding 6;
(5) the owner decisions: chain-interface coefficients (new polymorphic `chains` beside the pinned one plus a
`u = 0` comparison, an addition), the pre-PR chain tower;
(6) carried over: the twins listed in both MERGE receipts; the 40 Jev two-letter disagreements and the
auditors' ten low-confidence calls; dup-hom items 4–6; dup-sheaf items 1–5; dfiles-c's `sheaf`/`unit` removal;
moved's `Matrix.Pivot`/`Module.Presentation`/`sheetSum` items; the ~17 unattributed pins; the tool requests of
REVIEW-WAVES §4 for `~/lean-agent-ide`.
Standing rules (REVIEW-7-8 §4, REVIEW-FIX §4, REVIEW-WAVES §4, `wave-2/RULES.md`): at most three work seats at
a time, merge, then the next three; Opus 5.5 for work seats, Fable for review seats; per-seat `PROGRESS.md`
and small green commits; integrations replay per commit with original authorship; "verbatim" is checked on
the lines a split did not move as well (`set_option`, `… in` prefixes, `open`); a changed type hash with
identical text is a finding; a textbook is cited for a proof step only when its proof has that step; counts
come from one stated unit and one command; consumer counts allow `public import`; per-branch `envdiff.json`
committed; a "Left" list carries a reproducing command per bullet; Lake 5.0.0 has no `-j`, use `taskset`.
`w4-w1-solution` / `W4W1` must reroute its imports per the import map in `Lib/reports/center-proof/RECEIPT.md`
when it meets this branch (`SphereTwo` is `Center.Proof.Topology.Sheaves.Cohomology.SphereTwo`).

The reviewer pass (`Lib/reviews/REVIEW-7-8.md`, twenty-one Fable reviewers) accepted all receipts with
findings and found nothing unsound; the fix round (§5 there, eleven Opus agents) closed the whole §3 list;
three Fable reviewers checked the fix round (`Lib/reviews/REVIEW-FIX.md`: nothing unsound, receipt and
coordinator-text errors only, all closed by `wave1/residue`).

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
