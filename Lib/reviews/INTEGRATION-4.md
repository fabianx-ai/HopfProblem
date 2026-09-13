# Integration review 4 — `lib/A-10-layout`, `lib/C-17…C-20`, `lib/textbook-extraction-muse-i3`

Coordinator: Claude Fable 5.1 (this seat). Date: 2026-09-13/14. Base: `27f8e7f5` (the hand-off
head after integration 3 and the proof split). All six branches fork from it. Reviewers: three
fresh-context subagents, one per seat (owner rule of 2026-09-13: zero-context subagents count as
independent reviewers); their reports are folded into §4 and the seat files.

## 1. What was integrated

Merged in this order onto `27f8e7f5`, each as a merge commit:

1. `lib/C-17-citations` (Kimi seat, run by SWE-2; 1 commit): citations of the C lane rewritten
   to repository-relative paths, 74 artifacts imported under `Lib/docs/logs/C/`.
2. `lib/C-18-owner-gates` (1 commit): the two owner dispositions of `INTEGRATION-3.md` §5
   (Stage-2 order exception accepted; Comparator deferred) recorded in `Lib/reports/C.md`.
3. `lib/C-20-docstrings`, which contains `lib/C-19-hurewicz-leftovers` (10 commits): C-19 moves
   the nine FREE leftovers of `Hopf/Hurewicz.lean` into `Lib/` (`SphereHomology.twoOpenCover_*` to
   `FundamentalGroup/VanKampen.lean`, `suspensionConeCover` to the new
   `SingularHomology/SuspensionCover.lean`, the six `Third/Fourth/FifthHurewicz` wrappers to
   `Hurewicz/CubeSphere.lean`) and keeps seven CHARGED ones, ledger `Lib/docs/C19-LEFTOVERS.md`;
   C-20 documents 35 private helpers in eight Hurewicz files and puts the Straightening module
   docstring above the header, comments only.
4. `lib/textbook-extraction-muse-i3` (Muse seat, run by SWE-2; 15 commits): off-tree citations
   repointed with an editorial line per file, module docstrings for `Morse/MinimalSystem.lean`
   and `Whitney/BigonModel.lean`, `import all` removed from `Transversality/Basic.lean` and
   `Immersion/Relative.lean` by two transparent variants (`Diffeomorph.toPartialDiffeomorph'`,
   `IsLocalDiffeomorph.diffeomorph'`), E2/G/J Axis-5 reviews by fresh subagents, and the S-path
   landing: 88 declarations from `Hopf/LCP/CuspFilling.lean` (26) and
   `Hopf/Proof/LCP/CuspFilling.lean` (62) into the new
   `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean`.
5. `lib/A-10-layout` (GLM seat, run by GLM; 16 commits): lane I Wang closure, 50 rows into the
   new `Lib/Topology/MappingTorus/Wang.lean` with four consumers rerouted; the `Mathoverflow1973`
   wrapper removed tree-wide (96 Lib files, 26 stock files, 16 proof files, LibShims), with the
   forced rename `Lattice -> PeriodLattice` in `Hopf/Proof/` (Mathlib owns root `Lattice`); seven
   `import all` drops attempted and reverted with the reason (the files prove through
   `LocalDiffeomorph` internals); E1 layout scoping (the family cut is cyclic); H docstrings
   complete (0 of 484 missing), 115 CrossProduct docstrings; B status paragraph.

Merge commits: `f60b3ceb`, `3e43b123`, `57858633`, `010c3d00`, `80cb7a5e`; then the namespace fix
`47940380` (decision 2) and the documentation commit that contains this file. The hand-off head is
the commit the owner names.

Conflicts: one in `Lib/reports/C.md` (C-18's attribution sentence is the true one and is kept;
C-19/C-20's stale one dropped); six in the A-10 merge, each a lane move crossed with the wrapper
strip, resolved by keeping both intents (`Hopf/Hurewicz.lean`, `VanKampen.lean`,
`CubeSphere.lean`, `Transversality/Basic.lean`, `Straightening.lean`, `Hopf/LCP/CuspFilling.lean`).
The two Lib files created on seat branches (`CirclePaths.lean`, `SuspensionCover.lean`) still
carried the wrapper and were stripped to match the tree.

## 2. Integration decisions

1. **Double landing.** 23 circle-path declarations landed twice: in GLM's `Wang.lean` and in
   Muse's `CirclePaths.lean` (the seven `CirclePaths.circleTranslation*`/`positiveLoop` rows,
   `positiveCircleCross`, the two `crossProductEdge_*`, the seven `twoChain*`,
   `connectingHomomorphism_twoChain`, the five `biprod*_mo1973_*` helpers). Both copies are the
   base text modulo the same disclosed retargets; GLM's keeps the five helpers `private` and had
   turned `biprodElement_desc_mo1973_12803` into a `def`, Muse's widens the five to public (their
   exposed consumers need it) and keeps every kind. Kept in `CirclePaths.lean`, where the other 65
   declarations depend on them; removed from `Wang.lean`, which now imports `CirclePaths` and keeps
   its 27 mapping-torus rows. Recorded in `Lib/reports/I.md` (integration note).
2. **The final theorem keeps its namespace.** The wrapper strip had turned
   `Mathoverflow1973.mathoverflow_1973` into root `mathoverflow_1973` and re-spelt the
   `Solution.lean` probe. `comparator/config.json` and `Challenge.lean` name
   `Mathoverflow1973.mathoverflow_1973`; the integration restores `namespace Mathoverflow1973`
   around the final theorem only (`Hopf/Proof/Final.lean`) and the probe (commit `47940380`).
3. **The demoted list was wrong by 175 rows.** The Muse review found 62 of the 88 S-path rows in
   `DEMOTED.md`, moved without generalisation and compiling in `Lib/` without any `Hopf` import.
   Cause: the split planner counted a use of `Y._proof_n` as a use of `Y`; Lean shares identical
   abstracted proofs within a module, so the edge is spurious. Recomputed from the same table with
   those edges dropped: 300 demoted, 175 freed (`Lib/reports/proof-split/FREED.md`; `DEMOTED.md`
   annotated; `scripts/proof_split_plan.py --skip-proof-aux-edges`; the tool's `dump` spec now
   says `uses` is raw). The freed rows stay where they are (62 in `Lib/`, 113 under `Hopf/Proof/`,
   not census-counted) and are assigned: 73 `MappingTorusHomology` to GLM (lane I), 40
   `PeriodTorusHigherHomology` to Muse (J).

## 3. Checks on the merged head

| Check | Result |
|---|---|
| `sorry` / `axiom` in changed `.lean` files | 0 (the `sorry` in the upstream `Challenge.lean:42` is the challenge statement, unchanged) |
| `git diff --check` | clean for sources; the archived `.log` files under `Lib/docs/logs/C/` carry trailing whitespace from verbatim Lean output |
| `Mathoverflow1973` in `.lean` files under `Lib/`, `Hopf/` | 0 besides the prose line in `Hopf/LibShims.lean:7`; `Challenge.lean` (upstream) and the final theorem keep it |
| `Lib.lean` | 110 modules imported; 111 files (`AxiomAudit.lean` is run, not imported); three new modules `SuspensionCover`, `Wang`, `CirclePaths` |
| Declarations defined in two files (top-level names, `Lib/` + `Hopf/`) | 0 after decision 1 (23 before) |
| Statement scan over `Hopf/` (13,185 declarations, `LibShims.lean` excluded; text normalised by the wrapper strip and `PeriodLattice -> Lattice`) | 0 new, 0 changed statements; 2 "changed proofs" are block-boundary artefacts of deleted neighbours (`coordinatePeriodLoop_apply`, `fibreTorusCircleHomeomorph`, `fullHomology_subsingleton_of_four_lt`: the blocks absorb a following `end`/`attribute … in` line) |
| Declarations deleted from `Hopf/` | 124 (Proof/LCP/CuspFilling 62, LCP/CuspFilling 26, SingularHomology 15, LCP/IntegralHomology 10, Hurewicz 9, LCP/Specialization 2) |
| Deleted declarations present in `Lib/` under the same full name | 124 of 124 |
| Statement of the moved row vs its base text | 52 identical; 69 identical modulo the disclosed retargets (`FirstHurewicz. -> SingularChains.`, `PeriodTorusHigherHomology.CircleTopology. -> CircleTopology.`, `private` dropped); 3 differ by a qualifier only (`suspensionConeCover`: `Suspension.topSus -> Suspension`, owner-confirmed; `PassageHomology.{puncturedCylinderHomeomorph, radialCylinderDiffeomorph}`: `PassageHomology.` qualification) |
| Stock census (`scripts/lib_stock_census.py --check`) | 1648 -> 1586, prefix list unchanged, ratchet PASS |
| Full chain `lake build Lib` then `Solution S6Shortcuts S6 Challenge` (worktree `lib/integration`) | green at `80cb7a5e`: 8,817 + 8,856 jobs, `lib-exit 0`, `consumers-exit 0`, 23:46–00:00 CEST (`Lib/reports/integration-4/build.log`); green again at `47940380` after decision 2, `Solution.lean` probe `Mathoverflow1973.mathoverflow_1973` on the standard three (`build2.log`) |
| `Lib/AxiomAudit.lean` | 71 probes, 71 results, every axiom set within {`propext`, `Classical.choice`, `Quot.sound`} (`Lib/reports/integration-4/axioms.log`); `Solution.lean` probe: the standard three |
| Environment diff (`lean-agent-ide dump` at `27f8e7f5` vs the head, under the rename map `X -> Mathoverflow1973.X`, `PeriodLattice -> Lattice`; `envdiff`) | PASS at `47940380`: 31,422 -> 31,434 constants (base coverage plus the three new modules); 0 source declarations lost or added beyond the two accepted new Lib lemmas (`Diffeomorph.toPartialDiffeomorph'`, `IsLocalDiffeomorph.diffeomorph'`); 3 source names with a changed type hash: `suspensionConeCover` accepted (`Suspension.topSus` unfolded to `Suspension`, the confirmed rename), `CirclePaths.{quarter,threeQuarter}Intersection_component` differ only by which shared `_proof_n` auxiliary the type names; 121 one-to-one module moves (Hurewicz 8, LCP/CuspFilling 26, Proof/LCP/CuspFilling 60, LCP/IntegralHomology 10, LCP/Specialization 2, SingularHomology 15), 0 ambiguous; auxiliary constants: 40 lost, 52 added, 31 changed, 69 moved (not judged). Receipt `Lib/reports/integration-4/envdiff.json`; the rename map is regenerated by `int4_rename_map.py` from the two tables (30,617 entries; the 170 unmapped base names are notation artefacts whose generated names embed the old namespace, `rename-unmapped.txt`) |
| Comparator | not run (owner-deferred; `landrun` not installed) |
| Lean `module` system | 9 `import all` lines in 8 files (GLM-owned; the seven drops were reverted with reason; Muse removed two) |

Scripts and logs: `Lib/reports/integration-4/` (`int4_stmt_compare.py`, `int4_units.py`,
`int4_rename_map.py`, `int4_redemote.py`, `decl_blocks.py`, the build and dump scripts, the build,
axiom and rename-map logs, `envdiff.json`). The dump tables (18 MB each) stay in the coordinator's
session directory. The tool: `~/lean-agent-ide` (`dump --rename`, `ace56a8`; `uses` is raw,
`3652824`; `envdiff` proof-naming rule and `--accept`, `e7fe778`, `20a16cc`).

## 4. Findings per seat

### GLM seat (`lib/A-10-layout`)

Reviewer verdict NO-GO as-is for four small items; all four are handled or assigned:

1. **Off-tree citations.** `Lib/reports/I.md` cites `/tmp/wang_extract.py` and `/tmp/wang_gen.py`
   as tooling; the new root `AGENTS.md` reads "First read ~/collaboration-protocol.md". The I.md
   sentence is flagged in the integration note and is GLM item 1; `AGENTS.md` is an owner item (§5).
2. **Undisclosed kind change.** `biprodElement_desc_mo1973_12803` was `private theorem` at base and
   `private def` in `Wang.lean`. Moot after decision 1 (`CirclePaths.lean` keeps `theorem`).
3. **False sentence in I.md.** "de-privatized to compile outside their source file" — all six
   helpers were still `private` at the tip. Corrected in the integration note; GLM item 1.
4. **LibShims scope change.** `namespace HandleCoreAttachment / export … / end` became a root
   `export HandleCoreAttachment (core coreSpace coreInclusion)`, creating three root names;
   the commit message says inner scopes were kept. Nothing uses the bare names; GLM item 2.
5. Verified by the reviewer: the strip is mechanical (1,007 hunks classified: 235 wrapper lines,
   77 qualifier removals, 690 qualifier/`Lattice` pairs, 5 disclosed others); the `PeriodLattice`
   rename is consistent (0 unmatched lines; the only bare `Lattice` left is the separate
   `CuspHoneycombTiling.Lattice`); lane I accounting is exact (50 = 23 + 10 + 2 + 15; 43 in the
   JSON, 7 closure rows); the `import all` revert is clean; H 0/484 and CrossProduct 0/218 without
   docstring; cited hashes exist. Not reproducible in-tree: the census figures, the E1 edge counts,
   the job counts (no logs). Stale docs: `Lib/README.md:187`, `Lib/EXTRACTION_PLAN.md:11,148`.
6. **Final theorem name** (found by the coordinator, decision 2): the strip renamed the theorem the
   Comparator config names.
7. Retargets beyond the disclosed list are proof-body qualifications only
   (`connectingHomomorphism_cycleClass`, `biprodElement*`, `PassageHomology.*`).

### Kimi seat (`lib/C-17-citations`, `C-18`, `C-19`, `C-20`)

Reviewer verdict GO; three record items, all Kimi item 1:

1. C-19's two retargets (`Suspension.topSus.* -> Suspension.*` in `suspensionConeCover`;
   `HigherHurewicz.hurewiczLinearEquiv -> Hurewicz.hurewiczLinearEquiv` in the six wrappers) are
   real shim unwinds to the same constants, but the ledger says "unchanged apart from placement".
2. C-20 documented 35 private helpers, the report says 34. All nine commits are token-identical
   outside comments (verified by stripping comments before/after).
3. `Lib/docs/C-STAGE2-REVIEW.md:5` still cites `~/s6-notes/review/C.md` (in-tree as `Lib/docs/C.md`).
4. Verified: all nine moved declarations at the claimed destinations; seven CHARGED remain; the
   ledger classifies 9 + 7 = 16 (the seat file's "23" was pre-merge); 74 artifacts present, all
   cited, `.lean` sources as `.lean.txt`; every cited hash exists; the job counts match the logs;
   attribution: all commits `kimi`, so C-18's sentence is true and the older one was dropped in
   the merge.
5. Coordinator: the seven CHARGED leftovers are proof-specific and sit in a stock file; under the
   layout rule they belong in `Hopf/Proof/Hurewicz.lean` (Kimi item 2).

### Muse seat (`lib/textbook-extraction-muse-i3`)

Reviewer verdict GO for the code; two record items, both Muse item 1:

1. **62 of the 88 S-path rows were `DEMOTED.md` rows**, moved without generalisation and without
   saying so; `DEMOTED.md` was left stale. The move is nevertheless sound — the rows compile in
   `Lib/` with no `Hopf` import — and the finding exposed the planner defect of decision 3. The
   receipts must state the provenance.
2. **Corrupted quoted command** in `Lib/docs/E2-fresh2-subagent-review.md` from the mechanical
   path rewrite (`git -C the repository root rev-parse HEAD`), under an editorial note saying
   nothing else changed.
3. Verified: the 88 rows are verbatim modulo the disclosed retargets (one proof body drops a
   `PeriodTorusHigherHomology.` qualifier on two export aliases); kinds, `@[simp]`, binders,
   docstrings unchanged; the two transparent variants are new, nothing deleted, no existing
   statement changed; every cited hash resolves; census 1648 -> 1622 reproduced; ledger
   coordinates point at declaration lines (74 E2, 59 G, 204 J). Stale: the RECEIPTS section
   header `84d9450` predates the S-path landing; `J.md` was edited after its Axis-5 stamp.
   78 of the 128 copied batch-3 evidence files are empty (pre-existing).

## 5. Verdict and owner items

**GO.** The merged head builds, every probe is on the standard axioms, no statement under `Hopf/`
changed, every declaration that left `Hopf/` is in `Lib/` and the environment diff is a bijection
under the rename map. The seat findings are record items and are in `NEXT_STEPS.md`; the three decisions of §2 are the coordinator's and are recorded
here and in the affected reports.

Owner items:

1. **`AGENTS.md`** (added by GLM in `686b598e`) reads "First read ~/collaboration-protocol.md", an
   off-tree file on the owner's machine. Recommendation: point it at the in-tree
   `lean-protocol.md`, or drop the file. Decision (owner, 2026-09-14): keep as is.
2. **Freed rows** (decision 3): the 113 pure-move rows still under `Hopf/Proof/` are assigned to the
   seats as direct `Hopf/Proof/ -> Lib/` moves, not moved back into the stock files first (which would
   raise the census above its baseline for no gain). Decision (owner, 2026-09-14): the remainder is
   done by Claude agents, no seat assignment for now; the next steps of all lanes are in one file,
   `NEXT_STEPS.md`, which replaces the three seat files.
3. The Comparator stays deferred until publication (unchanged).
