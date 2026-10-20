# Integration review 6 — the `Lib/` work of `center-solution` (2026-09-20)

Coordinator: Claude Fable 5.1 (this seat); git replay and build by fresh subagents. Base: `22d23761`
(hand-off head after integration 5), which is an ancestor of `center-solution` (`bcf711d6`, the W4–W1
development by the owner's Astra seat). Question: bring the `Lib/` additions of that branch onto
`lib/textbook-extraction` as history, not as one commit.

## 1. What merged

`git rev-list lib/textbook-extraction..center-solution -- Lib Lib.lean` lists 359 commits: 139 touch only
`Lib/`, 219 also touch `PROVENANCE.md`, `LERAY_CONVERGENCE_MAP.md` or (12 of them) a `Hopf/` file, and
one is the merge `b1179031` of the W4–W1 lineage onto `22d23761`
(`Lib/reports/integration-6/commit-classification.txt`).

Every non-merge commit was replayed as its own commit on `lib/integration`
(`Lib/reports/integration-6/replay.py`, log `replay.log`): the commit's `Lib/` + `Lib.lean` diff applied
with `git apply -3 --index`, original author, author and committer dates and message kept, followed by
`(cherry picked from commit <sha>)` and, for the 219 mixed commits, the line
`Lib paths only; the original commit also changed: <paths>`. Result: 358 replayed commits and one
alignment commit, head `3d7d29bc`; `git diff center-solution -- Lib Lib.lean` is empty, i.e. `Lib/` and
`Lib.lean` are byte-identical to `center-solution`'s.

Content: 312 new modules (`Topology/Sheaves` 124, `Algebra/Homology` 60, `CategoryTheory/Sites` 24,
`AlgebraicTopology/SingularSmallChains` 23, `CategoryTheory/Abelian` 10, `Topology/Homotopy` 9, …), every
one importing only `Lib` and `Mathlib`, 308 in `module` style; `Lib.lean` gains 300 imports;
`Lib/AxiomAudit.lean` gains 3,334 probes; `LocalContributions.lean` gains the signed Mayer–Vietoris
coordinate theorems; `MappingTorus/Basic.lean` gets a module header. Lib file count 134 → 446.

Decisions taken by the coordinator:

| point | decision |
|---|---|
| Conflicts in the two append-only files `Lib.lean` and `Lib/AxiomAudit.lean` (the W4–W1 lineage branched off before `22d23761`, so their context differs) | resolved mechanically by the append rule: HEAD version plus the lines the patch adds, appended in patch order, duplicates skipped; used in 158 commits for `Lib.lean`, 5 for `AxiomAudit.lean` |
| The one added/added collision, `Lib/Topology/MappingTorus/Basic.lean` at `380ddd11` (the W4–W1 lineage created a 161-line extraction of that path; `22d23761` already had the 678-line Hatcher 2.48 file) | the `22d23761` file kept inside the replayed commit, as the merge `b1179031` itself had decided; noted in the commit message |
| The merge commit's own resolution (import and probe order, the `Basic.lean` module header, the `VanKampen.*` → `VanKampen.Cocone.*` renames and the `Mathoverflow1973` wrapper drops in 15 W4–W1 Lib files) | one final alignment commit `3d7d29bc` listing every file and change, so that the tree equals `center-solution`'s |
| The non-Lib parts of the 219 mixed commits (`PROVENANCE.md`, `LERAY_CONVERGENCE_MAP.md`, 12 `Hopf/Proof` deletions of material that moved into `Lib`) | not taken; the 12 `Hopf/Proof` deletions are the natural next move (§4) |

## 2. Checks on the merged head `3d7d29bc`

Receipts: `Lib/reports/integration-6/` (build logs transcribed, `times.log`, `census-3d7d29bc.log`).

| check | result |
|---|---|
| `lake build Lib` | green, 9,149 jobs, 94 s (the worktree cache already held most new modules from an interrupted earlier build) |
| `lake build Solution S6Shortcuts S6 Challenge` | green, 9,188 jobs, 376 s; 26 `Hopf.*` modules recompiled |
| `lake build Lib.AxiomAudit` | green; 3,361 probes, all `propext` / `Classical.choice` / `Quot.sound` only; no `sorryAx` |
| `scripts/lib_stock_census.py --check` | 123 (unchanged; `Hopf/` untouched) |
| `git diff center-solution -- Lib Lib.lean` | empty |
| environment diff | not run: no `Hopf/` declaration changed and no `Lib` declaration was moved; the additions are new modules |

Finding, not fixed (would break byte-identity with `center-solution`): 13 `Lib` modules are not imported
by `Lib.lean`, so `lake build Lib` does not build them (`BasedDiskLifting`, `RelativeDiskLifting`,
`Hurewicz/SphereGenerator`, `Topology/Gluing/OverBase`, `Geometry/Manifold/LocalDiffeomorph`,
`VanKampen/{Basic,PathValue}`, four `Sites/Leray/FibreStalkEvaluation/*`,
`Sheaves/PrincipalCoverLocalSystem{,.Stalk}`); some are reached transitively, three only through
`AxiomAudit`. Listed in `NEXT_STEPS.md`.

## 3. Process notes

- A first attempt took the whole `Lib/` tree as one commit; the owner asked for history instead. The
  replay took one agent two runs (stop at the added/added collision, decision, resume) and about
  ten minutes; the build about eight.
- The replayed commits' messages are the owner's originals; the alignment commit is the only
  coordinator-authored change to `Lib/` content, and it reproduces the merge's own resolution.

## 4. What remains

The 12 `Hopf/Proof` deletions of the mixed commits (material now duplicated in `Lib`); the 13 imports
missing from `Lib.lean`; the textbook-adherence audit over all 446 files (`NEXT_STEPS.md` §1).
