# Next steps (after integration review 4, 2026-09-14)

Owner decision 2026-09-14: the remainder is done by Claude agents; no seat assignment for now. This
file replaces `NEXT-STEPS-{GLM,KIMI,MUSE}.md` (their last versions are in the history at `37996bc3`).

Head: `lib/textbook-extraction`, the commit the owner names (`git log -1`). Review of the last
round: `Lib/reviews/INTEGRATION-4.md`. Layout: `Hopf/<path>.lean` holds only the stock still to be
moved into `Lib/`; proof-specific declarations are under `Hopf/Proof/<path>.lean` (same names and
namespaces); the `Mathoverflow1973` wrapper is gone except around the final theorem
(`comparator/config.json` names `Mathoverflow1973.mathoverflow_1973`). The census counts only outside
`Hopf/Proof/` (baseline 1648, now 1586). `Lib/reports/proof-split/FREED.md`: 175 of the 475 demoted
rows are pure moves (spurious `_proof_n` edges); 62 are in `Lib/` already, 113 remain under
`Hopf/Proof/`. `AGENTS.md` stays as it is (owner, 2026-09-14).

## Record fixes (docs only, one commit each)

1. `Lib/reports/I.md`: the tooling note cites `/tmp/wang_extract.py`, `/tmp/wang_gen.py` — bring
   the scripts in under `Lib/docs/logs/glm/` or drop the sentences; the "de-privatized" sentence is
   false (integration note at the end of the file says what is true).
2. `Lib/README.md:187`, `Lib/EXTRACTION_PLAN.md:11,148` still describe every file as wrapped in
   `namespace Mathoverflow1973`.
3. `Lib/docs/C19-LEFTOVERS.md` and the C19 checkpoint in `Lib/reports/C.md`: name the two retargets
   (`Suspension.topSus.* -> Suspension.*` in `suspensionConeCover`;
   `HigherHurewicz.hurewiczLinearEquiv -> Hurewicz.hurewiczLinearEquiv` in the six wrappers); C20
   documented 35 private helpers, not 34; `Lib/docs/C-STAGE2-REVIEW.md:5` cites `~/s6-notes/review/C.md`
   (in-tree as `Lib/docs/C.md`).
4. `Lib/reports/RECEIPTS.md`: the S-path bullet must say 62 of the 88 rows came from `Hopf/Proof/`
   (`FREED.md`), carry `6211eadc` and its job count; the section header "head `84d9450`" is stale;
   `J.md` was edited after its Axis-5 stamp at `90cd3d9`. `Lib/docs/E2-fresh2-subagent-review.md`:
   the path rewrite produced `git -C the repository root rev-parse HEAD`; restore the command with the
   path elided in brackets.

## Moves (full chain green per commit, receipts as in `Lib/reports/proof-split/` and `integration-4/`)

5. **Freed rows, 113** (`FREED.md`): 73 `MappingTorusHomology` rows under
   `Hopf/Proof/LCP/IntegralHomology.lean` and neighbours into `Lib/Topology/MappingTorus/Wang.lean`
   (or a second Wang file past 3,000 lines); 40 `PeriodTorusHigherHomology` rows under
   `Hopf/Proof/LCP/CuspFilling.lean` into `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean` or
   the module their subject names. Straight from `Hopf/Proof/` to `Lib/`, statements verbatim modulo
   disclosed retargets, dependency order, `envdiff` before/after. Give
   `MappingTorusHomology.Covering.sum_range_shift_of_endpoints_mo1973_27356` a real name in the pass.
6. **Seven CHARGED Hurewicz leftovers** (`SixSphereCube` data, pinned `Sphere.piN_subsingleton`) sit in
   the stock file `Hopf/Hurewicz.lean`; they are proof-specific and belong in
   `Hopf/Proof/Hurewicz.lean` (which imports `Hopf.Hurewicz`). Then say what `Hopf/Hurewicz.lean` still holds.
7. **De-shim pass**: in `Hopf/LibShims.lean` the root-level
   `export HandleCoreAttachment (core coreSpace coreInclusion)` (from `686b598e`) creates three root
   names; delete it (nothing uses the bare names) or restore the scope. Retire the `topSus` and
   `Hurewicz.DegreeTwo` aliases by re-spelling their `Hopf/Proof/` consumers if the chain stays green;
   record which aliases remain and why.
8. **Lane I** remainder per `I.md`; **J**: J-B/J-C/J-D/J-E certification per `J.md`, then the product
   at `(1, n)`; **E2** refactor at `2k+1 ≤ n` per `E2.md`; **B**: the van Kampen extraction itself.
9. **E1 layout**: `ConnectionCancellation.lean`/`Cancellation.lean` split needs a per-declaration
   DAG placement (`E1.md`, family cut is cyclic); four modules `Cubic`, `CubicFlow`, `Connection`,
   `Cancellation`, statements unchanged, edge counts and placement table in `E1.md`.
10. **`import all`** (owner: clean up when convenient): 9 lines in 8 files, each needs proof
    restructuring against the public `LocalDiffeomorph` API; not urgent; add none.
11. **Demoted rows, 300** (`DEMOTED.md` after the correction; `RiemannMapping` 124 and the rest):
    generalisation, not moves; last.

## Rules

`ps` before `lake build`; never `lake update`/`cache get`; never push; Lake, not direct `lean`;
reviewer ≠ author (a fresh-context subagent is a reviewer); probes and evidence in the tree, no
`/tmp`, `~`, `/home` citations; a lane report says "landed" only for declarations that exist in
`Lib/` at the head it names; nothing is "COMPLETE" while its probe theorem is still under `Hopf/`;
the Comparator stays deferred until publication.
