# Next steps — GLM seat (after integration review 4, 2026-09-14)

Layout note: `Hopf/<path>.lean` holds only the stock still to be moved into `Lib/`; proof-specific
declarations are under `Hopf/Proof/<path>.lean` (same names, same namespaces). The
`Mathoverflow1973` wrapper is gone from the tree since your `686b598e`; only the final theorem
`Mathoverflow1973.mathoverflow_1973` keeps the namespace, because `comparator/config.json` and
`Challenge.lean` name it so (restored by the integration). The census counts only outside
`Hopf/Proof/` (baseline 1648, now 1586). Receipts of the split: `Lib/reports/proof-split/`; the
demoted list was corrected there (`FREED.md`: 175 of the 475 rows are pure moves; 73 of them
are `MappingTorusHomology` rows in your lane).

Branch: `lib/textbook-extraction`, head = the commit the owner names when handing you the branch
(`git log -1`). Your `lib/A-10-layout` is in: Wang closure (50 rows, of which 23 now live in the
Muse seat's `CirclePaths.lean`, see the integration note at the end of `Lib/reports/I.md`), the
wrapper removal with `Lattice -> PeriodLattice`, the `import all` revert with its reason, the E1
scoping note, H and CrossProduct docstrings, the B status. Review: `Lib/reviews/INTEGRATION-4.md`
§4 "GLM seat". Start every new branch from this head. Commit identity: the seat's own (`glm`).

## In this order, branches `lib/A-<n>-<slug>` off the head above

1. **Record fixes** (one commit, docs only): (a) `Lib/reports/I.md` — the "Tooling note" cites
   `/tmp/wang_extract.py` and `/tmp/wang_gen.py`; bring both scripts in under
   `Lib/docs/logs/glm/` and cite those paths, or delete the two sentences; (b) the same file says
   the six auto-named helpers were "de-privatized" — they were not (see the integration note);
   correct the sentence; (c) `Lib/README.md:187` and `Lib/EXTRACTION_PLAN.md:11,148` still say every
   file is wrapped in `namespace Mathoverflow1973`; update.
2. **De-shim pass, part 1** (one commit, full chain green): in `Hopf/LibShims.lean` the block
   `namespace HandleCoreAttachment / export ... / end` became a root-level
   `export HandleCoreAttachment (core coreSpace coreInclusion)` in `686b598e`, which creates the root
   names `core`, `coreSpace`, `coreInclusion`; delete the line (nothing under `Hopf/` uses the bare
   names) or restore the scope. Then retire the `topSus` and `Hurewicz.DegreeTwo` aliases by
   re-spelling their `Hopf/Proof/` consumers, if the full chain stays green; say in the commit which
   aliases remain and why.
3. **Lane I, continued.** `Lib/reports/proof-split/FREED.md` lists 73 `MappingTorusHomology`
   declarations under `Hopf/Proof/LCP/IntegralHomology.lean` and neighbours that are pure moves
   (they were demoted by a spurious edge). Move them into `Lib/Topology/MappingTorus/Wang.lean` (or
   a second Wang file if it passes 3,000 lines) in dependency order, receipts as before, one green
   unit per commit; the FREE/CHARGED rule still decides per row. Give
   `MappingTorusHomology.Covering.sum_range_shift_of_endpoints_mo1973_27356` a real name in the same
   pass (hazard §7 of `I.md`).
4. **Layout, E1** (after item 3): your scoping note says the family cut of
   `ConnectionCancellation.lean`/`Cancellation.lean` is cyclic and a per-declaration DAG placement
   is needed. Do it with the mover machinery from item 1(a), in-tree: four modules `Cubic`,
   `CubicFlow`, `Connection`, `Cancellation`, statements unchanged, one commit per module, the
   edge counts and the placement table in `E1.md`.
5. **`import all`** stays as you left it (owner: clean up when convenient); the per-file proof
   restructuring you scoped is not urgent. Do not add new `import all` lines.
6. **Lane H** per `H.md`: the 115 `RiemannMapping` declarations are under `Hopf/Proof/` and still
   listed in `DEMOTED.md` after the correction (they bind to `SpecialPeriods.Triangle` through real
   edges); generalisation work, last.

Rules unchanged: `ps` before `lake build`; never `lake update`/`cache get`; never push; every
report cites only what is in the tree (no `/tmp`, no `~`); nothing is "COMPLETE" while its probe
theorem is still under `Hopf/`; never rewrite another seat's ledger, review or draft; do not
touch `Hopf/Proof/Final.lean`'s namespace or `Solution.lean`'s probe.
