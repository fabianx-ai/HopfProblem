# Round 7 packet 05 — receipt

Worktree `/home/goblin/hopf-r7-p05`, branch `r7/packet-05`, base `9552305f`
(Lean v4.33.0, Mathlib v4.33.0).

The packet's four files are large Morse/Whitney/transversality files. The audit
facts record **0 universe pins and 0 fixed `Type` binders** in all four
(`Lib/reports/textbook-audit/jev/results2.jsonl`: `universe_zero_pins: 0`,
`binders_Type_fixed: 0`), which I confirmed by reading the statements. Work
items 3 (universe pins) and 4 (`: Type` binders) are therefore empty for this
packet; items 1 (citations) and 2 (docstrings) are the whole job. No statement
was changed anywhere.

## Per file

### `Lib/Geometry/Manifold/Whitney/BigonModel.lean` (482 l., 52 decls)

* **Citations**: none to replace. The module docstring was already complete and
  already cited Milnor, *Lectures on the h-cobordism theorem*, §6 (Thm 6.6); it
  contains no manuscript coordinate and no process narrative.
* **Docstrings**: 52 added (0 → 52 of 52). Model space and the two sheets; the
  parabolic bigon with closedness, compactness, star-convexity, the
  interior/frontier descriptions and the boundary cover; the arc parameter, the
  two corner charts, the reflection and edge-exchange symmetries; the smooth
  corner transition/scale/sign; the lower and upper strip charts with their
  straightening and corner-matching identities.
* **Universe pins**: 0 present. **`: Type` binders**: 0 present.
* Left: nothing.

### `Lib/Geometry/Manifold/Whitney/AnnularExtension.lean` (795 l., 60 decls)

* **Citations**: 1 module docstring replaced. The old text was a move receipt
  ("Moved verbatim from the project stock file `Hopf/SingularHomology.lean`
  (integration 4, `Lib/reports/integration-4/singhom-moves.md`)", a list of five
  "families", "the file order is the dependency order"). Replaced by a
  mathematical summary with `## Main results` and the textbook references
  Milnor, h-cobordism theorem §§5–6, and Hatcher, *Algebraic Topology*, §4.1
  (with Milnor, *Topology from the differentiable viewpoint*, §7) for
  `π_m(Sⁿ) = 0`, `m < n`. All project-process sentences deleted.
* **Docstrings**: 60 added (0 → 60 of 60).
* **Universe pins**: 0 present. **`: Type` binders**: 0 present.
* Left: the audit's structural suggestions (splitting `SphereCone` +
  `AnnularExtension` out to `Topology/`, the three sphere-nullhomotopy theorems
  to `AlgebraicTopology/`, making `TubularBigon`'s codimension explicit) are file
  splits and statement changes, outside the four work items.

### `Lib/Geometry/Manifold/Whitney/CleanStrips.lean` (2533 l., 140 decls)

* **Citations**: 1 module docstring replaced. The old text was the same move
  receipt plus a list of eleven "families" and no `## Main results`. Replaced by
  a mathematical summary with `## Main results` and the references Milnor,
  h-cobordism theorem §§5–6, and Guillemin–Pollack, *Differential Topology*,
  §§1.5 and 2.3 (transverse crossing charts; finiteness of transverse
  intersections).
* **Docstrings**: 140 added (0 → 140 of 140).
* **Universe pins**: 0 present. **`: Type` binders**: 0 present.
* Left: the audit's structural suggestions (extracting `exists_clean_crossingChart`
  and `finite_transverse_intersections` into `Transversality/Crossing.lean`,
  moving the `MorseSurgeryData.beltIntersection*` block to `Morse/`, renaming the
  `native`/`Native` identifiers) are moves and renames, outside the four work
  items; a rename would also show as a lost/added pair in the envdiff.

### `Lib/Geometry/Manifold/Transversality/Basic.lean` (2904 l., 135 decls)

* **Citations**: 1 module docstring replaced. It was stale rather than a
  manuscript citation: its `## Outline` promised `NativeTransversality.Patch`,
  `WeightedPerturbation`, the `GeneralPosition` avoidance lemmas and a `NoExotic`
  dimension cluster, none of which is declared here. Rewritten around what the
  file proves, naming the transversality relation (Guillemin–Pollack §2.3), the
  equidimensional Sard theorem, the parametric transversality theorem (Hirsch
  Ch. 3), supported germ realisation, the radial maps and disc shrinking, and the
  disc theorem `DiskShrinking.exists_embedded_disk_isotopy_of_same_center`
  (Hirsch Thm 8.3.1; Palais) — the file's main result, which the old docstring
  did not name. References kept as `[hirsch76]`, `[gp74]`.
* **Docstrings**: 133 added (2 → 135 of 135); the two pre-existing ones
  (`Diffeomorph.toPartialDiffeomorph'`, `IsLocalDiffeomorph.diffeomorph'`) are
  unchanged.
* **Universe pins**: 0 present. **`: Type` binders**: 0 present.
* Left: the audit's structural suggestions (moving the
  `MorseHandle`/`SignedMorseChart`/`MorseSurgeryData` block to `Morse/`, renaming
  `NativeTransversality.At` → `IsTransverseAt` and dropping "native" everywhere)
  are moves and renames, outside the four work items.

## Totals

| item | count |
|---|---|
| module docstrings rewritten (move receipt / stale outline removed, textbook reference put in) | 3 |
| declaration docstrings added | 385 (52 + 60 + 140 + 133) |
| declarations documented / total | 387 / 387 |
| universe pins generalised | 0 (0 present in the packet) |
| `: Type` binders widened | 0 (0 present in the packet) |
| statements changed | 0 |
| items left with an obstacle | 0 |

## Builds

```
=== lake build Lib
✔ [9148/9150] Built Lib.Geometry.Manifold.Morse.SurgeryCollapse (86s)
✔ [9149/9150] Built Lib (4.0s)
Build completed successfully (9150 jobs).
=== lake build Solution S6Shortcuts S6 Challenge
ℹ [9188/9189] Built Solution (3.4s)
info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9189 jobs).
=== lake build Lib.AxiomAudit
Build completed successfully (9150 jobs).
```

Axiom audit, all 1854 reported declarations:

```
   1723 depends on axioms: [propext, Classical.choice, Quot.sound]
      1 depends on axioms: [propext, Classical.choice]
    115 depends on axioms: [propext, Quot.sound]
     15 depends on axioms: [propext]
```

Only `propext`, `Classical.choice`, `Quot.sound`.

Per-file builds (each file committed only after its own module went green):

```
✔ Built Lib.Geometry.Manifold.Whitney.BigonModel (8.3s)
✔ Built Lib.Geometry.Manifold.Whitney.AnnularExtension (14s)
✔ Built Lib.Geometry.Manifold.Whitney.CleanStrips (42s)
✔ Built Lib.Geometry.Manifold.Transversality.Basic (27s)
```

## Envdiff

`python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_base.jsonl dump_after.jsonl`:

```
constants before 21719 after 21719 (keys 21713 21713 )
lost 0 added 0 of which source declarations: 0 0 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 0 0
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT PASS
```

| changed type | explanation |
|---|---|
| *(none)* | no declaration changed type: the packet contained no universe pin and no fixed `Type` binder to generalise, and only docstrings were edited |

0 source declarations lost, 0 added, 0 changed type — every changed type is
explained because there are none.

Caveat recorded for honesty: the base dump was launched before the first edit
but, because nine sibling dumps were competing for the machine, it only finished
after the four modules had been rebuilt, so it may have read the post-edit
`.olean`s. This does not affect the comparison: the edits are docstrings and
module docstrings only, which change neither a declaration's name nor its
`typeHashPublic`, and `envdiff` uses the declaration range only as a boolean
"is a source declaration" flag.

## Commits

```
1ced9927 Lib/Geometry/Manifold/Whitney/BigonModel.lean: document all 52 declarations
7c7a8d0f Lib/Geometry/Manifold/Whitney/AnnularExtension.lean: cite Milnor and Hatcher, document all 60 declarations
f88440bf Lib/Geometry/Manifold/Whitney/CleanStrips.lean: cite Milnor and Guillemin-Pollack, document all 140 declarations
f2f0ea5a Lib/Geometry/Manifold/Transversality/Basic.lean: rewrite stale module docstring, document 133 declarations
```

Range `9552305f..f2f0ea5a` (plus this receipt).

## Corrections after the reviewer pass (2026-09-21)

Independent review: `Lib/reports/review-7-8/r7-packet-05.md` (ACCEPT WITH FINDINGS).  The reviewer
found **nothing `[unsound]` and nothing `[wrong receipt]`**: every numeric and "did X" claim in this
receipt checked out, and the strongest of them was reproduced independently — the comment-stripped
sources are **byte-identical** before and after for all four files, so the environment provably did
not change.  One correction to the record:

1. **No per-packet envdiff artefact is in the repository (finding 8).**  This receipt quotes the
   `envdiff.py` summary ("0 lost, 0 added, 0 changed type") but no `envdiff.json`/`.txt` sits beside
   it; none of the ten packet receipts has one, and the only round-7 artefact in the tree is the
   merged `Lib/reports/round-7/envdiff-merged-d950428a.{json,txt}`.  The honesty caveat recorded
   above — that the base dump may have read post-edit `.olean`s — therefore cannot be checked against
   the raw dump.  It is moot here: the reviewer confirmed the claim by other means (the merged
   envdiff has no `lost`/`added`/`changed_type_all`/`moves` entry in any of the four modules or their
   namespaces, and the stripped-source identity makes any environment change impossible).  Committing
   the `envdiff.json`/`.txt` beside each receipt is the round-8 rule and now stands for all rounds
   (`Lib/reviews/REVIEW-7-8.md` §4); for a docstring-only packet the cheaper and stronger check is
   the one used here — strip comments, diff, and record the sha256 in the receipt.

2. **Docstring findings are code fixes, not receipt fixes.**  `WhitneyPairModel.cornerScale`
   (docstring says "nearer corner"; the quantity is the distance to the far one),
   `CleanBigonBoundary` / the `CleanStrips` module docstring (overstate the cleanliness clause),
   `CleanStripPatch` (drops the `StripCoordinates.reverse`), `SupportedGerms.realizes_det_one` /
   `realizes_local_germ` (omit `dim E ≥ 2`), `DiskShrinking.exists_chart_disk_shrinking`, the
   `AnnularExtension` module-docstring bullets, and the Milnor *TDV* §7 citation (the argument
   formalised is §§2–3) are listed in `Lib/reviews/REVIEW-7-8.md` §3 for the packet-05 fix agent.
