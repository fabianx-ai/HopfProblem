# Round 8, seat `dfiles-a`: the five `Lib/Geometry/Manifold/Morse` D files

Packet: `Lib/reports/round-7/judgement/d-files.md`, the five
`Lib/Geometry/Manifold/Morse/` entries (`BeltCancellation`, `CutTransport`,
`MiddleBlocks`, `MinimalSystem`, `SurgeryHomology`).  Branch `r8/dfiles-a`,
worktree `/home/goblin/hopf-r8-dfiles-a`, base `4e15a034`.

## The constraint that shaped the result

`Lib` may never import `Hopf` (second guard of `scripts/lib_stock_census.py`).
So a declaration of one of these five modules can only go to `Hopf/Proof/` if
**no `Lib` module outside the five uses it**.  That was computed exactly, not by
grep: from the base `dump` table (`uses` edges) the set of constants reachable
downward from any `Lib` consumer was closed off, giving per module

| module | constants that must stay in `Lib` | constants free to move |
|---|---|---|
| `MinimalSystem` | 0 | 4 |
| `CutTransport` | 0 | 115 |
| `MiddleBlocks` | 0 | 80 |
| `BeltCancellation` | 96 | 19 |
| `SurgeryHomology` | 120 | 23 |

The single reason `BeltCancellation` and `SurgeryHomology` cannot follow the
auditors' suggestion is `Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean`
(5430 lines, itself "moved verbatim from `Hopf/SphereTopology.lean`") and
`Lib/Geometry/Manifold/Morse/OrderedCancellation.lean`, which consume the
dimension-6 index-2/3 material.  Neither is in this packet.  Both kept modules
now say so in their module docstring, naming the blocker.  **Open item for the
owner: split `SurgeryCollapse` and `OrderedCancellation`, then 40 more
declarations of `BeltCancellation` and the index-2/3 block predicates of
`SurgeryHomology` can follow their tails into `Hopf/Proof/`.**

## Per item

### 1. `Lib/Geometry/Manifold/Morse/MinimalSystem.lean` — whole module returned
Commit `5d75d095`.  All four declarations (`SixSphere`,
`simplyConnectedSpace_of_homotopySixSphere`,
`pathConnectedSpace_of_homotopySixSphere`,
`homotopySixSphere_homology_subsingleton`) are pinned to `Fin 7`; no general
island.  Moved verbatim to `Hopf/Proof/Geometry/Manifold/Morse/MinimalSystem.lean`
with a docstring that says the file is proof-specific and names the Mathlib /
`SphereHomology` facts each declaration instantiates.  The `Lib.lean` entry is
gone; the seven `Lib` files that imported the module use none of its
declarations and drop the import; 24 `Hopf` files retarget it.

### 2. `Lib/Geometry/Manifold/Morse/MiddleBlocks.lean` — 4 kept, 27 returned
Commit `c356eb79`.  Kept in the new `Lib/Geometry/Manifold/Morse/EqualRangeHomology.lean`
(module docstring + a docstring on each of the four): the equal-range unit lemmas
and the two `LocalDegree.SeparatedNeighborhoods` helpers.  The other 27
declarations (the native middle-block counts, the canonical cut sequence, the
basin families, the centered-passage normal factors, the belt-intersection
lemmas) moved to `Hopf/Proof/Geometry/Manifold/Morse/MiddleBlocks.lean`.
`Lib/Geometry/Manifold/Morse/MiddleBlocks.lean` is deleted.

### 3. `Lib/Geometry/Manifold/Morse/CutTransport.lean` — 17 kept, 42 returned
Commit `8c6fbde4`.  The `Lib` module keeps the sublevel/level inclusions and
their functoriality, `middleSectionClass`, the whole equal-cut comparison
(`equalCutSection`, `equalCutSublevelHomeomorph`, `equalCutHomologyEquiv`,
`equalCutSection_class` and the groupoid laws), the two
`SupportedDiffeomorph.IsotopicToIdentity` homotopy lemmas and the three lemmas
renamed into their mathematical namespaces.  The module docstring is rewritten
into a statement of what is proved, with Milnor/Hatcher references.  The other 42
declarations (flow transport between cuts, the canonical middle matrix, the
Whitney-trick sheet-passage geometry, the window arithmetic, the index-2/3
counting, `instLocal1`) moved to
`Hopf/Proof/Geometry/Manifold/Morse/CutTransport.lean`.

### 4. `Lib/Geometry/Manifold/Morse/BeltCancellation.lean` — 8 filed, 10 returned, 40 blocked
Commit `1a7358c0`.  The four general lemmas the auditors named are filed in the
modules that own their namespace: `RegularLevel.contMDiffWithinAt_iff_inclusion`
and `contMDiffOn_iff_inclusion` into `Lib/Geometry/Manifold/RegularLevel.lean`;
`PuncturedRadial.toSphere_fromSphere`, `deformation`, `sphereHomotopyEquiv` and
the two `LocalDegree` helpers into
`Lib/AlgebraicTopology/SingularHomology/LinearSphereAction.lean` (which already
holds `PuncturedRadial.toSphere`; the module gains `open scoped ContinuousMap`);
`surjective_coprod_comp_left`, renamed, into
`Lib/Geometry/Manifold/Transversality/Basic.lean`.  The lower-transport tail and
the radial parameter chart (10 declarations) moved to
`Hopf/Proof/Geometry/Manifold/Morse/BeltCancellation.lean`.  The remaining 40
are blocked by `SurgeryCollapse` (see above); the module docstring now states the
audit's finding, the blocker, and carries the two Milnor references.

### 5. `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean` — 17 split off, 2 returned, docstring rewritten
Commit `efce6afa`.  The two foreign subjects the auditors named became their own
documented modules: `Lib/Algebra/BigOperators/SignedCancellation.lean` (the five
`FiniteSignedCancellation` lemmas, pure `Finset`/`SignType`) and
`Lib/Geometry/Manifold/Morse/RadialFilling.lean` (the twelve `RadialFilling`
declarations).  `upperLevelInclusion` and `lastUpperHomeomorph`, the only two
declarations no `Lib` module consumes, moved to
`Hopf/Proof/Geometry/Manifold/Morse/SurgeryHomology.lean`.  The stale docstring
(it promised four declarations that live in `SurgeryCollapse.lean`) is replaced
by an inventory of what is declared, with the Milnor §4 reference, and records
why the index-2/3 block predicates stay.

## Rename map

| old | new |
|---|---|
| `MorseCancellation.same_image_sphere_maps_unit` | `SingularHomology.homologyMap_unit_smul_of_range_eq` |
| `MorseCancellation.same_image_section_classes_unit` | `MorseCancellation.middleSectionClass_unit_smul_of_range_eq` |
| `MorseCancellation.conjugate_level_isotopy` | `SupportedDiffeomorph.IsotopicToIdentity.conj` |
| `MorseCancellation.intersection_count_under_injective_map` | `Set.ncard_range_comp_inter_range_comp_of_injective` |
| `MorseCancellation.span_prefix_succ` | `Submodule.span_range_fin_succ` |
| `MorseCancellation.surjective_coprod_comp_left` | `ContinuousLinearMap.surjective_coprod_comp_left` |

`rename.txt` (used for the after-dump) lists both directions; the two name sets
are disjoint, so the map is direction-agnostic for `dump --rename`.

## Lost-name table

None.  `envdiff` reports **0 source declarations lost and 0 added**; nothing was
deleted in this packet, so there is no surviving-twin column to fill.

## Envdiff

`envdiff.txt` / `envdiff.json` in this directory (base dump `4e15a034`
pre-edit, after dump at `efce6afa` with `--rename rename.txt`):

```
constants before 38593 after 38593 (keys 38491 38491 )
lost 2 added 2 of which source declarations: 0 0 ; names with changed type 1 of which source: 1
  PROOF-NAMING MorseCancellation.span_prefix_succ
auxiliary lost/added/changed (not judged): 2 2 0
module moves (source declarations, 1-to-1):
      10  Lib.Geometry.Manifold.Morse.BeltCancellation -> Hopf.Proof.Geometry.Manifold.Morse.BeltCancellation
       5  Lib.Geometry.Manifold.Morse.BeltCancellation -> Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
       2  Lib.Geometry.Manifold.Morse.BeltCancellation -> Lib.Geometry.Manifold.RegularLevel
       1  Lib.Geometry.Manifold.Morse.BeltCancellation -> Lib.Geometry.Manifold.Transversality.Basic
      52  Lib.Geometry.Manifold.Morse.CutTransport -> Hopf.Proof.Geometry.Manifold.Morse.CutTransport
      27  Lib.Geometry.Manifold.Morse.MiddleBlocks -> Hopf.Proof.Geometry.Manifold.Morse.MiddleBlocks
       4  Lib.Geometry.Manifold.Morse.MiddleBlocks -> Lib.Geometry.Manifold.Morse.EqualRangeHomology
       4  Lib.Geometry.Manifold.Morse.MinimalSystem -> Hopf.Proof.Geometry.Manifold.Morse.MinimalSystem
       2  Lib.Geometry.Manifold.Morse.SurgeryHomology -> Hopf.Proof.Geometry.Manifold.Morse.SurgeryHomology
       5  Lib.Geometry.Manifold.Morse.SurgeryHomology -> Lib.Algebra.BigOperators.SignedCancellation
      12  Lib.Geometry.Manifold.Morse.SurgeryHomology -> Lib.Geometry.Manifold.Morse.RadialFilling
ambiguous module changes: 0
auxiliary constants that changed module: 100
VERDICT PASS
```

The one changed type is classified by `envdiff` itself as PROOF-NAMING: the
statement of `Submodule.span_range_fin_succ` contains a `by omega` side
condition, whose auxiliary constant `…._proof_1` is renamed with the theorem and
is not covered by the map (auxiliary names are not judged).  Its `uses` set is
byte-identical before and after, i.e. the statement is unchanged.  No
universe/binder generalisation was made anywhere in this packet.

## Build

Run from the worktree root with `lake` v4.33.0, after each commit:

```
lake build Lib Solution S6Shortcuts S6 Challenge   -> Build completed successfully (9196 jobs).
lake build Lib.AxiomAudit                          -> Build completed successfully (9149 jobs).
python3 scripts/lib_stock_census.py --check        -> ratchet PASS: 123 <= baseline 1648
```

`Lib.AxiomAudit` reports only `[propext, Classical.choice, Quot.sound]` and
subsets thereof; `Solution.lean:61` `Mathoverflow1973.mathoverflow_1973 depends
on axioms: [propext, Classical.choice, Quot.sound]`.  The stock census is
unchanged at 123 (everything moved went under `Hopf/Proof/`, which the census
skips).

## Commits

```
5d75d095  Lib/Geometry/Manifold/Morse/MinimalSystem.lean: return the six-sphere data to Hopf/Proof
c356eb79  Lib/Geometry/Manifold/Morse/MiddleBlocks.lean: keep the two general islands, return the index-2/3 accounting
8c6fbde4  Lib/Geometry/Manifold/Morse/CutTransport.lean: keep the sublevel/equal-cut island, return the index-2/3 bookkeeping
1a7358c0  Lib/Geometry/Manifold/Morse/BeltCancellation.lean: file the general lemmas, return the lower-transport tail
efce6afa  Lib/Geometry/Manifold/Morse/SurgeryHomology.lean: split off the two foreign subjects, return the upper-level tail
```

Splits were produced with `lean-agent-ide` `tools/split_module.py` against the
base dump; the per-unit receipts are `split-*.json` in this directory.  Note for
anyone repeating this: `split_module` anchors on the dump's line ranges, so the
source file must be at the revision the dump was taken from
(`SurgeryHomology.lean` had lost one import line in commit `5d75d095` and the
split had to be re-run against `git show 4e15a034:…`).
