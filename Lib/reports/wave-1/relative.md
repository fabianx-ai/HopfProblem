# Wave 1 receipt — `Lib/Geometry/Manifold/Immersion/Relative.lean` (NAME = relative)

Base `lib/integration` at `e669bc93`; branch `wave1/relative`; commits `7f6935d2`, `fda36003`, and the
receipt commit. Judgement entry: verdict C (omnibus of five topics; `MorseCancellation` names;
`Plane := ℝ × ℝ` specialisation; no docstrings — the last already repaired at the base, 214 of 215
declarations documented at `e669bc93`). Tool artefacts beside this file in `relative/`:
`split_<Piece>.json` (the twelve `split_module` receipts), `plan.json` (declaration → piece),
`rename.txt` (empty: no renames), `envdiff.json`, `envdiff.txt`.

## The cut

`tools/split_module.py` was run twelve times on the *original* source against
`dump_head.jsonl` (stay set = every declaration not in the piece); only the move file of each run
was used, so every one of the 215 ranged constants is written exactly once, verbatim (checked: each
unit's `sha256` in the receipt equals the SHA-256 of the original lines and the unit text occurs
verbatim in the piece; `plan.json` = union of the twelve receipts). The move files were then
assembled (`assemble.py` in the scratch): copied original module docstring dropped, piece docstring
inserted, import list set. `Relative.lean` is a facade: rewritten module docstring listing the
pieces, twelve `public import`s, no declarations. No consumer edited; `Lib.lean` untouched.

| piece `Lib/Geometry/Manifold/Immersion/Relative/…` | lines moved (original line ranges) | declarations | textbook topic |
|---|---|---|---|
| `PointMoving.lean` | 340 (73–431) | 20 | homogeneity of a manifold, supported diffeomorphisms isotopic to the identity, smooth paths avoiding a finite set (Milnor, *Topology from the differentiable viewpoint*, §4 Homogeneity Lemma; cf. Hirsch Ch. 8) |
| `ImmersionLocus.lean` | 296 (676–804; 1988–2144; 2257–2279) | 16 | immersion locus open, local immersion theorem, compact double-point set (Hirsch Ch. 1) |
| `ChartPerturbation.lean` | 257 (433–674; 806–831) | 13 | Sard-type count for chart-supported perturbations `ChartMapPerturbation` (Whitney 1936 Thm 5; Hirsch Ch. 2 §2, Ch. 3 §2) |
| `Embedding.lean` | 656 (833–1062; 1726–1782; 1822–1986; 2146–2210; 2357–2418; 2456–2551) | 25 | relative embedding theorem for a general source, `2 dim E < dim N`, with avoidance of a closed image; `OpenObstacle` (Hirsch Ch. 2 §2) |
| `AffinePerturbation.lean` | 312 (1064–1406) | 32 | `PlaneImmersion`: affine perturbations of maps of the plane, Hausdorff-dimension count of bad parameters (Whitney Thm 5) |
| `Plane.lean` | 499 (1408–1724; 1784–1820; 2212–2255; 2281–2355; 2420–2454) | 14 | relative immersion and embedding theorems for the plane, `dim N ≥ 5`, transported to any 2-dimensional source (Hirsch Ch. 2 §2) |
| `Curve.lean` | 472 (2811–3306) | 25 | `WeightedPerturbation`, `CurveImmersion`, relative immersion/embedding theorems for curves, `dim N ≥ 3` (Hirsch Ch. 2 §2) |
| `Arc.lean` | 467 (2553–2809; 3308–3479; 4518–4565) | 13 | embedded arcs with prescribed endpoint germs, clean of a finite set / a closed image; smoothing off a compact set (Hirsch Ch. 3 §2; Milnor h-cobordism §6) |
| `TubularNeighborhood.lean` | 326 (3481–3811) | 6 | tubular neighbourhoods of an embedded star-convex compact set, clean form (Hirsch Ch. 4 §5) |
| `TwoSheetArc.lean` | 253 (3813–4069) | 5 | clean charts along an arc joining two embedded surfaces in a 5-manifold (Milnor h-cobordism §6) |
| `FrameField.lean` | 574 (4071–4516; 4741–4896; 5006–5012) | 38 | `FrameField`, `AxisCoordinates`, `TransverseCoordinates`: complements, sheared blocks and maps, sheared tubular charts (cf. Hirsch Ch. 4) |
| `AxisChart.lean` | 274 (4567–4739; 4898–5004) | 8 | `LinearFramePaths` (two components of `GL(D)`), axis charts with prescribed endpoint germs |
| total | 4726 of 5012 lines | 215 | |

Piece dependency order (from the dump's `uses`, `_proof_n` edges dropped): ImmersionLocus →
ChartPerturbation → Embedding → {Plane (also AffinePerturbation), Curve} → Arc (also PointMoving) →
{TwoSheetArc (also TubularNeighborhood ← ImmersionLocus), AxisChart (also FrameField)}.

Imports: each piece has `public import Mathlib` plus the maximal `Lib` module it uses directly
according to the dump (`Transversality.Basic` for PointMoving, TubularNeighborhood, FrameField;
`Morse.SurgeryWindows` for ChartPerturbation, Embedding, AffinePerturbation; `Morse.Existence` for
ImmersionLocus) plus the pieces it depends on; the original's eight `Lib` imports were all
transitively contained in `Transversality.Basic`, and the duplicate
`public import Mathlib.Geometry.Manifold.LocalDiffeomorph` (inside `Mathlib`) is dropped. One build
correction: `TubularNeighborhood` first got `Collar` and failed on `Diffeomorph.toPartialDiffeomorph'`
(defined in `Transversality.Basic`); no further trimming attempted (each piece builds in 20–70 s, a
trim round was not worth the shared cores). No `set_option maxSynthPendingDepth`, `universe` or
kitchen-sink `open scoped` existed at the base (`open scoped ContDiff ENNReal` kept, used).

## `Hopf/Proof` moves: none

Closure over `dump_head.jsonl`: 68 constants of the module are used directly by constants of other
`Lib` modules (`consumers.json` in the scratch; e.g. `Rearrangement`, `SurgeryCollapse`,
`BeltCancellation`, `CircleGluing`, `OrderedCancellation`, `Whitney/EmbeddedArcs`, `Whitney/FrameField`,
`Whitney/RankThreeModel`, `Whitney/CleanStrips`, `Collar`, `Morse/Connection`,
`SingularHomology/OnePointCover`, `SingularHomology/LinearSphereAction`); the backward closure of
those 68 inside the module contains all 215 ranged constants. So nothing may leave `Lib`, and nothing
here is project material anyway (no dimension-6 hypothesis, no `Hemisphere.Sphere 2`, no `mo1973`).
`Lib/AxiomAudit.lean` probes none of the module's names. `lake build Lib` green (below).

## Renames: none

`rename.txt` is empty; no `mo1973` name exists in the module. The `MorseCancellation.*` prefix (16
names) and the `*native*` names were left: see Left.

## Universe lifts: none

Every declaration already takes `Type*` binders; no `.{0}` or `{X : Type}` in the module
(`grep -nE ': Type\}|\.\{0\}' Lib/Geometry/Manifold/Immersion/Relative/*.lean` empty).

## Docstrings

Computed: 215 declaration heads in the twelve pieces, 215 `/-- ` docstrings, each immediately above
its declaration (script over the pieces: no `NO DOCSTRING`). At the base 214 were present; the one
added (commit `fda36003`) is
`ManifoldImmersion.exists_relative_embedded_avoidance_of_clean_neighborhood_of_isClosed_range`
(`Plane.lean`; the head is `theorem` with the name on the next line, which is why the auditors'
`grep -c '^/-- '` and the head count differed by one). Twelve module docstrings written (mathematics
and textbook section; no invented theorem numbers).

## Checks (all under nohup, pinned to three cores with `taskset -c 12-14`; this Lake has no `-j`)

`lake build -j3` is rejected by Lake v4.33.0 (`error: unknown short option '-j'`, `build1.log`), so
parallelism was limited by `taskset` instead. Lines from `checks.log` / `build1.log` / `build2.log`:

```
lake build Lib.Geometry.Manifold.Immersion.Relative.{PointMoving,…,AxisChart} Lib.Geometry.Manifold.Immersion.Relative
  → all twelve pieces and the facade Built (build1.log after the import fix: build2.log)
  ✔ [8753/8753] Built Lib.Geometry.Manifold.Immersion.Relative (7.0s)
  Build completed successfully (8753 jobs).
=== 23:19:52 lake build Lib
Build completed successfully (9158 jobs).
exit 0
=== 23:36:06 lake build Solution S6Shortcuts S6 Challenge
Build completed successfully (9210 jobs).
exit 0
=== 23:51:39 lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
Build completed successfully (9160 jobs).
exit 0
  axiom sets in axiomaudit.log: 1692 × [propext, Classical.choice, Quot.sound], 111 × [propext, Quot.sound],
  10 × [propext]; sorryAx: 0
=== census
ratchet PASS: 123 <= baseline 1648
exit 0
=== import Hopf grep
grep -rn --include=*.lean '^import Hopf' Lib/   → empty (exit 1)
  (the unrestricted grep hits only prose and `.lean.txt` logs under Lib/docs/, pre-existing)
dump: 38251 constants from #[Solution, Lib] under #[Hopf, Lib]; rename map: 0 entries
envdiff exit 0
```

## envdiff (`envdiff.txt`)

```
constants before 38248 after 38251 (keys 38146 38149 )
lost 20 added 23 of which source declarations: 0 0 ; names with changed type 20 of which source: 0
auxiliary lost/added/changed (not judged): 20 23 20
module moves (source declarations, 1-to-1): 215, all Lib.Geometry.Manifold.Immersion.Relative -> <piece>
  32 AffinePerturbation, 13 Arc, 8 AxisChart, 13 ChartPerturbation, 25 Curve, 25 Embedding,
  38 FrameField, 16 ImmersionLocus, 14 Plane, 20 PointMoving, 6 TubularNeighborhood, 5 TwoSheetArc
ambiguous module changes: 0
VERDICT PASS
```

Moves = plan (`plan.json`), 0 lost, 0 added, 0 changed types among source declarations. The
auxiliary differences, name by name: `LinearFramePaths.matrixCoordinates._proof_1…18` (lost) vs
`._proof_1…20` (added) and `LinearFramePaths.operatorComponent._proof_1` — Lean re-abstracted and
renumbered the proofs of these two definitions in `AxisChart`, where the proofs previously shared
with `PlaneImmersion.linearMap._proof_1` (dump `uses`: `FrameField.complementQuotient`,
`correctedComplement`, `LinearFramePaths.matrixCoordinates` used that constant at the base) are now
local: `FrameField.complementQuotient._proof_2` (added); `FrameField.correctedComplement.eq_1` is the
equation lemma regenerated in `FrameField` with a new hash. None is a source declaration.

## Left

- **`MorseCancellation.*` prefix (16 names) not dropped.** Consumers outside the pieces
  (`grep -rlw <name> Lib Hopf Solution.lean S6.lean S6Shortcuts.lean Challenge.lean --include=*.lean`):
  `exists_isotopic_two_points_in_dense` ← `Morse/BeltCancellation`, `Morse/SurgeryCollapse`;
  `isotopicToIdentity_joined` ← `Morse/BeltCancellation`; `exists_isotopic_pointMoving_of_path` ←
  `SingularHomology/OnePointCover`; `exists_smooth_path_avoiding_closed_image` ←
  `Morse/Rearrangement`; `exists_smooth_path_avoiding_closed_image_in_open` ← `Morse/BeltCancellation`;
  `exists_clean_arc_with_local_endpoint_germs`, `chart_axis_curve_properties`,
  `exists_clean_two_sheet_arc` ← `Morse/Rearrangement`; the other eight
  (`exists_open_isotopic_pointMoving`, `isotopicPointOrbit`, `isOpen_isotopicPointOrbit`,
  `isOpen_sdiff_isotopicPointOrbit`, `exists_isotopic_pointMoving_of_preconnected`,
  `sheetAxisShuffle`, `exists_clean_sheet_axis_chart`, `terminalSheetCoordinates`) have none.
  `Rearrangement.lean` and `SurgeryCollapse.lean` are monoliths being split by other agents now, so
  their consumer edits are forbidden this wave, and renaming only the unblocked half of each family
  would leave mixed namespaces. Proposal for the follow-up: the isotopy block (8 names, `PointMoving`)
  → `SupportedDiffeomorph.*` beside the non-isotopic twins already there
  (`SupportedDiffeomorph.pointOrbit`, `…exists_pointMoving_of_path`), e.g.
  `SupportedDiffeomorph.exists_isotopic_pointMoving_of_path`; the two path lemmas (`Arc`) → root
  `exists_smooth_path_avoiding_closed_image(_in_open)`; the arc lemma → root
  `exists_clean_arc_with_local_endpoint_germs`; the sheet block (5 names, `TwoSheetArc`) → a
  `TwoSheetArc.*` namespace.
- **`*native*` names** (`grep -rn 'native' Lib/Geometry/Manifold/Immersion/Relative/`):
  `ManifoldImmersion.isOpen_injective_nativeDerivative`, `eventually_injective_nativeDerivative`,
  `exists_open_injOn_of_injective_nativeDerivative_on`, `exists_open_injOn_of_injective_nativeDerivative`
  (← `Whitney/EmbeddedArcs`, a monolith under split), `isCompact_doublePoints_of_injective_nativeDerivative`,
  `AxisCoordinates.exists_native_axis_transition_data`, `exists_native_axis_chart_with_endpoint_germs`
  (both ← `Morse/Rearrangement`), `NativeEuclideanEmbedding.exists_smooth_normalFrame_near_starConvex`
  (namespace of a structure defined in `WhitneyEmbedding`). Proposed: `nativeDerivative` → `mfderiv`
  (`isOpen_injective_mfderiv_family`, `exists_open_injOn_of_injective_mfderiv(_on)`,
  `isCompact_doublePoints_of_injective_mfderiv`), `exists_native_axis_*` → `exists_axis_*`; left as a
  set because one member of each family is blocked.
- **`PlaneImmersion.Plane := ℝ × ℝ` specialisation** (`grep -n 'abbrev PlaneImmersion.Plane'
  Lib/Geometry/Manifold/Immersion/Relative/AffinePerturbation.lean`): the headline theorems
  `exists_immersion_on_compact_rel`, `exists_relative_compact_embedding(_twoDimensional)` are stated for
  a 2-dimensional source with `5 ≤ dim N`; Hirsch/Whitney state them for any `m` with `n ≥ 2m + 1`.
  Generalising changes statements and proofs (a new `dimH` count in `AffinePerturbation` for
  `E × E` and `E × (E × F)`), out of this wave's scope; the general-source half of the argument
  (`Embedding.lean`, `2 dim E < dim G`) is already dimension-free, only the immersion-existence half
  (`Plane.lean`) is planar. `PlaneImmersion.Plane` has consumers in `Whitney/BigonModel`,
  `Whitney/FrameField`, `Whitney/RankThreeModel`, `Topology/Homotopy/PuncturedPlaneCyclic`, `Hopf/Proof/LCP/*`.
- **Twins, not duplicates** (nothing deleted, nothing found identical): `MorseCancellation.isotopicPointOrbit`
  / `isOpen_isotopicPointOrbit` / `isOpen_sdiff_isotopicPointOrbit` / `exists_isotopic_pointMoving_of_{preconnected,path}`
  are the isotopic variants of `SupportedDiffeomorph.pointOrbit` / `isOpen_pointOrbit` /
  `isOpen_sdiff_pointOrbit` / `exists_pointMoving_of_{preconnected,path}` (same proofs, stronger
  conclusion); `exists_smooth_curve_with_germ_at` (manifold) vs `exists_smooth_open_curve_with_germ`
  (open subset of a normed space, staying inside it); `ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact`
  sits in `Arc.lean` because its only consumer in the module is there, while its namespace lives in
  `Morse/Existence.lean` (a monolith): a better home once that split lands.
- **Import trims** beyond the choice above not attempted (see Imports).
