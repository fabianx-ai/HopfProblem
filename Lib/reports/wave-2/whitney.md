# Wave 2 — `Lib/Geometry/Manifold/Whitney/FrameField.lean` and `Whitney/EmbeddedArcs.lean`

Agent: Claude Opus 5.5 (model ID `claude-opus-5-5`). Started 2026-10-01 19:59 CEST, ended
2026-10-01 22:12 CEST. Base `lib/integration` at `3760f829`; branch `wave2/whitney`. Judgement
entries: `Lib/reports/round-7/judgement/monoliths.md` (both verdict C; twin Milnor, *Lectures on
the h-cobordism theorem*, §§5–6). A previous agent began this assignment and was stopped while
still reading, with no edits and no commits. This run started from its scratch notes but redid the
plan: its plan for FrameField had cycles between pieces.

FrameField (2,774 lines, 121 declarations) is cut into twelve topic modules under
`Lib/Geometry/Manifold/Whitney/FrameField/`. EmbeddedArcs (3,463 lines, 88 declarations) is cut
into thirteen under `Lib/Geometry/Manifold/Whitney/EmbeddedArcs/`. Each original module stays as
a facade: its module docstring is rewritten to list the pieces, and it imports the pieces and
nothing else. No consumer was edited (`RankThreeModel`, `Morse/BeltCancellation`,
`Morse/SurgeryCollapse/{DiskFilling,SphereOrientation}`, `Hopf/SingularHomology`, the
EmbeddedArcs pieces), and `Lib.lean` was not edited.

## Commits

| commit | subject |
|---|---|
| `39b0a233` | `Lib/Geometry/Manifold/Whitney/FrameField: split into twelve topic modules behind a facade` |
| `ce3e88c2` | `Lib/Geometry/Manifold/Whitney/EmbeddedArcs: split into thirteen topic modules behind a facade` |
| `7ff19d9f` | `Lib/Geometry/Manifold/Whitney: rename native and _dim_two names in the FrameField and EmbeddedArcs pieces` |
| `2f4fe4d0` | `Lib/Geometry/Manifold/Whitney/EmbeddedArcs/StripInterpolation: drop "native" from one docstring` |
| (this commit) | receipt and artefacts |

## The cut

Lines refer to the base files. Every unit was moved by `tools/split_module.py`, with one run per
piece on the base source and the stay set equal to all other ranged constants. The receipts are
`whitney/split_<Piece>.json`. The planned partition was checked for acyclicity over the dump's
`uses` before the runs (`plan_check.py` in the session scratch). The tool writes context lines
(the copyright header, the old module docstring, the imports, `open`, `noncomputable section`
and `end`) into every piece. A post-processing step then replaced the header up to the first
`open` line with a new header (copyright, imports and the piece's module docstring) and collapsed
the blank-line runs next to `noncomputable section`/`end`. No line inside a unit was touched.

Verbatimness check: the base text of every moved unit, at the lines recorded in the receipts, was
searched verbatim in its piece. FrameField: 121/121 units found, each exactly once. EmbeddedArcs:
88/88. Every unit moved exactly once overall.

### FrameField

| piece (`Lib/Geometry/Manifold/Whitney/…`) | base lines moved | declarations | topic |
|---|---|---|---|
| `FrameField/BlockDeterminant.lean` | 201–288, 1094–1125, 1173–1195, 1263–1321, 2010–2105 | 13: `FrameField.det_of_zero_lower_left` … `FrameField.opposite_intersectionDet_iff_normalDet` | determinants of block frames `G ⊞ C` (`Matrix.det_fromBlocks_zero₂₁` read through bases), frames on a line, sign constancy along paths of invertible maps |
| `FrameField/Complement.lean` | 498–620 | 3: `FrameField.bijective_coprod_of_orthogonal_range`, `exists_smooth_complement_near_starConvex(_on)` | smooth orthogonal complements of a smooth family of injective maps over a compact star-shaped set (cf. Milnor–Stasheff, Ch. 3) |
| `FrameField/FrameExtension.lean` | 739–798, 1008–1092, 1127–1171 | 8: `DiskFraming.puncturedModel` … `FrameField.exists_completed_one_column_frame` | nowhere-zero curves with endpoint germs; nowhere-zero fields and one-column frames extended relative to a closed set (cf. Hirsch Ch. 2) |
| `FrameField/PlanarFrame.lean` | 290–418, 800–953 | 23: `PlanarFrame.area` … `PlanarFrame.exists_smooth_join_of_same_determinant_sign` | 2×2 linear algebra on `ℝ × ℝ`; the two path components of `GL₂(ℝ)` |
| `FrameField/InvertibleJoin.lean` | 955–1006, 1197–1261, 1323–1387 | 4: `FrameField.exists_smooth_invertible_join_of_finrank_two` … `…_of_frame_sign_of_finrank_one_or_two` | smooth joins of invertible germs of equal determinant sign in dimension 1, 2; complements with endpoint germs (Milnor §6) |
| `FrameField/IntersectionCoordinates.lean` | 420–496, 1661–1733, 1980–2008 | 12: `IntersectionCoordinates.jointBlock` … `IntersectionCoordinates.det_jointBlock_eq_tangentSum`, `FrameField.transportComplement` (+5) | the joint block of two sheet frames (intersection sign as a determinant); transport of complements |
| `FrameField/BoundaryArcs.lean` | 42–199, 622–737 | 17: `WhitneyPairModel.lowerBoundaryArc` … `TubularBigon.upper_sheetFrame_complement_of_finrank` | the two boundary arcs of a tubular bigon; normal frames of the sheets along them |
| `FrameField/BoundaryField.lean` | 1389–1481 | 2: `WhitneyPairModel.exists_smooth_bigon_boundary_field`, `…exists_injective_bigon_boundary_field` | one field near the boundary of the bigon from fields along the two arcs |
| `FrameField/RankThreeFrame.lean` | 1483–1659, 1735–1978 | 12: `FrameField.rankThreePairCoordinates` … `TubularBigon.exists_rankThree_adapted_frame_of_opposite_corner_signs` | the adapted frame over a bigon of normal rank three (Milnor §6, case `rank = 3`) |
| `FrameField/SheetNormal.lean` | 2107–2453 | 19: `StripNormalData.sheetBaseFrame` … `StripNormalData.normalDetector_comp_sheet` | sheet frames, sheet complements and normal detectors along a strip |
| `FrameField/RankThreeCorners.lean` | 2455–2617 | 3: `TubularBigon.opposite_rankThree_corners_iff_normal_sheet_determinants`, `ManifoldMorse.MorseSurgeryData.beltSheetNormal`, `…opposite_belt_corners_iff_normal_sheet_determinants` | corner intersection signs from a defining map of one sheet; the belt-sphere case |
| `FrameField/SheetCoordinates.lean` | 2619–2772 | 5: `SliceChart.projection` … `SliceChart.exists_induced_sheet_chart` (renamed from `NativeSheetCoordinates.*`) | the chart induced on a sheet by a clean ambient chart (slice charts, Lee, *Introduction to Smooth Manifolds*, Thm 5.8) |

### EmbeddedArcs

| piece (`Lib/Geometry/Manifold/Whitney/…`) | base lines moved | declarations | topic |
|---|---|---|---|
| `EmbeddedArcs/SphereNormalCoordinates.lean` | 43–307 | 11: `SphereNormalCoordinates.radialFrame` … `SphereNormalCoordinates.opposite_normalJacobians_iff_retained_sheet` | radial frames and normal Jacobians along an embedded sphere |
| `EmbeddedArcs/InnerBigon.lean` | 423–580 | 14: `WhitneyPairModel.innerBigonMap` … `WhitneyPairModel.exists_inner_bigon_collar_in_open` | contractions of the standard bigon and their collars |
| `EmbeddedArcs/WhitneyDisc.lean` | 582–1141 | 7: `CleanBigonBoundary.exists_inner_clean_neighborhood` … `CleanBigonBoundary.nonempty_tubularBigon_of_complement_contractions` | filling a clean bigon boundary by an embedded Whitney disc with a tubular neighbourhood (Milnor §6) |
| `EmbeddedArcs/ImmersionRepair.lean` | 1143–1545 | 13: `ManifoldImmersion.exists_weighted_immersive_patch_with_property` … `ManifoldImmersion.exists_curve_endpoint_derivative_repair` | making a map immersive by small weighted perturbations (cf. Hirsch Ch. 2) |
| `EmbeddedArcs/Arcs.lean` | 1547–1723 | 3: `exists_short_embedded_arc`, `exists_embedded_connecting_arc_avoiding_finite_of_two_le_finrank` (was `…_dim_two`), `exists_tubular_connecting_arc_avoiding_finite_with_global_zero` | embedded arcs avoiding a finite set, dimension ≥ 2 (general position for arcs) |
| `EmbeddedArcs/CornerCharts.lean` | 1725–1886 | 3: `exists_clean_corner_of_tubular_arcs`, `nonempty_cleanCornerPatch_of_tubular_arcs`, `exists_clean_ambient_chart_along_embedded_arc` | clean corner charts; clean ambient charts along an arc |
| `EmbeddedArcs/TransverseCoordinates.lean` | 1888–2035 | 7: `TransverseCoordinates.bijective_normalDerivative_transverse_sheet` … `TransverseCoordinates.corner_normalDerivative_ne_zero`, `NativeParametrization.line(_apply)` | the normal derivative at a transverse intersection |
| `EmbeddedArcs/StripInterpolation.lean` | 2037–2410 | 6: `StripCoordinates.exists_smooth_strip_matching_germs` … `exists_clean_strip_matching_germs_in_chart` (was `exists_native_clean_strip_matching_germs`) | strips with prescribed germs at both ends |
| `EmbeddedArcs/StripAlongArc.lean` | 2412–2763 | 3: `exists_strip_neighborhood_with_exact_endpoint_contacts`, `exists_strip_along_arc_matching_parametrized_corners`, `exists_cleanStripPatch_of_tubular_arc_corners` | a clean strip along an arc with prescribed corners |
| `EmbeddedArcs/StripPair.lean` | 2765–3156 | 5: `exists_open_neighborhoods_with_coincidences_in` … `exists_shared_corner_strip_pair_of_two_le_finrank` (was `exists_native_shared_corner_strip_pair_dim_two`) | clean strip pairs along two arcs meeting at two corners |
| `EmbeddedArcs/BeltBigon.lean` | 309–421, 3158–3301 | 3: `ManifoldMorse.MorseSurgeryData.opposite_beltIntersectionSigns_iff_Whitney_corners`, `…nonempty_belt_tubularBigon`, `…exists_belt_tubular_strip_pair` | the three `finrank ℝ E = 6`, index-2, `Hemisphere.Sphere 2` statements (see below) |
| `EmbeddedArcs/FiberRestriction.lean` | 3303–3363 | 5: `FiberRestriction.embed` … `FiberRestriction.restrict` | restricting a fibre-preserving diffeomorphism of `X × V` to a subfibre |
| `EmbeddedArcs/SmallPerturbation.lean` | 3365–3461 | 8: `SmallPerturbation.lipschitzWith_slice` … `SmallPerturbation.exists_diffeomorph_composeFamily` | small weighted translations; finite composites of diffeomorphisms |

### Piece imports

Each piece imports `Mathlib` and the minimal set of modules whose constants it uses directly,
according to the dump's `uses` field. FrameField constants used by EmbeddedArcs pieces are
imported through their FrameField piece, not the facade. A module is left out when another import
already reaches it transitively. Examples: `FiberRestriction ← Mathlib` only;
`Complement ← Collar`; `ImmersionRepair ← Immersion.Relative.Curve`; `BeltBigon ←
FrameField.RankThreeCorners, EmbeddedArcs.{SphereNormalCoordinates, WhitneyDisc, StripPair}`.
`import Mathlib` was kept in every piece, as in wave 1 (see Left). Sizes: facades 60 (FrameField) and 58 (EmbeddedArcs) lines;
pieces 91–600 lines.

## `Hopf/Proof` moves and the closure argument

None. Closure script over `dump_head.jsonl` (`uses`, backward from every constant of a `Lib` module
outside the two files): every declaration of both files is reachable from another `Lib` module. The
exception is `NativeParametrization.line_apply`, which nothing uses. The `Lib` consumers are
`Whitney/RankThreeModel` (64 uses of FrameField, 19 of EmbeddedArcs),
`Morse/SurgeryCollapse/SphereOrientation` (11), `Morse/SurgeryCollapse/DiskFilling` (1) and
`Morse/BeltCancellation` (2 + 1).

In particular, the three project statements named by the judgement
(`opposite_beltIntersectionSigns_iff_Whitney_corners`, `nonempty_belt_tubularBigon`,
`exists_belt_tubular_strip_pair`; `Module.finrank ℝ E = 6`,
`finrank NegativeCoordinates = 2`, `Hemisphere.Sphere 2`) are used by
`Lib/Geometry/Manifold/Morse/BeltCancellation.lean` (l.123, l.131). The same holds for the
rank-three and `MorseSurgeryData.beltSheetNormal` material of FrameField, which
`RankThreeModel` and `BeltCancellation` use. Moving them would make `Lib` import `Hopf`.
They are therefore isolated in `EmbeddedArcs/BeltBigon.lean`, `FrameField/RankThreeFrame.lean`
and `FrameField/RankThreeCorners.lean`, so a later move needs no further cut (see Left).
`Lib/AxiomAudit.lean` and `Hopf/Proof/AxiomAudit.lean` were not changed.

## Renames

`grep -c mo1973` over both base files gives 0, so no rename was required. Nine `native`/`_dim_two`
names were renamed (commit `7ff19d9f`, map `whitney/rename.txt`, `<new> <old>`). Every consumer of
these names is one of the 25 pieces: a grep over `Lib Hopf Solution.lean S6.lean S6Shortcuts.lean
Challenge.lean` (incl. `Lib/AxiomAudit.lean`) found no other file. The new names were checked to be
absent from `Lib`, `Hopf` and Mathlib.

| new | old | reason |
|---|---|---|
| `exists_embedded_connecting_arc_avoiding_finite_of_two_le_finrank` | `exists_embedded_connecting_arc_avoiding_finite_dim_two` | hypothesis `2 ≤ finrank ℝ G` (judgement: Mathlib `_of_two_le_finrank`) |
| `exists_shared_corner_strip_pair_of_two_le_finrank` | `exists_native_shared_corner_strip_pair_dim_two` | hypotheses `2 ≤ finrank ℝ D`, `2 ≤ finrank ℝ Z` |
| `exists_clean_strip_matching_germs_in_chart` | `exists_native_clean_strip_matching_germs` | the statement is through an ambient chart `Φ` (the model-space version is `StripCoordinates.exists_clean_strip_matching_local_germs`) |
| `StripNormalData.normalDetector_eq_mfderiv_comp` | `StripNormalData.normalDetector_eq_native` | conclusion `normalDetector Ψ q t = mfderiv q _ ∘L mfderiv Ψ _` |
| `SliceChart.projection`, `.contMDiffOn_projection`, `.injective_mfderiv_projection`, `.isLocalDiffeomorphOn_projection`, `.exists_induced_sheet_chart` | `NativeSheetCoordinates.*` (same suffixes) | the projection and charts of a slice chart (Lee, Thm 5.8); the namespace had no member outside `FrameField/SheetCoordinates` |

`NativeParametrization.line(_apply)` was not renamed: `NativeParametrization` is a namespace shared
with `CleanStrips`, `Transversality/Basic` and eight other `Lib` modules (see Left).

## Universe lifts

None. All binders are already `Type*`.

## Docstrings

Computed from the after dump: of the 209 ranged declarations of the 25 pieces, 209 carry a
declaration docstring and 0 lack one. All of them were already documented at the base (121/121,
88/88). The judgement's "0 of 88"/"121/121 without" refers to an older revision. Docstrings added
on declarations: 0. Rewritten: 1, comment-only, in commit `2f4fe4d0`
(`exists_clean_strip_matching_germs_in_chart`, "Native form of the strip interpolation" → "Chart
form of the strip interpolation"). Module docstrings: 25 new (one per piece) and 2 rewritten (the
facades).

## Builds (verbatim last lines, logs in the session scratch)

At the split commits:

```
lake build Lib.Geometry.Manifold.Whitney.FrameField            Build completed successfully (8853 jobs).
lake build Lib.Geometry.Manifold.Whitney.RankThreeModel Lib.Geometry.Manifold.Morse.BeltCancellation
                                                                Build completed successfully (8856 jobs).
lake build Lib.Geometry.Manifold.Whitney.EmbeddedArcs Lib.Geometry.Manifold.Whitney.RankThreeModel
  Lib.Geometry.Manifold.Morse.BeltCancellation Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskFilling
  Lib.Geometry.Manifold.Morse.SurgeryCollapse.SphereOrientation  Build completed successfully (8885 jobs).
```

The same five-module build after the renames (`7ff19d9f`) gave `Build completed successfully (8885
jobs).` The full chain was run at `ce3e88c2` and again at the tip `2f4fe4d0`, with identical
results. At the tip:

```
lake build Lib                                                  Build completed successfully (9303 jobs).
lake build Solution S6Shortcuts S6 Challenge                    Build completed successfully (9362 jobs).
  info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit                 Build completed successfully (9305 jobs).
  3,302 axiom reports (3,298 Lib/AxiomAudit + 4 Hopf/Proof/AxiomAudit), union of all sets = {Classical.choice, Quot.sound, propext};
  12 "does not depend on any axioms"; sorryAx: 0
python3 scripts/lib_stock_census.py --check                     stock declarations under Hopf/: 123 … ratchet PASS: 123 <= baseline 1648
grep -rn '^import Hopf' Lib/ --include=*.lean                   (empty)
```

The warnings in these builds are the pre-existing ones of other files (`Hurewicz/CubeSphere`,
`HopfDegree`, `Naturality`, `Straightening`, `CubeChainDecomposition/*`,
`SingularHomology/LocalContributions`). There are none in the 25 pieces or the 2 facades.

## Environment diff (`whitney/envdiff.{json,txt}`)

Base `dump_head.jsonl` (38,301 constants). After dump of the tip `2f4fe4d0`, run as `lake env
lean-agent-ide dump Solution Lib --modules Hopf,Lib --rename whitney/rename.txt` with the map in
`<new> <old>` form: 38,303 constants. Lost 11, added 13, of which source declarations 0 and 0.
Names with a changed type: 1, of which source declarations 0. 209 source declarations moved 1-to-1
over 25 module pairs, exactly the plan above (FrameField 13 + 3 + 8 + 23 + 4 + 12 + 17 + 2 + 12 +
19 + 3 + 5; EmbeddedArcs 11 + 14 + 7 + 13 + 3 + 3 + 7 + 6 + 3 + 5 + 3 + 5 + 8). Ambiguous: 0.
Auxiliary constants that changed module: 74. **VERDICT PASS.** Under the map, all nine renamed
constants have the base's `typeHashPublic`. The dump of `ce3e88c2`, before the renames and without
a map, gave the same result with lost 1 / added 3 and 84 auxiliary moves.

The auxiliary differences, all of which are not source declarations, reconcile as follows.

**10 lost + 10 added: auxiliaries of a renamed theorem.**
`exists_native_shared_corner_strip_pair_dim_two._proof_1_{3,4,7,9,10}` and `._simp_1_{1,2,5,6,8}`
are lost; `exists_shared_corner_strip_pair_of_two_le_finrank.` with the same ten suffixes is added.
The map renames the declaration but not its generated auxiliaries. The ten pairs have identical
`typeHash` suffix by suffix (script check).

**1 lost + 3 added + 1 changed: per-module deduplication of the anonymous proof `_proof_n`.** At the
base, the side-condition proof with `typeHash 1158307750` existed once in the FrameField module, as
`IntersectionCoordinates.jointBlock._proof_1`. `FrameField.rankThreePairDet`,
`StripNormalData.sheetBaseFrame`, `StripNormalData.sheetComplement` and
`StripNormalData.contDiffOn_sheetBaseFrame` reused it. After the cut, `jointBlock` lives in
`FrameField.IntersectionCoordinates`, so `RankThreeFrame` and `SheetNormal` generate that proof
locally:

- in `RankThreeFrame` as `FrameField.rankThreePairDet._proof_1` (hash 1158307750). The base's own
  `rankThreePairDet._proof_1` (hash 1209676977) is renumbered to `_proof_2` with the same hash.
  This is the remaining lost 1 / changed 1 (`_proof_1` at 1209676977) and two of the remaining
  added 3 (`_proof_1` at 1158307750, `_proof_2` at 1209676977);
- in `SheetNormal` as `StripNormalData.sheetBaseFrame._proof_1` (hash 1158307750), the third
  added constant.

For the four declarations concerned, `typeHashPublic` is unchanged and the `uses` lists without
`_proof_n` entries are equal on both sides (script check). No ranged constant anywhere has a
changed `typeHashPublic`.

## Left

1. **Project material still in `Lib`, blocked by `Lib` consumers.** The three dimension-six belt
   statements (`EmbeddedArcs/BeltBigon.lean`), the rank-three frame and corners
   (`FrameField/RankThreeFrame.lean`, `FrameField/RankThreeCorners.lean`, incl.
   `MorseSurgeryData.beltSheetNormal`) are used by `Morse/BeltCancellation` and
   `Whitney/RankThreeModel`, which are not mine. A move to `Hopf/Proof` has to come together with
   (or after) those consumers.
   `grep -n "exists_belt_tubular_strip_pair\|opposite_beltIntersectionSigns_iff_Whitney_corners" Lib/Geometry/Manifold/Morse/BeltCancellation.lean`;
   `grep -rlE "rankThree|RankThree" Lib --include=*.lean | grep -v Whitney/FrameField/`.
2. **`native`/`Native` vocabulary left**: `NativeParametrization.line` and
   `NativeParametrization.line_apply` (`EmbeddedArcs/TransverseCoordinates.lean`). The
   `NativeParametrization` namespace is shared with 8 other `Lib` files and `Hopf/Recognition.lean` (`CleanStrips`,
   `Transversality/Basic`, `Immersion/Relative/TwoSheetArc`, …). Renaming two of its members alone
   would split the family, so this is left for a namespace-wide rename. The pieces also still call
   foreign `native` names (`exists_native_clean_corner_of_parametrizations` of CleanStrips,
   `ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative`,
   `NativeTransversality.At`), which are not mine.
   `grep -rnE "^(theorem|def) [^ ]*[Nn]ative" Lib/Geometry/Manifold/Whitney/FrameField Lib/Geometry/Manifold/Whitney/EmbeddedArcs`;
   `grep -rl "NativeParametrization\." Lib Hopf --include=*.lean`.
3. **`NativeParametrization.line_apply` has no trace in the dump's `uses`**, because the `simpa only`
   at `EmbeddedArcs/TransverseCoordinates.lean` l.121 uses it definitionally. The closure script
   therefore reports it as used by nothing, but the source does use it. Nothing to do; this is
   recorded so that the closure output is not misread.
   `grep -rn "line_apply" Lib Hopf --include=*.lean`.
4. The first two `_dim_two`/`native` items of the judgement are done by the rename above.
   `grep -rn "_dim_two\|NativeSheetCoordinates\|normalDetector_eq_native\|exists_native_clean_strip" Lib Hopf --include=*.lean`
   is empty.
5. **Twins, nothing deleted**: `PlanarFrame.area`/`PlanarFrame.determinant` duplicate
   `Matrix.det_fin_two`/`LinearMap.det` on `ℝ × ℝ` (bridged by `PlanarFrame.determinant_eq_det`);
   `FrameField.det_of_zero_lower_left` is `Matrix.det_fromBlocks_zero₂₁` through bases.
   `grep -n "det_fin_two\|det_fromBlocks_zero₂₁" Lib/Geometry/Manifold/Whitney/FrameField/*.lean`.
6. **Better homes not taken** (facade-dissolving step): `FrameField/BlockDeterminant` → linear
   algebra; `FrameField/Complement` → beside `gramProjection` (`WhitneyEmbedding`/`Collar`);
   `FrameField/SheetCoordinates` → slice charts; `EmbeddedArcs/FiberRestriction` and
   `EmbeddedArcs/SmallPerturbation` are not Whitney-specific (diffeomorphisms of products,
   small perturbations).
7. **Hygiene carried verbatim**: `import Mathlib` in every piece, although it is redundant through
   the `Lib` imports wherever a piece has one (`grep -l "^import Mathlib" Lib/Geometry/Manifold/Whitney/{FrameField,EmbeddedArcs}/*.lean | wc -l` → 25);
   `attribute [local instance 100] Classical.propDecidable in` before four declarations
   (`grep -rn "attribute \[local instance" Lib/Geometry/Manifold/Whitney/FrameField Lib/Geometry/Manifold/Whitney/EmbeddedArcs`);
   the `open` context lines in every piece.
8. **Pieces import `Whitney.CleanStrips`/`AnnularExtension`**, which are monoliths other agents are
   splitting behind facades. Once those are split, the imports can be narrowed to the CleanStrips
   pieces. `grep -ln "Whitney.CleanStrips\|Whitney.AnnularExtension" Lib/Geometry/Manifold/Whitney/{FrameField,EmbeddedArcs}/*.lean`.
