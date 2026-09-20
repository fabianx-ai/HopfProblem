# Round 7 checklist packet 04 — receipt

Worktree `/home/goblin/hopf-r7-p04`, branch `r7/packet-04`, base `9552305f`,
Lean v4.33.0 / Mathlib v4.33.0.  All 18 files of the packet were worked; each was built green
on its own and committed alone.

## Summary of the four work items

| item | total |
|---|---|
| 1. module docstrings rewritten (manuscript/process citations removed, textbook reference added) | 18 of 18 files |
| 1. declaration docstrings rewritten to remove process wording | 5 |
| 2. declaration docstrings added | 335 |
| 3. declarations generalised from an explicit `.{0}` pin to a universe variable | 26 |
| 3. `.{0}` pins left, forced by a declaration outside the packet | 81 |
| 4. `: Type` binders widened to `Type*` (declarations) | 13 |
| 4. explicit `Type` ascription dropped where Lean infers it | 1 (`E₂`) |

No statement was strengthened or weakened, no hypothesis added, no declaration deleted, no
`sorry`/`axiom`/`admit` introduced.  No file outside the packet was edited.

## The forced universe pins

Three declarations outside this packet pin the whole `CategoryTheory/Sites/Leray` cluster to
universe 0 and were not chased (the task forbids following a pin out of the packet):

* `TopCat.Sheaf.pushforwardAdditive` — `Lib/Topology/Sheaves/AddCommGrpPushforward.lean`,
  `variable {X Y : TopCat.{0}}`.  This is the obstacle recorded by the experiment below.
* `TopCat.ConstantSheaf.integralSheaf` — `Lib/Topology/Sheaves/ConstantPushforward/GlobalSections.lean`,
  `abbrev integralSheaf (X : TopCat.{0})`.
* `TopCat.Sheaf.OpenRestriction.freeOpen` / `freeHomAddEquiv` /
  `inclusion` / `openImage` / `restriction` — `Lib/Topology/Sheaves/OpenRestriction.lean` and
  `Lib/Topology/Sheaves/OpenRestriction/Cohomology.lean`, `variable {X : TopCat.{0}}`; and
  `TopCat.FiniteClosedPushforward.cohomologyForward` / `cohomologyEvaluation` —
  `Lib/Topology/Sheaves/FiniteClosedPushforward/Cohomology.lean`, `variable {X Y : TopCat.{0}}`.

The experiment: generalising `variable {X Y : TopCat.{0}}` for the
`pushforward`/`higherDirectImage`/`pushedResolution` block of `ResolutionTransgression.lean` to
`TopCat.{u}` gives, as first error,

```
ResolutionTransgression.lean:75:2: Type mismatch
  TopCat.Sheaf.pushforwardAdditive ?m.13
has type
  Functor.Additive.{0, 1, 0, 1} (TopCat.Sheaf.pushforward AddCommGrpCat ?m.13)
but is expected to have type
  Functor.Additive.{u, u + 1, u, u + 1} (pushforward f)
```

and four further failures of the same kind.  The block was reverted to `TopCat.{0}`; only the
declarations that do not go through `pushforwardAdditive` were generalised.

`ULift.{1}` in `resolutionPostnikovE₂Iso` is likewise forced, by
`HasDerivedCategory.standard` on `AbelianSheaf Y`.

## Per file

### `Lib/CategoryTheory/Sites/Leray/FibreStalkEvaluation/OpenRestrictionComposition.lean` — `f8b80d15`
* citations: module docstring replaced; it now displays `(i_*G)|_U ≅ (i')_*G` and cites
  Hartshorne II.1 / Godement II.1 for direct images and restriction.
* docstrings added: 2 (`induced_apply`, `restrictionPushforwardIso_hom_app`).
* universe pins: 18 left, forced (`OpenRestriction.inclusion`/`openImage`/`restriction`,
  `ConstantSheaf.integralSheaf`, `FiniteClosedPushforward.cohomologyForward`).

### `Lib/CategoryTheory/Sites/Leray/FibreStalkEvaluation/Stalk.lean` — `9e06b8e0`
* citations: module docstring now displays `(Rⁿf_*F)_y = colim_{U ∋ y} Hⁿ(f⁻¹U, F)` with
  Godement II.4.11 and Hartshorne III.8.1.
* docstrings: 0 missing; 4 rewritten to drop process wording ("The one missing normalization",
  "The current higher-direct-image comparison", "the normalization-relative derived-stalk
  adapter retains …"): `ResolutionCohomologyNormalization`, `derivedStalkIso`,
  `derivedStalkEvaluation`, `derivedStalkEvaluation_germ`.
* universe pins: 20 left, forced (`pushforwardAdditive` via `AbelianSheaf`/`higherDirectImageSheaf`,
  `FiniteClosedPushforward.cohomologyEvaluation`).

### `Lib/CategoryTheory/Sites/Leray/HigherDirectImageSheafification.lean` — `cff67f3d`
* citations: Hartshorne III.8.1 (with Godement II.4.17.1) in the module docstring and on
  `higherDirectImageResolutionSheafificationIso`; Godement II.1.2 for exactness of sheafification.
* docstrings added: 3 (`sheafification_additive`, `sheafification_preservesFiniteLimits`,
  `sheafification_preservesFiniteColimits`).
* universe pins generalised: 12 declarations moved into a `section Generic` at `TopCat.{u}` —
  `presheafStalk_preservesFiniteLimits`, `presheafStalk_preservesFiniteColimits`,
  `underlyingPresheafComplex`, `homologyPresheaf`, `stalkHomologyPresheafIso`, `sheafification`,
  `sheafification_additive`, `sheafification_preservesFiniteLimits`,
  `sheafification_preservesFiniteColimits`, `sheafificationUnderlyingIso`,
  `sheafificationComplexIso`, `sheafHomologyIsoSheafification`.
  `stalkHomologyPresheafIso` needed explicit `AddCommGrpCat.{u}` on its two `stalkFunctor`
  occurrences.
* universe pins left: 6 (from `higherDirectImageResolutionSheafificationIso` onwards), forced.

### `Lib/CategoryTheory/Sites/Leray/ResolutionAbutment.lean` — `1e627efd`
* citations: Godement II.4.17 / Weibel 5.8.6 for the Leray spectral sequence and its abutment;
  Weibel 2.3.10 on `pushforwardPreservesInjectiveObjects`.
* docstrings: 0 missing, 0 added.
* universe pins: 8 left, all forced.

### `Lib/CategoryTheory/Sites/Leray/ResolutionCohomologyPresheaf.lean` — `3ba7c621`
* citations: module docstring now displays the presheaf identification and names it as the first
  half of the proof of Hartshorne III.8.1; same reference on
  `resolutionCohomologyPresheafIsoPositive` and `pushedResolutionCohomologyPresheafIsoPositive`,
  whose docstring lost the project token "R1".
* docstrings added: 7 (`sectionsFunctor_additive`, `presheafEvaluation_additive`,
  `presheafEvaluation_preservesFiniteLimits`, `presheafEvaluation_preservesFiniteColimits`,
  `presheafPushforward_additive`, `presheafPushforward_preservesFiniteLimits`,
  `presheafPushforward_preservesFiniteColimits`).
* universe pins generalised: 8 declarations, in two new sections `Evaluation` and `PresheafLevel` —
  `presheafEvaluation` and its three exactness lemmas, `presheafPushforward` and its three.
* universe pins left: 12 (the free-sheaf block and everything downstream of it), forced by
  `OpenRestriction.freeOpen`/`freeHomAddEquiv`.

### `Lib/CategoryTheory/Sites/Leray/ResolutionPostnikov.lean` — `c423ff18`
* citations: the "page-construction owner … supplied downstream by the … owners" paragraph, which
  named five sibling files, was deleted and replaced by the statement of the Leray spectral
  sequence with Godement II.4.17.1 / Weibel 5.8.6 and the Postnikov construction reference
  (Kashiwara–Schapira §12–13, Verdier), plus a `## Main definitions` list.
* docstrings: 0 missing, 0 added.
* universe pins: 2 left, forced; the `ULift.{1}` is forced by `HasDerivedCategory.standard`.

### `Lib/CategoryTheory/Sites/Leray/ResolutionPostnikovD2.lean` — `1de5b691`
* citations: routing paragraph ("supplied downstream by …", "This owner exposes …") replaced by
  Verdier II.4.3 / Kashiwara–Schapira §12 for `d₂` as the connecting map of the two-slice
  triangle, and Godement II.4.17 for the Leray case.
* docstrings: 0 missing.  universe pins: 1 left, forced.

### `Lib/CategoryTheory/Sites/Leray/ResolutionPostnikovD2Coordinates.lean` — `2a72bf6a`
* citations: the audit's `twin: none` is now stated in the module docstring, together with the two
  constructions the lemmas identify and the theorem they serve (Godement II.4.17).
* docstrings: 0 missing.  universe pins: 1 left, forced.

### `Lib/CategoryTheory/Sites/Leray/ResolutionPostnikovD2Transgression.lean` — `4799e6be`
* citations: Godement II.4.17 / Weibel 5.8.6 (the Leray `d₂` on the edge is the transgression), in
  the module docstring and on `resolutionPostnikovE₂_d₂_eq_transgression`.
* docstrings: 0 missing.  universe pins: 1 left, forced.

### `Lib/CategoryTheory/Sites/Leray/ResolutionTransgression.lean` — `7c5050a3`
* citations: Hartshorne III.8 for `Rⁿf_*`, Godement II.4.17 / Weibel 5.8.6 for the Leray `d₂` as
  transgression; `## Main definitions` list added.
* docstrings: 0 missing, 0 added.
* universe pins generalised: 3 (`AbelianSheaf`, `abelianSheafHasExt`, `pushforward`).
* universe pins left: 9, forced (see the experiment above).
* `: Type` binder: the explicit `: Type` ascription on `abbrev E₂` was dropped (Lean infers it).

### `Lib/CategoryTheory/Sites/Leray/SheafificationNeighborhoodGerm.lean` — `a68150ea`
* citations: the disclaimer paragraph was replaced by the two textbook facts the statement rests
  on (Hartshorne III.8.1 and II.1.2) and by the audit's "no textbook counterpart".
* docstrings: 0 missing.  universe pins: 1 left, forced.

### `Lib/CategoryTheory/Sites/Leray/SheafificationStalkCompatibility.lean` — `bdf9778a`
* citations: Hartshorne II.1.2 / Godement II.1.2 (sheafification preserves stalks) and
  Hartshorne III.8.1 in the module docstring and on `stalkSheafificationUnitNatTrans`.
* docstrings added: 1 (`stalkSheafificationUnitNatTrans_app`).
* universe pins: 1 left, forced.

### `Lib/CategoryTheory/Sites/Leray/StalkLocalCriterion.lean` — `ecb8f370`
* citations: Godement II.1.1 (filtered-colimit criterion for bijectivity of a map out of a stalk).
* docstrings: 0 missing.
* universe pins generalised: all 3 (`TopCat.{0}`, `AddCommGrpCat.{0}` ×2 → `universe u`,
  `.{u}`); `stalkMap_bijective_of_local_lift_kill` is now universe-polymorphic.

### `Lib/CategoryTheory/Triangulated/CoyonedaTriangleShift.lean` — `f665c883`
* citations: the consumer-motivated closing sentence ("the exact parity factor needed when an
  adjacent Postnikov triangle is shifted") was replaced by Neeman, *Triangulated Categories*, §1.1
  for the shifted-triangle sign and by the Mathlib name
  `preadditiveCoyoneda_homologySequenceδ_apply`.
* docstrings: 0 missing.
* `: Type` binder ×1: not a defect.  The file already declares `universe v u` and writes
  `{C : Type u} [Category.{v} C]`, which is the Mathlib idiom for a category with a named hom
  universe; `Type*` would be equivalent.  No change.

### `Lib/Geometry/Manifold/Immersion/Relative.lean` — `7dd9dcbd`
* citations: the module docstring said "tubular-neighborhood one-offs", "arc/germ existence
  one-offs" and "representation-only generality dictated by the twin file".  Rewritten around the
  theorems the file proves, with Hirsch, *Differential Topology*, Ch. 3, Ch. 4 §5 and Ch. 8, and
  Whitney, *Differentiable manifolds*, Thm 5, plus an outline and a `## Main results` list.
* docstrings added: 214 of 214 (the whole file).  Textbook references appear on
  `PlaneImmersion.dense_injective_immersive_parameters` (Whitney Thm 5 / Hirsch Ch. 3),
  `ManifoldImmersion.exists_open_injOn_of_injective_fderiv` (local immersion theorem, Hirsch
  Ch. 1), `exists_immersion_on_compact_rel`, `exists_relative_compact_embedding`,
  `exists_relative_compact_embedding_twoDimensional`,
  `exists_relative_compact_curve_embedding` (Hirsch Ch. 8),
  `exists_compact_embedding_of_immersion_within_target` (Hirsch Ch. 3),
  `NativeEuclideanEmbedding.exists_smooth_normalFrame_near_starConvex` and the
  `exists_*_tubularNeighborhood_of_embedded_starConvex` family (Hirsch Ch. 4 §5), and
  `MorseCancellation.exists_clean_two_sheet_arc` (Hirsch Ch. 8 / Milnor §6).
* universe pins, `: Type` binders: none counted for this file; none found.

### `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean` — `e5d2b172`
* citations: the module docstring advertised three declarations that live in
  `Morse/SurgeryCollapse.lean` and carried the migration receipt ("Moved verbatim from
  `Hopf/SphereTopology.lean` (base `304a0fea`); see `Lib/reports/integration-4/spheretop-moves.md`").
  Both were deleted; the docstring now groups the 17 declarations actually present and cites
  Milnor, *Lectures on the h-cobordism theorem*, §4 (Thm 4.1, Thm 4.8).
* docstrings added: 17 of 17.
* no universe pins or `: Type` binders were counted for this file.

### `Lib/Geometry/Manifold/Morse/CircleGluing.lean` — `aa15cc58`
* citations: the module docstring listed the seven historical families and carried the migration
  receipt ("Moved verbatim from the project stock file `Hopf/SingularHomology.lean` … the
  declarations keep their historical dotted names").  Both were deleted; the docstring now states
  the gluing theorem (two embedded arcs with matching endpoint germs glue to a smooth embedded
  circle) and what the rest of the file does.  The `## Twin` section now names `Circle`,
  `Circle.exp` and `Function.Periodic` instead of "No Mathlib counterpart exists".
* docstrings added: 56 of 56.
* `: Type` binder widened: 1 (`MorseCancellation.unitSphere_eq_two_points_of_finrank_one`,
  `{V : Type}` → `{V : Type*}`).

### `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean` — `166b73ce`
* citations: the module docstring was an inventory plus the migration receipt (same two sentences
  as `AdaptedWindows.lean`).  It now states the file's two subjects with their references: general
  position by a compactly supported ambient isotopy (Hirsch, *Differential Topology*, Ch. 3) and
  the weighted inversion count of Milnor's proof of Theorem 4.8.
* docstrings added: 35 of 35.
* `: Type` binders widened: 12 declarations — `sheetSum` (now `X : Type u` with a `universe u`
  line, so that its result type `ℕ → Type u` can follow), `sheetSumTopology`, `sheetSumCompact`,
  `sheetSumT2`, `sheetSumSecondCountable`, `sheetSumChartedSpace`, `sheetSumIsManifold`,
  `sheetSumMap`, `range_sheetSumMap`, `contMDiff_sheetSumMap`,
  `exists_sheetSumMap_for_finite_family`, `exists_whole_family_avoidance`.

## Builds

```
lake build Lib                                  → Build completed successfully (9150 jobs).   exit 0
lake build Solution S6Shortcuts S6 Challenge    → Build completed successfully (9189 jobs).   exit 0
lake build Lib.AxiomAudit                       → Build completed successfully (9150 jobs).   exit 0
```

`Lib.AxiomAudit` reports only the three permitted axioms; the set of axiom lists occurring in its
output is exactly

```
[propext, Classical.choice, Quot.sound]
[propext, Classical.choice]
[propext, Quot.sound]
[propext]
```

## Environment diff

```
python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_base.jsonl dump_after.jsonl --receipt envdiff.json
constants before 21719 after 21720 (keys 21713 21714)
lost 249 added 250 of which source declarations: 0 0
names with changed type 249 of which source: 129
auxiliary lost/added/changed (not judged): 249 250 120
module moves (source declarations, 1-to-1): 0 ; ambiguous module changes: 0
VERDICT PASS
```

**0 source declarations lost, 0 added.**  All 249 lost/added constants are auxiliary (equation
lemmas, `match` and proof-term auxiliaries regenerated by the recompilation).

### Changed types — all 129 explained

| group | count | explanation |
|---|---|---|
| `CategoryTheory.Sheaf.Leray.{AbelianSheaf, abelianSheafHasExt, pushforward}` | 3 | generalised to `universe u` in `ResolutionTransgression.lean` |
| `CategoryTheory.Sheaf.Leray.{presheafStalk_preservesFiniteLimits, presheafStalk_preservesFiniteColimits, underlyingPresheafComplex, homologyPresheaf, stalkHomologyPresheafIso, sheafification, sheafification_additive, sheafification_preservesFiniteLimits, sheafification_preservesFiniteColimits, sheafificationUnderlyingIso, sheafificationComplexIso, sheafHomologyIsoSheafification}` | 12 | generalised to `universe u` in `HigherDirectImageSheafification.lean` |
| `CategoryTheory.Sheaf.Leray.{presheafEvaluation, presheafEvaluation_additive, presheafEvaluation_preservesFiniteLimits, presheafEvaluation_preservesFiniteColimits, presheafPushforward, presheafPushforward_additive, presheafPushforward_preservesFiniteLimits, presheafPushforward_preservesFiniteColimits}` | 8 | generalised to `universe u` in `ResolutionCohomologyPresheaf.lean` |
| `CategoryTheory.Sheaf.Leray.stalkMap_bijective_of_local_lift_kill` | 1 | generalised to `universe u` in `StalkLocalCriterion.lean` |
| `CategoryTheory.Sheaf.Leray.E₂` | 1 | explicit `: Type` ascription dropped; the body now also mentions the universe-parametrised `pushforward` |
| the remaining `CategoryTheory.Sheaf.Leray.*` (91) | 91 | their types mention the now universe-parametrised `AbelianSheaf`, `pushforward`, `integralSheaf`, `homologyPresheaf`, `sheafification` or `presheafPushforward`, so the type is elaborated as `AbelianSheaf.{0} X` etc. and its hash changes; the type at level `0` is the same as before |
| `MorseRearrangement.{sheetSum, sheetSumTopology, sheetSumCompact, sheetSumT2, sheetSumSecondCountable, sheetSumChartedSpace, sheetSumIsManifold, sheetSumMap, range_sheetSumMap, contMDiff_sheetSumMap, exists_sheetSumMap_for_finite_family, exists_whole_family_avoidance}` | 12 | `: Type` binders widened to `Type*` / `Type u` in `RearrangementAmbient.lean` |
| `MorseCancellation.unitSphere_eq_two_points_of_finrank_one` | 1 | `{V : Type}` widened to `{V : Type*}` in `CircleGluing.lean` |

The 91 declarations of the sixth row, listed in full for the record:

```
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ResolutionCohomologyNormalization
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.canonicalDerivedNeighborhoodGermPositive
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.canonicalDerivedNeighborhoodSectionPositive
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.canonicalDerivedNeighborhoodSectionPositive_comp_germ
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.canonicalDerivedStalkEvaluationPositive
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.canonicalDerivedStalkEvaluation_germPositive
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.canonicalDerivedStalkEvaluation_isIso_of_cofinal_bijectivePositive
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.canonicalDerivedStalkEvaluation_isIso_of_local_lift_killPositive
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.canonicalDerivedStalkIsoPositive
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.canonicalResolutionCohomologyNormalizationPositive
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.derivedNeighborhoodGerm
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.derivedStalkEvaluation
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.derivedStalkEvaluation_germ
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.derivedStalkEvaluation_isIso_of_local_lift_kill
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.derivedStalkIso
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.evaluationCocone
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.presheafStalkEvaluation
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.presheafStalkEvaluation_bijective_of_local_lift_kill
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.presheafStalkEvaluation_germ
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.sourceCohomologyPresheaf
CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.sourceResolutionPresheaf
CategoryTheory.Sheaf.Leray.derivedNeighborhoodGerm_eq_germ_of_localRepresentative
CategoryTheory.Sheaf.Leray.evaluationHomologyIso_hom_naturality_open
CategoryTheory.Sheaf.Leray.evaluationHomologyIso_hom_naturality_open_assoc
CategoryTheory.Sheaf.Leray.higherDirectImage
CategoryTheory.Sheaf.Leray.higherDirectImageResolutionIso
CategoryTheory.Sheaf.Leray.higherDirectImageResolutionPresheafObjIso
CategoryTheory.Sheaf.Leray.higherDirectImageResolutionSheafificationIso
CategoryTheory.Sheaf.Leray.higherDirectImageResolutionSheafificationStalkIso
CategoryTheory.Sheaf.Leray.higherDirectImageResolutionSheafificationStalkIso_eq
CategoryTheory.Sheaf.Leray.higherDirectImageResolutionStalkIso
CategoryTheory.Sheaf.Leray.higherDirectImageSheaf
CategoryTheory.Sheaf.Leray.homSectionsHomologyIso
CategoryTheory.Sheaf.Leray.homSectionsHomologyIso_hom_naturality_open
CategoryTheory.Sheaf.Leray.homSectionsHomologyIso_hom_naturality_open_assoc
CategoryTheory.Sheaf.Leray.homologyPresheafPushforwardIso
CategoryTheory.Sheaf.Leray.integralCoyonedaPushforwardHomologyIso
CategoryTheory.Sheaf.Leray.integralCoyonedaPushforwardIso
CategoryTheory.Sheaf.Leray.integralDerivedObject
CategoryTheory.Sheaf.Leray.integralDerivedObject_isLE
CategoryTheory.Sheaf.Leray.integralSheaf
CategoryTheory.Sheaf.Leray.inverseImageResolutionSections
CategoryTheory.Sheaf.Leray.mapComplexHomologyIso_sheafification_stalk_comp
CategoryTheory.Sheaf.Leray.mappedExtendedResolution
CategoryTheory.Sheaf.Leray.mappedExtendedResolutionIso
CategoryTheory.Sheaf.Leray.mappedExtendedResolution_isKInjective
CategoryTheory.Sheaf.Leray.pushedResolution
CategoryTheory.Sheaf.Leray.pushedResolutionCohomologyPresheafIsoPositive
CategoryTheory.Sheaf.Leray.pushedResolutionDerivedObject
CategoryTheory.Sheaf.Leray.pushedResolutionDerivedObjectHomologyHigherDirectImageIso
CategoryTheory.Sheaf.Leray.pushedResolutionDerivedObjectHomologyIso
CategoryTheory.Sheaf.Leray.pushedResolutionDerivedObject_isGE
CategoryTheory.Sheaf.Leray.pushforwardAdditive
CategoryTheory.Sheaf.Leray.pushforwardPreservesInjectiveObjects
CategoryTheory.Sheaf.Leray.representedHomologyPresheafIso
CategoryTheory.Sheaf.Leray.resolutionCohomologyIso
CategoryTheory.Sheaf.Leray.resolutionCohomologyIso_hom_apply
CategoryTheory.Sheaf.Leray.resolutionCohomologyIso_inv_apply
CategoryTheory.Sheaf.Leray.resolutionCohomologyPresheafIsoPositive
CategoryTheory.Sheaf.Leray.resolutionDerivedHomCohomologyEquiv
CategoryTheory.Sheaf.Leray.resolutionExtZeroIso
CategoryTheory.Sheaf.Leray.resolutionExtZeroIso_hom_apply
CategoryTheory.Sheaf.Leray.resolutionExtZeroIso_inv_apply
CategoryTheory.Sheaf.Leray.resolutionPostnikovE₂AddEquiv
CategoryTheory.Sheaf.Leray.resolutionPostnikovE₂AddEquiv_source_coordinate
CategoryTheory.Sheaf.Leray.resolutionPostnikovE₂AddEquiv_target_coordinate
CategoryTheory.Sheaf.Leray.resolutionPostnikovE₂Iso
CategoryTheory.Sheaf.Leray.resolutionPostnikovE₂PageIso
CategoryTheory.Sheaf.Leray.resolutionPostnikovE₂_d₂_eq
CategoryTheory.Sheaf.Leray.resolutionPostnikovE₂_d₂_eq_transgression
CategoryTheory.Sheaf.Leray.resolutionPostnikovShiftedSliceHigherDirectImageIso
CategoryTheory.Sheaf.Leray.resolutionPostnikovSliceHigherDirectImageIso
CategoryTheory.Sheaf.Leray.resolutionPostnikovSpectralObject
CategoryTheory.Sheaf.Leray.resolutionPostnikovSpectralSequence
CategoryTheory.Sheaf.Leray.resolutionPostnikovTotalCohomologyEquiv
CategoryTheory.Sheaf.Leray.resolutionPostnikovTotalIso
CategoryTheory.Sheaf.Leray.resolutionTransgression
CategoryTheory.Sheaf.Leray.resolutionTransgressionAdd
CategoryTheory.Sheaf.Leray.resolutionTransgressionAddOfResolution
CategoryTheory.Sheaf.Leray.resolutionTransgressionAddOfResolution_apply_eq_connectingTwo
CategoryTheory.Sheaf.Leray.resolutionTransgressionAddOfResolution_apply_ne_zero_iff_connectingTwo
CategoryTheory.Sheaf.Leray.resolutionTransgressionMorphism
CategoryTheory.Sheaf.Leray.resolutionTransgressionMorphismOfResolution
CategoryTheory.Sheaf.Leray.resolutionTransgressionMorphismOfResolution_eq_connectingTwo
CategoryTheory.Sheaf.Leray.resolutionTransgressionOfResolution
CategoryTheory.Sheaf.Leray.resolutionTransgression_apply_ne_zero_iff_connectingTwo
CategoryTheory.Sheaf.Leray.sheafCohomologyAddCommGroup
CategoryTheory.Sheaf.Leray.sheafificationComplexIso_symm_hom_underlying
CategoryTheory.Sheaf.Leray.stalkHomologyPresheafIso_hom_comp_sheafificationUnit
CategoryTheory.Sheaf.Leray.stalkSheafificationUnitNatTrans
CategoryTheory.Sheaf.Leray.stalkSheafificationUnitNatTrans_app
```

No changed type is unexplained.

## Commits (base `9552305f`, one file each, in order)

| hash | file |
|---|---|
| `ecb8f370` | `Lib/CategoryTheory/Sites/Leray/StalkLocalCriterion.lean` |
| `f665c883` | `Lib/CategoryTheory/Triangulated/CoyonedaTriangleShift.lean` |
| `7c5050a3` | `Lib/CategoryTheory/Sites/Leray/ResolutionTransgression.lean` |
| `cff67f3d` | `Lib/CategoryTheory/Sites/Leray/HigherDirectImageSheafification.lean` |
| `3ba7c621` | `Lib/CategoryTheory/Sites/Leray/ResolutionCohomologyPresheaf.lean` |
| `1e627efd` | `Lib/CategoryTheory/Sites/Leray/ResolutionAbutment.lean` |
| `c423ff18` | `Lib/CategoryTheory/Sites/Leray/ResolutionPostnikov.lean` |
| `1de5b691` | `Lib/CategoryTheory/Sites/Leray/ResolutionPostnikovD2.lean` |
| `4799e6be` | `Lib/CategoryTheory/Sites/Leray/ResolutionPostnikovD2Transgression.lean` |
| `2a72bf6a` | `Lib/CategoryTheory/Sites/Leray/ResolutionPostnikovD2Coordinates.lean` |
| `f8b80d15` | `Lib/CategoryTheory/Sites/Leray/FibreStalkEvaluation/OpenRestrictionComposition.lean` |
| `9e06b8e0` | `Lib/CategoryTheory/Sites/Leray/FibreStalkEvaluation/Stalk.lean` |
| `bdf9778a` | `Lib/CategoryTheory/Sites/Leray/SheafificationStalkCompatibility.lean` |
| `a68150ea` | `Lib/CategoryTheory/Sites/Leray/SheafificationNeighborhoodGerm.lean` |
| `e5d2b172` | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean` |
| `166b73ce` | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean` |
| `aa15cc58` | `Lib/Geometry/Manifold/Morse/CircleGluing.lean` |
| `7dd9dcbd` | `Lib/Geometry/Manifold/Immersion/Relative.lean` |

Files left: none.
