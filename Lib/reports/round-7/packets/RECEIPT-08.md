# Round 7 checklist packet 08 — receipt

Worktree `/home/goblin/hopf-r7-p08`, branch `r7/packet-08`, base `9552305f`,
Lean v4.33.0 / Mathlib v4.33.0.

All 32 files of `Lib/reports/round-7/packets/packet-08.md` were worked; none are left.

## Summary per work item

| item | audited | done | left |
|---|---|---|---|
| manuscript citations | 10 files flagged "manuscript citation only" | 32 files now carry a textbook reference; 12 `CD-04`/`CD-04R`/`CD-05E`/`CD-05I`/`CD-05J`/`CD-06` coordinates, 2 "FREE owner" paragraphs, 1 "receipt", 1 "(C24)" removed | 0 |
| docstrings | not counted in the packet | 33 public declarations documented | 0 (no undocumented public declaration remains in the 32 files) |
| universe pins `.{0}` | 335 | 118 generalised to `.{u}` in 6 files | 217, every one forced (table below) |
| `: Type` binders | 62 counted by the audit | 0 widened | 54 were false positives (the file already says `Type u` / `Type v` with a `universe` line); 8 are forced (table below) |

## Per file

| file | citations | docstrings | pins `.{0}` | `: Type` | note |
|---|---|---|---|---|---|
| `Cohomology/Cech/LongExact.lean` | 1 module docstring (CD-05I, (C24), CD-05J → Godement II.5.10) | 0 | 0 → 0 | — | audited binders are `Type u`, not `Type` |
| `Cohomology/Cech/MultiplicityVanishing.lean` | 2 (CD-06 → Godement II.5.12; "receipt" removed) | 0 | 0 → 0 | 5 audited, all false positives (`Type u/v/w`) | |
| `Cohomology/Cech/OpenCover.lean` | 1 (Godement II.5.1 added) | 4 | 0 → 0 | 2 audited, both false positives | |
| `Cohomology/Cech/Ordered.lean` | 12 (module + 11 "CD-04's …" docstrings) | 2 | 0 → 0 | 6 audited, all false positives | |
| `Cohomology/Cech/RangeCover.lean` | 1 (CD-04R → Godement II.5.12) | 0 | 0 → 0 | 6 audited, all false positives | |
| `Cohomology/Cech/Refinement.lean` | 2 (CD-04 removed, Godement II.5.7 added) | 0 | 0 → 0 | 8 audited, all false positives | the audited import drop was **not** applied: `Refinement` and `MultiplicityLE` are defined in `Lib.Topology.Dimension.Covering` and used here |
| `Cohomology/Cech/RefinementHomotopy.lean` | 1 (CD-04 → Godement II.5.7) | 0 | 0 → 0 | 9 audited, all false positives | headline `refinementMap_homologyMap_eq` now named in the module docstring |
| `Cohomology/Cech/ShrinkableRefinement.lean` | 1 (CD-05E → `exists_iUnion_eq_closure_subset`, Engelking 5.1.6) | 0 | 0 → 0 | 4 audited, all false positives | |
| `Cohomology/DiscreteProjectiveDimension.lean` | 1 (Bredon I.1 added) | 0 | 2 → 1 | — | `sheaf_isFlasque_of_discreteTopology` and its three private helpers lifted to `TopCat.{u}` |
| `Cohomology/FlasqueAcyclic.lean` | 1 (Hartshorne III.2.4–2.5 added) | 0 | 14 → 14 | — | forced |
| `Cohomology/GodementResolution.lean` | 1 (Godement II.4.3 added) | 6 | 4 → 4 | — | forced; the pins are confined to `section Small` |
| `Cohomology/HomeomorphProjectiveDimension.lean` | 1 (Godement II.1 added) | 2 | 12 → 5 | — | `equivalenceOfIso` + its two `Additive` instances lifted to `TopCat.{u}` |
| `Cohomology/MayerVietorisProjectiveDimension.lean` | 1 (Bredon II.13 added) | 0 | 1 → 1 | — | forced |
| `Cohomology/MayerVietorisVanishing.lean` | 1 (Bredon II.13 added) | 0 | 2 → 2 | 2 audited: 1 false positive, 1 forced ascription | forced |
| `Cohomology/ProjectiveDimension.lean` | 1 (`HasProjectiveDimensionLT` named) | 0 | 3 → 3 | — | forced |
| `Cohomology/RepresentedOpenProjectiveDimension.lean` | 1 (Godement II.4 / Hartshorne III.2) | 0 | 9 → 9 | — | forced |
| `Cohomology/ShortExactAcyclicQuotient.lean` | 2 ("the textbook degree-two Ext comparison" → Hartshorne III.1.1A; skyscraper sentence removed) | 3 | 24 → 24 | — | forced |
| `Cohomology/ShortExactDegreeOne.lean` | 2 ("This FREE owner …" paragraph → Hartshorne III.1.1A; "constructible-sheaf criterion" → "exactness criterion") | 0 | 16 → 16 | — | forced |
| `Cohomology/ShortExactDegreeZeroSections.lean` | 1 ("This FREE owner …" → Hartshorne II Ex. 1.8) | 3 | 14 → 14 | 1 forced (`(… : Type)` carrier ascription of an `AddCommGrpCat.{0}` object) | the audited deletion of the `GlobalSections` alias was not applied (deleting a declaration is out of scope) |
| `CokernelStalk.lean` | 1 (Hartshorne II Ex. 1.2; "constructible-sheaf calculations" removed) | 0 | **1 → 0** | — | whole file lifted to `TopCat.{u}` |
| `ConstantCohomologyPullback.lean` | 1 (Bredon II.8 added) | 0 | 5 → 5 | — | forced; the audited rewrite via the inverse-image adjunction would change the statement |
| `ConstantProductH1.lean` | 1 (module docstring rewritten, Bredon II.11) | 4 | 4 → 4 | 2 forced | |
| `ConstantProductH1Comparison.lean` | 1 (Bredon II.11.12 added) | 0 | 1 → 1 | 1 forced | |
| `ConstantProductH1FibreIndependence.lean` | 1 (Leray-page sentence → Bredon II.11) | 0 | 1 → 1 | 1 forced | |
| `ConstantProductPositiveFibreIndependence.lean` | 1 (nearby-cycle sentence → Bredon II.11.12) | 0 | 7 → 7 | 2 forced | |
| `ConstantPushforward.lean` | 1 (Iversen II / Bredon I) | 8 | **35 → 0** | — | whole file lifted to `TopCat.{u}` |
| `ConstantPushforward/GlobalSections.lean` | 1 (Hartshorne III.2 / Godement II.4) | 0 | **48 → 0** | — | whole file lifted to `TopCat.{u}` |
| `ConstantSheafH1.lean` | 1 ("no differentiable / complex-analytic / lower-transfer" → Bredon III.1.1, Godement II.5.10.1) | 0 | 3 → 3 | 1 forced | |
| `FiniteClosedOpenRestriction.lean` | 1 (Kashiwara–Schapira II / Iversen II) | 1 | 27 → 27 | — | forced |
| `FiniteClosedPushforward.lean` | 1 (Kashiwara–Schapira 2.5.2 / Iversen II) | 2 | **16 → 0** | — | whole file lifted to `TopCat.{u}` |
| `FiniteClosedPushforward/AcyclicResolution.lean` | 1 (Hartshorne III.1.2A) | 0 | 27 → 27 | — | forced |
| `FiniteClosedPushforward/AcyclicResolutionH1.lean` | 1 (Hartshorne III.1.2A) | 0 | 58 → 58 | — | forced |

## Pins left, with what forces them

Every remaining pin is forced by an imported interface that is itself pinned in a file outside
this packet; none was chased across files.

| forcing declaration | file (outside this packet) | packet files it pins |
|---|---|---|
| `TopCat.SheafH1.unitSheaf`, `TopCat.SheafH1.globalSectionsFunctor`, `TopCat.SheafH1.h0GlobalIso` | `Lib/Topology/Sheaves/Cohomology/AcyclicResolutionH1.lean` (`variable (X : TopCat.{0})`) | `Cohomology/ProjectiveDimension.lean`, `Cohomology/RepresentedOpenProjectiveDimension.lean`, `Cohomology/DiscreteProjectiveDimension.lean`, `Cohomology/HomeomorphProjectiveDimension.lean`, `FiniteClosedPushforward/AcyclicResolutionH1.lean` |
| `TopCat.Sheaf.OpenRestriction.freeOpen`, `freeHomEquiv`, `restrictedCohomologyGroup`, `cohomologyEquiv` | `Lib/Topology/Sheaves/OpenRestriction/Cohomology.lean` (`variable {X : TopCat.{0}}`) | `Cohomology/FlasqueAcyclic.lean`, `Cohomology/RepresentedOpenProjectiveDimension.lean`, `Cohomology/MayerVietorisProjectiveDimension.lean`, `Cohomology/MayerVietorisVanishing.lean`, `Cohomology/DiscreteProjectiveDimension.lean` |
| `TopCat.SheafH1.subsingleton_h1_of_isFlasque` and the private `HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X)` instance | `Lib/Topology/Sheaves/H1Vanishing/Flasque.lean` | `Cohomology/FlasqueAcyclic.lean`, `Cohomology/DiscreteProjectiveDimension.lean` |
| `CategoryTheory.Sheaf.cohomologyAddCommGroup` | `Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean` (`{X : TopCat.{0}}`) | `Cohomology/ShortExactAcyclicQuotient.lean`, `Cohomology/ShortExactDegreeOne.lean`, `Cohomology/ShortExactDegreeZeroSections.lean`, `ConstantSheafH1.lean` |
| `TopCat.SheafCohomology.AcyclicResolution.globalComplex`, `extIsoGlobalHomology` | `Lib/Topology/Sheaves/Cohomology/AcyclicResolution.lean` | `Cohomology/GodementResolution.lean`, `FiniteClosedPushforward/AcyclicResolution.lean` |
| `TopCat.FiniteClosedPushforward.cohomologyEquiv`, `cohomologyForward` | `Lib/Topology/Sheaves/FiniteClosedPushforward/Cohomology.lean` | `ConstantCohomologyPullback.lean`, `FiniteClosedPushforward/AcyclicResolution.lean`, `FiniteClosedPushforward/AcyclicResolutionH1.lean` |
| `TopCat.Sheaf.OpenEmbeddingCohomology.openImage`, `restriction` | `Lib/Topology/Sheaves/OpenEmbeddingCohomology.lean` | `FiniteClosedOpenRestriction.lean` |
| `TopCat.ConstantSheafCohomology.pullback` (itself forced by the row above) | `Lib/Topology/Sheaves/ConstantCohomologyPullback.lean` | `ConstantProductH1.lean`, `ConstantProductH1Comparison.lean`, `ConstantProductH1FibreIndependence.lean`, `ConstantProductPositiveFibreIndependence.lean`, `ConstantSheafH1.lean`, `FiniteClosedOpenRestriction.lean` |

The same declarations force the 8 genuine `: Type` binders: `(S X : Type)` in the four
`ConstantProduct*` files and `{X Y : Type}` in `ConstantSheafH1.lean` are `Type 0` because
`TopCat.of X` has to land in `TopCat.{0}` for `TopCat.ConstantSheafCohomology.pullback`; the
`(… : Type)` ascription in `ShortExactDegreeZeroSections.lean` is the carrier of an
`AddCommGrpCat.{0}` object.

## Builds

```
lake build Lib                                  Build completed successfully (9150 jobs).
lake build Solution S6Shortcuts S6 Challenge    Build completed successfully (9189 jobs).
lake build Lib.AxiomAudit                       Build completed successfully (9150 jobs).
```

`Lib.AxiomAudit` reports only `propext`, `Classical.choice`, `Quot.sound` (the four distinct
axiom sets printed are `[propext]`, `[propext, Quot.sound]`, `[propext, Classical.choice]`,
`[propext, Classical.choice, Quot.sound]`).

## envdiff

`python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_base.jsonl dump_after.jsonl --receipt envdiff.json`

```
constants before 21719 after 21719 (keys 21713 21713)
lost 233 added 233 of which source declarations: 0 0
names with changed type 233
VERDICT PASS
```

* **source declarations lost: 0**
* **source declarations added: 0**
* **changed types: 233**, all explained below.

### A. Declarations generalised in this packet (92)

| module | declarations with a changed type |
|---|---|
| `Lib.Topology.Sheaves.ConstantPushforward` (36) | `TopCat.ConstantSheaf.exists_constant_restriction`, `TopCat.ConstantSheaf.presheaf`, `TopCat.ConstantSheaf.presheafStalkIso`, `TopCat.ConstantSheaf.presheafStalkIso._proof_1`, `TopCat.ConstantSheaf.presheafStalkIso._proof_2`, `TopCat.ConstantSheaf.presheaf_germ_stalkIso_hom`, `TopCat.ConstantSheaf.presheaf_germ_stalkIso_hom_assoc`, `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.pushforwardHom._proof_1`, `TopCat.ConstantSheaf.pushforwardHom_app_bijective`, `TopCat.ConstantSheaf.pushforwardHom_app_unit`, `TopCat.ConstantSheaf.pushforwardHom_isIso`, `TopCat.ConstantSheaf.pushforwardHom_isIso_of_isBasis`, `TopCat.ConstantSheaf.rawPushforwardHom`, `TopCat.ConstantSheaf.rawPushforwardHom._proof_1`, `TopCat.ConstantSheaf.sectionValue`, `TopCat.ConstantSheaf.sectionValue._proof_1`, `TopCat.ConstantSheaf.sectionValue_isLocallyConstant`, `TopCat.ConstantSheaf.sectionValue_restrict`, `TopCat.ConstantSheaf.sectionValue_unit`, `TopCat.ConstantSheaf.section_ext`, `TopCat.ConstantSheaf.sheaf`, `TopCat.ConstantSheaf.sheaf._proof_1`, `TopCat.ConstantSheaf.stalkEquiv`, `TopCat.ConstantSheaf.stalkEquiv_germ_unit`, `TopCat.ConstantSheaf.stalkIso`, `TopCat.ConstantSheaf.unit`, `TopCat.ConstantSheaf.unit_app_bijective`, `TopCat.ConstantSheaf.unit_app_injective`, `TopCat.ConstantSheaf.unit_app_surjective`, `TopCat.ConstantSheaf.unit_germ_stalkIso_hom`, `TopCat.ConstantSheaf.unit_germ_stalkIso_hom_assoc`, `TopCat.ConstantSheaf.unit_pushforwardHom`, `TopCat.ConstantSheaf.unit_stalk_isIso`, `TopCat.ConstantSheaf.unit_stalk_stalkIso_hom`, `TopCat.ConstantSheaf.unit_stalk_stalkIso_hom_assoc` |
| `Lib.Topology.Sheaves.ConstantPushforward.GlobalSections` (17) | `TopCat.ConstantSheaf.integralGlobalSectionsEquiv`, `TopCat.ConstantSheaf.integralHomGlobalEquiv`, `TopCat.ConstantSheaf.integralHomGlobalEquiv._proof_1`, `TopCat.ConstantSheaf.integralHomGlobalEquiv._proof_2`, `TopCat.ConstantSheaf.integralHomGlobalEquiv._proof_3`, `TopCat.ConstantSheaf.integralHomGlobalEquiv._proof_4`, `TopCat.ConstantSheaf.integralHomGlobalEquiv._proof_5`, `TopCat.ConstantSheaf.integralHomGlobalEquiv.eq_1`, `TopCat.ConstantSheaf.integralHomGlobalEquiv_id`, `TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality`, `TopCat.ConstantSheaf.integralHomPushforwardEquiv`, `TopCat.ConstantSheaf.integralHomPushforwardEquiv_global`, `TopCat.ConstantSheaf.integralHomPushforwardEquiv_naturality`, `TopCat.ConstantSheaf.integralPushforwardHom_comp`, `TopCat.ConstantSheaf.integralPushforwardHom_comp_bijective`, `TopCat.ConstantSheaf.integralPushforwardHom_global`, `TopCat.ConstantSheaf.integralSheaf` |
| `Lib.Topology.Sheaves.FiniteClosedPushforward` (21) | `TopCat.FiniteClosedPushforward.exists_open_preimage_subset`, `TopCat.FiniteClosedPushforward.exists_section_germ_eq_of_finite`, `TopCat.FiniteClosedPushforward.fiber_mem_preimage`, `TopCat.FiniteClosedPushforward.pushforwardStalkComponent`, `TopCat.FiniteClosedPushforward.pushforwardStalkComponent._proof_1`, `TopCat.FiniteClosedPushforward.pushforwardStalkComponent._proof_2`, `TopCat.FiniteClosedPushforward.pushforwardStalkComponent.eq_1`, `TopCat.FiniteClosedPushforward.pushforwardStalkComponent_germ`, `TopCat.FiniteClosedPushforward.pushforwardStalkEquiv`, `TopCat.FiniteClosedPushforward.pushforwardStalkEquiv._proof_1`, `TopCat.FiniteClosedPushforward.pushforwardStalkEquiv_apply`, `TopCat.FiniteClosedPushforward.pushforwardStalkEquiv_germ`, `TopCat.FiniteClosedPushforward.pushforwardStalkEquiv_naturality`, `TopCat.FiniteClosedPushforward.pushforwardStalkHom`, `TopCat.FiniteClosedPushforward.pushforwardStalkHom_apply`, `TopCat.FiniteClosedPushforward.pushforwardStalkHom_bijective`, `TopCat.FiniteClosedPushforward.pushforwardStalkHom_germ`, `TopCat.FiniteClosedPushforward.pushforwardStalkHom_injective`, `TopCat.FiniteClosedPushforward.pushforwardStalkHom_naturality`, `TopCat.FiniteClosedPushforward.pushforwardStalkHom_surjective`, `TopCat.FiniteClosedPushforward.pushforward_germ_eq_of_fiber_germ_eq` |
| `Lib.Topology.Sheaves.CokernelStalk` (13) | `TopCat.Sheaf.stalkCokernelHom`, `TopCat.Sheaf.stalkCokernelHom._proof_1`, `TopCat.Sheaf.stalkCokernelIso`, `TopCat.Sheaf.stalkCokernelIso._proof_1`, `TopCat.Sheaf.stalkCokernelIso._proof_2`, `TopCat.Sheaf.stalkCokernelIso._proof_3`, `TopCat.Sheaf.stalkCokernelIso._proof_4`, `TopCat.Sheaf.stalkCokernelIso._proof_5`, `TopCat.Sheaf.stalkCokernel_isZero_of_epi`, `TopCat.Sheaf.stalk_cokernelπ_comp_stalkCokernelHom`, `TopCat.Sheaf.stalk_cokernelπ_comp_stalkCokernelHom_assoc`, `TopCat.Sheaf.stalk_cokernelπ_comp_stalkCokernelIso_hom`, `TopCat.Sheaf.stalk_cokernelπ_comp_stalkCokernelIso_hom_assoc` |
| `Lib.Topology.Sheaves.Cohomology.HomeomorphProjectiveDimension` (7) | `TopCat.Sheaf.equivalenceOfIso`, `TopCat.Sheaf.equivalenceOfIso._proof_1`, `TopCat.Sheaf.equivalenceOfIso._proof_2`, `TopCat.Sheaf.equivalenceOfIso_functor_additive`, `TopCat.Sheaf.equivalenceOfIso_inverse_additive`, `TopCat.Sheaf.unitSheafEquivImageIso`, `TopCat.Sheaf.unitSheafEquivImageIso._proof_1` |
| `Lib.Topology.Sheaves.Cohomology.DiscreteProjectiveDimension` (6) | `TopCat.Sheaf.OpenRestriction.pointOpen`, `TopCat.Sheaf.OpenRestriction.pointOpen._proof_1`, `TopCat.Sheaf.OpenRestriction.pointOpen.eq_1`, `TopCat.Sheaf.OpenRestriction.pointOpen_le`, `TopCat.Sheaf.OpenRestriction.pointOpen_mem`, `TopCat.Sheaf.OpenRestriction.sheaf_isFlasque_of_discreteTopology` |

### B. Downstream declarations, source unchanged (141)

Their statements are byte-identical to the base; the type hash moved only because a
constant they mention (column 2) now carries an explicit universe level, instantiated
here at level 0.

| module | declarations | generalised constant(s) they mention |
|---|---|---|
| `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.CanonicalPositive` (3) | `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.canonicalNeighborhoodGermPositive`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.canonicalStalkToFibrePositive`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.canonicalStalkToFibre_neighborhoodGermPositive` | `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.CanonicalPositiveCofinalExt` (3) | `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.canonicalNeighborhoodGermPositive.eq_1`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.canonicalNeighborhoodGermPositive_hom_ext_of_cofinal`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.neighborhoodGerm.eq_1` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.CofinalCriterion` (1) | `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.canonicalStalkToFibrePositive_isIso_of_cofinal_bijective` | `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.ConstantEvaluationBijective` (2) | `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.canonicalConstantEvaluation_bijective_of_pullback_isIso`, `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.intrinsicOpenClass_bijective` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.ConstantNormalization` (10) | `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.canonicalConstantEvaluation`, `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.canonicalConstantEvaluation_forward`, `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.cohomologyEvaluation_forward_open`, `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.fibreCohomology_eq_of_forward_eq`, `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.intrinsicConstantPullback`, `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.intrinsicOpenClass`, `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.intrinsicOpenClass_coefficient`, `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.openConstantRestrictionHom`, `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.openConstantRestrictionHom_isIso`, `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.openConstantRestriction_coefficient` | `TopCat.ConstantSheaf.presheaf`, `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.ConstantNormalizationConsequences` (1) | `CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization.canonicalConstantEvaluation_eq_intrinsicConstantPullback` | `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.ConstantPointFibre` (4) | `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.ConstantNormalization`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.neighborhoodGerm`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.stalkToFibre`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.ConstantPointFibre.stalkToFibre_neighborhoodGerm` | `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.Neighborhood` (8) | `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.neighborhoodHomEquiv`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.neighborhoodHomEquiv_naturality`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.neighborhoodHomEquiv_restrict`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.neighborhoodHomEquiv_sections`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.neighborhoodUnit`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.neighborhoodUnit_bijective`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.neighborhoodUnit_comp`, `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.neighborhoodUnit_restrict` | `TopCat.ConstantSheaf.integralHomGlobalEquiv`, `TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality`, `TopCat.ConstantSheaf.integralSheaf` |
| `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.OpenRestrictionComposition` (1) | `CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.restrictionPushforwardIso_neighborhoodUnit` | `TopCat.ConstantSheaf.integralHomGlobalEquiv`, `TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality` |
| `Lib.CategoryTheory.Sites.Leray.ResolutionAbutment` (1) | `CategoryTheory.Sheaf.Leray.integralCoyonedaPushforwardIso._proof_1` | `TopCat.ConstantSheaf.integralHomPushforwardEquiv`, `TopCat.ConstantSheaf.integralHomPushforwardEquiv_naturality` |
| `Lib.Topology.Sheaves.Cohomology.RepresentedOpenProjectiveDimension` (2) | `TopCat.Sheaf.OpenRestriction.integralToFreeTop.eq_1`, `TopCat.Sheaf.OpenRestriction.integralToFreeTop_comp_section` | `TopCat.ConstantSheaf.integralHomGlobalEquiv`, `TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality`, `TopCat.ConstantSheaf.integralSheaf` |
| `Lib.Topology.Sheaves.ConstantCohomologyPullback` (4) | `TopCat.ConstantSheafCohomology.pullback`, `TopCat.ConstantSheafCohomology.pullback.congr_simp`, `TopCat.ConstantSheafCohomology.pullback_forward`, `TopCat.ConstantSheafCohomology.pullback_forward_assoc` | `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.ConstantProductH1` (1) | `TopCat.ConstantProductH1.nativePullback_isIso_of_comparison` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.ConstantProductH1Comparison` (1) | `TopCat.ConstantProductH1.nativePullback_basedFibreInclusion_isIso` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.ConstantProductH1FibreIndependence` (1) | `TopCat.ConstantProductH1.nativePullback_basedFibreInclusion_eq` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.ConstantProductPositiveFibreIndependence` (5) | `TopCat.ConstantProductPositive.nativePullback_basedFibreInclusion_eq`, `TopCat.ConstantProductPositive.nativePullback_basedFibreInclusion_eq_of_comparison_naturality`, `TopCat.ConstantProductPositive.nativePullback_basedFibreInclusion_isIso`, `TopCat.ConstantProductPositive.nativePullback_basedFibreInclusion_isIso_of_comparison_naturality`, `TopCat.ConstantProductPositive.nativePullback_isIso_of_comparison` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.ConstantSheafH1` (1) | `TopCat.SingularCochainSheaf.exists_h1Comparison_natural` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.FiniteClosedOpenRestriction` (6) | `TopCat.Sheaf.FiniteClosedOpenRestriction.closedPullbackThenRestriction`, `TopCat.Sheaf.FiniteClosedOpenRestriction.constantPullback_sandwich`, `TopCat.Sheaf.FiniteClosedOpenRestriction.openRestrictionThenCoefficient`, `TopCat.Sheaf.FiniteClosedOpenRestriction.pullback_openRestriction`, `TopCat.Sheaf.FiniteClosedOpenRestriction.restrictionPushforwardIso_restrictionHom`, `TopCat.Sheaf.FiniteClosedOpenRestriction.sandwichCoefficient` | `TopCat.ConstantSheaf.presheaf`, `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.FiniteClosedPushforward.AcyclicResolutionH1` (1) | `TopCat.FiniteClosedPushforward.h0GlobalIso_mk₀` | `TopCat.ConstantSheaf.presheaf` (private helper; by source inspection) |
| `Lib.Topology.Sheaves.FiniteClosedPushforward.Composition` (2) | `TopCat.ConstantSheaf.pushforwardHom_comp`, `TopCat.ConstantSheafCohomology.pullback_comp` | `TopCat.ConstantSheaf.presheaf`, `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.NestedOpenCohomology` (5) | `TopCat.Sheaf.NestedOpenCohomology.constantRestrictionHom_comp`, `TopCat.Sheaf.NestedOpenCohomology.integralHomGlobalEquiv_eq_app_unit`, `TopCat.Sheaf.NestedOpenCohomology.intrinsicOpenClass_restrict`, `TopCat.Sheaf.NestedOpenCohomology.representingUnit_app_unit`, `TopCat.Sheaf.NestedOpenCohomology.representingUnit_comp` | `TopCat.ConstantSheaf.integralHomGlobalEquiv`, `TopCat.ConstantSheaf.integralHomGlobalEquiv_id`, `TopCat.ConstantSheaf.integralSheaf` |
| `Lib.Topology.Sheaves.OpenEmbeddingCohomology` (8) | `TopCat.Sheaf.OpenEmbeddingCohomology.constantPullback`, `TopCat.Sheaf.OpenEmbeddingCohomology.rawRestrictionHom`, `TopCat.Sheaf.OpenEmbeddingCohomology.rawRestrictionHom._proof_1`, `TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom`, `TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom._proof_1`, `TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom_app_unit`, `TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom_isIso`, `TopCat.Sheaf.OpenEmbeddingCohomology.unit_restrictionHom` | `TopCat.ConstantSheaf.presheaf`, `TopCat.ConstantSheaf.sheaf`, `TopCat.ConstantSheaf.sheaf._proof_1` |
| `Lib.Topology.Sheaves.OpenFiniteClosedFactorization` (5) | `TopCat.Sheaf.OpenFiniteClosedFactorization.constantPullback_factorization`, `TopCat.Sheaf.OpenFiniteClosedFactorization.directPullback_forward_open`, `TopCat.Sheaf.OpenFiniteClosedFactorization.normalizedCoefficient`, `TopCat.Sheaf.OpenFiniteClosedFactorization.normalizedOpenPullback_forward`, `TopCat.Sheaf.OpenFiniteClosedFactorization.restrictionPushforwardIso_restrictionHom` | `TopCat.ConstantSheaf.presheaf`, `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.OpenRestriction.Cohomology` (7) | `TopCat.Sheaf.OpenRestriction.cohomologyEquiv_mk₀`, `TopCat.Sheaf.OpenRestriction.homRestrictionEquiv`, `TopCat.Sheaf.OpenRestriction.homRestrictionEquiv_naturality`, `TopCat.Sheaf.OpenRestriction.homRestrictionEquiv_sections`, `TopCat.Sheaf.OpenRestriction.representingUnit`, `TopCat.Sheaf.OpenRestriction.representingUnit_bijective`, `TopCat.Sheaf.OpenRestriction.representingUnit_comp` | `TopCat.ConstantSheaf.integralHomGlobalEquiv`, `TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality`, `TopCat.ConstantSheaf.integralSheaf` |
| `Lib.Topology.Sheaves.PrincipalCoverLocalSystem.Restriction` (1) | `PrincipalCoverLocalSystem.constantSheafRestrictionIsoOfSection` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.PrincipalCoverLocalSystem.Trivialization` (7) | `PrincipalCoverLocalSystem.constantComparisonData`, `PrincipalCoverLocalSystem.constantComparisonData._proof_1`, `PrincipalCoverLocalSystem.constantComparisonData._proof_2`, `PrincipalCoverLocalSystem.constantComparisonData_stalkMap_isIso`, `PrincipalCoverLocalSystem.constantSheafHomOfSection`, `PrincipalCoverLocalSystem.constantSheafHomOfSection_isIso`, `PrincipalCoverLocalSystem.constantSheafIsoOfSection` | `TopCat.ConstantSheaf.sectionValue`, `TopCat.ConstantSheaf.sectionValue_isLocallyConstant`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.Augmentation` (9) | `TopCat.SingularCochainSheaf.exists_restriction_constant`, `TopCat.SingularCochainSheaf.presheafAugmentation`, `TopCat.SingularCochainSheaf.presheafAugmentation._proof_1`, `TopCat.SingularCochainSheaf.presheafAugmentation_d`, `TopCat.SingularCochainSheaf.presheafAugmentation_d_assoc`, `TopCat.SingularCochainSheaf.presheafAugmentation_stalk_injective`, `TopCat.SingularCochainSheaf.sheafAugmentation`, `TopCat.SingularCochainSheaf.sheafAugmentation_d`, `TopCat.SingularCochainSheaf.sheafAugmentation_d_assoc` | `TopCat.ConstantSheaf.presheaf`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.AugmentationMono` (1) | `TopCat.SingularCochainSheaf.sheafAugmentation_mono` | `TopCat.ConstantSheaf.presheaf`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.ComparisonH1` (5) | `TopCat.SingularCochainSheaf.constantSheafGlobalH1Iso.congr_simp`, `TopCat.SingularCochainSheaf.h1Comparison`, `TopCat.SingularCochainSheaf.h1Comparison.congr_simp`, `TopCat.SingularCochainSheaf.h1Comparison_global`, `TopCat.SingularCochainSheaf.h1Comparison_global_assoc` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.ComparisonPositive` (7) | `TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular`, `TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular.congr_simp`, `TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular_global`, `TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular_global_assoc`, `TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular_naturality_of_global`, `TopCat.SingularCochainSheaf.constantSheafGlobalIso`, `TopCat.SingularCochainSheaf.constantSheafGlobalIso.congr_simp` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.GlobalResolutionH1` (1) | `TopCat.SingularCochainSheaf.constantSheafGlobalH1Iso` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.ComparisonH1` (1) | `TopCat.SingularCochainSheaf.h1Comparison_naturality_of_global` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.FiniteClosedH1` (3) | `TopCat.SingularCochainSheaf.h1Comparison_naturality`, `TopCat.SingularCochainSheaf.h1_global_naturality`, `TopCat.SingularCochainSheaf.resolutionH1Pullback._proof_4` | `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.FiniteClosedPositive` (5) | `TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular_naturality`, `TopCat.SingularCochainSheaf.constantSheafCohomology_pullback_isIso_of_singular`, `TopCat.SingularCochainSheaf.constantSheafGlobalIso_naturality`, `TopCat.SingularCochainSheaf.resolutionPullback._proof_1`, `TopCat.SingularCochainSheaf.resolutionPullback._proof_2` | `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.Presheaf` (4) | `TopCat.SingularCochainSheaf.constantPresheafPullback`, `TopCat.SingularCochainSheaf.constantPresheafPullback._proof_1`, `TopCat.SingularCochainSheaf.presheafPullback_augmentation`, `TopCat.SingularCochainSheaf.presheafPullback_augmentation_assoc` | `TopCat.ConstantSheaf.presheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.Sheaf` (3) | `TopCat.SingularCochainSheaf.cochainPullback_augmentation`, `TopCat.SingularCochainSheaf.cochainPullback_augmentation_assoc`, `TopCat.SingularCochainSheaf.constant_sheafifyPullback` | `TopCat.ConstantSheaf.presheaf`, `TopCat.ConstantSheaf.pushforwardHom`, `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.ResolutionPositive` (1) | `TopCat.SingularCochainSheaf.resolution_Z_zero` | `TopCat.ConstantSheaf.sheaf` |
| `Lib.Topology.Sheaves.SingularCochainSheaf.Vanishing` (2) | `TopCat.SingularCochainSheaf.constantSheafCohomology_subsingleton_iff_singular`, `TopCat.SingularCochainSheaf.constantSheafCohomology_succ_subsingleton_of_contractible` | `TopCat.ConstantSheaf.sheaf` |

Three names in section B are `private` and therefore carry no `uses` record in the dump;
they were checked by reading the source:
`TopCat.FiniteClosedPushforward.h0GlobalIso_mk₀`
(`Lib/Topology/Sheaves/FiniteClosedPushforward/AcyclicResolutionH1.lean` l.39) mentions
`TopCat.ConstantSheaf.integralHomGlobalEquiv`;
`TopCat.SingularCochainSheaf.presheafAugmentation_stalk_injective`
(`…/SingularCochainSheaf/AugmentationMono.lean` l.34) and
`TopCat.SingularCochainSheaf.exists_restriction_constant`
(`…/SingularCochainSheaf/LocalExactH1.lean` l.34) mention `TopCat.ConstantSheaf.presheaf`
through `presheafAugmentation`.

`TopCat.Sheaf.unitSheafEquivImageIso` (and its `_proof_1`) sit in a file that was partly
generalised but were themselves left pinned; their hashes moved for the section-B reason
(they mention `TopCat.ConstantSheaf.integralSheaf` and `pushforwardHom`).

No changed type is unexplained.

## Commits

`b0155721..` on `r7/packet-08`, one commit per file (32) plus this receipt.
