# Round 7 checklist packet 09 — receipt

Worktree `/home/goblin/hopf-r7-p09`, branch `r7/packet-09`, base `9552305f`, Lean v4.33.0.
All 34 files of `packet-09.md` are done; one commit per file, in the order listed below.

## Summary per work item

| item | done | left |
|---|---|---|
| 1. manuscript citations | 34 module docstrings rewritten to a textbook or Mathlib reference; 177 docstring blocks replaced in total (process narrative, "native"/"actual"/"literal"/"genuine", negated-claims paragraphs, lane/consumer language removed) | 0 |
| 2. docstrings | 83 missing public docstrings added (260 docstring blocks in the diff, 177 of them replacements); every public declaration in the 34 files is now documented | 0 |
| 3. universe pins | 77 explicit `.{0}` pins removed across 8 files, now stated for `TopCat.{u}` / `AddCommGrpCat.{u}` | 316 pins left, each forced by an imported interface outside the packet (listed per file below) |
| 4. `: Type` binders | 5 `: Type` coercion ascriptions widened to `Type u` (SkyscraperGlobalSections), `{ι : Type}` → `{ι : Type*}` in GlobalPatch/GlobalPatchLocal, `{G : Type uG} {E X : Type u}` → `{G E X : Type*}` in DeckTranslate | 37 binders left, forced (listed per file below) |

No statement was weakened or strengthened, no hypothesis added, no declaration deleted, no `sorry`/`axiom`/`admit` introduced.
The only proof-side change anywhere is one local `set_option synthInstance.maxHeartbeats 80000` on
`TopCat.Sheaf.OpenRestriction.extension_preservesMonomorphisms`, whose instance search is slower at a general universe.

## Per file

| file | citations | docstrings added | universe pins | `: Type` binders |
|---|---|---|---|---|
| `FiniteClosedPushforward/Cohomology.lean` | module + 6 restated → Hartshorne III Ex. 4.1 / Ex. 8.2, Iversen II | 1 (`cohomologyEquiv_symm_apply`) | 32 left, forced by `CategoryTheory.Sheaf.cohomologyAddCommGroup` (`Cohomology/AddCommGroup.lean`) and `TopCat.ConstantSheaf.integralPushforwardHom_comp_bijective` (`ConstantPushforward/GlobalSections.lean`) | — |
| `FiniteClosedPushforward/Composition.lean` | module + 3 restated → Hartshorne III Ex. 8.2 | 0 | 39 left, forced by `TopCat.ConstantSheafCohomology.pullback` (`ConstantCohomologyPullback.lean`) | — |
| `FiniteClosedPushforward/Exact.lean` | module + 6 restated → Hartshorne II Ex. 1.19 / III Prop. 2.4, Iversen II; dropped `open scoped AlgebraicGeometry` | 0 | 29 left, forced by `TopCat.FiniteClosedPushforward.pushforwardStalkEquiv` and `TopCat.Sheaf.pushforwardAdditive` | — |
| `FiniteSupport/SkyscraperGlobalSections.lean` | module + 6 restated → Hartshorne II Ex. 1.17, Mathlib `skyscraperSheaf` | 0 | **6 generalised** to `TopCat.{u}`/`AddCommGrpCat.{u}` | **5 widened** (`: Type` → `: Type u`) |
| `FiniteSupport/SkyscraperReconstruction.lean` | module + 7 restated → Hartshorne II Prop. 1.1 / Ex. 1.17, Mathlib `isIso_of_stalkFunctor_map_iso` | 0 | **1 (+ implicit level-0 `AddCommGrpCat`) generalised** | — |
| `FiniteSupport/SkyscraperSupport.lean` | module docstring created → Hartshorne II Ex. 1.17, Mathlib `skyscraperPresheafStalkOfSpecializes` | 8 | **1 (+ implicit) generalised** | — |
| `H1Vanishing/Flasque.lean` | module + 1 restated → Hartshorne III Prop. 2.5, Godement II.4.3 | 0 | 37 left, forced by `CategoryTheory.Sheaf.cohomologyAddCommGroup` | — |
| `NestedOpenCohomology.lean` | module (+ `## Main results`) + 4 restated → Hartshorne II §1, Iversen II.2 | 3 | 23 left, forced by `…ConstantFibreEvaluationNormalization.intrinsicOpenClass` | — |
| `OpenEmbeddingCohomology.lean` | module + 6 restated → Iversen II.5, Bredon II.9 | 8 | 20 left, forced by `cohomologyAddCommGroup` and `TopCat.ConstantSheaf.sheaf` | — |
| `OpenFiniteClosedFactorization.lean` | module + 6 restated → Hartshorne II §1, Iversen II (twin was "none found") | 1 | 27 left, forced by `TopCat.ConstantSheafCohomology.pullback` | — |
| `OpenRestriction.lean` | module (+ `## Main results`) + 9 restated → Hartshorne III Lemma 6.1, Iversen II.6, Godement II.4 | 13 | **5 generalised** to `TopCat.{u}`/`AddCommGrpCat.{u}` (23 declarations) | — |
| `OpenRestriction/Cohomology.lean` | module (+ `## Main results`) + 6 restated → Godement II.4, Hartshorne III §6 | 8 | 27 left, forced by `TopCat.ConstantSheaf.integralSheaf` / `integralHomGlobalEquiv` | — |
| `OpenRestriction/NearbyEvaluationCompatibility.lean` | module + 4 restated → Mathlib `stalk_hom_ext`, `stalkFunctor_map_germ` | 0 | **14 generalised**; `[Category.{0, u} C]` → `[Category.{u', u} C]`, `TopCat.{u'}` | — |
| `OpenRestriction/StalkCriterion.lean` | module + 5 restated → Iversen II.6, Kashiwara–Schapira Prop. 2.3.6, Mathlib `isIso_of_stalkFunctor_map_iso` | 1 | 7 left, forced by `TopCat.Sheaf.OpenRestriction.germ_stalkIso_hom_nearbyRestrictionUnit` (`OpenRestriction/NearbyRestrictionGerm.lean`, outside the packet); with `TopCat.{u}`: *"Application type mismatch: `F` has type `Sheaf.{u, u, u+1} AddCommGrpCat X` … but is expected to have type `Sheaf.{0, 0, 1} AddCommGrpCat ?m`"* at l.73, plus a `whnf` timeout in `nearbyStalkUnit_comp_nearbyStalkPushforward` | — |
| `OpenRestriction/StalkUnit.lean` | module (+ `## Main results`) + 7 restated → Iversen II.6, Godement II.2.9 | 1 | **12 generalised** | — |
| `OpenRestrictionStalk.lean` | module + 4 restated → Hartshorne II §1, Mathlib `stalkPullbackIso` | 0 | **4 generalised** | — |
| `PrincipalCoverLocalSystem.lean` | module (+ `## Main results`) + 11 restated → Whitehead VI.1–2, Hatcher §3.H | 2 | — | 4 left: `{E X M : Type u}` forced; with `Type*` the sheaf condition needs `Limits.HasLimitsOfSize.{u_3, u_3, max u_2 u_4, max (u_2+1) (u_4+1)} AddCommGrpCat` (l.122) and `(sheaf p hp).obj.obj (op ⊤)` loses its type (l.218) |
| `PrincipalCoverLocalSystem/Comparison.lean` | module (+ `## Main results`) + 8 restated → Whitehead VI.2 | 0 | — | 2 left, same obstacle |
| `PrincipalCoverLocalSystem/CyclicComponentSections.lean` | module (+ `## Main results`) + 3 restated → Whitehead VI.2, Hatcher §3.H | 14 | — | 2 left, same obstacle |
| `PrincipalCoverLocalSystem/DeckTranslate.lean` | module (+ `## Main results`) + 1 restated → Hatcher Prop. 1.39, Spanier 2.6 | 6 | — | **3 widened**: `{G : Type uG} {E X : Type u}` → `{G E X : Type*}` |
| `PrincipalCoverLocalSystem/Stalk.lean` | module (+ `## Main results`) + 4 restated → Whitehead VI.1 | 1 | — | 2 left, same obstacle |
| `SheafificationLocalGerm.lean` | module → Mathlib `stalkFunctor_map_germ`; negated-claims paragraph dropped | 0 | 3 left, forced by `TopCat.SheafificationLocal.sheaf` | — |
| `SheafificationPushforward.lean` | module + 4 restated → Mathlib `sheafifyLift`, `toSheafify_sheafifyLift` | 3 | **34 generalised** | — |
| `SingularCochainSheaf/Augmentation.lean` | module + 16 restated → Bredon III §1, Warner 5.31 | 1 | 16 left, forced by `AlgebraicTopology.SingularCochains.chains`, `TopCat.toSSet` | 8 left, same: *"`X` has type `Type u_1` … but is expected to have type `Type`"* at l.36 |
| `SingularCochainSheaf/AugmentationMono.lean` | module + 1 restated → Bredon III §1, Warner 5.31 | 0 | 4 left, forced by `TopCat.SingularCochainSheaf.sheafAugmentation` | — |
| `SingularCochainSheaf/BarycentricSmallChains.lean` | module + 1 restated → Hatcher Prop. 2.21 | 0 | 1 left, forced by `TopCat.SingularCochainSheaf.HasSmallChainEquivalences` | — |
| `SingularCochainSheaf/ComparisonH1.lean` | module + 2 restated → Bredon III Thm. 1.1, Warner 5.32 | 0 | 3 left, forced by `TopCat.SingularCochainSheaf.globalCochainComparison` | — |
| `SingularCochainSheaf/ComparisonPositive.lean` | module + 5 restated → Bredon III Thm. 1.1, Warner 5.32, Godement II.3.9 | 0 | 8 left, forced by `TopCat.ConstantSheaf.sheaf`, `globalCochainComplex` | — |
| `SingularCochainSheaf/DegreeZeroAcyclic.lean` | module + 5 restated → Bredon III §1 / II §5, Warner 5.31, Godement II.3.1 | 0 | 7 left, forced by `TopCat.SingularCochainSheaf.sheaf`, `TopCat.SheafH1.subsingleton_h1_of_isFlasque` | — |
| `SingularCochainSheaf/DegreeZeroFunctions.lean` | module + 16 restated → Bredon III §1, Warner 5.31 | 9 | 20 left, forced as in Augmentation.lean | 18 left, same obstacle |
| `SingularCochainSheaf/GlobalKernelLocal.lean` | module + 3 restated → Bredon III §1 | 0 | 2 left, forced by `TopCat.SingularCochainSheaf.presheaf` | — |
| `SingularCochainSheaf/GlobalKernelSmall.lean` | module + 7 restated → Bredon III §1, Hatcher Prop. 2.21 | 0 | 3 left, forced by `AlgebraicTopology.SingularCochains.Cochains` | 1 left: `{X : Type}` forced by `Cochains`, `{ι : Type}` by `TopCat.SingularSmallChains.IsSmallSimplex` |
| `SingularCochainSheaf/GlobalPatch.lean` | module + 5 restated → Bredon III Prop. 1.1, Warner 5.31 | 3 | 7 left, forced by `TopCat.SingularCochainSheaf.presheaf` | **`{ι : Type}` → `{ι : Type*}`** (5 declarations) |
| `SingularCochainSheaf/GlobalPatchLocal.lean` | module + 2 restated → Bredon III Prop. 1.1 | 0 | 1 left, forced by `presheaf` | **`{ι : Type}` → `{ι : Type*}`** (2 declarations) |

## Builds

```
lake build Lib                                 → Build completed successfully (9150 jobs).   exit 0
lake build Solution S6Shortcuts S6 Challenge   → Build completed successfully (9189 jobs).   exit 0
    (one pre-existing warning: Challenge.lean:42:8: declaration uses `sorry` — the open-problem statement, unchanged from the base)
lake build Lib.AxiomAudit                      → Build completed successfully (9150 jobs).   exit 0
    axioms reported, over all audited declarations: {propext}, {propext, Quot.sound},
    {propext, Classical.choice}, {propext, Classical.choice, Quot.sound}.  No `sorryAx`, no other axiom.
```

## envdiff

`python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_base.jsonl dump_after.jsonl --receipt envdiff.json`

```
constants before 21719 after 21719 (keys 21713 21713)
lost 219 added 219 of which source declarations: 0 0
names with changed type 219 of which source: 159
module moves (source declarations, 1-to-1): 0 ; ambiguous module changes: 0 ; auxiliary constants that changed module: 0
VERDICT PASS
```

* **0 source declarations lost, 0 added.** The 219 lost/added constants are all auxiliary (`_proof_*`, `_aux_*`, `.eq_def`, …) regenerated by recompilation.
* **159 declarations with a changed type.** Every one is either a declaration this packet generalised, or a declaration in a downstream module whose *type* mentions a generalised declaration and therefore now carries a universe variable. No other changed type occurs.

### Changed-type table

Generalised in this packet (8 files, 77 pins + the binder widenings):

* `Lib.Topology.Sheaves.OpenRestriction` (23): `costructuredArrow_isEmpty`, `extension`, `extension_preservesMonomorphisms`, `inclusion`, `inclusion_isOpenEmbedding`, `inclusion_mono`, `lan_obj_isZero_of_not_le`, `lan_preservesMonomorphisms`, `openImage`, `openImage_cocontinuous`, `openImage_continuous`, `openImage_full`, `openImage_obj_le`, `openImage_preimage`, `preimageOpen`, `restriction`, `restriction_additive`, `restriction_eq_sheafRestrict`, `restriction_leftAdjoint`, `restriction_preservesFiniteColimits`, `restriction_preservesFiniteLimits`, `restriction_preservesInjectiveObjects`, `restriction_rightAdjoint` — `TopCat.{0}` → `TopCat.{u}`
* `Lib.Topology.Sheaves.OpenRestriction.StalkUnit` (10): `germ_nearbyStalkUnit`, `nearbyExtension`, `nearbyExtensionObjIso`, `nearbyNeighborhoodDiagram`, `nearbyRestrictionUnit`, `nearbySectionsStalk`, `nearbySectionsStalk_eq_colimit`, `nearbyStalkUnit`, `nearbyStalkUnit_natural`, `pullbackRestrictionIso` — `TopCat.{u}`
* `Lib.Topology.Sheaves.OpenRestrictionStalk` (4): `inclusion_mem_openImage`, `presheafStalkIso`, `stalkIso`, `stalkIso_inv_germ` — `TopCat.{u}`
* `Lib.Topology.Sheaves.OpenRestriction.NearbyEvaluationCompatibility` (6): `stalk_hom_ext_of_cofinal` (`[Category.{u', u} C]`, `TopCat.{u'}`), `germ_nearbyStalkUnit_comp_map_comp_stalkMap`, `germ_nearbyStalkUnit_comp_stalkMap`, `nearbyStalkUnit_comp_map_comp_stalkMap`, `nearbyStalkUnit_comp_stalkMap`, `pullbackNearbyEvaluation` — `TopCat.{u}`
* `Lib.Topology.Sheaves.SheafificationPushforward` (9): `liftToPushforward`, `liftToPushforward_hom_ext`, `sheafification`, `sheafifyPullback`, `sheafifyPullback_naturality`, `toSheafify_liftToPushforward`, `toSheafify_liftToPushforward_assoc`, `toSheafify_sheafifyPullback`, `toSheafify_sheafifyPullback_assoc` — `TopCat.{u}`
* `Lib.Topology.Sheaves.FiniteSupport.SkyscraperGlobalSections` (6): `globalSectionsEquivOfSkyscraperBiprodIso`, `globalSectionsIsoOfSkyscraperBiprodIso`, `sectionsBiprodIso`, `skyscraperAt`, `skyscraperAtTopIso`, `topEvaluation` — `TopCat.{u}`, `: Type` → `: Type u`
* `Lib.Topology.Sheaves.FiniteSupport.SkyscraperReconstruction` (8 public + 6 private helpers `biprodIsoProd_hom_comp_fst/_snd`, `sectionsBiprodIso_hom_comp_fst/_snd` and their `_assoc` forms): `globalSectionsEquivOfStalkwiseSkyscraperBiprod_apply`, `globalSectionsIsoOfStalkwiseSkyscraperBiprod_hom_comp_fst`, `…_hom_comp_snd`, `skyscraperAtTopIso_hom_eqToHom`, `skyscraperBiprodIsoOfStalkwiseIso`, `toSkyscraperAt`, `toSkyscraperAt_top`, `toSkyscraperBiprod` — `TopCat.{u}`
* `Lib.Topology.Sheaves.FiniteSupport.SkyscraperSupport` (10): `isIso_stalkFunctor_map_toSkyscraperBiprod`, `…_at_left`, `…_at_right`, `sheafStalkBiprodIso`, `skyscraperAt_stalk_isZero_of_ne`, `skyscraperBiprodIsoOfTwoPointSupport`, `stalkMap_toSkyscraperAt_comp_counit`, `stalkMap_toSkyscraperBiprod_comp_mapBiprod`, `…_assoc`, `stalkSkyscraperAtIso` — `TopCat.{u}`
* `Lib.Topology.Sheaves.PrincipalCoverLocalSystem.DeckTranslate` (11): `deckMonodromyHom`, `deckMonodromyHom_fiberTransport`, `deckMonodromyHom_homeomorph_comp`, `deckMonodromyHom_liftedPath`, `deckMonodromyHom_translate`, `deckMonodromyHom_translate_apply`, `deckMonodromyHom_translate_range`, `fiberTransport`, `fundamentalGroupToMulOpposite_translate`, `inverseFundamentalGroupToMulOpposite_translate`, `map_conj_zpowers_inv_mul_mul` — `{E X : Type u}` → `{E X : Type*}`
* `Lib.Topology.Sheaves.SingularCochainSheaf.GlobalPatch` (5): `patchIndex`, `patchedCochain`, `patchedCochain_simplex`, `patchedCochain_simplex_of_subset`, `patchedValue` — `{ι : Type}` → `{ι : Type*}`
* `Lib.Topology.Sheaves.SingularCochainSheaf.GlobalPatchLocal` (2): `exists_neighborhood_patchedCochain_eq`, `patchedCochain_restrict_of_compatible` — `{ι : Type}` → `{ι : Type*}`

Downstream, not edited: their statements are unchanged, but their types now mention a universe-polymorphic declaration above, so the type hash moved.

* `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.ConstantNormalization` (6): `canonicalConstantEvaluation_forward`, `cohomologyEvaluation_forward_open`, `intrinsicOpenClass_coefficient`, `openConstantRestrictionHom`, `openConstantRestrictionHom_isIso`, `openConstantRestriction_coefficient` — via `OpenRestriction.restriction`
* `Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.OpenRestrictionComposition` (8): `induced_comp_inclusion`, `neighborhoodCohomologyForward_openRestriction`, `openImage_preimage`, `openImage_preimage_obj`, `restrictionPushforwardIso`, `restrictionPushforwardIso_global`, `restrictionPushforwardIso_hom_app`, `restrictionPushforwardIso_neighborhoodUnit` — via `OpenRestriction.restriction`
* `Lib.Topology.Sheaves.NestedOpenCohomology` (9): `cohomologyEquiv_restrict`, `constantRestrictionHom_comp`, `inclusion_comp_ambientInclusion`, `openImage_comp`, `openImage_comp_obj`, `representingUnit_app_unit`, `representingUnit_comp`, `restrictionIso`, `restrictionIso_hom_app` — via `OpenRestriction.restriction`/`openImage`
* `Lib.Topology.Sheaves.OpenRestriction.Cohomology` (11): `cohomologyEquiv_mk₀`, `cohomologyEquiv_naturality`, `homRestrictionEquiv`, `homRestrictionEquiv_naturality`, `homRestrictionEquiv_sections`, `openImage_top`, `representingUnit`, `representingUnit_bijective`, `representingUnit_comp`, `restrictionGlobalEquiv`, `restrictionGlobalEquiv_naturality` — via `OpenRestriction.restriction`/`openImage`
* `Lib.Topology.Sheaves.OpenRestriction.NearbyRestrictionGerm` (3): `germ_stalkIso_hom_nearbyRestrictionUnit`, `nearbyRestrictionUnit_app`, `stalkIso_inv_germ_nearbyRestrictionUnit` — via `stalkIso`, `nearbyRestrictionUnit`
* `Lib.Topology.Sheaves.OpenRestriction.StalkCriterion` (6): `globalRestrictionIsoOfIsIsoOutside`, `nearbyRestrictionUnit_app_isIso_of_isIso_outside`, `nearbyStalkPushforward`, `nearbyStalkPushforward_isIso`, `nearbyStalkUnit_comp_nearbyStalkPushforward`, `nearbyStalkUnit_isIso_of_mem` — via `nearbyStalkUnit`, `restriction` (the file itself stays at `TopCat.{0}`; only the universe *arguments* of the polymorphic constants it mentions changed)
* `Lib.Topology.Sheaves.PrincipalCoverLocalSystem.Restriction` (8): `constantSheafRestrictionIsoOfSection`, `restrictedBasePoint`, `restrictedBasePoint_mem`, `restrictionLiftedOpenHomeomorph`, `restrictionLiftedOpenHomeomorph_liftedAction`, `restrictionPresheafIso`, `restrictionSectionsEquiv`, `restrictionSheafIso` — via `OpenRestriction.restriction`
* `Lib.Topology.Sheaves.SingularCochainSheaf.OpenRestriction` (7): `openImageCochainIso`, `openImageHomeomorph`, `openImageMap`, `openImageMapInv`, `sheafIso`, `unit_sheafIso_hom`, `unit_sheafIso_hom_app` — via `OpenRestriction.restriction`/`openImage`
* `Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.Sheaf` (1): `constant_sheafifyPullback` — via `SheafificationPushforward.sheafifyPullback`

Every changed type is accounted for; there is no unexplained entry.

## Commits (34, one per file, base `9552305f`)

```
48961de8 Lib/Topology/Sheaves/SingularCochainSheaf/BarycentricSmallChains.lean
1ecc505e Lib/Topology/Sheaves/SingularCochainSheaf/ComparisonH1.lean
b5abef44 Lib/Topology/Sheaves/SheafificationLocalGerm.lean
76e5732e Lib/Topology/Sheaves/SingularCochainSheaf/GlobalKernelLocal.lean
521e2f26 Lib/Topology/Sheaves/SingularCochainSheaf/DegreeZeroAcyclic.lean
b1b0ab0b Lib/Topology/Sheaves/FiniteClosedPushforward/Exact.lean
d13b6f69 Lib/Topology/Sheaves/FiniteClosedPushforward/Cohomology.lean
a657e638 Lib/Topology/Sheaves/FiniteClosedPushforward/Composition.lean
1d3d4e2a Lib/Topology/Sheaves/H1Vanishing/Flasque.lean
3c678341 Lib/Topology/Sheaves/SingularCochainSheaf/AugmentationMono.lean
c78bd851 Lib/Topology/Sheaves/SingularCochainSheaf/ComparisonPositive.lean
dd08933b Lib/Topology/Sheaves/OpenEmbeddingCohomology.lean
a3d526be Lib/Topology/Sheaves/OpenRestriction/Cohomology.lean
026a0eeb Lib/Topology/Sheaves/OpenFiniteClosedFactorization.lean
bbf3e9aa Lib/Topology/Sheaves/NestedOpenCohomology.lean
5294fb3a Lib/Topology/Sheaves/OpenRestriction.lean
ff2914b1 Lib/Topology/Sheaves/OpenRestriction/StalkUnit.lean
76655541 Lib/Topology/Sheaves/OpenRestrictionStalk.lean
4cc4b122 Lib/Topology/Sheaves/OpenRestriction/StalkCriterion.lean
74ea81b7 Lib/Topology/Sheaves/OpenRestriction/NearbyEvaluationCompatibility.lean
240fc149 Lib/Topology/Sheaves/SheafificationPushforward.lean
180038a1 Lib/Topology/Sheaves/FiniteSupport/SkyscraperGlobalSections.lean
690f265b Lib/Topology/Sheaves/FiniteSupport/SkyscraperReconstruction.lean
e8857441 Lib/Topology/Sheaves/FiniteSupport/SkyscraperSupport.lean
d57007fb Lib/Topology/Sheaves/SingularCochainSheaf/GlobalPatch.lean
540d8ed1 Lib/Topology/Sheaves/SingularCochainSheaf/GlobalPatchLocal.lean
74c86086 Lib/Topology/Sheaves/SingularCochainSheaf/GlobalKernelSmall.lean
3a8917e8 Lib/Topology/Sheaves/SingularCochainSheaf/Augmentation.lean
af3067ff Lib/Topology/Sheaves/SingularCochainSheaf/DegreeZeroFunctions.lean
23efb8ac Lib/Topology/Sheaves/PrincipalCoverLocalSystem.lean
525332c6 Lib/Topology/Sheaves/PrincipalCoverLocalSystem/Stalk.lean
bafb67f4 Lib/Topology/Sheaves/PrincipalCoverLocalSystem/Comparison.lean
cde3d94e Lib/Topology/Sheaves/PrincipalCoverLocalSystem/DeckTranslate.lean
de03fcc6 Lib/Topology/Sheaves/PrincipalCoverLocalSystem/CyclicComponentSections.lean
```

## Suggestions not carried out (out of the four work items)

The auditors' one-line suggestions that are refactors rather than doc/universe/binder work were not
applied, so that no declaration is renamed, merged or deleted: merging `H1Vanishing/Flasque.lean` into
`Cohomology/FlasqueAcyclic.lean`; replacing `skyscraperAt` by a finset-indexed sum of Mathlib skyscrapers;
renaming `nearby*` to `pushforwardRestrict*`; replacing `inclusion`/`restriction` by `Opens.inclusion'`/
`Opens.sheafRestrict`; deleting `BarycentricSmallChains.lean`; folding `ComparisonH1.lean` into
`ComparisonPositive.lean`; moving `DeckTranslate.lean` under `Lib/Topology/Covering/`.
