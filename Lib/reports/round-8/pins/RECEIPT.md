# Round-8 receipt — `pins` (chokepoint universe pins)

Packet: `Lib/reports/round-7/judgement/chokepoint-pins.md`.
Branch `r8/pins`, base `4e15a034`.

Scope: lift the universe-zero pins on the chokepoint declarations the packet names, one commit
per chokepoint, rebuild the consumers, then re-run the round-7 checklist item "universe pins" on
the files the lifted chokepoints release.

`.{0}` pins in `Lib`: **1024 in 99 files before → 320 in 48 files after** (704 lifted, 51 files
cleared).  No renames; no rename map.

## 1. Chokepoints lifted

| chokepoint | file | commit | what it is now |
|---|---|---|---|
| `CategoryTheory.Sheaf.cohomologyAddCommGroup` | `Cohomology/AddCommGroup.lean` | `feba6a42` | `{X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) : AddCommGroup (Sheaf.H.{u} F n)`.  The instance was **lifted, not deleted**, as instructed; `Ext.instAddCommGroup` supplies it at every `u`, `HasExt.{u}` coming from `IsGrothendieckAbelian.hasExt` |
| `TopCat.SheafH1.unitSheaf` (with `globalSectionsFunctor`, `h0GlobalIso`, `h0GlobalIso_naturality`, `AcyclicResolutionH1.globalComplex`, `extZeroGlobalIso`, `h1GlobalIso`) | `Cohomology/AcyclicResolutionH1.lean` | `63bdbb61` | `.{u}` throughout; `ULift.{u} ℤ` is the constant sheaf's value |
| `HasExt.{0}` private instance `abelianSheaf_hasExt` and `subsingleton_h1_of_isFlasque` | `H1Vanishing/Flasque.lean` | `f5a50893` | `HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X)`; the whole file `.{u}` |
| `OpenEmbeddingCohomology.openImage` and its namespace | `OpenEmbeddingCohomology.lean` | `6973220d` | `.{u}` |
| `TopCat.Sheaf.freeOpen`, `freeHomEquiv`, `OpenRestriction.freeOpen`, `OpenRestriction.cohomologyEquiv` | `OpenRestriction/Cohomology.lean` | `ccf092a2` | `.{u}` |
| `TopCat.FiniteClosedPushforward.pushforwardStalkEquiv` | `FiniteClosedPushforward/Exact.lean` | `b457a9fe` | `.{u}` |
| `TopCat.ConstantSheafCohomology.pullback` | `ConstantCohomologyPullback.lean` | `f59653c5` | `.{u}` |
| `TopCat.Sheaf.OpenRestriction.germ_stalkIso_hom_nearbyRestrictionUnit` (and `nearbyRestrictionUnit_app`) | `OpenRestriction/NearbyRestrictionGerm.lean` | `6f4277d9` | was pinned invisibly — a bare `{X : TopCat}` binder and bare `AddCommGrpCat` arguments, which elaborate at universe 0 under this repo's `autoImplicit false`.  Now `{X : TopCat.{u}}`, `AddCommGrpCat.{u}` |

Already lifted before this packet, verified rather than redone:
`TopCat.ConstantSheaf.sheaf`, `.integralSheaf`, `integralHomGlobalEquiv`,
`integralPushforwardHom_comp_bijective` (`ConstantPushforward.lean`,
`ConstantPushforward/GlobalSections.lean`) are `.{u}` since packet 08; `TopCat.Sheaf.pushforwardAdditive`
is `.{u}` since packet 07.  Their consumers in the Leray cluster are lifted below.

## 2. Files released and re-checked (checklist item "universe pins")

Every declaration of each file below is now `.{u}`.  Found by grepping the round-7 receipts for the
chokepoint names, then by rebuilding.

* `85312af3` — `Cohomology/{AcyclicResolution, AcyclicResolutionH1Naturality, ProjectiveDimension,
  ShortExactAcyclicQuotient, ShortExactDegreeOne, ShortExactDegreeZeroSections,
  RepresentedOpenProjectiveDimension, FlasqueAcyclic, MayerVietorisProjectiveDimension,
  MayerVietorisVanishing, HomeomorphProjectiveDimension, GodementResolution,
  DiscreteProjectiveDimension}.lean`, `FiniteClosedPushforward/Cohomology.lean`.
* `f59653c5` — `ConstantCohomologyPullback.lean`, `FiniteClosedPushforward/{AcyclicResolution,
  AcyclicResolutionH1, Composition}.lean`, `FiniteClosedOpenRestriction.lean`,
  `OpenFiniteClosedFactorization.lean`.
* `6f4277d9` — `OpenRestriction/StalkCriterion.lean` (round-7 recorded this one as blocked by a
  `whnf` timeout; the timeout was a consequence of the universe defaulting, and is gone).
* `a140e4b1` — the Leray cluster: `CanonicalPositiveNeighborhoodSection`,
  `FibreStalkEvaluation/{CanonicalPositive, CanonicalPositiveCofinalExt, CofinalCriterion,
  ConstantEvaluationBijective, ConstantNormalization, ConstantNormalizationConsequences,
  ConstantPointFibre, Neighborhood, OpenRestrictionComposition, Stalk}`,
  `HigherDirectImageSheafification`, `ResolutionAbutment`, `ResolutionCohomologyPresheaf`,
  `ResolutionPostnikov`, `ResolutionPostnikovD2`, `ResolutionPostnikovD2Coordinates`,
  `ResolutionPostnikovD2Transgression`, `ResolutionTransgression`,
  `SheafificationNeighborhoodGerm`, `SheafificationStalkCompatibility`; plus
  `Lib/Topology/Sheaves/{SheafificationLocal, SheafificationLocalGerm, NestedOpenCohomology}.lean`.

Two `: Type` binders were widened where the lift forced it, both recorded as forced by round 7:
`TopCat.SheafCohomology.GlobalSections`'s carrier ascription (`Type` → `Type u`) and
`ConstantPointFibre.Fibre : Type` → `Type u`.

Universe arguments the elaborator used to default to `0` are now written out.  They are the only
proof-text edits in this packet:
`(C := AbelianSheaf Y)` on `ExtTransgression.cochainTransgression`,
`ExtTransgression.homologyTwoStepResolution` and
`homologyTwoStepResolutionExtendUpNat_connectingTwo`;
`AddCommGrpCat.{u}` on `TopCat.Presheaf.stalkFunctor` / `TopCat.Sheaf.forget`;
`ULift.{u + 1}` for the Postnikov `E₂` page (was `ULift.{1}`);
`HasSmallLocalizedShiftedHom.{u + 1}` and `homEquivCoyonedaHomologyOfIsKInjective.{u + 1}`
in `ResolutionAbutment.lean` (were `.{1}`).

## 3. Chokepoints recorded and skipped

### `AlgebraicTopology.SingularCochains.chains` / `.complex` (packet priority 1)

The pin is `ModuleCat.of ℤ ℤ : ModuleCat.{0} ℤ`, the coefficient object fed to
`AlgebraicTopology.singularChainComplexFunctor`.  The only way to state it at `ModuleCat.{u} ℤ`
is to replace the literal `ℤ` by `ULift.{u} ℤ`.  That version **elaborates**: with

```
abbrev chains (X : Type u) [TopologicalSpace X] : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X)
```

(and the same substitution in `complex`, `pullback`, `pullback_id`, `pullback_comp`,
`pullbackHomotopy` and their `X Y Z : Type` binders) `Lib.AlgebraicTopology.SingularCochains`
builds clean and the file's 7 remaining pins and 9 `: Type` binders all go.
`HasCoproducts.{u} (ModuleCat.{u} ℤ)` is available, so the coproduct side is not the obstacle.

It is skipped because the coefficient object is no longer the literal `ℤ`, and four consumer
modules then need real proof rewrites (`lake build Lib` stops at):

```
Lib/AlgebraicTopology/SingularCochains/PositivePrimitives.lean:67:2: Type mismatch
  (HomotopyEquiv.ofIso
        (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace (ModuleCat ℤ) (ModuleCat.of ℤ ℤ)
          (TopCat.of Unit))).trans
    (ChainComplex.alternatingConstHomotopyEquiv pointFreeModule)
has type
  HomotopyEquiv (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of Unit))
    ((ChainComplex.single₀ (ModuleCat ℤ)).obj pointFreeModule)
but is expected to have type
  HomotopyEquiv (chains Unit) ((ChainComplex.single₀ (ModuleCat ℤ)).obj pointFreeModule)
```

and

```
Lib/AlgebraicTopology/SingularSmallChains/Basic.lean:53:2: Type mismatch
  (ConcreteCategory.hom ((singularSet X).ιChainComplex (simplexIndex X n sigma))) 1
has type
  ↑(((singularSet X).chainComplex (ModuleCat.of ℤ ℤ)).X n)
but is expected to have type
  ↑((AlgebraicTopology.SingularCochains.chains X).X n)
```

followed by `LinearMap.toSpanSingleton ℤ`, `LinearMap.ext_ring` and `iota_functionChainHom`
failures in `SingularSmallChains/Basic.lean`, `SingularCochainSheaf/DegreeZeroFunctions.lean`
and `SingularCochainSheaf/Augmentation.lean`: the singular basis element is the literal `1 : ℤ`
there, and moving to `ULift ℤ` rewrites those proofs.  The attempt is kept out of tree; the
packet's remaining 26 `SingularCochainSheaf/*` files, `SingularCochains/{Generators, Vanishing,
PositivePrimitives}`, `DualEvaluation/CoefficientNormalization` (the `ULift.{0} ℤ` block),
`SingularSmallChains/{Basic, CochainHomotopy, Projective}` and
`Topology/Sheaves/{ConstantProductH1, ConstantProductH1Comparison,
ConstantProductH1FibreIndependence, ConstantProductPositiveFibreIndependence,
ConstantSheafH1}` stay pinned for exactly this reason — 271 of the 320 pins left.

### `SingularChains.singularComplex` (`AlgebraicTopology/SingularHomology/Chains.lean`)

The same obstacle in the homology-side interface: `(TopCat.toSSet.obj (TopCat.of X)).chainComplex
(ModuleCat.of ℤ ℤ)` with `(X : Type)`, and `chainLift` / `chainMap_ext` reading off the value at
`1 : ℤ`.  It forces the 8 pins of `AlgebraicTopology/SingularHomology/Coproduct.lean`
(`ModuleCat.{0} ℤ` in `singularChainsFiniteBiproducts`, `HasFiniteBiproducts`) — the packet's
"Mathlib `ModuleCat.hasLimits` at `max v w`" item: the coproduct instance is not what pins the
file, the literal-`ℤ` chain complex is.  Skipped for the same reason.

### `Cohomology/SphereTwo.lean`

Lifted, built, and reverted.  `hasExt_of_enoughInjectives.{0,0,1}` lifts to `.{u,u,u+1}` without
trouble, but the theorem's hypothesis is a homeomorphism `B ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ
(Fin 3)) 1`, and

```
Lib/Topology/Sheaves/Cohomology/SphereTwo.lean:64:4: Type mismatch
  SphereTwo.hasCoveringDimensionLE_two_of_homeomorph ?m.127
has type
  ∀ (U : ?m.128 → Opens ?m.125), IsOpenCover U → ∃ κ V x, IsOpenCover V ∧ OpenCover.MultiplicityLE V (2 + 1)
but is expected to have type
  ∀ (U : ι✝ → Opens ↑B), IsOpenCover U → ∃ κ V x, IsOpenCover V ∧ OpenCover.MultiplicityLE V (2 + 1)
```

`TopologicalSpace.SphereTwo.hasCoveringDimensionLE_two_of_homeomorph` goes through
`HasCoveringDimensionLE.of_homeomorph {X Y : Type u}`, one universe for both spaces, and the
sphere is in `Type 0`.  This is the obstacle round 7 already recorded for
`Lib/Topology/Dimension/SphereTwo.lean`; widening it needs a cross-universe transport lemma in
`Covering.lean`, i.e. a proof rewrite.  The file's 23 pins stay.

### `Lib/AlgebraicTopology/Hurewicz/Degree1.lean`

Its single `.{0}` is inside the module docstring, explaining the `ModuleCat.{0} ℤ` coefficient
pin; it is accurate and untouched.

## 4. Lost names

None.  `envdiff` reports `lost 682 added 681 of which source declarations: 0 0`.  All 682/681 are
auxiliary proof constants (`_proof_n`, `_eq_n`), explicitly "not judged" by the tool.  One of them,
`CategoryTheory.Sheaf.Leray.higherDirectImageResolutionSheafificationIso._proof_5`, is lost without
a replacement: the universe-explicit form of `higherDirectImageResolutionStalkIso` in
`HigherDirectImageSheafification.lean` produces one side goal fewer.  No source name moved module.

## 5. Builds

```
lake build Lib                                  Build completed successfully (9150 jobs).  rc=0
lake build Solution S6Shortcuts S6 Challenge    Build completed successfully (9189 jobs).  rc=0
lake build Lib.AxiomAudit                       Build completed successfully (9150 jobs).  rc=0
python3 scripts/lib_stock_census.py --check     rc=0
```

`Lib.AxiomAudit` reports only `propext`, `Classical.choice`, `Quot.sound` (1724 declarations with
all three, 115 with `propext, Quot.sound`, 15 with `propext`, 1 with `propext, Classical.choice`).

## 6. Envdiff

`Lib/reports/round-8/pins/envdiff.json` (copy of the receipt file).

```
constants before 38593 after 38592 (keys 38491 38490 )
lost 682 added 681 of which source declarations: 0 0 ; names with changed type 681 of which source: 398
auxiliary lost/added/changed (not judged): 682 681 283
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT PASS
```

All 398 changed source types are the universe generalisations of this packet and their dependents.
The largest groups are `FibreStalkEvaluation/Neighborhood` (25), `ResolutionTransgression` (24),
`OpenRestriction/Cohomology` (22), `OpenEmbeddingCohomology` (17), `ResolutionCohomologyPresheaf`
(16), `ResolutionPostnikov` (14), `NestedOpenCohomology` (14).  The `SingularCochainSheaf/*` and
`Cohomology/SphereTwo` entries in that list are dependents whose statements mention a lifted
declaration; those files themselves were not edited.

## 7. Commits

```
feba6a42 Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean: lift cohomologyAddCommGroup to .{u}
63bdbb61 Lib/Topology/Sheaves/Cohomology/AcyclicResolutionH1.lean: lift the H1 acyclic-resolution interface to .{u}
f5a50893 Lib/Topology/Sheaves/H1Vanishing/Flasque.lean: lift flasque H1 vanishing to .{u}
6973220d Lib/Topology/Sheaves/OpenEmbeddingCohomology.lean: lift the open-embedding cohomology comparison to .{u}
ccf092a2 Lib/Topology/Sheaves/OpenRestriction/Cohomology.lean: lift open-restriction cohomology to .{u}
b457a9fe Lib/Topology/Sheaves/FiniteClosedPushforward/Exact.lean: lift the finite-closed pushforward exactness to .{u}
85312af3 Lib/Topology/Sheaves/Cohomology: lift the files released by cohomologyAddCommGroup
f59653c5 Lib/Topology/Sheaves: lift ConstantSheafCohomology.pullback and the finite-closed cluster
6f4277d9 Lib/Topology/Sheaves/OpenRestriction: lift the nearby-restriction germ chokepoint to .{u}
a140e4b1 Lib/CategoryTheory/Sites/Leray: lift the Leray cluster to .{u}
```
