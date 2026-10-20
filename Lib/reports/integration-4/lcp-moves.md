# LCP stock moves (integration 4, 2026-09-14)

Base `304a0fea` (worktree branch `lib/next-lcp`). Source coordinates are file:line of the declaration
line at `304a0fea`; destination coordinates are at commit `d7286ef3`. Every declaration block
(attributes, `attribute [local instance] … in` prefixes, statement, proof) was copied verbatim by
`scratch/move.py` (session tool, not committed) from the base text; the only textual changes are the
qualifier retargets listed per row, all naming the constant the source already used through the
`Hopf/LibShims.lean` aliases.

## Summary

| source file | rows at base | moved | residue (CHARGED) | blocked |
|---|---|---|---|---|
| `Hopf/LCP/Specialization.lean` | 59 | 59 | 0 | 0 |
| `Hopf/LCP/CuspFilling.lean` | 23 | 23 | 0 | 0 |
| `Hopf/LCP/BoundaryTopology.lean` | 5 | 5 | 0 | 0 |
| `Hopf/LCP/PeriodConstruction.lean` | 4 | 4 | 0 | 0 |
| `Hopf/LCP/IntegralHomology.lean` | 1 | 1 | 0 | 0 |
| `Hopf/DifferentialTopology.lean` | 2 | 2 | 0 | 0 |
| total | 94 | 94 | 0 | 0 |

Destinations: `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean` (16), `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean` (15), `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean` (54), `Lib/Geometry/Manifold/Immersion/Relative.lean` (1), `Lib/Geometry/Manifold/Morse/Cancellation.lean` (1), `Lib/Geometry/Manifold/Quotient/Atlas.lean` (5), `Lib/Geometry/Manifold/Quotient/LocalOrbit.lean` (1), `Lib/Topology/MappingTorus/Wang.lean` (1).

New modules (registered in `Lib.lean` after `CirclePaths`): `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean` (plain file, imports `Mathlib` and the
`SingularHomology` modules `Chains`, `MayerVietoris`, `HomotopyInvariance`, `CircleProduct`, `CrossProduct`,
`Torus`, `PathClass`, `CirclePaths`; `Torus.lean` itself sits upstream of `CircleProduct`/`HomotopyInvariance`/
`PathClass`, so the coordinate rows could not be appended there) and
`Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean` (imports `Chains`, `PathClass`,
`Hurewicz.HomotopyExtension` for `SingularChains.triangleFacePath`/`triangleEdges_homotopic`).

## Retargets (qualifier only, same constant)

- `FirstHurewicz. -> SingularChains.` (22 rows)
- `PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule` (14 rows)
- `PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule` (14 rows)
- `PeriodTorusHigherHomology.CircleTopology.Circle -> SingularHomology.CircleTopology.Circle` (6 rows)
- `PeriodTorusHigherHomology.crossProductHomology -> SingularHomology.crossProductHomology` (3 rows)
- `PeriodTorusHigherHomology.singularHomologyMap_id -> SingularHomology.singularHomologyMap_id` (1 rows)
- `PeriodTorusHigherHomology.singularHomologyMap_comp -> SingularHomology.singularHomologyMap_comp` (1 rows)
- declaration names `FirstHurewicz.X` -> `SingularChains.X` (16 rows; `Lib` has no `FirstHurewicz` namespace,
  the source names were the `FirstHurewicz` export of `SingularChains`, cf. `Hopf/LibShims.lean`)
- bare `CircleTopology.productSection`, `homeomorphHomologyEquiv`, `pointClass`, `singularHomologyMap_*`,
  `homotopy_homologyMap`, `circleProductHomologyEquiv*`, `circleSectionHomology`, `connectedHomologyZeroEquiv*`,
  `crossProductHomology_pointClass_right` resolve through `open SingularHomology` in `TorusCoordinates.lean`
  (the source resolved them through the `PeriodTorusHigherHomology` export of `SingularHomology`); no text change.

## Consumers

The stock files keep their headers and imports and gained the `Lib` imports of their former rows
(`Hopf/LCP/CuspFilling.lean`: `TorusCoordinates`, `FirstHurewicz`; `Hopf/LCP/Specialization.lean`:
`TorusCoordinates`, `Pontryagin`, `Quotient.Atlas`; `Hopf/LCP/BoundaryTopology.lean`: `TorusCoordinates`;
the other three already imported their destinations). The `Hopf/Proof/` twins import the stock files and
needed no edit. `Hopf/Proof/LCP/{CuspFilling,BoundaryTopology,IntegralHomology}.lean` spell
`FirstHurewicz.singularH1EquivOfPi1`, `FirstHurewicz.singularH1EquivOfPi1_loopHomologyClass`,
`FirstHurewicz.loopHomologyClass_surjective`; `Hopf/LibShims.lean` is owned by another agent in this pass, so
the alias block `namespace FirstHurewicz export SingularChains (…16 names…) end FirstHurewicz` sits in the
stock file `Hopf/LCP/CuspFilling.lean` (not a declaration; the census does not count it). The de-shim pass
(`NEXT_STEPS.md` §7) can fold it into `LibShims` or re-spell the three consumers.
`MorseCancellation.surgery_pair_inner_band_regular` (consumers `Hopf/Recognition.lean`,
`Hopf/SphereTopology.lean`) and `FrameField.isInvertible_coprod_of_bijective` (`Hopf/SingularHomology.lean`)
keep their names; the consumers reach them through `Hopf.DifferentialTopology`, which already imported
`Lib.Geometry.Manifold.Morse.Cancellation` and `Lib.Geometry.Manifold.Immersion.Relative`.

## Residue and blocked rows

CHARGED residue: none — every row of the six files was FREE (no statement mentions a project object;
`MappingTorusHomology.Covering.inverseMonodromy_period_mo1973_27385` carries a `mo1973` name suffix only,
its statement is `B ^ m = 1 → B.symm ^ m = 1` for a self-homeomorphism; the name is kept verbatim, cf.
`NEXT_STEPS.md` §5 on real names for such helpers). Blocked rows: none — the dependency harvest
(`scratch/deps.py`, identifiers of each block against the declaration index of `Lib/` and `Hopf/`) found
only intra-batch edges (`coordinateProjection`/`coordinatePeriodLoop*` from `CuspFilling` used by
`Specialization`; `BranchedQuotientAtlas.contDiffAt_transition_of_lift` from `Specialization` used by
`PeriodConstruction`), which fixed the order inside `TorusCoordinates.lean` and `Atlas.lean`.
What the stock files still hold: `Hopf/LCP/Specialization.lean`, `BoundaryTopology.lean`,
`PeriodConstruction.lean`, `IntegralHomology.lean`: header, imports, empty `noncomputable section`;
`Hopf/LCP/CuspFilling.lean`: the `FirstHurewicz` alias block; `Hopf/DifferentialTopology.lean`: three
file-level `attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2` lines (not declarations,
no longer used by anything in the file).

## Rows

### `Hopf/LCP/CuspFilling.lean` (23)

| declaration (base name) | source | destination | retargets |
|---|---|---|---|
| `FirstHurewicz.basedLoopClass_triangleFacePath → SingularChains.basedLoopClass_triangleFacePath` | `Hopf/LCP/CuspFilling.lean:151` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:42` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.edgeLoopCochain_boundaryTwo_simplex → SingularChains.edgeLoopCochain_boundaryTwo_simplex` | `Hopf/LCP/CuspFilling.lean:157` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:48` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.edgeLoopCochain_comp_boundaryTwo → SingularChains.edgeLoopCochain_comp_boundaryTwo` | `Hopf/LCP/CuspFilling.lean:176` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:67` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.edgeLoopCochain_boundaryTwo → SingularChains.edgeLoopCochain_boundaryTwo` | `Hopf/LCP/CuspFilling.lean:182` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:73` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.inverseHurewiczMap → SingularChains.inverseHurewiczMap` | `Hopf/LCP/CuspFilling.lean:186` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:77` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.inverseHurewiczMap_cycleClass → SingularChains.inverseHurewiczMap_cycleClass` | `Hopf/LCP/CuspFilling.lean:191` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:82` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.inverseHurewiczMap_loopHomologyClass → SingularChains.inverseHurewiczMap_loopHomologyClass` | `Hopf/LCP/CuspFilling.lean:197` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:88` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.inverseHurewiczMap_hurewiczMap → SingularChains.inverseHurewiczMap_hurewiczMap` | `Hopf/LCP/CuspFilling.lean:203` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:94` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.hurewiczMap_inverseHurewiczMap → SingularChains.hurewiczMap_inverseHurewiczMap` | `Hopf/LCP/CuspFilling.lean:208` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:99` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.firstHurewiczEquivOfPaths → SingularChains.firstHurewiczEquivOfPaths` | `Hopf/LCP/CuspFilling.lean:215` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:106` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.firstHurewiczEquiv → SingularChains.firstHurewiczEquiv` | `Hopf/LCP/CuspFilling.lean:223` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:114` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.firstHurewiczEquiv_loopClass → SingularChains.firstHurewiczEquiv_loopClass` | `Hopf/LCP/CuspFilling.lean:228` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:119` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.loopHomologyClass_surjective → SingularChains.loopHomologyClass_surjective` | `Hopf/LCP/CuspFilling.lean:233` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:124` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.singularH1EquivOfPi1 → SingularChains.singularH1EquivOfPi1` | `Hopf/LCP/CuspFilling.lean:241` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:132` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.singularH1EquivOfPi1_hurewiczFunction → SingularChains.singularH1EquivOfPi1_hurewiczFunction` | `Hopf/LCP/CuspFilling.lean:247` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:138` | FirstHurewicz. -> SingularChains. |
| `FirstHurewicz.singularH1EquivOfPi1_loopHomologyClass → SingularChains.singularH1EquivOfPi1_loopHomologyClass` | `Hopf/LCP/CuspFilling.lean:259` | `Lib/AlgebraicTopology/SingularHomology/FirstHurewicz.lean:150` | FirstHurewicz. -> SingularChains. |
| `PeriodTorusHigherHomology.coordinateProjection` | `Hopf/LCP/CuspFilling.lean:265` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:50` | — |
| `PeriodTorusHigherHomology.coordinateProjection_apply` | `Hopf/LCP/CuspFilling.lean:272` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:57` | — |
| `PeriodTorusHigherHomology.coordinateProjection_continuous` | `Hopf/LCP/CuspFilling.lean:276` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:61` | — |
| `PeriodTorusHigherHomology.coordinateProjection_eq_zero_iff` | `Hopf/LCP/CuspFilling.lean:280` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:65` | — |
| `PeriodTorusHigherHomology.coordinateProjection_surjective` | `Hopf/LCP/CuspFilling.lean:297` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:82` | — |
| `PeriodTorusHigherHomology.coordinatePeriodLoop` | `Hopf/LCP/CuspFilling.lean:306` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:91` | — |
| `PeriodTorusHigherHomology.coordinatePeriodLoop_apply` | `Hopf/LCP/CuspFilling.lean:314` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:99` | — |

### `Hopf/LCP/BoundaryTopology.lean` (5)

| declaration (base name) | source | destination | retargets |
|---|---|---|---|
| `PeriodTorusHigherHomology.rightTranslation` | `Hopf/LCP/BoundaryTopology.lean:170` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:106` | — |
| `PeriodTorusHigherHomology.rightTranslation_apply` | `Hopf/LCP/BoundaryTopology.lean:175` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:111` | — |
| `PeriodTorusHigherHomology.rightTranslationHomotopyAlong` | `Hopf/LCP/BoundaryTopology.lean:179` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:115` | — |
| `PeriodTorusHigherHomology.rightTranslation_singularHomologyMap_of_path` | `Hopf/LCP/BoundaryTopology.lean:188` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:124` | — |
| `PeriodTorusHigherHomology.rightTranslation_singularHomologyMap` | `Hopf/LCP/BoundaryTopology.lean:194` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:130` | — |

### `Hopf/LCP/Specialization.lean` (59)

| declaration (base name) | source | destination | retargets |
|---|---|---|---|
| `PeriodTorusHigherHomologyPontryagin.product_natural` | `Hopf/LCP/Specialization.lean:156` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:251` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule; PeriodTorusHigherHomology.crossProductHomology -> SingularHomology.crossProductHomology |
| `PeriodTorusHigherHomologyPontryagin.tripleProduct_natural` | `Hopf/LCP/Specialization.lean:171` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:266` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomologyPontryagin.tripleProduct_eq_cross` | `Hopf/LCP/Specialization.lean:188` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:283` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule; PeriodTorusHigherHomology.singularHomologyMap_id -> SingularHomology.singularHomologyMap_id; PeriodTorusHigherHomology.singularHomologyMap_comp -> SingularHomology.singularHomologyMap_comp; PeriodTorusHigherHomology.crossProductHomology -> SingularHomology.crossProductHomology |
| `PeriodTorusHigherHomology.coordinatePeriodLoop_eq_projection` | `Hopf/LCP/Specialization.lean:228` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:135` | — |
| `PeriodTorusHigherHomology.torusTailMap` | `Hopf/LCP/Specialization.lean:235` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:142` | — |
| `PeriodTorusHigherHomology.torusTailMap_apply` | `Hopf/LCP/Specialization.lean:240` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:147` | — |
| `PeriodTorusHigherHomology.torusTailMap_add` | `Hopf/LCP/Specialization.lean:244` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:151` | — |
| `PeriodTorusHigherHomology.torusTailMap_zero` | `Hopf/LCP/Specialization.lean:250` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:157` | — |
| `PeriodTorusHigherHomology.torusTailMap_coordinatePeriodLoop` | `Hopf/LCP/Specialization.lean:254` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:161` | — |
| `PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology` | `Hopf/LCP/Specialization.lean:269` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:176` | FirstHurewicz. -> SingularChains. |
| `PeriodTorusHigherHomologyPontryagin.product11_skew` | `Hopf/LCP/Specialization.lean:279` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:325` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomologyPontryagin.product11_self` | `Hopf/LCP/Specialization.lean:285` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:331` | — |
| `PeriodTorusHigherHomologyPontryagin.homologyAlternatingTwo` | `Hopf/LCP/Specialization.lean:293` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:339` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo` | `Hopf/LCP/Specialization.lean:302` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:348` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo_apply_ιMulti` | `Hopf/LCP/Specialization.lean:312` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:358` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomologyPontryagin.tripleProduct_cyclic` | `Hopf/LCP/Specialization.lean:321` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:367` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule; PeriodTorusHigherHomology.crossProductHomology -> SingularHomology.crossProductHomology |
| `PeriodTorusHigherHomologyPontryagin.tripleProduct_self12` | `Hopf/LCP/Specialization.lean:339` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:385` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomologyPontryagin.tripleProduct_self02` | `Hopf/LCP/Specialization.lean:347` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:393` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomologyPontryagin.tripleProduct_self01` | `Hopf/LCP/Specialization.lean:355` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:401` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomologyPontryagin.homologyAlternatingThree` | `Hopf/LCP/Specialization.lean:363` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:409` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomologyPontryagin.homologyWedgeThree` | `Hopf/LCP/Specialization.lean:373` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:419` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomologyPontryagin.homologyWedgeThree_apply_ιMulti` | `Hopf/LCP/Specialization.lean:383` | `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean:429` | PeriodTorusHigherHomology.integerLinearMapModule -> SingularHomology.integerLinearMapModule; PeriodTorusHigherHomology.integerTensorModule -> SingularHomology.integerTensorModule |
| `PeriodTorusHigherHomology.omitHeadMatrix` | `Hopf/LCP/Specialization.lean:390` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:184` | — |
| `PeriodTorusHigherHomology.takeHeadMatrix` | `Hopf/LCP/Specialization.lean:394` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:188` | — |
| `PeriodTorusHigherHomology.coordinateTorusMap` | `Hopf/LCP/Specialization.lean:398` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:192` | PeriodTorusHigherHomology.CircleTopology.Circle -> SingularHomology.CircleTopology.Circle |
| `PeriodTorusHigherHomology.coordinateTorusMap_degree_zero` | `Hopf/LCP/Specialization.lean:420` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:214` | — |
| `PeriodTorusHigherHomology.coordinateTorusMap_omit_apply` | `Hopf/LCP/Specialization.lean:424` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:218` | — |
| `PeriodTorusHigherHomology.coordinateTorusMap_take_apply` | `Hopf/LCP/Specialization.lean:432` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:226` | — |
| `PeriodTorusHigherHomology.coordinateTorusMap_omit` | `Hopf/LCP/Specialization.lean:439` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:233` | PeriodTorusHigherHomology.CircleTopology.Circle -> SingularHomology.CircleTopology.Circle |
| `PeriodTorusHigherHomology.coordinateTorusMap_take` | `Hopf/LCP/Specialization.lean:455` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:249` | PeriodTorusHigherHomology.CircleTopology.Circle -> SingularHomology.CircleTopology.Circle |
| `PeriodTorusHigherHomology.coordinateTorusMatrix` | `Hopf/LCP/Specialization.lean:474` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:268` | — |
| `PeriodTorusHigherHomology.coordinateTorusMatrix_omit` | `Hopf/LCP/Specialization.lean:485` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:279` | — |
| `PeriodTorusHigherHomology.coordinateTorusMatrix_take` | `Hopf/LCP/Specialization.lean:492` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:286` | — |
| `PeriodTorusHigherHomology.coordinateTorusClass` | `Hopf/LCP/Specialization.lean:497` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:291` | — |
| `PeriodTorusHigherHomology.coordinateTorusClass_zero` | `Hopf/LCP/Specialization.lean:502` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:296` | — |
| `PeriodTorusHigherHomology.homeomorphHomology_coordinateTorusMap_omit` | `Hopf/LCP/Specialization.lean:508` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:302` | PeriodTorusHigherHomology.CircleTopology.Circle -> SingularHomology.CircleTopology.Circle |
| `PeriodTorusHigherHomology.homeomorphHomology_coordinateTorusMap_take` | `Hopf/LCP/Specialization.lean:531` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:325` | PeriodTorusHigherHomology.CircleTopology.Circle -> SingularHomology.CircleTopology.Circle |
| `PeriodTorusHigherHomology.circleCoordinates_coordinateTorusClass_omit` | `Hopf/LCP/Specialization.lean:554` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:348` | — |
| `PeriodTorusHigherHomology.circleCoordinates_coordinateTorusClass_take` | `Hopf/LCP/Specialization.lean:564` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:358` | — |
| `PeriodTorusHigherHomology.productTorusHomologyEquiv_succ_pair` | `Hopf/LCP/Specialization.lean:575` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:369` | — |
| `PeriodTorusHigherHomology.productTorusHomologyEquiv_coordinateTorusClass_zero` | `Hopf/LCP/Specialization.lean:584` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:378` | — |
| `PeriodTorusHigherHomology.productTorusHomologyEquiv_coordinateTorusClass` | `Hopf/LCP/Specialization.lean:595` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:389` | — |
| `PeriodTorusHigherHomology.coordinateTorusBasis` | `Hopf/LCP/Specialization.lean:628` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:422` | — |
| `PeriodTorusHigherHomology.coordinateTorusBasis_apply` | `Hopf/LCP/Specialization.lean:634` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:428` | — |
| `PeriodTorusHigherHomology.coordinateTorusMapAlong` | `Hopf/LCP/Specialization.lean:640` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:434` | — |
| `PeriodTorusHigherHomology.coordinateTorusClassAlong` | `Hopf/LCP/Specialization.lean:644` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:438` | — |
| `PeriodTorusHigherHomology.coordinateTorusBasisAlong` | `Hopf/LCP/Specialization.lean:650` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:444` | — |
| `PeriodTorusHigherHomology.coordinateTorusBasisAlong_apply` | `Hopf/LCP/Specialization.lean:656` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:450` | — |
| `PeriodTorusHigherHomology.coordinateTorusBasisAlong_coe` | `Hopf/LCP/Specialization.lean:671` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:465` | — |
| `PeriodTorusHigherHomology.coordinateTorusClassAlong_span` | `Hopf/LCP/Specialization.lean:676` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:470` | — |
| `PeriodTorusHigherHomology.surjective_of_coordinateTorusClassAlong_mem_range` | `Hopf/LCP/Specialization.lean:681` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:475` | — |
| `PeriodTorusHigherHomology.homeomorph_symm_add_of_add` | `Hopf/LCP/Specialization.lean:693` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:487` | — |
| `PeriodTorusHigherHomology.coordinateH1Add` | `Hopf/LCP/Specialization.lean:699` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:493` | FirstHurewicz. -> SingularChains. |
| `PeriodTorusHigherHomology.coordinateH1` | `Hopf/LCP/Specialization.lean:706` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:500` | FirstHurewicz. -> SingularChains. |
| `PeriodTorusHigherHomology.coordinateH1_basis` | `Hopf/LCP/Specialization.lean:716` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:510` | FirstHurewicz. -> SingularChains. |
| `PeriodTorusHigherHomology.coordinateH1_single` | `Hopf/LCP/Specialization.lean:722` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:516` | FirstHurewicz. -> SingularChains. |
| `PeriodTorusHigherHomology.positiveCircleCross_pointClass` | `Hopf/LCP/Specialization.lean:727` | `Lib/AlgebraicTopology/SingularHomology/TorusCoordinates.lean:521` | PeriodTorusHigherHomology.CircleTopology.Circle -> SingularHomology.CircleTopology.Circle; FirstHurewicz. -> SingularChains. |
| `BranchedQuotientAtlas.project_localInverse_eventuallyEq` | `Hopf/LCP/Specialization.lean:734` | `Lib/Geometry/Manifold/Quotient/Atlas.lean:261` | — |
| `BranchedQuotientAtlas.contDiffAt_transition_of_lift` | `Hopf/LCP/Specialization.lean:759` | `Lib/Geometry/Manifold/Quotient/Atlas.lean:286` | — |

### `Hopf/LCP/PeriodConstruction.lean` (4)

| declaration (base name) | source | destination | retargets |
|---|---|---|---|
| `BranchedQuotientAtlas.Data.contDiffOn_transition` | `Hopf/LCP/PeriodConstruction.lean:158` | `Lib/Geometry/Manifold/Quotient/Atlas.lean:317` | — |
| `BranchedQuotientAtlas.Data.isManifold` | `Hopf/LCP/PeriodConstruction.lean:174` | `Lib/Geometry/Manifold/Quotient/Atlas.lean:333` | — |
| `BranchedQuotientAtlas.Data.contMDiff_project` | `Hopf/LCP/PeriodConstruction.lean:184` | `Lib/Geometry/Manifold/Quotient/Atlas.lean:343` | — |
| `LocalOrbitQuotient.localHomeomorph` | `Hopf/LCP/PeriodConstruction.lean:203` | `Lib/Geometry/Manifold/Quotient/LocalOrbit.lean:181` | — |

### `Hopf/LCP/IntegralHomology.lean` (1)

| declaration (base name) | source | destination | retargets |
|---|---|---|---|
| `MappingTorusHomology.Covering.inverseMonodromy_period_mo1973_27385` | `Hopf/LCP/IntegralHomology.lean:173` | `Lib/Topology/MappingTorus/Wang.lean:445` | — |

### `Hopf/DifferentialTopology.lean` (2)

| declaration (base name) | source | destination | retargets |
|---|---|---|---|
| `MorseCancellation.surgery_pair_inner_band_regular` | `Hopf/DifferentialTopology.lean:103` | `Lib/Geometry/Manifold/Morse/Cancellation.lean:6360` | — |
| `FrameField.isInvertible_coprod_of_bijective` | `Hopf/DifferentialTopology.lean:112` | `Lib/Geometry/Manifold/Immersion/Relative.lean:4642` | — |

## Build and census

```
stock declarations under Hopf/: 1492  (prefixes: 222, prefixes now absent from Hopf/: 86)
ratchet PASS: 1492 <= baseline 1648
```

Full chain `lake build Lib && lake build Solution S6Shortcuts S6 Challenge` (`scratch/build.log`, not committed):

```
Build completed successfully (8819 jobs).
Build completed successfully (8858 jobs).
error: lines: 0
last job lines: ✔ [8856/8858] Built Hopf.Proof.Final (8.8s) | ℹ [8857/8858] Built Solution (5.7s)
```
