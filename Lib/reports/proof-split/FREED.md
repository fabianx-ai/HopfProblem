# Demoted rows freed by the corrected dependency rule (integration 4, 2026-09-14)

`DEMOTED.md` (475 rows) was computed with an edge for every constant a declaration uses, including
another declaration's `_proof_n` auxiliary constants. Lean reuses an identical abstracted proof within a
module, so `X` using `Y._proof_1` does not mean `X` uses `Y`: the edge is spurious. The Muse seat's S-path
move (integration 4) showed it in practice: 62 "demoted" rows compiled in `Lib/` without any `Hopf` import.
Recomputed from the same table (`dump_base.jsonl` at `2e28cf5b`) with `_proof_n` edges dropped
(`scripts/proof_split_plan.py --skip-proof-aux-edges`, script `int4_redemote.py` in the session notes):
stock 2328, keep 2028, demoted 300. The 175 rows below are pure moves. They live where the split put them
(`Hopf/Proof/`, not census-counted) or already in `Lib/`; they are not moved back to the stock files.

| family | rows | in `Lib/` already | still under `Hopf/Proof/` | lane |
|---|---|---|---|---|
| MappingTorusHomology | 73 | 0 | 73 | I (GLM, Wang) |
| PeriodTorusHigherHomology | 102 | 62 | 40 | J (Muse) |

## MappingTorusHomology (73)

| declaration | now in |
|---|---|
| `MappingTorusHomology.Covering.affineCircleArc` | `Hopf/Proof/LCP/IntegralHomology.lean:7931` |
| `MappingTorusHomology.Covering.affineCircleArc_apply` | `Hopf/Proof/LCP/IntegralHomology.lean:7936` |
| `MappingTorusHomology.Covering.affineCircleArc_self` | `Hopf/Proof/LCP/IntegralHomology.lean:7942` |
| `MappingTorusHomology.Covering.affineCircleArc_trans_homotopic` | `Hopf/Proof/LCP/IntegralHomology.lean:7949` |
| `MappingTorusHomology.Covering.arcSumChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8061` |
| `MappingTorusHomology.Covering.arcSumCycle` | `Hopf/Proof/LCP/IntegralHomology.lean:8070` |
| `MappingTorusHomology.Covering.arcSumCycle_positiveLoop_class` | `Hopf/Proof/LCP/IntegralHomology.lean:8100` |
| `MappingTorusHomology.Covering.arcSumCycle_val` | `Hopf/Proof/LCP/IntegralHomology.lean:8075` |
| `MappingTorusHomology.Covering.boundaryOne_arcPrefix` | `Hopf/Proof/LCP/IntegralHomology.lean:8030` |
| `MappingTorusHomology.Covering.boundaryOne_arcSumChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8066` |
| `MappingTorusHomology.Covering.chainClass_arcPrefix` | `Hopf/Proof/LCP/IntegralHomology.lean:8046` |
| `MappingTorusHomology.Covering.chainClass_arcSumChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8080` |
| `MappingTorusHomology.Covering.coverSmallCycle` | `Hopf/Proof/LCP/IntegralHomology.lean:8421` |
| `MappingTorusHomology.Covering.coverSmallCycle_ambient_sum_val` | `Hopf/Proof/LCP/IntegralHomology.lean:8449` |
| `MappingTorusHomology.Covering.coverSmallCycle_ambient_val` | `Hopf/Proof/LCP/IntegralHomology.lean:8433` |
| `MappingTorusHomology.Covering.coverSmallCycle_boundaryCoordinates` | `Hopf/Proof/LCP/IntegralHomology.lean:8485` |
| `MappingTorusHomology.Covering.coverSmallCycle_connecting` | `Hopf/Proof/LCP/IntegralHomology.lean:8464` |
| `MappingTorusHomology.Covering.differenceCycle` | `Hopf/Proof/LCP/IntegralHomology.lean:8317` |
| `MappingTorusHomology.Covering.differenceCycle_class` | `Hopf/Proof/LCP/IntegralHomology.lean:8384` |
| `MappingTorusHomology.Covering.differenceCycle_class_coordinates` | `Hopf/Proof/LCP/IntegralHomology.lean:8402` |
| `MappingTorusHomology.Covering.differenceCycle_val` | `Hopf/Proof/LCP/IntegralHomology.lean:8331` |
| `MappingTorusHomology.Covering.eq_comp_circleBoundary_of_section_cross` | `Hopf/Proof/LCP/IntegralHomology.lean:8540` |
| `MappingTorusHomology.Covering.eq_comp_circleBoundary_of_section_cross_apply` | `Hopf/Proof/LCP/IntegralHomology.lean:8522` |
| `MappingTorusHomology.Covering.homologyNorm_eq_sum_powers` | `Hopf/Proof/LCP/IntegralHomology.lean:8248` |
| `MappingTorusHomology.Covering.lowerSection` | `Hopf/Proof/LCP/IntegralHomology.lean:7670` |
| `MappingTorusHomology.Covering.lowerSection_chain_sum_shift` | `Hopf/Proof/LCP/IntegralHomology.lean:8342` |
| `MappingTorusHomology.Covering.lowerSection_component` | `Hopf/Proof/LCP/IntegralHomology.lean:7804` |
| `MappingTorusHomology.Covering.lowerSection_homology_coordinates` | `Hopf/Proof/LCP/IntegralHomology.lean:7820` |
| `MappingTorusHomology.Covering.lowerSection_period` | `Hopf/Proof/LCP/IntegralHomology.lean:7795` |
| `MappingTorusHomology.Covering.lowerSection_val` | `Hopf/Proof/LCP/IntegralHomology.lean:7692` |
| `MappingTorusHomology.Covering.monodromyHomologyMap_pow` | `Hopf/Proof/LCP/IntegralHomology.lean:8240` |
| `MappingTorusHomology.Covering.monodromyHomologyMonoidHom` | `Hopf/Proof/LCP/IntegralHomology.lean:8233` |
| `MappingTorusHomology.Covering.pathClass_affineCircleArc_add` | `Hopf/Proof/LCP/IntegralHomology.lean:7962` |
| `MappingTorusHomology.Covering.pathClass_affineCircleArc_period` | `Hopf/Proof/LCP/IntegralHomology.lean:8086` |
| `MappingTorusHomology.Covering.pathClass_uPath_add_vPath` | `Hopf/Proof/LCP/IntegralHomology.lean:8012` |
| `MappingTorusHomology.Covering.positiveCircleCross_subdivision_cycleClass` | `Hopf/Proof/LCP/IntegralHomology.lean:8209` |
| `MappingTorusHomology.Covering.quarterLift` | `Hopf/Proof/LCP/IntegralHomology.lean:7969` |
| `MappingTorusHomology.Covering.quarterLift_circle_period` | `Hopf/Proof/LCP/IntegralHomology.lean:8024` |
| `MappingTorusHomology.Covering.quarterLift_period` | `Hopf/Proof/LCP/IntegralHomology.lean:8017` |
| `MappingTorusHomology.Covering.sub_cross_boundary_mem_range_circleSection` | `Hopf/Proof/LCP/IntegralHomology.lean:8504` |
| `MappingTorusHomology.Covering.threeQuarterLift` | `Hopf/Proof/LCP/IntegralHomology.lean:7972` |
| `MappingTorusHomology.Covering.uCircleMap` | `Hopf/Proof/LCP/IntegralHomology.lean:8110` |
| `MappingTorusHomology.Covering.uCircleMap_pathChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8116` |
| `MappingTorusHomology.Covering.uCrossChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8257` |
| `MappingTorusHomology.Covering.uCrossChainSum` | `Hopf/Proof/LCP/IntegralHomology.lean:8305` |
| `MappingTorusHomology.Covering.uCrossChainSum_boundary` | `Hopf/Proof/LCP/IntegralHomology.lean:8354` |
| `MappingTorusHomology.Covering.uCrossChain_boundary` | `Hopf/Proof/LCP/IntegralHomology.lean:8273` |
| `MappingTorusHomology.Covering.uPath` | `Hopf/Proof/LCP/IntegralHomology.lean:7975` |
| `MappingTorusHomology.Covering.uPath_apply` | `Hopf/Proof/LCP/IntegralHomology.lean:7985` |
| `MappingTorusHomology.Covering.uStrip` | `Hopf/Proof/LCP/IntegralHomology.lean:7716` |
| `MappingTorusHomology.Covering.uStrip_one` | `Hopf/Proof/LCP/IntegralHomology.lean:7758` |
| `MappingTorusHomology.Covering.uStrip_val` | `Hopf/Proof/LCP/IntegralHomology.lean:7733` |
| `MappingTorusHomology.Covering.uStrip_zero` | `Hopf/Proof/LCP/IntegralHomology.lean:7747` |
| `MappingTorusHomology.Covering.uTime` | `Hopf/Proof/LCP/IntegralHomology.lean:7704` |
| `MappingTorusHomology.Covering.uTime_continuous` | `Hopf/Proof/LCP/IntegralHomology.lean:7707` |
| `MappingTorusHomology.Covering.upperSection` | `Hopf/Proof/LCP/IntegralHomology.lean:7681` |
| `MappingTorusHomology.Covering.upperSection_component` | `Hopf/Proof/LCP/IntegralHomology.lean:7812` |
| `MappingTorusHomology.Covering.upperSection_homology_coordinates` | `Hopf/Proof/LCP/IntegralHomology.lean:7830` |
| `MappingTorusHomology.Covering.upperSection_val` | `Hopf/Proof/LCP/IntegralHomology.lean:7698` |
| `MappingTorusHomology.Covering.vCircleMap` | `Hopf/Proof/LCP/IntegralHomology.lean:8113` |
| `MappingTorusHomology.Covering.vCircleMap_pathChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8123` |
| `MappingTorusHomology.Covering.vCrossChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8265` |
| `MappingTorusHomology.Covering.vCrossChainSum` | `Hopf/Proof/LCP/IntegralHomology.lean:8311` |
| `MappingTorusHomology.Covering.vCrossChainSum_boundary` | `Hopf/Proof/LCP/IntegralHomology.lean:8363` |
| `MappingTorusHomology.Covering.vCrossChain_boundary` | `Hopf/Proof/LCP/IntegralHomology.lean:8289` |
| `MappingTorusHomology.Covering.vPath` | `Hopf/Proof/LCP/IntegralHomology.lean:7980` |
| `MappingTorusHomology.Covering.vPath_apply` | `Hopf/Proof/LCP/IntegralHomology.lean:7998` |
| `MappingTorusHomology.Covering.vStrip` | `Hopf/Proof/LCP/IntegralHomology.lean:7724` |
| `MappingTorusHomology.Covering.vStrip_one` | `Hopf/Proof/LCP/IntegralHomology.lean:7783` |
| `MappingTorusHomology.Covering.vStrip_val` | `Hopf/Proof/LCP/IntegralHomology.lean:7740` |
| `MappingTorusHomology.Covering.vStrip_zero` | `Hopf/Proof/LCP/IntegralHomology.lean:7769` |
| `MappingTorusHomology.Covering.vTime` | `Hopf/Proof/LCP/IntegralHomology.lean:7710` |
| `MappingTorusHomology.Covering.vTime_continuous` | `Hopf/Proof/LCP/IntegralHomology.lean:7713` |

## PeriodTorusHigherHomology (102)

| declaration | now in |
|---|---|
| `PeriodTorusHigherHomology.CirclePaths.arcSumCycle` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:623` |
| `PeriodTorusHigherHomology.CirclePaths.arcSumCycle_class` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:628` |
| `PeriodTorusHigherHomology.CirclePaths.arcSumCycle_positiveLoop_class` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:642` |
| `PeriodTorusHigherHomology.CirclePaths.boundaryOne_arcSum` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:616` |
| `PeriodTorusHigherHomology.CirclePaths.quarterIntersection` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:425` |
| `PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:647` |
| `PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection_comp` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:679` |
| `PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection_component` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:663` |
| `PeriodTorusHigherHomology.CirclePaths.quarterIntersection_component` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:450` |
| `PeriodTorusHigherHomology.CirclePaths.quarterLoop` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:555` |
| `PeriodTorusHigherHomology.CirclePaths.quarterLoop_apply` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:568` |
| `PeriodTorusHigherHomology.CirclePaths.quarterLoop_eq_translation` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:590` |
| `PeriodTorusHigherHomology.CirclePaths.quarterLoop_homologyClass` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:602` |
| `PeriodTorusHigherHomology.CirclePaths.quarterPoint` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:437` |
| `PeriodTorusHigherHomology.CirclePaths.quarterPoint_coe` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:445` |
| `PeriodTorusHigherHomology.CirclePaths.quarterTranslation_zero` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:585` |
| `PeriodTorusHigherHomology.CirclePaths.quarterU` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:462` |
| `PeriodTorusHigherHomology.CirclePaths.quarterV` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:466` |
| `PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersection` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:431` |
| `PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:655` |
| `PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection_comp` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:705` |
| `PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection_component` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:688` |
| `PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersection_component` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:456` |
| `PeriodTorusHigherHomology.CirclePaths.threeQuarterPoint` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:441` |
| `PeriodTorusHigherHomology.CirclePaths.threeQuarterU` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:470` |
| `PeriodTorusHigherHomology.CirclePaths.threeQuarterV` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:474` |
| `PeriodTorusHigherHomology.CirclePaths.uCirclePath` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:537` |
| `PeriodTorusHigherHomology.CirclePaths.uCirclePath_apply` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:543` |
| `PeriodTorusHigherHomology.CirclePaths.uCirclePath_trans_vCirclePath` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:574` |
| `PeriodTorusHigherHomology.CirclePaths.uPath` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:478` |
| `PeriodTorusHigherHomology.CirclePaths.vCirclePath` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:540` |
| `PeriodTorusHigherHomology.CirclePaths.vCirclePath_apply` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:549` |
| `PeriodTorusHigherHomology.CirclePaths.vPath` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:507` |
| `PeriodTorusHigherHomology.arcCrossChains_inclusion_sum` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:942` |
| `PeriodTorusHigherHomology.circleBoundaryCoordinates_positiveCircleCross` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:1044` |
| `PeriodTorusHigherHomology.circleBoundaryCoordinates_positiveCircleCross_cycleClass` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:1025` |
| `PeriodTorusHigherHomology.circleBoundary_positiveCircleCross` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:1052` |
| `PeriodTorusHigherHomology.circleConnecting_positiveCircleCross_cycleClass` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:1005` |
| `PeriodTorusHigherHomology.circleHomologyOneEquiv_positiveLoop` | `Hopf/Proof/LCP/Specialization.lean:5508` |
| `PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_int` | `Hopf/Proof/LCP/Specialization.lean:5521` |
| `PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_one` | `Hopf/Proof/LCP/Specialization.lean:5515` |
| `PeriodTorusHigherHomology.circleProductHomologyEquiv_positiveCircleCross` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:1059` |
| `PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_eq_section_add_cross` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:1073` |
| `PeriodTorusHigherHomology.coordinateCircleMap` | `Hopf/Proof/LCP/Specialization.lean:3233` |
| `PeriodTorusHigherHomology.coordinateCircleMap_add` | `Hopf/Proof/LCP/Specialization.lean:3251` |
| `PeriodTorusHigherHomology.coordinateCircleMap_apply` | `Hopf/Proof/LCP/Specialization.lean:3239` |
| `PeriodTorusHigherHomology.coordinateCircleMap_positiveHomology` | `Hopf/Proof/LCP/Specialization.lean:3276` |
| `PeriodTorusHigherHomology.coordinateCircleMap_positiveLoop` | `Hopf/Proof/LCP/Specialization.lean:3268` |
| `PeriodTorusHigherHomology.coordinateCircleMap_positiveLoop_apply` | `Hopf/Proof/LCP/Specialization.lean:3257` |
| `PeriodTorusHigherHomology.coordinateCircleMap_zero` | `Hopf/Proof/LCP/Specialization.lean:3245` |
| `PeriodTorusHigherHomology.coordinateTorusMapAlong_add` | `Hopf/Proof/LCP/Specialization.lean:3714` |
| `PeriodTorusHigherHomology.coordinateTorusMap_add` | `Hopf/Proof/LCP/Specialization.lean:3706` |
| `PeriodTorusHigherHomology.coordinateTorusMap_eq_torusMatrixMap` | `Hopf/Proof/LCP/Specialization.lean:3623` |
| `PeriodTorusHigherHomology.intersectionDifferenceCycle` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:760` |
| `PeriodTorusHigherHomology.intersectionDifferenceCycle_class_coordinates` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:788` |
| `PeriodTorusHigherHomology.intersectionDifferenceCycle_val` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:772` |
| `PeriodTorusHigherHomology.positiveCircleCross_arcSum_cycleClass` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:714` |
| `PeriodTorusHigherHomology.positiveCircleCross_eq_symm` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:1067` |
| `PeriodTorusHigherHomology.positiveCircleCross_naturality` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:1085` |
| `PeriodTorusHigherHomology.positiveCircleSmallCycle` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:952` |
| `PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_class` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:989` |
| `PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_eq` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:977` |
| `PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_val` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:961` |
| `PeriodTorusHigherHomology.productTorusSucc_inverse_eq_add` | `Hopf/Proof/LCP/Specialization.lean:3328` |
| `PeriodTorusHigherHomology.productTorusTopClass_one` | `Hopf/Proof/LCP/Specialization.lean:3387` |
| `PeriodTorusHigherHomology.productTorusTopClass_succ_cross` | `Hopf/Proof/LCP/Specialization.lean:3363` |
| `PeriodTorusHigherHomology.productTorusTopClass_succ_product` | `Hopf/Proof/LCP/Specialization.lean:3378` |
| `PeriodTorusHigherHomology.productTorusTopClass_three` | `Hopf/Proof/LCP/Specialization.lean:3415` |
| `PeriodTorusHigherHomology.productTorusTopClass_three_is_tripleProduct` | `Hopf/Proof/LCP/Specialization.lean:3557` |
| `PeriodTorusHigherHomology.productTorusTopClass_two` | `Hopf/Proof/LCP/Specialization.lean:3405` |
| `PeriodTorusHigherHomology.productTorusTopClass_two_is_product` | `Hopf/Proof/LCP/Specialization.lean:3548` |
| `PeriodTorusHigherHomology.quarterIntersectionHomology_coordinates` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:740` |
| `PeriodTorusHigherHomology.quarterIntersectionSection_toU` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:816` |
| `PeriodTorusHigherHomology.quarterIntersectionSection_toV` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:823` |
| `PeriodTorusHigherHomology.threeQuarterIntersectionHomology_coordinates` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:750` |
| `PeriodTorusHigherHomology.threeQuarterIntersectionSection_toU` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:830` |
| `PeriodTorusHigherHomology.threeQuarterIntersectionSection_toV` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:839` |
| `PeriodTorusHigherHomology.torusHeadCircleMap` | `Hopf/Proof/LCP/Specialization.lean:3314` |
| `PeriodTorusHigherHomology.torusHeadCircleMap_apply` | `Hopf/Proof/LCP/Specialization.lean:3318` |
| `PeriodTorusHigherHomology.torusHeadCircleMap_positiveHomology` | `Hopf/Proof/LCP/Specialization.lean:3357` |
| `PeriodTorusHigherHomology.torusMatrixLinearMap` | `Hopf/Proof/LCP/Specialization.lean:2539` |
| `PeriodTorusHigherHomology.torusMatrixLinearMap_continuous` | `Hopf/Proof/LCP/Specialization.lean:2556` |
| `PeriodTorusHigherHomology.torusMatrixMap` | `Hopf/Proof/LCP/Specialization.lean:2563` |
| `PeriodTorusHigherHomology.torusMatrixMap_add` | `Hopf/Proof/LCP/Specialization.lean:3701` |
| `PeriodTorusHigherHomology.torusMatrixMap_apply` | `Hopf/Proof/LCP/Specialization.lean:2567` |
| `PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology` | `Hopf/Proof/LCP/Specialization.lean:3306` |
| `PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodLoop` | `Hopf/Proof/LCP/Specialization.lean:3298` |
| `PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodLoop_apply` | `Hopf/Proof/LCP/Specialization.lean:3284` |
| `PeriodTorusHigherHomology.torusMatrixMap_coordinateProjection` | `Hopf/Proof/LCP/Specialization.lean:2572` |
| `PeriodTorusHigherHomology.torusMatrixMap_mul` | `Hopf/Proof/LCP/Specialization.lean:2594` |
| `PeriodTorusHigherHomology.torusMatrixMap_omitHeadMatrix` | `Hopf/Proof/LCP/Specialization.lean:3593` |
| `PeriodTorusHigherHomology.torusMatrixMap_one` | `Hopf/Proof/LCP/Specialization.lean:2586` |
| `PeriodTorusHigherHomology.torusMatrixMap_takeHeadMatrix` | `Hopf/Proof/LCP/Specialization.lean:3604` |
| `PeriodTorusHigherHomology.torusMatrixMap_zero` | `Hopf/Proof/LCP/Specialization.lean:3293` |
| `PeriodTorusHigherHomology.torusMatrixMap_zero_source` | `Hopf/Proof/LCP/Specialization.lean:3614` |
| `PeriodTorusHigherHomology.torusSplit_positiveCircleCross` | `Hopf/Proof/LCP/Specialization.lean:3341` |
| `PeriodTorusHigherHomology.uCrossChain` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:848` |
| `PeriodTorusHigherHomology.uCrossChain_boundary` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:866` |
| `PeriodTorusHigherHomology.uCrossChain_inclusion` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:906` |
| `PeriodTorusHigherHomology.vCrossChain` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:857` |
| `PeriodTorusHigherHomology.vCrossChain_boundary` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:886` |
| `PeriodTorusHigherHomology.vCrossChain_inclusion` | `Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean:924` |
