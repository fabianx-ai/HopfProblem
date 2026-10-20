# Receipt: freed `MappingTorusHomology` rows into `Lib/Topology/MappingTorus/Wang.lean`

`NEXT_STEPS.md` item 5, MappingTorusHomology part. Branch `lib/next-wang`, commit `7e01c4f2`
(`feat: move 73 freed MappingTorusHomology.Covering rows into Lib Wang`), 2026-09-14.

## Moved (73 of 73)

All 73 `MappingTorusHomology.Covering.*` rows of `Lib/reports/proof-split/FREED.md` moved as whole
declaration blocks (attributes, declaration, proof), text verbatim, in source order, appended to
`Lib/Topology/MappingTorus/Wang.lean` (now 1,152 lines; no second file needed). Source lines are
those of the parent commit `304a0fea`; destination lines are those of `7e01c4f2`. Every block's
references were checked: each names a constant already in `Lib/`, a Mathlib constant, or an earlier
row of the same move. No row is blocked.

| Declaration | Source (before) | Destination (after) |
|---|---|---|
| `MappingTorusHomology.Covering.lowerSection` | `Hopf/Proof/LCP/IntegralHomology.lean:7670` | `Lib/Topology/MappingTorus/Wang.lean:445` |
| `MappingTorusHomology.Covering.upperSection` | `Hopf/Proof/LCP/IntegralHomology.lean:7681` | `Lib/Topology/MappingTorus/Wang.lean:456` |
| `MappingTorusHomology.Covering.lowerSection_val` | `Hopf/Proof/LCP/IntegralHomology.lean:7693` | `Lib/Topology/MappingTorus/Wang.lean:468` |
| `MappingTorusHomology.Covering.upperSection_val` | `Hopf/Proof/LCP/IntegralHomology.lean:7699` | `Lib/Topology/MappingTorus/Wang.lean:474` |
| `MappingTorusHomology.Covering.uTime` | `Hopf/Proof/LCP/IntegralHomology.lean:7704` | `Lib/Topology/MappingTorus/Wang.lean:479` |
| `MappingTorusHomology.Covering.uTime_continuous` | `Hopf/Proof/LCP/IntegralHomology.lean:7707` | `Lib/Topology/MappingTorus/Wang.lean:482` |
| `MappingTorusHomology.Covering.vTime` | `Hopf/Proof/LCP/IntegralHomology.lean:7710` | `Lib/Topology/MappingTorus/Wang.lean:485` |
| `MappingTorusHomology.Covering.vTime_continuous` | `Hopf/Proof/LCP/IntegralHomology.lean:7713` | `Lib/Topology/MappingTorus/Wang.lean:488` |
| `MappingTorusHomology.Covering.uStrip` | `Hopf/Proof/LCP/IntegralHomology.lean:7716` | `Lib/Topology/MappingTorus/Wang.lean:491` |
| `MappingTorusHomology.Covering.vStrip` | `Hopf/Proof/LCP/IntegralHomology.lean:7724` | `Lib/Topology/MappingTorus/Wang.lean:499` |
| `MappingTorusHomology.Covering.uStrip_val` | `Hopf/Proof/LCP/IntegralHomology.lean:7734` | `Lib/Topology/MappingTorus/Wang.lean:509` |
| `MappingTorusHomology.Covering.vStrip_val` | `Hopf/Proof/LCP/IntegralHomology.lean:7741` | `Lib/Topology/MappingTorus/Wang.lean:516` |
| `MappingTorusHomology.Covering.uStrip_zero` | `Hopf/Proof/LCP/IntegralHomology.lean:7747` | `Lib/Topology/MappingTorus/Wang.lean:522` |
| `MappingTorusHomology.Covering.uStrip_one` | `Hopf/Proof/LCP/IntegralHomology.lean:7758` | `Lib/Topology/MappingTorus/Wang.lean:533` |
| `MappingTorusHomology.Covering.vStrip_zero` | `Hopf/Proof/LCP/IntegralHomology.lean:7769` | `Lib/Topology/MappingTorus/Wang.lean:544` |
| `MappingTorusHomology.Covering.vStrip_one` | `Hopf/Proof/LCP/IntegralHomology.lean:7783` | `Lib/Topology/MappingTorus/Wang.lean:558` |
| `MappingTorusHomology.Covering.lowerSection_period` | `Hopf/Proof/LCP/IntegralHomology.lean:7795` | `Lib/Topology/MappingTorus/Wang.lean:570` |
| `MappingTorusHomology.Covering.lowerSection_component` | `Hopf/Proof/LCP/IntegralHomology.lean:7804` | `Lib/Topology/MappingTorus/Wang.lean:579` |
| `MappingTorusHomology.Covering.upperSection_component` | `Hopf/Proof/LCP/IntegralHomology.lean:7812` | `Lib/Topology/MappingTorus/Wang.lean:587` |
| `MappingTorusHomology.Covering.lowerSection_homology_coordinates` | `Hopf/Proof/LCP/IntegralHomology.lean:7820` | `Lib/Topology/MappingTorus/Wang.lean:595` |
| `MappingTorusHomology.Covering.upperSection_homology_coordinates` | `Hopf/Proof/LCP/IntegralHomology.lean:7830` | `Lib/Topology/MappingTorus/Wang.lean:605` |
| `MappingTorusHomology.Covering.affineCircleArc` | `Hopf/Proof/LCP/IntegralHomology.lean:7931` | `Lib/Topology/MappingTorus/Wang.lean:615` |
| `MappingTorusHomology.Covering.affineCircleArc_apply` | `Hopf/Proof/LCP/IntegralHomology.lean:7937` | `Lib/Topology/MappingTorus/Wang.lean:621` |
| `MappingTorusHomology.Covering.affineCircleArc_self` | `Hopf/Proof/LCP/IntegralHomology.lean:7943` | `Lib/Topology/MappingTorus/Wang.lean:627` |
| `MappingTorusHomology.Covering.affineCircleArc_trans_homotopic` | `Hopf/Proof/LCP/IntegralHomology.lean:7949` | `Lib/Topology/MappingTorus/Wang.lean:633` |
| `MappingTorusHomology.Covering.pathClass_affineCircleArc_add` | `Hopf/Proof/LCP/IntegralHomology.lean:7962` | `Lib/Topology/MappingTorus/Wang.lean:646` |
| `MappingTorusHomology.Covering.quarterLift` | `Hopf/Proof/LCP/IntegralHomology.lean:7969` | `Lib/Topology/MappingTorus/Wang.lean:653` |
| `MappingTorusHomology.Covering.threeQuarterLift` | `Hopf/Proof/LCP/IntegralHomology.lean:7972` | `Lib/Topology/MappingTorus/Wang.lean:656` |
| `MappingTorusHomology.Covering.uPath` | `Hopf/Proof/LCP/IntegralHomology.lean:7975` | `Lib/Topology/MappingTorus/Wang.lean:659` |
| `MappingTorusHomology.Covering.vPath` | `Hopf/Proof/LCP/IntegralHomology.lean:7980` | `Lib/Topology/MappingTorus/Wang.lean:664` |
| `MappingTorusHomology.Covering.uPath_apply` | `Hopf/Proof/LCP/IntegralHomology.lean:7986` | `Lib/Topology/MappingTorus/Wang.lean:670` |
| `MappingTorusHomology.Covering.vPath_apply` | `Hopf/Proof/LCP/IntegralHomology.lean:7999` | `Lib/Topology/MappingTorus/Wang.lean:683` |
| `MappingTorusHomology.Covering.pathClass_uPath_add_vPath` | `Hopf/Proof/LCP/IntegralHomology.lean:8012` | `Lib/Topology/MappingTorus/Wang.lean:696` |
| `MappingTorusHomology.Covering.quarterLift_period` | `Hopf/Proof/LCP/IntegralHomology.lean:8017` | `Lib/Topology/MappingTorus/Wang.lean:701` |
| `MappingTorusHomology.Covering.quarterLift_circle_period` | `Hopf/Proof/LCP/IntegralHomology.lean:8024` | `Lib/Topology/MappingTorus/Wang.lean:708` |
| `MappingTorusHomology.Covering.boundaryOne_arcPrefix` | `Hopf/Proof/LCP/IntegralHomology.lean:8030` | `Lib/Topology/MappingTorus/Wang.lean:714` |
| `MappingTorusHomology.Covering.chainClass_arcPrefix` | `Hopf/Proof/LCP/IntegralHomology.lean:8046` | `Lib/Topology/MappingTorus/Wang.lean:730` |
| `MappingTorusHomology.Covering.arcSumChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8061` | `Lib/Topology/MappingTorus/Wang.lean:745` |
| `MappingTorusHomology.Covering.boundaryOne_arcSumChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8066` | `Lib/Topology/MappingTorus/Wang.lean:750` |
| `MappingTorusHomology.Covering.arcSumCycle` | `Hopf/Proof/LCP/IntegralHomology.lean:8070` | `Lib/Topology/MappingTorus/Wang.lean:754` |
| `MappingTorusHomology.Covering.arcSumCycle_val` | `Hopf/Proof/LCP/IntegralHomology.lean:8076` | `Lib/Topology/MappingTorus/Wang.lean:760` |
| `MappingTorusHomology.Covering.chainClass_arcSumChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8080` | `Lib/Topology/MappingTorus/Wang.lean:764` |
| `MappingTorusHomology.Covering.pathClass_affineCircleArc_period` | `Hopf/Proof/LCP/IntegralHomology.lean:8086` | `Lib/Topology/MappingTorus/Wang.lean:769` |
| `MappingTorusHomology.Covering.arcSumCycle_positiveLoop_class` | `Hopf/Proof/LCP/IntegralHomology.lean:8100` | `Lib/Topology/MappingTorus/Wang.lean:782` |
| `MappingTorusHomology.Covering.uCircleMap` | `Hopf/Proof/LCP/IntegralHomology.lean:8110` | `Lib/Topology/MappingTorus/Wang.lean:792` |
| `MappingTorusHomology.Covering.vCircleMap` | `Hopf/Proof/LCP/IntegralHomology.lean:8113` | `Lib/Topology/MappingTorus/Wang.lean:795` |
| `MappingTorusHomology.Covering.uCircleMap_pathChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8117` | `Lib/Topology/MappingTorus/Wang.lean:799` |
| `MappingTorusHomology.Covering.vCircleMap_pathChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8124` | `Lib/Topology/MappingTorus/Wang.lean:806` |
| `MappingTorusHomology.Covering.positiveCircleCross_subdivision_cycleClass` | `Hopf/Proof/LCP/IntegralHomology.lean:8209` | `Lib/Topology/MappingTorus/Wang.lean:812` |
| `MappingTorusHomology.Covering.monodromyHomologyMonoidHom` | `Hopf/Proof/LCP/IntegralHomology.lean:8233` | `Lib/Topology/MappingTorus/Wang.lean:836` |
| `MappingTorusHomology.Covering.monodromyHomologyMap_pow` | `Hopf/Proof/LCP/IntegralHomology.lean:8241` | `Lib/Topology/MappingTorus/Wang.lean:844` |
| `MappingTorusHomology.Covering.homologyNorm_eq_sum_powers` | `Hopf/Proof/LCP/IntegralHomology.lean:8248` | `Lib/Topology/MappingTorus/Wang.lean:850` |
| `MappingTorusHomology.Covering.uCrossChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8257` | `Lib/Topology/MappingTorus/Wang.lean:858` |
| `MappingTorusHomology.Covering.vCrossChain` | `Hopf/Proof/LCP/IntegralHomology.lean:8265` | `Lib/Topology/MappingTorus/Wang.lean:866` |
| `MappingTorusHomology.Covering.uCrossChain_boundary` | `Hopf/Proof/LCP/IntegralHomology.lean:8273` | `Lib/Topology/MappingTorus/Wang.lean:874` |
| `MappingTorusHomology.Covering.vCrossChain_boundary` | `Hopf/Proof/LCP/IntegralHomology.lean:8289` | `Lib/Topology/MappingTorus/Wang.lean:890` |
| `MappingTorusHomology.Covering.uCrossChainSum` | `Hopf/Proof/LCP/IntegralHomology.lean:8305` | `Lib/Topology/MappingTorus/Wang.lean:906` |
| `MappingTorusHomology.Covering.vCrossChainSum` | `Hopf/Proof/LCP/IntegralHomology.lean:8311` | `Lib/Topology/MappingTorus/Wang.lean:912` |
| `MappingTorusHomology.Covering.differenceCycle` | `Hopf/Proof/LCP/IntegralHomology.lean:8317` | `Lib/Topology/MappingTorus/Wang.lean:918` |
| `MappingTorusHomology.Covering.differenceCycle_val` | `Hopf/Proof/LCP/IntegralHomology.lean:8332` | `Lib/Topology/MappingTorus/Wang.lean:933` |
| `MappingTorusHomology.Covering.lowerSection_chain_sum_shift` | `Hopf/Proof/LCP/IntegralHomology.lean:8342` | `Lib/Topology/MappingTorus/Wang.lean:943` |
| `MappingTorusHomology.Covering.uCrossChainSum_boundary` | `Hopf/Proof/LCP/IntegralHomology.lean:8354` | `Lib/Topology/MappingTorus/Wang.lean:955` |
| `MappingTorusHomology.Covering.vCrossChainSum_boundary` | `Hopf/Proof/LCP/IntegralHomology.lean:8363` | `Lib/Topology/MappingTorus/Wang.lean:964` |
| `MappingTorusHomology.Covering.differenceCycle_class` | `Hopf/Proof/LCP/IntegralHomology.lean:8384` | `Lib/Topology/MappingTorus/Wang.lean:985` |
| `MappingTorusHomology.Covering.differenceCycle_class_coordinates` | `Hopf/Proof/LCP/IntegralHomology.lean:8402` | `Lib/Topology/MappingTorus/Wang.lean:1003` |
| `MappingTorusHomology.Covering.coverSmallCycle` | `Hopf/Proof/LCP/IntegralHomology.lean:8421` | `Lib/Topology/MappingTorus/Wang.lean:1022` |
| `MappingTorusHomology.Covering.coverSmallCycle_ambient_val` | `Hopf/Proof/LCP/IntegralHomology.lean:8433` | `Lib/Topology/MappingTorus/Wang.lean:1034` |
| `MappingTorusHomology.Covering.coverSmallCycle_ambient_sum_val` | `Hopf/Proof/LCP/IntegralHomology.lean:8449` | `Lib/Topology/MappingTorus/Wang.lean:1050` |
| `MappingTorusHomology.Covering.coverSmallCycle_connecting` | `Hopf/Proof/LCP/IntegralHomology.lean:8464` | `Lib/Topology/MappingTorus/Wang.lean:1065` |
| `MappingTorusHomology.Covering.coverSmallCycle_boundaryCoordinates` | `Hopf/Proof/LCP/IntegralHomology.lean:8485` | `Lib/Topology/MappingTorus/Wang.lean:1086` |
| `MappingTorusHomology.Covering.sub_cross_boundary_mem_range_circleSection` | `Hopf/Proof/LCP/IntegralHomology.lean:8504` | `Lib/Topology/MappingTorus/Wang.lean:1105` |
| `MappingTorusHomology.Covering.eq_comp_circleBoundary_of_section_cross_apply` | `Hopf/Proof/LCP/IntegralHomology.lean:8522` | `Lib/Topology/MappingTorus/Wang.lean:1123` |
| `MappingTorusHomology.Covering.eq_comp_circleBoundary_of_section_cross` | `Hopf/Proof/LCP/IntegralHomology.lean:8540` | `Lib/Topology/MappingTorus/Wang.lean:1141` |

## Retargets (disclosed; same constants, previously reached through `Hopf/LibShims.lean` exports)

- `FirstHurewicz.X -> SingularChains.X` for: Chains, Cycles1, boundaryOne, boundaryOne_pathChain,
  chainClass, cycleClass, homologyToChainClass_cycleClass, homologyToChainClass_injective,
  homologyToChainClass_loopHomologyClass, inducedChain, inducedChain_boundary, inducedChain_comp,
  inducedChain_pathChain, loopHomologyClass, mkCycle1, pathChain, pathClass, pathClass_cast,
  pathClass_homotopic, pathClass_trans, pointChain, singularChainMap, singularComplex (23 names).
- `PeriodTorusHigherHomology.X -> SingularHomology.X` for: CircleTopology.Circle, circleBoundary,
  circleBoundary_exact, circleSectionHomology, crossInsertLeft, crossProductCycles, crossProductEdge,
  crossProductHomology, crossProductHomology_cycleClass, singularHomologyMap_comp,
  singularHomologyMap_id, sumHomologyEquiv_inl, sumHomologyEquiv_inr (13 names).
- Kept as written (real `Lib/` names): `PeriodTorusHigherHomology.CirclePaths.positiveLoop`,
  `PeriodTorusHigherHomology.positiveCircleCross`, `.circleBoundary_positiveCircleCross`,
  `.connectingHomomorphism_twoChain`, `.crossProductEdge_path_boundary`, `.twoChainSmallCycle`,
  `.twoChainSmallCycle_ambient_val`; all `MappingTorus.HomologyCover.*`, `MappingTorusHomology.*`,
  `SingularMayerVietoris.*`.

Check: the 636 non-blank deleted lines and the 636 non-blank inserted lines agree line for line
after these substitutions (script over `git diff -U0`). No `private -> public` change was needed.
No statement or proof changed.

## Blocked rows

None.

## Left in place (not in FREED.md)

The 13 blocks interleaved with the moved ones stay in `Hopf/Proof/LCP/IntegralHomology.lean`:
`productCover`, `productCover_real_apply`, `productCover_zero_apply`,
`productCover_comp_productSection`, `productCoverHomology`,
`productCoverHomology_comp_circleSection`, `productCoverHomology_circleSection_apply`,
`wangBoundary_productCover_circleSection`, `wangBoundary_productCover_circleSection_apply`,
`productCover_uCircleMap`, `productCover_vCircleMap`, `uStrip_inclusion_crossProduct`,
`vStrip_inclusion_crossProduct` (they use `Elliptic.HigherHomology.MappingTorusQuotient.*` or
`productCover`), plus `wangBoundary_productCover_eq_of_cross` and `coverSmallCycle_productCover_eq`
after them.

## Rename

`MappingTorusHomology.Covering.sum_range_shift_of_endpoints_mo1973_27356` (private, Wang.lean:374)
is now `MappingTorusHomology.Covering.sum_range_shift_of_endpoints_eq`; its only use
(`homologyNorm_symm`, Wang.lean:407) updated; no other `.lean` file used it. Still private.
The old name remains in the historical records `Lib/reports/I.md` and `NEXT_STEPS.md` (not edited).

## Imports

No import added: `Hopf/Proof/LCP/IntegralHomology.lean` imports `Hopf.LCP.IntegralHomology`, which
imports `Lib.Topology.MappingTorus.Wang` (line 151). `Lib.lean` already registers Wang (line 106).

## Build (worktree `/home/goblin/hopf-wt-wang`, toolchain v4.33.0)

`lake build Lib`:
```
✔ [8815/8817] Built Lib.Topology.MappingTorus.Wang (8.4s)
✔ [8816/8817] Built Lib (3.1s)
Build completed successfully (8817 jobs).
```
`lake build Solution S6Shortcuts S6 Challenge`:
```
✔ [8843/8856] Built Hopf.LCP.IntegralHomology (6.6s)
✔ [8846/8856] Built Hopf.Proof.LCP.CuspFilling (65s)
✔ [8852/8856] Built Hopf.Proof.LCP.IntegralHomology (88s)
ℹ [8855/8856] Built Solution (3.3s)
info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8856 jobs).
```
`grep -c error:` on both logs: 0.

## Census

```
ratchet PASS: 1586 <= baseline 1648
```
(unchanged: the rows came from `Hopf/Proof/`, which the census does not count.)
