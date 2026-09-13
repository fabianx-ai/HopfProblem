# SphereTopology moves (integration 4: stock of `Hopf/SphereTopology.lean` into `Lib/`)

Base: `304a0fea` (`git show 304a0fea:Hopf/SphereTopology.lean`); source lines below refer to that
revision (the worktree file was identical to base before the move). The destination line is the
first line of the block (docstring / `attribute ... in` prefix included) in the new module.

Method: every declaration block (docstring, attributes, declaration, proof) was cut verbatim and
appended in source order to one of six new `Lib/` modules, which import each other in a chain
(in the order listed below) so that every in-file dependency of a moved row is available.
FREE/CHARGED and the dependency closure were computed textually: the tokens of each block were
resolved against the declaration names of `Hopf/`, `Lib/` and the `Hopf/LibShims.lean` export
map (bare names also through the declaration's own namespace prefixes; every component after a
dot against the last components of in-file and `Hopf/`-only names of this file's families), then
a fixpoint over in-file references; a row whose closure reaches a CHARGED row or a name that
exists only under `Hopf/` stays. The last resolver step over-approximates (field-name
collisions), so some rows listed as blocked below may in fact be free; the full chain build is
the check for what moved.

## Modules (import chain in this order)

1. `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean` — 65 rows: `LocalDegree` 37, `NativeChartTransition` 10, `ChartPuncturedBall` 9, `LinearSphereAction` 5, `SublevelDisk` 2, `PuncturedBall` 1, `NativeParametrization` 1
2. `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean` — 35 rows: `MorseRearrangement` 35
3. `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean` — 48 rows: `SpherePoint` 20, `EmbeddedCellAttachment` 8, `DiskOnePointCollapse` 7, `OnePointCover` 7, `DiskShrinking` 2, `SphereNormalCoordinates` 2, `CoverLocalContributions` 2
4. `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean` — 80 rows: `ManifoldMorse` 51, `RadialFilling` 12, `MorseHandle` 9, `FiniteSignedCancellation` 5, `FlowConstruction` 3
5. `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean` — 86 rows: `MorseCancellation` 84, `IntLinearAutomorphism` 2
6. `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean` — 17 rows: `AdaptedWindows` 16, `FlowSuspension` 1

Families placed away from their home module for dependency order: `PuncturedBall.toSphere` and
`SublevelDisk.*` (module 1, used by `LinearSphereAction` / `LocalDegree` rows there);
`NativeParametrization.centered_symm_self` (module 1); `FlowSuspension` (module 6);
`FiniteSignedCancellation`, `FlowConstruction`, `MorseHandle`, `RadialFilling` (module 4, with the
`ManifoldMorse` rows that use them); `IntLinearAutomorphism` (module 5).

## Disclosed changes (no statement changed)

Qualifier retargets (shim alias -> the same Lib constant, per the `Hopf/LibShims.lean` export
map), counted per occurrence in code; comments and docstrings untouched:

- `FirstHurewicz.Chains` -> `SingularChains.Chains` (4)
- `FirstHurewicz.Simplex` -> `SingularChains.Simplex` (1)
- `FirstHurewicz.boundaryOne` -> `SingularChains.boundaryOne` (3)
- `FirstHurewicz.boundaryOne_pathChain` -> `SingularChains.boundaryOne_pathChain` (1)
- `FirstHurewicz.boundaryOne_simplex` -> `SingularChains.boundaryOne_simplex` (1)
- `FirstHurewicz.chainLift` -> `SingularChains.chainLift` (1)
- `FirstHurewicz.chainLift_simplex` -> `SingularChains.chainLift_simplex` (2)
- `FirstHurewicz.chainMap_ext` -> `SingularChains.chainMap_ext` (2)
- `FirstHurewicz.pathChain` -> `SingularChains.pathChain` (1)
- `FirstHurewicz.pointChain` -> `SingularChains.pointChain` (3)
- `FirstHurewicz.simplexFace_zero_one` -> `SingularChains.simplexFace_zero_one` (1)
- `FirstHurewicz.simplexFace_zero_zero` -> `SingularChains.simplexFace_zero_zero` (1)
- `FirstHurewicz.simplexPath` -> `SingularChains.simplexPath` (1)
- `FirstHurewicz.simplexZero_eq_vertex` -> `SingularChains.simplexZero_eq_vertex` (1)
- `FirstHurewicz.singularComplex` -> `SingularChains.singularComplex` (7)
- `PeriodTorusHigherHomology.contractible_homology_subsingleton` -> `SingularHomology.contractible_homology_subsingleton` (2)
- `PeriodTorusHigherHomology.homeomorphHomologyEquiv` -> `SingularHomology.homeomorphHomologyEquiv` (3)
- `PeriodTorusHigherHomology.homotopyEquivHomologyEquiv` -> `SingularHomology.homotopyEquivHomologyEquiv` (2)
- `PeriodTorusHigherHomology.pointClass` -> `SingularHomology.pointClass` (4)
- `PeriodTorusHigherHomology.pointCycle` -> `SingularHomology.pointCycle` (4)
- `PeriodTorusHigherHomology.singularHomologyMap_comp` -> `SingularHomology.singularHomologyMap_comp` (2)
- `PeriodTorusHigherHomology.singularHomologyMap_pointClass` -> `SingularHomology.singularHomologyMap_pointClass` (2)

`private` -> public: `LocalDegree.NativeNeighborhood.identity_center_mo1973_5731`, `SphereNormalCoordinates.sign_factor_mo1973_5719` (each is used by a row that stays in
`Hopf/SphereTopology.lean` or lives in another module).

The final `end` (closing `noncomputable section`) that followed the last moved block stays in the
source file; `Hopf/SphereTopology.lean` imports the six modules; `Lib.lean` registers them.

## Moved declarations

| declaration | source lines at 304a0fea | destination |
|---|---|---|
| `PuncturedBall.toSphere` | 161-164 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:77` |
| `LocalDegree.exists_native_boundaryData` | 8536-8576 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:81` |
| `LocalDegree.NeighborhoodData` | 8577-8586 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:122` |
| `LocalDegree.nonempty_neighborhoodData` | 8587-8598 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:132` |
| `LocalDegree.nonempty_neighborhoodData_of_contDiffAt` | 8599-8608 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:144` |
| `LocalDegree.NeighborhoodData.image_ne_zero` | 8609-8614 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:154` |
| `LocalDegree.NeighborhoodData.innerBoundary` | 8615-8629 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:160` |
| `LocalDegree.NeighborhoodData.innerBoundary_radius` | 8630-8635 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:175` |
| `LocalDegree.NeighborhoodData.innerBoundary_mem_ball` | 8636-8644 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:181` |
| `LocalDegree.exists_native_neighborhoodData` | 8645-8673 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:190` |
| `ChartPuncturedBall.openSet` | 8674-8677 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:219` |
| `ChartPuncturedBall.puncturedSet` | 8678-8681 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:223` |
| `ChartPuncturedBall.zero_mem_source` | 8682-8686 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:227` |
| `ChartPuncturedBall.ball_subset_source` | 8687-8691 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:232` |
| `ChartPuncturedBall.isOpen_openSet` | 8692-8696 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:237` |
| `ChartPuncturedBall.center_mem_openSet` | 8697-8701 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:242` |
| `ChartPuncturedBall.ballHomeomorph` | 8702-8706 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:247` |
| `ChartPuncturedBall.image_puncturedBall` | 8707-8723 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:252` |
| `ChartPuncturedBall.puncturedHomeomorph` | 8724-8731 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:269` |
| `LocalDegree.NativeNeighborhood.openSet` | 8732-8742 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:277` |
| `LocalDegree.NativeNeighborhood.closedBall_subset_source` | 8743-8753 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:288` |
| `LocalDegree.NativeNeighborhood.isOpen_openSet` | 8754-8765 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:299` |
| `LocalDegree.NativeNeighborhood.center_mem_openSet` | 8766-8781 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:311` |
| `LocalDegree.NativeNeighborhood.openSet_subset` | 8782-8792 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:327` |
| `LocalDegree.NativeNeighborhood.puncturedHomeomorph` | 8793-8808 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:338` |
| `LocalDegree.SeparatedNeighborhoods` | 8824-8838 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:354` |
| `LocalDegree.nonempty_separatedNeighborhoods` | 8839-8875 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:369` |
| `LocalDegree.SeparatedNeighborhoods.neighborhood` | 8876-8881 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:406` |
| `LocalDegree.SeparatedNeighborhoods.isOpen_neighborhood` | 8882-8888 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:412` |
| `LocalDegree.SeparatedNeighborhoods.center_mem_neighborhood` | 8889-8895 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:419` |
| `LocalDegree.SeparatedNeighborhoods.neighborhood_subset` | 8896-8902 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:426` |
| `LocalDegree.SeparatedNeighborhoods.pairwise_disjoint` | 8903-8909 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:433` |
| `LocalDegree.SeparatedNeighborhoods.points_inter_neighborhood` | 8910-8925 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:440` |
| `LocalDegree.SeparatedNeighborhoods.overlap_eq` | 8926-8943 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:456` |
| `LocalDegree.SeparatedNeighborhoods.open_cover` | 8944-8954 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:474` |
| `LocalDegree.NeighborhoodData.puncturedMap` | 8972-8980 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:485` |
| `LocalDegree.NativeNeighborhood.overlapMap` | 8981-8990 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:494` |
| `LocalDegree.NativeNeighborhood.overlapMap_coe` | 8991-9003 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:504` |
| `LocalDegree.SeparatedNeighborhoods.overlapMap` | 9004-9011 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:517` |
| `LocalDegree.SeparatedNeighborhoods.overlapMap_coe` | 9012-9018 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:525` |
| `SublevelDisk.contractibleSpace` | 9681-9686 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:532` |
| `SublevelDisk.homology_subsingleton` | 9687-9692 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:538` |
| `LinearSphereAction.sphereMap_comp` | 9788-9801 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:544` |
| `LinearSphereAction.sphereMap_trans` | 9802-9809 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:558` |
| `LinearSphereAction.normalized_linearSphereMap` | 9810-9820 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:566` |
| `LinearSphereAction.sphereMap_relative` | 9821-9831 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:577` |
| `LocalDegree.NativeNeighborhood.singlePoint_cover` | 9982-9997 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:588` |
| `LocalDegree.NativeNeighborhood.openSet_contractible` | 9998-10013 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:604` |
| `NativeParametrization.centered_symm_self` | 10045-10050 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:620` |
| `NativeChartTransition.chart` | 10051-10056 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:626` |
| `NativeChartTransition.chart_apply` | 10057-10064 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:632` |
| `NativeChartTransition.zero_mem_source` | 10065-10076 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:640` |
| `NativeChartTransition.chart_zero` | 10077-10082 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:652` |
| `NativeChartTransition.contDiffAt_chart` | 10083-10089 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:658` |
| `NativeChartTransition.bijective_derivative` | 10090-10096 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:665` |
| `NativeChartTransition.linear` | 10097-10102 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:672` |
| `NativeChartTransition.linear_eq_derivative` | 10103-10108 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:678` |
| `NativeChartTransition.hasFDerivAt_chart` | 10109-10115 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:684` |
| `NativeChartTransition.nonempty_neighborhoodData` | 10116-10137 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:691` |
| `LinearSphereAction.homology_relative_sign` | 10228-10239 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:713` |
| `LocalDegree.PointTransition.maps_point_complement` | 10431-10435 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:725` |
| `LocalDegree.NeighborhoodData.restrictRadius` | 10522-10533 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:730` |
| `LocalDegree.NativeNeighborhood.identity_center_mo1973_5731` | 10534-10537 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:742` |
| `LocalDegree.NativeNeighborhood.openSet_restrictRadius_subset` | 10538-10553 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:746` |
| `LocalDegree.NativeNeighborhood.mapsTo_restrictRadius` | 10554-10565 | `Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean:762` |
| `MorseRearrangement.exists_radius_supported_bump_preparation` | 530-574 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:78` |
| `MorseRearrangement.ambient_patch_support_compact` | 575-582 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:123` |
| `MorseRearrangement.exists_ambient_patch_in_open` | 583-632 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:131` |
| `MorseRearrangement.exists_relative_ambient_patch_step` | 633-706 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:181` |
| `MorseRearrangement.compose_supported_ambient_isotopies` | 707-732 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:255` |
| `MorseRearrangement.exists_finite_relative_patch_diffeomorph` | 733-787 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:281` |
| `MorseRearrangement.exists_supported_ambient_transverse_in_open` | 788-821 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:336` |
| `MorseRearrangement.exists_supported_ambient_disjoint_in_open` | 822-861 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:370` |
| `MorseRearrangement.exists_supported_ambient_disjoint_fixing_closed` | 862-884 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:410` |
| `MorseRearrangement.otherSheetImages` | 885-887 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:433` |
| `MorseRearrangement.mem_otherSheetImages` | 888-891 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:436` |
| `MorseRearrangement.sheetSum` | 892-895 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:440` |
| `MorseRearrangement.sheetSumTopology` | 896-902 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:444` |
| `MorseRearrangement.sheetSumCompact` | 903-909 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:451` |
| `MorseRearrangement.sheetSumT2` | 910-916 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:458` |
| `MorseRearrangement.sheetSumSecondCountable` | 917-923 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:465` |
| `MorseRearrangement.sheetSumChartedSpace` | 924-930 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:472` |
| `MorseRearrangement.sheetSumIsManifold` | 931-940 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:479` |
| `MorseRearrangement.sheetSumMap` | 941-945 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:489` |
| `MorseRearrangement.range_sheetSumMap` | 946-977 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:494` |
| `MorseRearrangement.contMDiff_sheetSumMap` | 978-987 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:526` |
| `MorseRearrangement.exists_sheetSumMap_for_finite_family` | 988-1012 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:536` |
| `MorseRearrangement.exists_whole_family_avoidance` | 1904-1944 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:561` |
| `MorseRearrangement.upperValueRank` | 2745-2748 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:602` |
| `MorseRearrangement.finiteIndexDisorder` | 2749-2752 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:606` |
| `MorseRearrangement.upperValueRank_comp_equiv` | 2753-2760 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:610` |
| `MorseRearrangement.finiteIndexDisorder_comp_equiv` | 2761-2773 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:618` |
| `MorseRearrangement.upperValueRank_consecutive` | 2774-2797 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:631` |
| `MorseRearrangement.sum_erase_two_nat` | 2798-2807 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:655` |
| `MorseRearrangement.weighted_sum_swap_identity` | 2808-2827 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:665` |
| `MorseRearrangement.finiteIndexDisorder_swap_lt` | 2828-2849 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:685` |
| `MorseRearrangement.exists_adjacent_index_inversion` | 2850-2868 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:707` |
| `MorseRearrangement.exists_consecutive_below_of_intermediate` | 2869-2881 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:726` |
| `MorseRearrangement.beforeValueRank` | 2882-2884 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:739` |
| `MorseRearrangement.beforeValueRank_exchange_lt` | 2885-2910 | `Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean:742` |
| `EmbeddedCellAttachment.oldHomologyEquiv` | 3138-3143 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:78` |
| `EmbeddedCellAttachment.attachingHomologyMap` | 3150-3155 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:84` |
| `EmbeddedCellAttachment.oldHomologyMap` | 3156-3161 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:90` |
| `EmbeddedCellAttachment.diskPatch_homology_subsingleton` | 3170-3176 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:96` |
| `EmbeddedCellAttachment.coverRight_old` | 3198-3212 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:103` |
| `EmbeddedCellAttachment.coverRight_formula` | 3224-3241 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:118` |
| `EmbeddedCellAttachment.range_coverRight` | 3257-3268 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:136` |
| `DiskShrinking.exists_embedded_disk_isotopy_of_path` | 5725-5756 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:148` |
| `DiskShrinking.exists_embedded_disk_isotopy` | 5757-5773 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:180` |
| `DiskOnePointCollapse.boundary` | 7878-7881 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:197` |
| `DiskOnePointCollapse.boundary_closed` | 7882-7885 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:201` |
| `DiskOnePointCollapse.not_mem_boundary_iff` | 7886-7892 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:205` |
| `DiskOnePointCollapse.interiorHomeomorph` | 7893-7897 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:212` |
| `DiskOnePointCollapse.compress` | 7928-7931 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:217` |
| `DiskOnePointCollapse.norm_compress_lt` | 7932-7935 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:221` |
| `DiskOnePointCollapse.compress_zero` | 7936-7939 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:225` |
| `EmbeddedCellAttachment.collapse_piece_cover` | 8018-8022 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:229` |
| `OnePointCover.oldPatch` | 8061-8063 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:234` |
| `OnePointCover.finitePatch` | 8064-8066 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:237` |
| `OnePointCover.cover` | 8067-8076 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:240` |
| `OnePointCover.oldPatch_open` | 8077-8080 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:250` |
| `OnePointCover.finitePatch_open` | 8081-8084 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:254` |
| `OnePointCover.overlapRadius` | 8156-8158 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:258` |
| `OnePointCover.overlapRadius_pos` | 8159-8162 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:261` |
| `SphereNormalCoordinates.normalDerivative_smul_isInvertible` | 9285-9293 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:265` |
| `CoverLocalContributions.localMap` | 9519-9523 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:274` |
| `CoverLocalContributions.connecting_sum` | 9524-9542 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:279` |
| `SpherePoint.hyperplaneReflection_det` | 9858-9863 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:298` |
| `SpherePoint.positive_transport_of_normal` | 9864-9887 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:304` |
| `SpherePoint.exists_positive_transport` | 9888-9910 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:328` |
| `SpherePoint.positiveTransport` | 9911-9914 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:351` |
| `SpherePoint.positiveTransport_apply` | 9915-9918 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:355` |
| `SpherePoint.positiveTransport_det` | 9919-9922 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:359` |
| `SpherePoint.sphereHomeomorph` | 9923-9930 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:363` |
| `SpherePoint.sphereHomeomorph_eq_normalized` | 9931-9941 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:371` |
| `SpherePoint.contMDiff_sphereHomeomorph` | 9942-9949 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:382` |
| `SpherePoint.sphereDiffeomorph` | 9950-9957 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:390` |
| `SpherePoint.sphereHomeomorph_homology_of_det_pos` | 9958-9966 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:398` |
| `SpherePoint.positiveTransport_moves` | 9967-9971 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:407` |
| `SpherePoint.positiveTransport_homology` | 9972-9981 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:412` |
| `SpherePoint.ambient_chart_hasFDerivAt` | 10138-10148 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:422` |
| `SpherePoint.chart_transition_eventually_eq` | 10149-10167 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:433` |
| `SpherePoint.chart_transition_ambient_derivative` | 10168-10192 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:452` |
| `SphereNormalCoordinates.sign_factor_mo1973_5719` | 10321-10327 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:477` |
| `SpherePoint.instLocal2` | 10847-10850 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:484` |
| `SpherePoint.instLocal3` | 11002-11005 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:488` |
| `SpherePoint.referencePoint` | 11006-11009 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:492` |
| `SpherePoint.referenceNeighborhood` | 11010-11024 | `Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean:496` |
| `ManifoldMorse.MorseSurgeryData.attachingSphere_pathConnected` | 3752-3759 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:78` |
| `ManifoldMorse.SurgeryWindows.values` | 3822-3826 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:86` |
| `ManifoldMorse.SurgeryWindows.count` | 3827-3831 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:91` |
| `ManifoldMorse.SurgeryWindows.point` | 3832-3839 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:96` |
| `ManifoldMorse.SurgeryWindows.point_value` | 3840-3851 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:104` |
| `ManifoldMorse.SurgeryWindows.point_strictMono` | 3852-3860 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:116` |
| `ManifoldMorse.SurgeryWindows.point_consecutive` | 3861-3872 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:125` |
| `ManifoldMorse.SurgeryWindows.ordered_windows` | 3873-3878 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:137` |
| `ManifoldMorse.SurgeryWindows.consecutive_regular` | 3879-3886 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:143` |
| `ManifoldMorse.SurgeryWindows.exists_consecutiveBandBridge` | 3887-3903 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:151` |
| `ManifoldMorse.SignedMorseChart.positive_eq_zero_of_localMax` | 3904-3926 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:168` |
| `ManifoldMorse.SignedMorseChart.subsingleton_positive_of_localMax` | 3927-3934 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:191` |
| `ManifoldMorse.SurgeryWindows.first` | 3935-3940 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:199` |
| `ManifoldMorse.SurgeryWindows.last` | 3941-3946 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:205` |
| `ManifoldMorse.SurgeryWindows.value_first_le` | 3947-3953 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:211` |
| `ManifoldMorse.SurgeryWindows.value_le_last` | 3954-3961 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:218` |
| `ManifoldMorse.SurgeryWindows.count_pos` | 3962-3972 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:226` |
| `ManifoldMorse.SurgeryWindows.first_globalMin` | 3973-3983 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:237` |
| `ManifoldMorse.SurgeryWindows.last_globalMax` | 3984-3994 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:248` |
| `ManifoldMorse.SurgeryWindows.unique_first` | 3995-4004 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:259` |
| `ManifoldMorse.SurgeryWindows.last_upper_univ` | 4005-4013 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:269` |
| `ManifoldMorse.SurgeryWindows.first_index_zero` | 4014-4024 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:278` |
| `ManifoldMorse.SurgeryWindows.last_index_dimension` | 4025-4037 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:289` |
| `ManifoldMorse.SurgeryWindows.nonempty_firstSublevelDisk` | 4038-4051 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:302` |
| `FlowConstruction.regularLevelHomeomorphOfFlow` | 4160-4191 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:316` |
| `FlowConstruction.nonempty_regularLevelHomeomorph` | 4192-4200 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:348` |
| `FlowConstruction.circle_nullhomotopies_regular_level` | 4201-4223 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:357` |
| `FiniteSignedCancellation.opposite_signs_distinct` | 4875-4877 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:380` |
| `FiniteSignedCancellation.cast_add_eq_zero_of_opposite` | 4878-4880 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:383` |
| `FiniteSignedCancellation.sum_sdiff_pair` | 4881-4896 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:386` |
| `FiniteSignedCancellation.sum_sdiff_pair_of_eq` | 4897-4904 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:402` |
| `FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite` | 4905-4925 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:410` |
| `RadialFilling.direction` | 5901-5909 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:431` |
| `RadialFilling.direction_coe` | 5910-5914 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:440` |
| `RadialFilling.direction_of_mem_sphere` | 5915-5921 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:445` |
| `RadialFilling.radialTime` | 5945-5948 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:452` |
| `RadialFilling.coe_radialTime` | 5949-5952 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:456` |
| `RadialFilling.radialTime_le_quarter` | 5953-5957 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:460` |
| `RadialFilling.three_quarters_le_radialTime` | 5958-5962 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:465` |
| `RadialFilling.contMDiffAt_radialTime` | 5963-5975 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:470` |
| `RadialFilling.filling` | 5976-5980 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:483` |
| `RadialFilling.filling_eq_center` | 5981-5987 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:488` |
| `RadialFilling.filling_eq_boundary` | 5988-5995 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:495` |
| `RadialFilling.filling_on_sphere` | 5996-6003 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:503` |
| `ManifoldMorse.MorseSurgeryData.beltFaceCoordinates` | 9031-9040 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:511` |
| `ManifoldMorse.MorseSurgeryData.beltClosedDiskPoint` | 9041-9052 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:521` |
| `ManifoldMorse.MorseSurgeryData.beltClosedDiskMap` | 9053-9069 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:533` |
| `ManifoldMorse.MorseSurgeryData.newPiece_beltFaceCoordinates` | 9070-9134 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:550` |
| `ManifoldMorse.MorseSurgeryData.range_newPiece_eq_range_beltClosedDiskMap` | 9135-9147 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:615` |
| `ManifoldMorse.MorseSurgeryData.beltClosedDiskMap_mem_newInterior_iff` | 9148-9158 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:628` |
| `MorseHandle.contDiff_beltFaceMap` | 9159-9164 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:639` |
| `MorseHandle.hasFDerivAt_beltFaceMap_zero` | 9165-9173 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:645` |
| `MorseHandle.hasFDerivAt_univUnitBall_symm_zero` | 9174-9185 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:654` |
| `MorseHandle.beltCollapseCoordinate` | 9186-9189 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:666` |
| `MorseHandle.beltCollapseCoordinate_zero` | 9190-9194 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:670` |
| `MorseHandle.contDiffOn_beltCollapseCoordinate` | 9195-9201 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:675` |
| `MorseHandle.hasFDerivAt_beltCollapseCoordinate_zero` | 9202-9213 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:682` |
| `MorseHandle.hasFDerivAt_scaled_beltCollapseCoordinate_zero` | 9214-9225 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:694` |
| `MorseHandle.scaled_beltCollapseCoordinate_factor_pos` | 9226-9228 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:706` |
| `ManifoldMorse.MorseSurgeryData.beltNormal_beltClosedDiskMap` | 9229-9238 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:709` |
| `ManifoldMorse.MorseSurgeryData.collapseNormal` | 9239-9245 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:719` |
| `ManifoldMorse.MorseSurgeryData.collapseNormal_belt` | 9246-9253 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:726` |
| `ManifoldMorse.MorseSurgeryData.mfderiv_collapseNormal_comp` | 9326-9353 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:734` |
| `ManifoldMorse.MorseSurgeryData.contMDiffAt_collapseNormal_comp` | 9410-9447 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:762` |
| `ManifoldMorse.MorseSurgeryData.upperLevelInclusion` | 9626-9631 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:800` |
| `ManifoldMorse.MorseSurgeryData.bandSublevelHomeomorph` | 9632-9639 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:806` |
| `ManifoldMorse.SurgeryWindows.BandData` | 9640-9648 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:814` |
| `ManifoldMorse.SurgeryWindows.nonempty_consecutiveBandData` | 9649-9658 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:823` |
| `ManifoldMorse.SurgeryWindows.consecutiveBandData` | 9659-9665 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:833` |
| `ManifoldMorse.SurgeryWindows.BandData.sublevelHomeomorph` | 9666-9672 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:840` |
| `ManifoldMorse.MorseSurgeryData.attachingHomology_subsingleton_of_index` | 9753-9774 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:847` |
| `ManifoldMorse.MorseSurgeryData.indexTwoNormalModel` | 11125-11131 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:869` |
| `ManifoldMorse.SurgeryWindows.HasIndexTwoPrefix` | 11228-11233 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:876` |
| `ManifoldMorse.SurgeryWindows.indexTwoPrefix_mono` | 11234-11238 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:882` |
| `ManifoldMorse.MorseSurgeryData.indexThreeBoundaryEquiv` | 11298-11311 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:887` |
| `ManifoldMorse.MorseSurgeryData.indexThreeBoundary_scalar` | 11312-11323 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:901` |
| `ManifoldMorse.SurgeryWindows.HasIndexThreeBlock` | 11408-11414 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:913` |
| `ManifoldMorse.SurgeryWindows.indexThreeBlock_mono` | 11415-11420 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:920` |
| `ManifoldMorse.SurgeryWindows.indexThreeBlock_last` | 11421-11427 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:926` |
| `ManifoldMorse.SurgeryWindows.lastUpperHomeomorph` | 11449-11455 | `Lib/Geometry/Manifold/Morse/SurgeryHomology.lean:933` |
| `IntLinearAutomorphism.apply_eq_mul` | 129-131 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:78` |
| `IntLinearAutomorphism.apply_one_eq_one_or_neg_one` | 132-136 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:81` |
| `MorseCancellation.two_sphere_map_unit_of_homology_bijective` | 137-160 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:86` |
| `MorseCancellation.nativeBeltTubeSource` | 202-218 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:110` |
| `MorseCancellation.nativeBeltTubeInComplement` | 219-241 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:127` |
| `MorseCancellation.nativeBeltTubeMeridian` | 242-250 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:150` |
| `MorseCancellation.parameterBallBoundary` | 296-305 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:159` |
| `MorseCancellation.parameterBallCenter` | 306-309 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:169` |
| `MorseCancellation.parameterBallContraction` | 310-332 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:173` |
| `MorseCancellation.parameterBall_boundary_nullhomotopic` | 333-340 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:196` |
| `MorseCancellation.normalized_pos_smul` | 341-345 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:204` |
| `MorseCancellation.beltBallCoordinates` | 346-356 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:209` |
| `MorseCancellation.beltBallCoordinates_normal` | 357-364 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:220` |
| `MorseCancellation.beltBallBoundaryNormal` | 365-376 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:228` |
| `MorseCancellation.beltBallBoundaryInComplement` | 377-388 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:240` |
| `MorseCancellation.beltBallBoundaryInComplement_coe` | 389-411 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:252` |
| `MorseCancellation.beltBallBoundary_normalized_coe` | 429-444 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:275` |
| `MorseCancellation.exists_small_native_belt_neighborhood` | 489-529 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:291` |
| `MorseCancellation.exists_morseSurgeryData_of_field_germ_lt` | 1111-1194 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:332` |
| `MorseCancellation.exists_adapted_windows_with_prescribed_flow` | 1195-1238 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:416` |
| `MorseCancellation.standardCircleParametrization` | 1300-1304 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:460` |
| `MorseCancellation.contMDiff_comp_standardCircle` | 1305-1310 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:465` |
| `MorseCancellation.injective_comp_standardCircle` | 1311-1315 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:471` |
| `MorseCancellation.injective_derivative_comp_standardCircle` | 1316-1326 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:476` |
| `MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt` | 1533-1582 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:487` |
| `MorseCancellation.nativeIndexThreeAttachingSphere` | 2138-2150 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:537` |
| `MorseCancellation.IsNativeMiddleBasinFamily` | 2332-2346 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:550` |
| `MorseCancellation.exists_signed_morse_chart_of_germ_preserving_field` | 2572-2598 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:565` |
| `MorseCancellation.exists_signed_morse_chart_of_shift_germ_preserving_field` | 2599-2607 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:592` |
| `MorseCancellation.injOn_of_exchanged_values` | 2608-2634 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:601` |
| `MorseCancellation.nativeMorseCount_eq_of_preserved_indices` | 2635-2652 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:628` |
| `MorseCancellation.adapted_surgery_system_after_value_exchange` | 2653-2669 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:646` |
| `MorseCancellation.exists_flow_preserving_value_exchange` | 2670-2744 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:663` |
| `MorseCancellation.exists_flow_preserving_consecutive_pair` | 2911-3042 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:738` |
| `MorseCancellation.isOpen_forward_basin_of_native_index_zero` | 3043-3068 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:870` |
| `MorseCancellation.cancel_unique_zero_one_connection` | 3069-3137 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:896` |
| `MorseCancellation.componentChainWeight` | 3496-3500 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:965` |
| `MorseCancellation.componentChainWeight_point` | 3501-3505 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:970` |
| `MorseCancellation.componentChainWeight_boundary` | 3506-3522 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:975` |
| `MorseCancellation.pointClass_eq_iff_joined` | 3523-3546 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:992` |
| `MorseCancellation.joined_iff_of_homologyZero_injective` | 3547-3554 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1016` |
| `MorseCancellation.pathConnectedSpace_of_homologyZero_injective` | 3555-3562 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1024` |
| `MorseCancellation.pathConnectedSpace_of_homotopyEquiv` | 3563-3569 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1032` |
| `MorseCancellation.ordered_upper_pathConnected_of_later_transfers` | 4052-4100 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1039` |
| `MorseCancellation.cell_old_empty_of_empty_boundary` | 4101-4122 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1088` |
| `MorseCancellation.native_index_zero_point_unique` | 4286-4310 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1110` |
| `MorseCancellation.native_index_one_excluded` | 4311-4328 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1135` |
| `MorseCancellation.zeroChainCycle` | 4372-4384 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1153` |
| `MorseCancellation.zeroChainClass` | 4385-4389 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1166` |
| `MorseCancellation.zeroChainClass_surjective` | 4390-4397 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1171` |
| `MorseCancellation.homologyZero_linearMap_ext` | 4398-4416 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1179` |
| `MorseCancellation.isMorseAt_neg` | 4734-4750 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1198` |
| `MorseCancellation.isMorse_neg` | 4751-4754 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1215` |
| `MorseCancellation.negative_finrank_neg_chart` | 4755-4768 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1219` |
| `MorseCancellation.nativeMorseIndex_neg_add` | 4769-4775 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1233` |
| `MorseCancellation.nativeMorseCount_neg` | 4776-4798 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1240` |
| `MorseCancellation.exists_minimal_excellent_morse_system` | 4799-4829 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1263` |
| `MorseCancellation.minimal_excellent_morse_forbids_pair_removal` | 4830-4846 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1294` |
| `MorseCancellation.distinct_critical_values_neg` | 4847-4854 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1311` |
| `MorseCancellation.minimal_excellent_morse_neg` | 4855-4874 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1319` |
| `MorseCancellation.unitSphere_isEmpty_of_finrank_zero` | 5221-5229 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1339` |
| `MorseCancellation.nativeIndexDisorder` | 5359-5368 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1348` |
| `MorseCancellation.nativeIndexDisorder_eq_of_finite` | 5369-5378 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1358` |
| `MorseCancellation.nativeIndexDisorder_transport` | 5379-5409 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1368` |
| `MorseCancellation.nativeIndexDisorder_exchange_lt` | 5410-5451 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1399` |
| `MorseCancellation.exists_transverse_sheet_of_circle_placement` | 5696-5724 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1441` |
| `MorseCancellation.exists_embedded_avoidance_into_level_basin` | 5774-5831 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1470` |
| `MorseCancellation.superlevel_bound_of_critical_bound` | 6369-6387 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1528` |
| `MorseCancellation.birth_preserves_lower_levels` | 6388-6422 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1547` |
| `MorseCancellation.equalLevelDiffeomorph` | 6423-6449 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1582` |
| `MorseCancellation.regular_level_of_retained_critical_germs` | 6450-6464 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1609` |
| `MorseCancellation.isotopicToIdentity_conj` | 6465-6489 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1624` |
| `MorseCancellation.unit_level_count_of_circle_placement` | 6611-6640 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1649` |
| `MorseCancellation.no_other_connections_of_two_level_endpoints` | 6895-6929 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1679` |
| `MorseCancellation.cancel_transverse_pair_after_flow_preserving_descent` | 6930-7019 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1714` |
| `MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one` | 7097-7111 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1804` |
| `MorseCancellation.birth_preserves_lower_index_bound` | 7300-7317 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1819` |
| `MorseCancellation.birth_first_new_value_gap` | 7318-7337 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1837` |
| `MorseCancellation.birth_preserves_unique_index_zero` | 7338-7355 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1857` |
| `MorseCancellation.indexed_criticalPoints_removed_of_index_eq` | 7356-7379 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1875` |
| `MorseCancellation.nativeMorseCount_removed_of_index_eq` | 7380-7427 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1899` |
| `MorseCancellation.nativeMorseCount_adjacent_removed_of_index_eq` | 7428-7450 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1947` |
| `MorseCancellation.outer_index_minimality_neg` | 7769-7801 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:1970` |
| `MorseCancellation.native_indices_monotone` | 11588-11600 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:2003` |
| `MorseCancellation.exists_middle_index_blocks` | 11601-11677 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:2016` |
| `MorseCancellation.nativeMiddleBlockPoint` | 11678-11683 | `Lib/Geometry/Manifold/Morse/OrderedCancellation.lean:2093` |
| `FlowSuspension.exists_relative_regular_level_isotopy_realization` | 1013-1110 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:78` |
| `AdaptedWindows.attachingSphere_reaches_lower_cut` | 1350-1373 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:176` |
| `AdaptedWindows.backward_basin_reaches_attaching_level` | 1437-1456 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:200` |
| `AdaptedWindows.transported_attaching_range_iff` | 1457-1491 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:220` |
| `AdaptedWindows.forward_endpoint_of_attaching_branches` | 1492-1512 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:255` |
| `AdaptedWindows.attaching_branches_of_same_flow` | 1513-1532 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:276` |
| `AdaptedWindows.exists_same_flow_windows_avoiding_level` | 1583-1620 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:296` |
| `AdaptedWindows.regular_interval_around_level` | 1621-1638 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:334` |
| `AdaptedWindows.exists_relative_level_surgery_system` | 1737-1801 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:352` |
| `AdaptedWindows.reaches_lower_of_excluded_critical_limit` | 1860-1884 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:417` |
| `AdaptedWindows.reaches_old_lower_of_belt_avoidance` | 1885-1903 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:442` |
| `AdaptedWindows.not_backward_basin_on_upper_level` | 2082-2096 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:461` |
| `AdaptedWindows.transported_backward_basin_image` | 2097-2137 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:476` |
| `AdaptedWindows.reaches_lower_in_regular_band` | 2270-2288 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:517` |
| `AdaptedWindows.no_connection_of_upper_index_zero` | 5230-5249 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:536` |
| `AdaptedWindows.no_connection_of_lower_positive_zero` | 5250-5269 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:556` |
| `AdaptedWindows.exists_ordered_index_cut` | 7591-7632 | `Lib/Geometry/Manifold/Morse/AdaptedWindows.lean:576` |

## Rows that stay (254)

CHARGED (statement or proof mentions a project-specific object):

- `exists_smooth_nullhomotopy_of_homotopySixSphere` (6034-6049)
- `exists_smooth_disk_extension_of_homotopySixSphere` (6050-6066)
- `exists_embedded_disk_of_homotopySixSphere` (6067-6082)
- `MorseCancellation.exists_disk_in_level_basin_of_index_cut` (6083-6129)
- `MorseCancellation.exists_actual_regular_level_disk_of_index_cut` (6130-6168)
- `MorseCancellation.exists_embedded_regular_level_disk_of_index_cut` (6223-6265)
- `MorseCancellation.exists_native_middle_level_circle_disk` (6266-6310)
- `MorseCancellation.exists_native_middle_level_circle_isotopy` (6311-6368)
- `MorseCancellation.exists_equal_level_circle_isotopy` (6490-6548)
- `MorseCancellation.exists_new_attaching_circle_placement` (6549-6610)
- `MorseCancellation.exists_handle_trade_transverse_level_data` (6641-6716)
- `MorseCancellation.cancel_one_two_pair_at_preserved_middle_cut` (7020-7096)
- `MorseCancellation.cancel_one_two_pair_at_unchanged_cut_of_unique_minimum` (7256-7299)
- `MorseCancellation.exists_one_to_three_handle_trade` (7451-7539)
- `MorseCancellation.exists_one_to_three_handle_trade_at_cut` (7540-7590)
- `MorseCancellation.exists_one_to_three_handle_trade_of_ordered_indices` (7633-7660)
- `MorseCancellation.outer_index_minimal_index_one_count_zero` (7721-7768)
- `MorseCancellation.outer_index_minimal_outer_counts_zero` (7802-7850)
- `MorseCancellation.exists_minimal_ordered_morse_system_without_outer_indices` (7851-7877)
- `DiskOnePointCollapse.collapse` (7898-7903)
- `DiskOnePointCollapse.collapse_boundary` (7904-7910)
- `DiskOnePointCollapse.collapse_interior` (7911-7917)
- `DiskOnePointCollapse.collapse_eq_iff` (7918-7927)
- `OnePointCover.sphereConnecting_injective` (8249-8261)
- `OnePointCover.sphereHomologyEquiv` (8262-8272)
- `LocalDegree.NativeNeighborhood.sphereHomologyEquiv` (10029-10044)
- `ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton` (11456-11487)
- `ManifoldMorse.SurgeryWindows.upper_homology_subsingleton_of_later_indices` (11488-11545)
- `ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_homotopySphere` (11554-11575)
- `ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_complete_blocks` (11576-11587)

Blocked: a dependency exists only under `Hopf/` (`external`, mostly `Hopf/SingularHomology.lean`)
or is an in-file row that itself stays (`in-file`, first four shown):

- `PuncturedBall.toSphere_fromSphere` (165-169) — external: `PuncturedRadial.toSphere_fromSphere`
- `PuncturedBall.deformation` (170-188) — external: `PuncturedRadial.deformation`
- `PuncturedBall.sphereHomotopyEquiv` (189-201) — in-file: `LinearSphereAction.sphereHomotopyEquiv`, `PuncturedBall.deformation`, `PuncturedBall.toSphere_fromSphere`
- `MorseCancellation.nativeBeltTube_homotopic_meridian` (251-275) — in-file: `PuncturedBall.deformation`
- `MorseCancellation.nativeBeltTubeMeridian_eq` (276-295) — external: `MorseCancellation.nativeUpperMeridianInComplement`
- `MorseCancellation.beltBallBoundary_homotopic_meridian` (412-428) — in-file: `MorseCancellation.nativeBeltTube_homotopic_meridian`
- `MorseCancellation.normal_boundary_homotopic_native_meridian` (445-488) — external: `LocalDegree.BoundaryData.normalizedMap`; in-file: `MorseCancellation.beltBallBoundary_homotopic_meridian`
- `AdaptedWindows.exists_embedded_level_transport` (1239-1299) — external: `AdaptedWindows.exists_native_level_basin_transport`
- `MorseCancellation.transverse_comp_standardCircle` (1327-1349) — external: `MorseCancellation.surjective_coprod_comp_left`
- `AdaptedWindows.exists_attaching_circle_lower_transport` (1374-1436) — in-file: `AdaptedWindows.exists_embedded_level_transport`
- `AdaptedWindows.realize_one_handle_minimum_branches` (1639-1736) — external: `AdaptedWindows.place_one_handle_in_distinct_minimum_basins`, `ManifoldMorse.MorseSurgeryData.coreBoundaryMap`
- `AdaptedWindows.exists_native_family_level_transport` (1802-1859) — external: `AdaptedWindows.exists_native_level_basin_transport`
- `AdaptedWindows.exists_middle_family_descent` (1945-2028) — in-file: `AdaptedWindows.exists_native_family_level_transport`
- `AdaptedWindows.exists_native_attaching_lower_cut` (2029-2081) — in-file: `AdaptedWindows.exists_embedded_level_transport`
- `AdaptedWindows.exists_middle_family_step` (2151-2269) — in-file: `AdaptedWindows.exists_middle_family_descent`, `AdaptedWindows.exists_native_attaching_lower_cut`
- `AdaptedWindows.exists_regular_band_family_transport` (2289-2331) — in-file: `AdaptedWindows.exists_native_family_level_transport`
- `AdaptedWindows.exists_regular_band_middle_basin_family` (2347-2367) — in-file: `AdaptedWindows.exists_regular_band_family_transport`
- `AdaptedWindows.exists_middle_basin_family_step` (2368-2397) — in-file: `AdaptedWindows.exists_middle_family_step`
- `AdaptedWindows.exists_middle_block_realization` (2398-2521) — in-file: `AdaptedWindows.exists_middle_basin_family_step`, `AdaptedWindows.exists_regular_band_middle_basin_family`
- `MorseCancellation.unique_connection_of_distinct_minimum_branches` (2522-2571) — external: `MorseCancellation.unitSphere_eq_two_points_of_finrank_one`
- `EmbeddedCellAttachment.overlapHomologyEquiv` (3144-3149) — in-file: `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.overlapHomologyEquiv`, `OnePointCover.overlapSphereEquiv`
- `EmbeddedCellAttachment.cellConnectingMap` (3162-3169) — in-file: `EmbeddedCellAttachment.overlapHomologyEquiv`, `OnePointCover.overlapHomologyEquiv`
- `EmbeddedCellAttachment.coverLeft_old` (3177-3197) — in-file: `EmbeddedCellAttachment.overlapHomologyEquiv`, `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.overlapHomologyEquiv` ...
- `EmbeddedCellAttachment.coverLeft_formula` (3213-3223) — in-file: `EmbeddedCellAttachment.coverLeft_old`, `EmbeddedCellAttachment.overlapHomologyEquiv`, `OnePointCover.overlapHomologyEquiv`
- `EmbeddedCellAttachment.cellConnecting_eq_zero_iff` (3242-3256) — in-file: `EmbeddedCellAttachment.cellConnectingMap`, `EmbeddedCellAttachment.overlapHomologyEquiv`, `OnePointCover.overlapHomologyEquiv`
- `EmbeddedCellAttachment.cell_exact_at_old` (3269-3317) — in-file: `EmbeddedCellAttachment.coverLeft_formula`, `EmbeddedCellAttachment.overlapHomologyEquiv`, `OnePointCover.overlapHomologyEquiv`
- `EmbeddedCellAttachment.cell_exact_at_ambient` (3318-3326) — in-file: `EmbeddedCellAttachment.cellConnectingMap`, `EmbeddedCellAttachment.cellConnecting_eq_zero_iff`
- `EmbeddedCellAttachment.mem_range_cellConnecting` (3327-3344) — in-file: `EmbeddedCellAttachment.cellConnectingMap`, `EmbeddedCellAttachment.overlapHomologyEquiv`, `OnePointCover.overlapHomologyEquiv`
- `EmbeddedCellAttachment.coverLeft_eq_zero_iff` (3345-3366) — in-file: `EmbeddedCellAttachment.coverLeft_formula`, `EmbeddedCellAttachment.overlapHomologyEquiv`, `OnePointCover.overlapHomologyEquiv`
- `EmbeddedCellAttachment.cell_exact_at_sphere` (3367-3376) — in-file: `EmbeddedCellAttachment.cellConnectingMap`, `EmbeddedCellAttachment.coverLeft_eq_zero_iff`, `EmbeddedCellAttachment.mem_range_cellConnecting`
- `EmbeddedCellAttachment.cellConnecting_zero_apply` (3377-3402) — in-file: `EmbeddedCellAttachment.cellConnectingMap`, `EmbeddedCellAttachment.mem_range_cellConnecting`, `EmbeddedCellAttachment.overlapHomologyEquiv`, `LocalDegree.NativeNeighborhood.overlapSphereEquiv` ...
- `MorseCancellation.cell_oldHomologyMap_zero_injective` (3403-3444) — in-file: `EmbeddedCellAttachment.overlapHomologyEquiv`, `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.overlapHomologyEquiv` ...
- `MorseCancellation.cell_oldHomologyMap_zero_surjective` (3445-3490) — in-file: `EmbeddedCellAttachment.overlapHomologyEquiv`, `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.overlapHomologyEquiv` ...
- `MorseCancellation.cell_oldHomologyMap_zero_bijective` (3491-3495) — in-file: `MorseCancellation.cell_oldHomologyMap_zero_injective`, `MorseCancellation.cell_oldHomologyMap_zero_surjective`
- `ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv` (3570-3577) — external: `ManifoldMorse.MorseSurgeryData.cellOldHomeomorph`, `ManifoldMorse.MorseSurgeryData.coreCellPresentation`
- `ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv` (3578-3587) — external: `ManifoldMorse.MorseSurgeryData.coreMap`, `ManifoldMorse.MorseSurgeryData.coreUnionHomotopyEquiv`
- `ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap` (3588-3596) — external: `ManifoldMorse.MorseSurgeryData.coreBoundaryMap`
- `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap` (3597-3604) — external: `ManifoldMorse.MorseSurgeryData.realizedLowerInclusion`
- `ManifoldMorse.MorseSurgeryData.morseConnectingMap` (3605-3614) — external: `ManifoldMorse.MorseSurgeryData.coreCellPresentation`; in-file: `EmbeddedCellAttachment.cellConnectingMap`, `ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv`
- `ManifoldMorse.MorseSurgeryData.cellAttachingHomology_compare` (3615-3631) — external: `ManifoldMorse.MorseSurgeryData.cellOldHomeomorph`, `ManifoldMorse.MorseSurgeryData.coreBoundaryMap`, `ManifoldMorse.MorseSurgeryData.coreCellPresentation`, `ManifoldMorse.MorseSurgeryData.coreCell_attaching_eq`; in-file: `ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap`
- `ManifoldMorse.MorseSurgeryData.cellOldHomology_compare` (3632-3650) — external: `ManifoldMorse.MorseSurgeryData.cellOldHomeomorph`, `ManifoldMorse.MorseSurgeryData.coreCellPresentation`, `ManifoldMorse.MorseSurgeryData.coreUnionHomotopyEquiv`, `ManifoldMorse.MorseSurgeryData.realizedLowerInclusion`; in-file: `ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap`
- `ManifoldMorse.MorseSurgeryData.morseConnecting_compare` (3651-3666) — external: `ManifoldMorse.MorseSurgeryData.coreCellPresentation`, `ManifoldMorse.MorseSurgeryData.coreMap`; in-file: `EmbeddedCellAttachment.cellConnectingMap`, `ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.morseConnectingMap`
- `ManifoldMorse.MorseSurgeryData.morse_exact_at_lower` (3667-3689) — external: `ManifoldMorse.MorseSurgeryData.coreCellPresentation`; in-file: `EmbeddedCellAttachment.cell_exact_at_old`, `ManifoldMorse.MorseSurgeryData.cellAttachingHomology_compare`, `ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.cellOldHomology_compare` ...
- `ManifoldMorse.MorseSurgeryData.morse_exact_at_upper` (3690-3708) — external: `ManifoldMorse.MorseSurgeryData.coreCellPresentation`; in-file: `EmbeddedCellAttachment.cellConnectingMap`, `EmbeddedCellAttachment.cell_exact_at_ambient`, `ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.cellOldHomology_compare` ...
- `ManifoldMorse.MorseSurgeryData.morse_exact_at_attachingSphere` (3709-3727) — external: `ManifoldMorse.MorseSurgeryData.coreCellPresentation`; in-file: `EmbeddedCellAttachment.cellConnectingMap`, `EmbeddedCellAttachment.cell_exact_at_sphere`, `ManifoldMorse.MorseSurgeryData.cellAttachingHomology_compare`, `ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv` ...
- `ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_sphere` (3728-3751) — in-file: `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap`, `ManifoldMorse.MorseSurgeryData.morse_exact_at_lower`
- `ManifoldMorse.MorseSurgeryData.morseConnecting_zero_apply` (3760-3768) — external: `ManifoldMorse.MorseSurgeryData.coreCellPresentation`; in-file: `EmbeddedCellAttachment.cellConnecting_zero_apply`, `ManifoldMorse.MorseSurgeryData.morseConnectingMap`
- `ManifoldMorse.MorseSurgeryData.lowerRealization_one_surjective` (3769-3779) — in-file: `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap`, `ManifoldMorse.MorseSurgeryData.morseConnectingMap`, `ManifoldMorse.MorseSurgeryData.morseConnecting_zero_apply`, `ManifoldMorse.MorseSurgeryData.morse_exact_at_upper`
- `ManifoldMorse.MorseSurgeryData.upperHomologyOne_subsingleton` (3780-3789) — in-file: `ManifoldMorse.MorseSurgeryData.lowerRealization_one_surjective`
- `MorseCancellation.native_lowerRealization_zero_bijective` (3790-3808) — external: `ManifoldMorse.MorseSurgeryData.coreCellPresentation`; in-file: `ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.cellOldHomology_compare`, `ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap` ...
- `MorseCancellation.native_lower_pathConnected_of_upper` (3809-3821) — external: `ManifoldMorse.MorseSurgeryData.coreBoundaryMap`, `ManifoldMorse.MorseSurgeryData.realizedLowerInclusion`; in-file: `MorseCancellation.native_lowerRealization_zero_bijective`
- `MorseCancellation.native_zero_handle_lower_isEmpty` (4123-4142) — external: `ManifoldMorse.MorseSurgeryData.cellOldHomeomorph`, `ManifoldMorse.MorseSurgeryData.coreCellPresentation`, `ManifoldMorse.MorseSurgeryData.coreMap`, `ManifoldMorse.MorseSurgeryData.coreUnionHomotopyEquiv`
- `SublevelDisk.circle_nullhomotopies` (4143-4159) — external: `sphere_sphere_nullhomotopic`
- `ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices` (4224-4285) — in-file: `SublevelDisk.circle_nullhomotopies`
- `MorseCancellation.lower_circle_nullhomotopies_of_ordered_native_indices` (4329-4371) — in-file: `ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices`
- `MorseCancellation.cellDiskBoundaryHomologyMap` (4417-4423) — in-file: `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.overlapSphereEquiv`
- `MorseCancellation.cell_oldHomologyMap_zero_iff` (4424-4481) — in-file: `EmbeddedCellAttachment.coverLeft_old`, `EmbeddedCellAttachment.overlapHomologyEquiv`, `MorseCancellation.cellDiskBoundaryHomologyMap`, `OnePointCover.overlapHomologyEquiv`
- `MorseCancellation.cell_oldHomologyMap_injective_of_attaching_component` (4482-4507) — in-file: `MorseCancellation.cellDiskBoundaryHomologyMap`, `MorseCancellation.cell_oldHomologyMap_zero_iff`
- `MorseCancellation.cell_old_pathConnected_of_attaching_component` (4508-4516) — in-file: `MorseCancellation.cell_oldHomologyMap_injective_of_attaching_component`
- `MorseCancellation.native_lower_pathConnected_of_attaching_component` (4517-4532) — external: `ManifoldMorse.MorseSurgeryData.cellOldHomeomorph`, `ManifoldMorse.MorseSurgeryData.coreBoundaryMap`, `ManifoldMorse.MorseSurgeryData.coreCellPresentation`, `ManifoldMorse.MorseSurgeryData.coreCell_attaching_eq` ...; in-file: `MorseCancellation.cell_old_pathConnected_of_attaching_component`
- `MorseCancellation.native_attaching_component_of_pairwise_joined` (4533-4543) — external: `ManifoldMorse.MorseSurgeryData.coreBoundaryMap`
- `MorseCancellation.native_minimum_count_one_of_one_handle_components` (4544-4611) — external: `ManifoldMorse.MorseSurgeryData.coreBoundaryMap`; in-file: `MorseCancellation.native_lower_pathConnected_of_attaching_component`, `MorseCancellation.native_lower_pathConnected_of_upper`, `MorseCancellation.native_zero_handle_lower_isEmpty`
- `MorseCancellation.exists_native_one_handle_joining_components` (4612-4632) — external: `ManifoldMorse.MorseSurgeryData.coreBoundaryMap`; in-file: `MorseCancellation.native_attaching_component_of_pairwise_joined`, `MorseCancellation.native_minimum_count_one_of_one_handle_components`
- `MorseCancellation.cancel_realized_higher_minimum` (4633-4700) — in-file: `MorseCancellation.unique_connection_of_distinct_minimum_branches`
- `MorseCancellation.exists_excellent_morse_reduction_of_multiple_minima` (4701-4733) — in-file: `AdaptedWindows.realize_one_handle_minimum_branches`, `MorseCancellation.cancel_realized_higher_minimum`, `MorseCancellation.exists_native_one_handle_joining_components`
- `ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step` (4926-4976) — external: `ManifoldMorse.MorseSurgeryData.IsTransverseBeltSphere`, `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`, `ManifoldMorse.MorseSurgeryData.beltIntersectionSign`, `ManifoldMorse.MorseSurgeryData.exists_signed_belt_cancellation_step`
- `ManifoldMorse.MorseSurgeryData.exists_finite_belt_reduction` (4977-5040) — external: `ManifoldMorse.MorseSurgeryData.IsTransverseBeltSphere`, `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`, `ManifoldMorse.MorseSurgeryData.beltIntersectionSign`; in-file: `ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step`
- `ManifoldMorse.MorseSurgeryData.exists_minimal_signed_belt_sphere` (5041-5106) — external: `ManifoldMorse.MorseSurgeryData.IsTransverseBeltSphere`, `ManifoldMorse.MorseSurgeryData.beltIntersectionCount`, `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`, `ManifoldMorse.MorseSurgeryData.beltIntersectionSign` ...; in-file: `ManifoldMorse.MorseSurgeryData.exists_finite_belt_reduction`
- `ManifoldMorse.MorseSurgeryData.exists_single_belt_intersection_of_unit_count` (5107-5146) — external: `ManifoldMorse.MorseSurgeryData.IsTransverseBeltSphere`, `ManifoldMorse.MorseSurgeryData.beltIntersectionCount`, `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`, `ManifoldMorse.MorseSurgeryData.finite_points_of_isTransverseBeltSphere`; in-file: `ManifoldMorse.MorseSurgeryData.exists_minimal_signed_belt_sphere`
- `AdaptedWindows.remove_connections_of_index_le` (5147-5220) — external: `AdaptedWindows.exists_orbit_bandBridge`, `AdaptedWindows.transported_attaching_basin_iff`, `FlowSuspension.no_connection_of_level_basin_disjointness`, `MorseCancellation.surgery_pair_inner_band_regular`
- `AdaptedWindows.remove_connections_of_nonincreasing_indices` (5270-5302) — in-file: `AdaptedWindows.remove_connections_of_index_le`
- `AdaptedWindows.exchange_nonincreasing_native_indices` (5303-5358) — in-file: `AdaptedWindows.remove_connections_of_nonincreasing_indices`
- `MorseCancellation.exists_index_ordered_morse_system_preserving_critical_points` (5452-5504) — in-file: `AdaptedWindows.exchange_nonincreasing_native_indices`
- `MorseCancellation.minimal_excellent_morse_minimum_count_one` (5505-5522) — in-file: `MorseCancellation.exists_excellent_morse_reduction_of_multiple_minima`
- `MorseCancellation.minimal_excellent_morse_extreme_counts_one` (5523-5546) — in-file: `MorseCancellation.minimal_excellent_morse_minimum_count_one`
- `AdaptedWindows.exists_transverse_middle_belt_loop` (5547-5695) — external: `AdaptedWindows.exists_native_level_basin_transport`, `AdaptedWindows.exists_transverse_belt_circle_reaching_level_with_endpoints`; in-file: `MorseCancellation.transverse_comp_standardCircle`
- `SphereBoundary.exists_extension_immersive_on_sphere` (5832-5861) — external: `ManifoldImmersion.exists_compact_boundary_derivative_repair`, `SphereBoundary.common_kernel_of_immersive_sphere_extension`, `SphereBoundary.contDiff_definingFunction`, `SphereBoundary.definingFunction` ...
- `exists_embedded_disk_extension_of_smooth_extension` (5862-5900) — in-file: `SphereBoundary.exists_extension_immersive_on_sphere`
- `RadialFilling.contMDiffAt_direction` (5922-5944) — external: `contMDiff_normalize`
- `RadialFilling.contMDiff_filling` (6004-6033) — in-file: `RadialFilling.contMDiffAt_direction`
- `MorseCancellation.circle_nullhomotopy_of_disk` (6169-6197) — external: `SphereCone.continuous_point`, `SphereCone.point`
- `MorseCancellation.exists_smooth_embedded_disk_of_continuous_filling` (6198-6222) — in-file: `MorseCancellation.circle_nullhomotopy_of_disk`, `RadialFilling.contMDiff_filling`, `exists_embedded_disk_extension_of_smooth_extension`
- `AdaptedWindows.realize_unit_level_isotopy` (6717-6783) — external: `FlowSuspension.exists_unique_connection_of_unit_level_count`
- `AdaptedWindows.realize_unit_transverse_level_isotopy` (6784-6894) — in-file: `AdaptedWindows.realize_unit_level_isotopy`
- `AdaptedWindows.place_one_handle_in_unique_minimum_basin` (7112-7150) — external: `AdaptedWindows.dense_regular_level_minimum_basins`, `AdaptedWindows.forward_limit_below_regular_level`, `MorseCancellation.unitSphere_eq_two_points_of_finrank_one`
- `AdaptedWindows.realize_unique_minimum_one_handle_branches` (7151-7255) — in-file: `AdaptedWindows.place_one_handle_in_unique_minimum_basin`
- `MorseCancellation.exists_outer_index_minimal_ordered_morse_system` (7661-7720) — in-file: `MorseCancellation.exists_index_ordered_morse_system_preserving_critical_points`, `MorseCancellation.minimal_excellent_morse_extreme_counts_one`
- `DiskOnePointCollapse.collapse_compress` (7940-7946) — in-file: `DiskOnePointCollapse.collapse`, `DiskOnePointCollapse.collapse_interior`
- `DiskOnePointCollapse.collapse_eq_coe_iff` (7947-7956) — in-file: `DiskOnePointCollapse.collapse`, `DiskOnePointCollapse.collapse_compress`, `DiskOnePointCollapse.collapse_eq_iff`
- `DiskOnePointCollapse.collapse_eq_zero_iff` (7957-7966) — in-file: `DiskOnePointCollapse.collapse`, `DiskOnePointCollapse.collapse_eq_coe_iff`
- `DiskOnePointCollapse.collapse_eq_infty_iff` (7967-7975) — in-file: `DiskOnePointCollapse.collapse`, `DiskOnePointCollapse.collapse_boundary`, `DiskOnePointCollapse.collapse_interior`
- `ClosedHandleCore.collapseMaps_agree` (7976-7986) — in-file: `DiskOnePointCollapse.collapse`, `DiskOnePointCollapse.collapse_boundary`, `EmbeddedCellAttachment.collapseMaps_agree`
- `ClosedHandleCore.collapseMap` (7987-7995) — in-file: `ClosedHandleCore.collapseMaps_agree`, `DiskOnePointCollapse.collapse`, `EmbeddedCellAttachment.collapseMap`, `EmbeddedCellAttachment.collapseMaps_agree`
- `ClosedHandleCore.collapseMap_old` (7996-8005) — in-file: `ClosedHandleCore.collapseMap`, `ClosedHandleCore.collapseMaps_agree`, `DiskOnePointCollapse.collapse`, `EmbeddedCellAttachment.collapseMap` ...
- `ClosedHandleCore.collapseMap_handle` (8006-8017) — in-file: `ClosedHandleCore.collapseMap`, `ClosedHandleCore.collapseMaps_agree`, `DiskOnePointCollapse.collapse`, `EmbeddedCellAttachment.collapseMap` ...
- `EmbeddedCellAttachment.collapseMaps_agree` (8023-8028) — in-file: `ClosedHandleCore.collapseMaps_agree`, `DiskOnePointCollapse.collapse`, `DiskOnePointCollapse.collapse_boundary`
- `EmbeddedCellAttachment.collapseMap` (8029-8035) — in-file: `ClosedHandleCore.collapseMap`, `ClosedHandleCore.collapseMaps_agree`, `DiskOnePointCollapse.collapse`, `EmbeddedCellAttachment.collapseMaps_agree`
- `EmbeddedCellAttachment.collapseMap_old` (8036-8043) — in-file: `ClosedHandleCore.collapseMap`, `ClosedHandleCore.collapseMap_old`, `ClosedHandleCore.collapseMaps_agree`, `DiskOnePointCollapse.collapse` ...
- `EmbeddedCellAttachment.collapseMap_cell` (8044-8052) — in-file: `ClosedHandleCore.collapseMap`, `ClosedHandleCore.collapseMaps_agree`, `DiskOnePointCollapse.collapse`, `EmbeddedCellAttachment.collapseMap` ...
- `EmbeddedCellAttachment.collapseMap_infty_iff` (8053-8060) — in-file: `ClosedHandleCore.collapseMap`, `ClosedHandleCore.collapseMap_old`, `DiskOnePointCollapse.collapse_eq_infty_iff`, `EmbeddedCellAttachment.collapseMap` ...
- `OnePointCover.instLocal1` (8085-8088) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `SpherePoint.instLocal1`
- `OnePointCover.spherePunctureHomeomorph_mo1973_5327` (8089-8097) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `SpherePoint.instLocal1`
- `OnePointCover.punctureHomeomorph` (8098-8110) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `OnePointCover.spherePunctureHomeomorph_mo1973_5327`, `SpherePoint.instLocal1`, `SpherePoint.punctureHomeomorph`
- `OnePointCover.oldPatch_contractible` (8111-8115) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `OnePointCover.punctureHomeomorph`, `SpherePoint.instLocal1`, `SpherePoint.punctureHomeomorph`
- `OnePointCover.finitePatch_contractible` (8116-8120) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `OnePointCover.punctureHomeomorph`, `SpherePoint.instLocal1`, `SpherePoint.punctureHomeomorph`
- `OnePointCover.overlap_subset_range` (8121-8128) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `SpherePoint.instLocal1`
- `OnePointCover.overlap_preimage` (8129-8139) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `SpherePoint.instLocal1`
- `OnePointCover.overlapHomeomorph` (8140-8145) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `OnePointCover.overlap_subset_range`, `SpherePoint.instLocal1`
- `OnePointCover.overlapHomeomorph_apply` (8146-8150) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `OnePointCover.overlapHomeomorph`, `SpherePoint.instLocal1`
- `OnePointCover.overlapSphereEquiv` (8151-8155) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`, `PuncturedRadial.sphereHomotopyEquiv`; in-file: `LinearSphereAction.sphereHomotopyEquiv`, `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.instLocal1` ...
- `EmbeddedCellAttachment.collapseMap_eq_zero_iff` (8163-8181) — in-file: `ClosedHandleCore.collapseMap`, `ClosedHandleCore.collapseMap_old`, `DiskOnePointCollapse.collapse_eq_zero_iff`, `EmbeddedCellAttachment.collapseMap` ...
- `EmbeddedCellAttachment.collapseMaps_oldNeighborhood` (8182-8192) — in-file: `ClosedHandleCore.collapseMap`, `EmbeddedCellAttachment.collapseMap`, `EmbeddedCellAttachment.collapseMap_eq_zero_iff`
- `EmbeddedCellAttachment.collapseMaps_diskPatch` (8193-8199) — in-file: `ClosedHandleCore.collapseMap`, `EmbeddedCellAttachment.collapseMap`, `EmbeddedCellAttachment.collapseMap_infty_iff`
- `EmbeddedCellAttachment.collapseOverlapMap` (8200-8207) — in-file: `ClosedHandleCore.collapseMap`, `EmbeddedCellAttachment.collapseMap`, `EmbeddedCellAttachment.collapseMaps_diskPatch`, `EmbeddedCellAttachment.collapseMaps_oldNeighborhood` ...
- `EmbeddedCellAttachment.collapseOverlap_sphere` (8208-8226) — in-file: `ClosedHandleCore.collapseMap`, `DiskOnePointCollapse.collapse_interior`, `EmbeddedCellAttachment.collapseMap`, `EmbeddedCellAttachment.collapseMap_cell` ...
- `EmbeddedCellAttachment.collapseOverlap_comp_sphere` (8227-8234) — in-file: `EmbeddedCellAttachment.collapseOverlapMap`, `EmbeddedCellAttachment.collapseOverlap_sphere`, `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv` ...
- `OnePointCover.overlapHomologyEquiv` (8235-8240) — in-file: `EmbeddedCellAttachment.overlapHomologyEquiv`, `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.overlapSphereEquiv`
- `OnePointCover.sphereConnecting` (8241-8248) — in-file: `EmbeddedCellAttachment.overlapHomologyEquiv`, `LocalDegree.NativeNeighborhood.sphereConnecting`, `OnePointCover.overlapHomologyEquiv`
- `EmbeddedCellAttachment.collapse_overlapHomology_compare` (8273-8287) — in-file: `EmbeddedCellAttachment.collapseOverlapMap`, `EmbeddedCellAttachment.collapseOverlap_comp_sphere`, `EmbeddedCellAttachment.overlapHomologyEquiv`, `LocalDegree.NativeNeighborhood.overlapSphereEquiv` ...
- `EmbeddedCellAttachment.collapse_connecting_compare` (8288-8311) — in-file: `ClosedHandleCore.collapseMap`, `EmbeddedCellAttachment.cellConnectingMap`, `EmbeddedCellAttachment.collapseMap`, `EmbeddedCellAttachment.collapseMaps_diskPatch` ...
- `ManifoldMorse.MorseSurgeryData.attachmentCollapseMap` (8312-8321) — external: `ManifoldMorse.MorseSurgeryData.handleMap`; in-file: `ClosedHandleCore.collapseMap`, `EmbeddedCellAttachment.collapseMap`
- `ManifoldMorse.MorseSurgeryData.upperCollapseMap` (8322-8328) — in-file: `ManifoldMorse.MorseSurgeryData.attachmentCollapseMap`
- `ManifoldMorse.MorseSurgeryData.upperCollapse_realization` (8329-8337) — external: `ManifoldMorse.MorseSurgeryData.handleMap`; in-file: `ManifoldMorse.MorseSurgeryData.attachmentCollapseMap`, `ManifoldMorse.MorseSurgeryData.upperCollapseMap`
- `ManifoldMorse.MorseSurgeryData.upperCollapse_old` (8338-8350) — external: `ManifoldMorse.MorseSurgeryData.handleMap`, `ManifoldMorse.MorseSurgeryData.realizedLowerInclusion`; in-file: `ClosedHandleCore.collapseMap_old`, `EmbeddedCellAttachment.collapseMap_old`, `ManifoldMorse.MorseSurgeryData.upperCollapseMap`, `ManifoldMorse.MorseSurgeryData.upperCollapse_realization`
- `ManifoldMorse.MorseSurgeryData.upperCollapse_handle` (8351-8362) — external: `ManifoldMorse.MorseSurgeryData.HandleDomain`, `ManifoldMorse.MorseSurgeryData.handleMap`; in-file: `ClosedHandleCore.collapseMap_handle`, `DiskOnePointCollapse.collapse`, `ManifoldMorse.MorseSurgeryData.upperCollapseMap`, `ManifoldMorse.MorseSurgeryData.upperCollapse_realization`
- `ManifoldMorse.MorseSurgeryData.levelCollapseMap` (8363-8369) — in-file: `ManifoldMorse.MorseSurgeryData.upperCollapseMap`
- `ManifoldMorse.MorseSurgeryData.levelCollapse_realized` (8370-8382) — external: `ManifoldMorse.MorseSurgeryData.handleMap`; in-file: `ManifoldMorse.MorseSurgeryData.attachmentCollapseMap`, `ManifoldMorse.MorseSurgeryData.levelCollapseMap`, `ManifoldMorse.MorseSurgeryData.upperCollapseMap`, `ManifoldMorse.MorseSurgeryData.upperCollapse_realization`
- `ManifoldMorse.MorseSurgeryData.levelCollapse_newExterior` (8383-8390) — external: `ManifoldMorse.MorseSurgeryData.handleMap`; in-file: `ClosedHandleCore.collapseMap_old`, `EmbeddedCellAttachment.collapseMap_old`, `ManifoldMorse.MorseSurgeryData.levelCollapseMap`, `ManifoldMorse.MorseSurgeryData.levelCollapse_realized`
- `ManifoldMorse.MorseSurgeryData.levelCollapse_newPiece` (8391-8405) — external: `ManifoldMorse.MorseSurgeryData.handleMap`; in-file: `ClosedHandleCore.collapseMap_handle`, `DiskOnePointCollapse.collapse`, `ManifoldMorse.MorseSurgeryData.levelCollapseMap`, `ManifoldMorse.MorseSurgeryData.levelCollapse_realized`
- `ManifoldMorse.MorseSurgeryData.levelCollapse_zero_iff` (8406-8422) — in-file: `DiskOnePointCollapse.collapse_eq_zero_iff`, `ManifoldMorse.MorseSurgeryData.levelCollapseMap`, `ManifoldMorse.MorseSurgeryData.levelCollapse_newExterior`, `ManifoldMorse.MorseSurgeryData.levelCollapse_newPiece`
- `ManifoldMorse.MorseSurgeryData.upperCollapse_coreCell` (8423-8439) — external: `ManifoldMorse.MorseSurgeryData.coreCellPresentation`, `ManifoldMorse.MorseSurgeryData.coreUnionHomotopyEquiv`, `ManifoldMorse.MorseSurgeryData.handleMap`; in-file: `ClosedHandleCore.collapseMap`, `ClosedHandleCore.collapseMap_old`, `EmbeddedCellAttachment.collapseMap`, `EmbeddedCellAttachment.collapseMap_cell` ...
- `ManifoldMorse.MorseSurgeryData.upperCollapseHomology_coreCell` (8440-8457) — external: `ManifoldMorse.MorseSurgeryData.coreCellPresentation`, `ManifoldMorse.MorseSurgeryData.coreMap`, `ManifoldMorse.MorseSurgeryData.coreUnionHomotopyEquiv`; in-file: `ClosedHandleCore.collapseMap`, `EmbeddedCellAttachment.collapseMap`, `ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.upperCollapseMap` ...
- `ManifoldMorse.MorseSurgeryData.upperCollapse_connecting_compare` (8458-8471) — external: `ManifoldMorse.MorseSurgeryData.coreCellPresentation`; in-file: `EmbeddedCellAttachment.collapse_connecting_compare`, `LocalDegree.NativeNeighborhood.sphereConnecting`, `ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.morseConnectingMap` ...
- `ManifoldMorse.MorseSurgeryData.upperCollapse_homology_equiv_compare` (8472-8483) — in-file: `LocalDegree.NativeNeighborhood.sphereHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.morseConnectingMap`, `ManifoldMorse.MorseSurgeryData.upperCollapseMap`, `ManifoldMorse.MorseSurgeryData.upperCollapse_connecting_compare` ...
- `ManifoldMorse.MorseSurgeryData.upperCollapse_homology_kernel` (8484-8505) — in-file: `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap`, `ManifoldMorse.MorseSurgeryData.morseConnectingMap`, `ManifoldMorse.MorseSurgeryData.morse_exact_at_upper`, `ManifoldMorse.MorseSurgeryData.upperCollapseMap` ...
- `ManifoldMorse.MorseSurgeryData.morseConnecting_surjective_of_lower` (8506-8518) — in-file: `ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap`, `ManifoldMorse.MorseSurgeryData.morseConnectingMap`, `ManifoldMorse.MorseSurgeryData.morse_exact_at_attachingSphere`
- `ManifoldMorse.MorseSurgeryData.upperCollapse_surjective_of_lower` (8519-8535) — in-file: `LocalDegree.NativeNeighborhood.sphereHomologyEquiv`, `ManifoldMorse.MorseSurgeryData.morseConnecting_surjective_of_lower`, `ManifoldMorse.MorseSurgeryData.upperCollapseMap`, `ManifoldMorse.MorseSurgeryData.upperCollapse_homology_equiv_compare` ...
- `LocalDegree.NativeNeighborhood.overlapSphereEquiv` (8809-8823) — in-file: `LinearSphereAction.sphereHomotopyEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.overlapSphereEquiv`, `PuncturedBall.sphereHomotopyEquiv`
- `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv` (8955-8962) — in-file: `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `OnePointCover.overlapSphereEquiv`
- `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv_apply` (8963-8971) — in-file: `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.overlapSphereEquiv`
- `LocalDegree.SeparatedNeighborhoods.overlapMap_sphereEquiv` (9019-9030) — in-file: `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv_apply`, `OnePointCover.overlapSphereEquiv`
- `ManifoldMorse.MorseSurgeryData.levelCollapse_beltClosedDiskMap` (9254-9267) — in-file: `DiskOnePointCollapse.collapse`, `ManifoldMorse.MorseSurgeryData.levelCollapseMap`, `ManifoldMorse.MorseSurgeryData.levelCollapse_newPiece`
- `ManifoldMorse.MorseSurgeryData.levelCollapse_eq_coe_collapseNormal` (9268-9284) — in-file: `DiskOnePointCollapse.collapse_interior`, `ManifoldMorse.MorseSurgeryData.levelCollapseMap`, `ManifoldMorse.MorseSurgeryData.levelCollapse_beltClosedDiskMap`
- `SphereNormalCoordinates.normalJacobian_smul_mul_pow` (9294-9315) — external: `SphereNormalCoordinates.normalJacobian`, `SphereNormalCoordinates.normalJacobian_mul_chartDet`
- `SphereNormalCoordinates.sign_normalJacobian_smul_pos` (9316-9325) — external: `SphereNormalCoordinates.normalJacobian`; in-file: `SphereNormalCoordinates.normalJacobian_smul_mul_pow`
- `ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign` (9354-9374) — external: `ManifoldMorse.MorseSurgeryData.beltIntersectionSign`, `SphereNormalCoordinates.normalJacobian`; in-file: `SphereNormalCoordinates.sign_normalJacobian_smul_pos`
- `ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign_of_transverse` (9375-9409) — external: `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`, `ManifoldMorse.MorseSurgeryData.beltIntersectionSign`, `ManifoldMorse.MorseSurgeryData.bijective_beltNormal_comp_of_transverse`, `SphereNormalCoordinates.normalJacobian`; in-file: `ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign`
- `ManifoldMorse.MorseSurgeryData.isInvertible_collapseNormal_comp_of_transverse` (9448-9478) — external: `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`, `ManifoldMorse.MorseSurgeryData.bijective_beltNormal_comp_of_transverse`
- `ManifoldMorse.MorseSurgeryData.CollapseNeighborhoods` (9479-9486) — external: `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`
- `ManifoldMorse.MorseSurgeryData.nonempty_collapseNeighborhoods` (9487-9518) — external: `ManifoldMorse.MorseSurgeryData.finite_beltIntersectionPoints`; in-file: `ManifoldMorse.MorseSurgeryData.CollapseNeighborhoods`, `ManifoldMorse.MorseSurgeryData.isInvertible_collapseNormal_comp_of_transverse`
- `ManifoldMorse.MorseSurgeryData.attachingCollapse` (9543-9550) — in-file: `ManifoldMorse.MorseSurgeryData.levelCollapseMap`
- `ManifoldMorse.MorseSurgeryData.attachingCollapse_zero_iff` (9551-9559) — external: `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`; in-file: `ManifoldMorse.MorseSurgeryData.attachingCollapse`, `ManifoldMorse.MorseSurgeryData.levelCollapse_zero_iff`
- `ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_old` (9560-9569) — external: `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`; in-file: `ManifoldMorse.MorseSurgeryData.attachingCollapse`, `ManifoldMorse.MorseSurgeryData.attachingCollapse_zero_iff`
- `ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_neighborhood` (9570-9582) — external: `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`; in-file: `ManifoldMorse.MorseSurgeryData.CollapseNeighborhoods`, `ManifoldMorse.MorseSurgeryData.attachingCollapse`, `ManifoldMorse.MorseSurgeryData.levelCollapseMap`, `ManifoldMorse.MorseSurgeryData.levelCollapse_eq_coe_collapseNormal`
- `ManifoldMorse.MorseSurgeryData.collapseOverlapMap` (9583-9596) — external: `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`; in-file: `EmbeddedCellAttachment.collapseOverlapMap`, `ManifoldMorse.MorseSurgeryData.CollapseNeighborhoods`, `ManifoldMorse.MorseSurgeryData.attachingCollapse`, `ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_neighborhood` ...
- `ManifoldMorse.MorseSurgeryData.collapseOverlapMap_eq` (9597-9614) — external: `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`; in-file: `EmbeddedCellAttachment.collapseOverlapMap`, `ManifoldMorse.MorseSurgeryData.CollapseNeighborhoods`, `ManifoldMorse.MorseSurgeryData.collapseOverlapMap`, `ManifoldMorse.MorseSurgeryData.levelCollapseMap` ...
- `ManifoldMorse.MorseSurgeryData.collapseOverlapMap_sphereEquiv` (9615-9625) — external: `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints`; in-file: `EmbeddedCellAttachment.collapseOverlapMap`, `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapMap_sphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv` ...
- `ManifoldMorse.SurgeryWindows.BandData.homologyEquiv` (9673-9680) — in-file: `LinearSphereAction.homologyEquiv`
- `ManifoldMorse.SurgeryWindows.lower_homologyOne_subsingleton_of_indices` (9693-9752) — in-file: `ManifoldMorse.MorseSurgeryData.upperHomologyOne_subsingleton`
- `ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_index` (9775-9787) — in-file: `ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_sphere`
- `LinearSphereAction.sphereHomotopyEquiv` (9832-9837) — external: `LocalDegree.linearSphereEquiv`, `PuncturedRadial.sphereHomotopyEquiv`; in-file: `PuncturedBall.sphereHomotopyEquiv`
- `LinearSphereAction.sphereHomotopyEquiv_toFun` (9838-9842) — external: `sphereHomotopyEquiv`; in-file: `LinearSphereAction.sphereHomotopyEquiv`
- `LinearSphereAction.homologyEquiv` (9843-9848) — external: `sphereHomotopyEquiv`; in-file: `LinearSphereAction.sphereHomotopyEquiv`, `ManifoldMorse.SurgeryWindows.BandData.homologyEquiv`
- `LinearSphereAction.homologyEquiv_apply` (9849-9857) — external: `sphereHomotopyEquiv`; in-file: `LinearSphereAction.homologyEquiv`, `LinearSphereAction.sphereHomotopyEquiv`, `LinearSphereAction.sphereHomotopyEquiv_toFun`, `ManifoldMorse.SurgeryWindows.BandData.homologyEquiv`
- `LocalDegree.NativeNeighborhood.sphereConnecting` (10014-10028) — in-file: `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.overlapSphereEquiv`, `OnePointCover.sphereConnecting`
- `SpherePoint.chart_radial_frame_comp` (10193-10227) — external: `SphereNormalCoordinates.chartRadialFrame`
- `LocalDegree.BoundaryData.normalized_homology_compare` (10240-10251) — external: `LocalDegree.BoundaryData.normalizedMap`
- `LocalDegree.BoundaryData.normalized_homology_eq_sign_smul` (10252-10264) — external: `LocalDegree.BoundaryData.normalizedMap`; in-file: `LocalDegree.BoundaryData.normalized_homology_compare`
- `SphereNormalCoordinates.chartJacobian` (10265-10275) — external: `SphereNormalCoordinates.chartRadialFrame`
- `SphereNormalCoordinates.chartJacobian_ne_zero` (10276-10288) — external: `SphereNormalCoordinates.bijective_chartRadialFrame`; in-file: `SphereNormalCoordinates.chartJacobian`
- `SphereNormalCoordinates.chartJacobian_factor` (10289-10320) — external: `SphereNormalCoordinates.chartRadialFrame_eq`, `SphereNormalCoordinates.normalJacobian`, `SphereNormalCoordinates.normalJacobian_change_normal_model`, `SphereNormalCoordinates.normalJacobian_mul_chartDet`; in-file: `SphereNormalCoordinates.chartJacobian`
- `SphereNormalCoordinates.chartJacobian_sign_factor` (10328-10346) — external: `SphereNormalCoordinates.normalJacobian`; in-file: `SphereNormalCoordinates.chartJacobian`, `SphereNormalCoordinates.chartJacobian_factor`, `SphereNormalCoordinates.chartJacobian_ne_zero`
- `SpherePoint.chart_radial_frame_det` (10347-10398) — external: `SphereNormalCoordinates.chartRadialFrame`; in-file: `SpherePoint.chart_radial_frame_comp`
- `SpherePoint.chartJacobian_transport` (10399-10412) — in-file: `SphereNormalCoordinates.chartJacobian`, `SpherePoint.chart_radial_frame_det`
- `SpherePoint.chartJacobian_transport_sign` (10413-10430) — in-file: `SphereNormalCoordinates.chartJacobian`, `SpherePoint.chartJacobian_transport`
- `LocalDegree.PointTransition.coordinateMap` (10436-10459) — in-file: `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv`, `OnePointCover.overlapSphereEquiv`
- `LocalDegree.PointTransition.coordinateMap_coe` (10460-10488) — in-file: `LocalDegree.PointTransition.coordinateMap`
- `LocalDegree.PointTransition.connecting_naturality` (10489-10521) — in-file: `LocalDegree.NativeNeighborhood.overlapSphereEquiv`, `LocalDegree.NativeNeighborhood.sphereConnecting`, `LocalDegree.PointTransition.coordinateMap`, `LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv` ...
- `LocalDegree.NativeNeighborhood.coordinateMap_restrictRadius` (10566-10599) — in-file: `LocalDegree.PointTransition.coordinateMap`, `LocalDegree.PointTransition.coordinateMap_coe`
- `LocalDegree.NativeNeighborhood.sphereConnecting_restrictRadius` (10600-10621) — in-file: `LocalDegree.NativeNeighborhood.coordinateMap_restrictRadius`, `LocalDegree.NativeNeighborhood.sphereConnecting`, `LocalDegree.PointTransition.connecting_naturality`, `OnePointCover.sphereConnecting`
- `LocalDegree.NativeNeighborhood.sphereConnecting_eq` (10622-10643) — in-file: `LocalDegree.NativeNeighborhood.sphereConnecting`, `LocalDegree.NativeNeighborhood.sphereConnecting_restrictRadius`, `OnePointCover.sphereConnecting`
- `LocalDegree.PointTransition.coordinateMap_eq_boundary` (10644-10665) — external: `LocalDegree.BoundaryData.normalizedMap`; in-file: `LocalDegree.PointTransition.coordinateMap`
- `LocalDegree.PointTransition.coordinateMap_homology` (10666-10691) — in-file: `LocalDegree.BoundaryData.normalized_homology_compare`, `LocalDegree.PointTransition.coordinateMap`, `LocalDegree.PointTransition.coordinateMap_eq_boundary`
- `LocalDegree.PointTransition.connecting_derivative_naturality` (10692-10727) — in-file: `LocalDegree.NativeNeighborhood.sphereConnecting`, `LocalDegree.NativeNeighborhood.sphereConnecting_eq`, `LocalDegree.PointTransition.connecting_naturality`, `LocalDegree.PointTransition.coordinateMap_homology` ...
- `LocalDegree.pointConnecting_diffeomorph` (10728-10764) — in-file: `LocalDegree.NativeNeighborhood.sphereConnecting`, `LocalDegree.PointTransition.connecting_derivative_naturality`, `OnePointCover.sphereConnecting`
- `SpherePoint.instLocal1` (10765-10768) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`
- `SpherePoint.pointDiffeomorph` (10769-10774) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `SpherePoint.instLocal1`
- `SpherePoint.pointDiffeomorph_apply` (10775-10779) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `SpherePoint.instLocal1`, `SpherePoint.pointDiffeomorph`
- `SpherePoint.pointChartLinear` (10780-10784) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `OnePointCover.instLocal1`, `SpherePoint.instLocal1`, `SpherePoint.pointDiffeomorph`, `SpherePoint.pointDiffeomorph_apply`
- `SpherePoint.pointClass_sign_compare` (10785-10816) — external: `ManifoldMorse.MorseSurgeryData.instLocal1`; in-file: `LocalDegree.NativeNeighborhood.sphereConnecting`, `LocalDegree.pointConnecting_diffeomorph`, `OnePointCover.instLocal1`, `OnePointCover.sphereConnecting` ...
- `SpherePoint.punctureHomeomorph` (10817-10823) — in-file: `OnePointCover.punctureHomeomorph`
- `SpherePoint.puncture_contractible` (10824-10828) — in-file: `OnePointCover.punctureHomeomorph`, `SpherePoint.punctureHomeomorph`
- `SpherePoint.connectingHomologyEquiv` (10829-10846) — in-file: `LocalDegree.NativeNeighborhood.sphereHomologyEquiv`, `OnePointCover.sphereHomologyEquiv`, `SpherePoint.puncture_contractible`
- `SpherePoint.outwardPointClass` (10851-10870) — in-file: `LocalDegree.NativeNeighborhood.sphereConnecting`, `OnePointCover.sphereConnecting`, `SphereNormalCoordinates.chartJacobian`
- `SpherePoint.outwardPointClass_eq` (10871-10911) — in-file: `LocalDegree.NativeNeighborhood.sphereConnecting`, `OnePointCover.sphereConnecting`, `SphereNormalCoordinates.chartJacobian`, `SpherePoint.chartJacobian_transport_sign` ...
- `SpherePoint.chartSign_mul_self` (10912-10939) — in-file: `SphereNormalCoordinates.chartJacobian`, `SphereNormalCoordinates.chartJacobian_ne_zero`
- `SpherePoint.connecting_eq_sign_outward` (10940-10971) — in-file: `LocalDegree.NativeNeighborhood.sphereConnecting`, `OnePointCover.sphereConnecting`, `SphereNormalCoordinates.chartJacobian`, `SpherePoint.chartSign_mul_self` ...
- `SpherePoint.outwardPointClassEquiv` (10972-11001) — in-file: `SphereNormalCoordinates.chartJacobian`, `SpherePoint.chartSign_mul_self`, `SpherePoint.connectingHomologyEquiv`, `SpherePoint.outwardPointClass`
- `SpherePoint.outwardClass` (11025-11032) — in-file: `SpherePoint.outwardPointClass`
- `SpherePoint.outwardClassEquiv` (11033-11040) — in-file: `SpherePoint.outwardPointClassEquiv`
- `SpherePoint.outwardPointClass_eq_global` (11041-11054) — in-file: `SpherePoint.outwardClass`, `SpherePoint.outwardPointClass`, `SpherePoint.outwardPointClass_eq`
- `SpherePoint.pointConnecting_eq_outward` (11055-11075) — in-file: `LocalDegree.NativeNeighborhood.sphereConnecting`, `OnePointCover.sphereConnecting`, `SphereNormalCoordinates.chartJacobian`, `SpherePoint.connecting_eq_sign_outward` ...
- `SpherePoint.sourceCountMark` (11076-11081) — in-file: `SpherePoint.outwardClassEquiv`
- `SpherePoint.overlapCountMark` (11082-11087) — in-file: `LinearSphereAction.homologyEquiv`, `ManifoldMorse.SurgeryWindows.BandData.homologyEquiv`
- `SpherePoint.targetCountMark` (11088-11092) — in-file: `LocalDegree.NativeNeighborhood.sphereHomologyEquiv`, `OnePointCover.sphereHomologyEquiv`, `SpherePoint.overlapCountMark`
- `SpherePoint.overlapCountMark_linear` (11093-11107) — in-file: `LinearSphereAction.homologyEquiv`, `LinearSphereAction.homologyEquiv_apply`, `ManifoldMorse.SurgeryWindows.BandData.homologyEquiv`, `SpherePoint.overlapCountMark`
- `SpherePoint.countMark_of_connecting` (11108-11124) — in-file: `LocalDegree.NativeNeighborhood.sphereConnecting`, `OnePointCover.sphereConnecting`, `SpherePoint.outwardClass`, `SpherePoint.overlapCountMark` ...
- `ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate` (11132-11139) — in-file: `ManifoldMorse.MorseSurgeryData.upperCollapseMap`, `SpherePoint.targetCountMark`
- `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_surjective` (11140-11149) — in-file: `ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate`, `ManifoldMorse.MorseSurgeryData.upperCollapse_surjective_of_lower`, `SpherePoint.targetCountMark`
- `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_kernel` (11150-11167) — in-file: `ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate`, `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap`, `ManifoldMorse.MorseSurgeryData.upperCollapseMap`, `ManifoldMorse.MorseSurgeryData.upperCollapse_homology_kernel` ...
- `ManifoldMorse.MorseSurgeryData.lowerRealization_two_injective` (11168-11185) — in-file: `ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap`, `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap`, `ManifoldMorse.MorseSurgeryData.morse_exact_at_lower`
- `ManifoldMorse.MorseSurgeryData.exists_indexTwoHomology_split` (11186-11202) — in-file: `ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate`, `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_kernel`, `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_surjective`, `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap` ...
- `ManifoldMorse.MorseSurgeryData.exists_indexTwoBasis_extension` (11203-11227) — in-file: `ManifoldMorse.MorseSurgeryData.exists_indexTwoHomology_split`, `ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate`, `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap`
- `ManifoldMorse.SurgeryWindows.indexTwoBasis_step` (11239-11273) — in-file: `LinearSphereAction.homologyEquiv`, `ManifoldMorse.MorseSurgeryData.exists_indexTwoBasis_extension`, `ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate`, `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap` ...
- `ManifoldMorse.SurgeryWindows.indexTwoBasis` (11274-11297) — in-file: `ManifoldMorse.SurgeryWindows.indexTwoBasis_step`
- `ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass` (11324-11330) — in-file: `ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap`
- `ManifoldMorse.MorseSurgeryData.coreBoundary_two_eq_smul` (11331-11343) — in-file: `ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap`, `ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass`
- `ManifoldMorse.MorseSurgeryData.coreBoundary_two_range` (11344-11371) — in-file: `ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap`, `ManifoldMorse.MorseSurgeryData.coreBoundary_two_eq_smul`, `ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass`
- `ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_surjective` (11372-11386) — in-file: `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap`, `ManifoldMorse.MorseSurgeryData.morseConnectingMap`, `ManifoldMorse.MorseSurgeryData.morse_exact_at_upper`
- `ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_kernel` (11387-11394) — in-file: `ManifoldMorse.MorseSurgeryData.coreBoundary_two_range`, `ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass`, `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap`, `ManifoldMorse.MorseSurgeryData.morse_exact_at_lower`
- `ManifoldMorse.MorseSurgeryData.indexThreePresentation` (11395-11407) — in-file: `ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass`, `ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_kernel`, `ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_surjective`, `ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap`
- `ManifoldMorse.SurgeryWindows.middlePresentation` (11428-11448) — in-file: `LinearSphereAction.homologyEquiv`, `ManifoldMorse.MorseSurgeryData.indexThreePresentation`, `ManifoldMorse.SurgeryWindows.BandData.homologyEquiv`, `ManifoldMorse.SurgeryWindows.indexTwoBasis`
- `ManifoldMorse.SurgeryWindows.middleMatrix` (11546-11553) — in-file: `ManifoldMorse.SurgeryWindows.middlePresentation`
- `AdaptedWindows.exists_ordered_middle_family` (11684-11730) — in-file: `AdaptedWindows.exists_middle_block_realization`


## Build (worktree, full chain)

```
Build completed successfully (8823 jobs).
Build completed successfully (8862 jobs).
error lines: 0
```

Census: `ratchet PASS: 1255 <= baseline 1648`
