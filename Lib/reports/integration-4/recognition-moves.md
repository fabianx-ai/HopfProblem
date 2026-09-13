# Recognition moves (unit 1)

Worktree `lib/next-recognition`, base `304a0fea`. Commit `1e9506bb`. Source lines are those of
`Hopf/Recognition.lean` at `304a0fea` (whole block: docstring, attributes, declaration, proof).
Dependency analysis: `lean-agent-ide dump Hopf.Recognition --modules Hopf,Lib` on the seeded build
(scratch, not committed): a row is BLOCKED when one of its constants uses a constant defined in a stock
file under `Hopf/` other than `Hopf/Recognition.lean` (`_proof_n` edges included), CHARGED when its text
mentions a project-specific object (`SixSphere*` here), OK otherwise (transitively through rows of the
same file).


## Moved (28)

Text verbatim; qualifier retargets naming the same constants: `HigherHurewicz.* -> Hurewicz.*`,
`FirstHurewicz.* -> SingularChains.*`, `SecondHurewicz.mapGenLoop -> Hurewicz.DegreeTwo.mapGenLoop`
(`DegreeSix.lean`); `PeriodTorusHigherHomology.singularHomologyMap_{comp,id} ->
SingularHomology.singularHomologyMap_{comp,id}` (`LocalContributionsNaturality.lean`). The Lib files carry the
header `open`/`open scoped`/`universe`/`noncomputable section` lines of the source file.

| declaration | source `304a0fea` | destination |
|---|---|---|
| `SixthHurewicz.fundamentalCubeChain` | `Hopf/Recognition.lean:179-180` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:51` |
| `SixthHurewicz.cubeChain` | `Hopf/Recognition.lean:182-184` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:54` |
| `SixthHurewicz.cubeChain_eq_induced` | `Hopf/Recognition.lean:186-189` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:58` |
| `SixthHurewicz.cubeCycle` | `Hopf/Recognition.lean:191-193` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:63` |
| `SixthHurewicz.cubeCycle_val` | `Hopf/Recognition.lean:195-198` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:68` |
| `SixthHurewicz.cubeHomologyClass` | `Hopf/Recognition.lean:200-202` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:72` |
| `SixthHurewicz.cubeHomologyClass_homotopic` | `Hopf/Recognition.lean:204-207` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:76` |
| `SixthHurewicz.homotopyMap` | `Hopf/Recognition.lean:209-211` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:81` |
| `SixthHurewicz.hurewiczFunction` | `Hopf/Recognition.lean:213-215` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:85` |
| `SixthHurewicz.hurewiczPi6` | `Hopf/Recognition.lean:217-219` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:89` |
| `SixthHurewicz.hurewiczMap` | `Hopf/Recognition.lean:221-223` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:93` |
| `SixthHurewicz.hurewiczMap_representative` | `Hopf/Recognition.lean:225-230` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:97` |
| `SixthHurewicz.hurewiczInverse` | `Hopf/Recognition.lean:232-238` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:104` |
| `SixthHurewicz.hurewiczLinearEquiv` | `Hopf/Recognition.lean:240-246` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:112` |
| `SixthHurewicz.hurewiczPi6Equiv` | `Hopf/Recognition.lean:248-259` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:120` |
| `SixthHurewicz.cubeChain_natural` | `Hopf/Recognition.lean:261-264` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:133` |
| `SixthHurewicz.cubeCycle_natural` | `Hopf/Recognition.lean:266-271` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:138` |
| `SixthHurewicz.cubeHomologyClass_natural` | `Hopf/Recognition.lean:273-277` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:145` |
| `SixthHurewicz.hurewiczFunction_natural` | `Hopf/Recognition.lean:279-283` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:151` |
| `SixthHurewicz.hurewiczMap_natural` | `Hopf/Recognition.lean:285-289` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:157` |
| `SixthHurewicz.hurewiczLinearEquiv_natural` | `Hopf/Recognition.lean:291-300` | `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean:163` |
| `CoverOverlapHomology.homologyEquiv_symm_single` | `Hopf/Recognition.lean:5723-5733` | `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean:46` |
| `CoverOverlapHomology.homologyEquiv_inclusion` | `Hopf/Recognition.lean:5735-5743` | `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean:58` |
| `CoverOverlapHomology.componentMap` | `Hopf/Recognition.lean:5745-5749` | `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean:68` |
| `CoverOverlapHomology.overlapMap` | `Hopf/Recognition.lean:5751-5759` | `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean:74` |
| `CoverOverlapHomology.overlapMap_component` | `Hopf/Recognition.lean:5761-5766` | `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean:84` |
| `CoverOverlapHomology.homologyEquiv_map` | `Hopf/Recognition.lean:5768-5784` | `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean:91` |
| `CoverLocalContributions.componentConnecting_enlarge` | `Hopf/Recognition.lean:5786-5837` | `Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean:109` |

## Blocked (92)

The blocking constant is the first one found (a stock declaration still under `Hopf/`; its file is given).

| declaration | source `304a0fea` | blocked by |
|---|---|---|
| `cylinderQuotient_isQuotientMap` | `Hopf/Recognition.lean:422-423` | `SixSphereCube.StandardSphere` (`Hopf/Hurewicz.lean`) |
| `MorseCancellation.nativeMorseCount_eq_interval_length` | `Hopf/Recognition.lean:517-551` | `ManifoldMorse.SurgeryWindows.count` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.native_middle_block_counts` | `Hopf/Recognition.lean:553-597` | `ManifoldMorse.SurgeryWindows.HasIndexTwoPrefix` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.attaching_sphere_reaches_of_compact_basin_section` | `Hopf/Recognition.lean:599-677` | `AdaptedWindows.exists_native_level_basin_transport` (`Hopf/SingularHomology.lean`) |
| `MorseCancellation.nativeIndexThreeAttachingSphere_regular` | `Hopf/Recognition.lean:679-709` | `MorseCancellation.nativeIndexThreeAttachingSphere._proof_5` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_canonical_basin_sphere` | `Hopf/Recognition.lean:711-753` | `AdaptedWindows.transported_attaching_range_iff` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_canonical_middle_family` | `Hopf/Recognition.lean:755-780` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass_parametrized` | `Hopf/Recognition.lean:852-863` | `ManifoldMorse.MorseSurgeryData.coreBoundaryMap` (`Hopf/SingularHomology.lean`) |
| `AdaptedWindows.native_attaching_class_of_flow_section` | `Hopf/Recognition.lean:875-908` | `MorseCancellation.nativeIndexThreeAttachingSphere` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_native_core_inclusion_equiv` | `Hopf/Recognition.lean:910-932` | `ManifoldMorse.MorseSurgeryData.coreMap` (`Hopf/SingularHomology.lean`) |
| `AdaptedWindows.exists_core_inclusion_homology_comparison` | `Hopf/Recognition.lean:934-976` | `ManifoldMorse.MorseSurgeryData.coreCellPresentation` (`Hopf/SingularHomology.lean`) |
| `AdaptedWindows.native_sublevel_inclusion_exact` | `Hopf/Recognition.lean:978-1007` | `ManifoldMorse.MorseSurgeryData.coreCellPresentation` (`Hopf/SingularHomology.lean`) |
| `AdaptedWindows.native_index_three_inclusion_relation` | `Hopf/Recognition.lean:1009-1046` | `ManifoldMorse.MorseSurgeryData.coreCellPresentation` (`Hopf/SingularHomology.lean`) |
| `AdaptedWindows.middle_inclusion_step` | `Hopf/Recognition.lean:1075-1135` | `MorseCancellation.nativeIndexThreeAttachingSphere` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.finite_middle_inclusion_relations` | `Hopf/Recognition.lean:1149-1241` | `MorseCancellation.nativeIndexThreeAttachingSphere` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.nativeMiddleBaseCut` | `Hopf/Recognition.lean:1243-1246` | `ManifoldMorse.SurgeryWindows.count` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.nativeMiddleCutSequence` | `Hopf/Recognition.lean:1248-1253` | `ManifoldMorse.SurgeryWindows.count` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.nativeMiddleCutSequence_bands` | `Hopf/Recognition.lean:1255-1307` | `MorseCancellation.nativeMiddleBlockPoint._proof_2` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.ordered_middle_inclusion_relations` | `Hopf/Recognition.lean:1309-1336` | `MorseCancellation.nativeIndexThreeAttachingSphere` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.no_connection_above_canonical_cut` | `Hopf/Recognition.lean:1346-1389` | `MorseCancellation.nativeIndexThreeAttachingSphere` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.lower_cuts_preserved_of_critical_bound` | `Hopf/Recognition.lean:1391-1416` | `MorseCancellation.superlevel_bound_of_critical_bound` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_common_cut_value_exchange` | `Hopf/Recognition.lean:1418-1524` | `MorseCancellation.injOn_of_exchanged_values` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.nativeMiddleBasinFamily_equalCut` | `Hopf/Recognition.lean:1584-1634` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_middle_family_value_exchange` | `Hopf/Recognition.lean:1682-1777` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.nativeMiddleBasinFamily_labels_injective` | `Hopf/Recognition.lean:1779-1794` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_first_middle_pivot` | `Hopf/Recognition.lean:1796-1958` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.backward_basin_reaches_compact_section` | `Hopf/Recognition.lean:1960-1985` | `AdaptedWindows.backward_basin_reaches_attaching_level` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_higher_middle_family` | `Hopf/Recognition.lean:2041-2074` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_relative_surgery_cut_transport` | `Hopf/Recognition.lean:2230-2372` | `MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_relative_family_lower_transport` | `Hopf/Recognition.lean:2374-2499` | `AdaptedWindows.reaches_old_lower_of_belt_avoidance` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.same_image_sphere_maps_unit` | `Hopf/Recognition.lean:2555-2597` | `MorseCancellation.two_sphere_map_unit_of_homology_bijective` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.same_image_section_classes_unit` | `Hopf/Recognition.lean:2599-2612` | `MorseCancellation.same_image_sphere_maps_unit->MorseCancellation.two_sphere_map_unit_of_homology_bijective` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.nativeMiddleBasinFamily_replace_zero` | `Hopf/Recognition.lean:2614-2656` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.exists_radial_link_meridian_with_derivative` | `Hopf/Recognition.lean:2990-3095` | `MorseCancellation.radialParameterChart_link` (`Hopf/SingularHomology.lean`) |
| `AdaptedWindows.exists_passage_derivative_class_addition` | `Hopf/Recognition.lean:3097-3187` | `MorseCancellation.nativeBeltTubeMeridian_eq` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.attaching_contributions_opposite_of_relative_det_neg` | `Hopf/Recognition.lean:3189-3212` | `LinearSphereAction.homology_relative_sign` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.exists_centered_passage_normal_factors` | `Hopf/Recognition.lean:3530-3651` | `MorseCancellation.radialParameterChart_zero` (`Hopf/SingularHomology.lean`) |
| `MorseCancellation.opposite_centered_passages_of_normal_factors` | `Hopf/Recognition.lean:3653-3715` | `MorseCancellation.radialParameterChart` (`Hopf/SingularHomology.lean`) |
| `MorseCancellation.exists_native_opposite_centered_passages` | `Hopf/Recognition.lean:3717-3768` | `ManifoldMorse.MorseSurgeryData.surjective_beltNormal_derivative` (`Hopf/SingularHomology.lean`) |
| `MorseCancellation.choose_prescribed_normal_passage` | `Hopf/Recognition.lean:3770-3832` | `MorseCancellation.two_sphere_map_unit_of_homology_bijective` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.exists_native_prescribed_centered_passage` | `Hopf/Recognition.lean:3834-3880` | `MorseCancellation.radialParameterChart` (`Hopf/SingularHomology.lean`) |
| `MorseCancellation.exists_native_prescribed_finite_family_passage` | `Hopf/Recognition.lean:3882-3940` | `MorseRearrangement.otherSheetImages` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_higher_family_prescribed_passage` | `Hopf/Recognition.lean:3942-4032` | `MorseRearrangement.otherSheetImages` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.prescribed_passage_actual_endpoint_classes` | `Hopf/Recognition.lean:4034-4144` | `MorseCancellation.nativeIndexThreeAttachingSphere` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_prescribed_family_slide` | `Hopf/Recognition.lean:4146-4285` | `MorseRearrangement.otherSheetImages` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_common_cut_prescribed_slide` | `Hopf/Recognition.lean:4287-4419` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_common_cut_prescribed_family_slide` | `Hopf/Recognition.lean:4421-4488` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_repeatable_column_slide` | `Hopf/Recognition.lean:4531-4592` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_iterated_column_slide` | `Hopf/Recognition.lean:4594-4680` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_integer_column_slide` | `Hopf/Recognition.lean:4682-4738` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.nativeMiddleBasinFamily_reindex` | `Hopf/Recognition.lean:4740-4753` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_labelled_integer_slide` | `Hopf/Recognition.lean:4833-4978` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_arbitrary_column_addition` | `Hopf/Recognition.lean:4980-5106` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_arbitrary_column_sequence` | `Hopf/Recognition.lean:5149-5312` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_primitive_functional_unit` | `Hopf/Recognition.lean:5314-5461` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.exists_lower_cut_geometric_matrix` | `Hopf/Recognition.lean:5473-5521` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.native_middle_block_complete_and_cut` | `Hopf/Recognition.lean:5523-5593` | `ManifoldMorse.SurgeryWindows.HasIndexTwoPrefix` (`Hopf/SphereTopology.lean`) |
| `SpherePoint.sourceCountMark_topClass_natAbs` | `Hopf/Recognition.lean:5595-5600` | `SpherePoint.sourceCountMark` (`Hopf/SphereTopology.lean`) |
| `OnePointCover.overlapHomologyEquiv_symm_include` | `Hopf/Recognition.lean:5602-5618` | `OnePointCover.finitePatch` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapseComponentConnecting` | `Hopf/Recognition.lean:5620-5632` | `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints` (`Hopf/SingularHomology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapseLocalClass` | `Hopf/Recognition.lean:5634-5644` | `ManifoldMorse.MorseSurgeryData.beltIntersectionPoints` (`Hopf/SingularHomology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapseConnecting_sum_overlaps` | `Hopf/Recognition.lean:5646-5665` | `LocalDegree.SeparatedNeighborhoods.open_cover` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapseConnecting_sum_boundaries` | `Hopf/Recognition.lean:5667-5694` | `OnePointCover.finitePatch` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapseSphereConnecting_sum` | `Hopf/Recognition.lean:5696-5721` | `OnePointCover.finitePatch` (`Hopf/SphereTopology.lean`) |
| `LocalDegree.SeparatedNeighborhoods.pointComplementInclusion` | `Hopf/Recognition.lean:5839-5844` | `LocalDegree.SeparatedNeighborhoods` (`Hopf/SphereTopology.lean`) |
| `LocalDegree.SeparatedNeighborhoods.pointComplementInclusion_sphereEquiv` | `Hopf/Recognition.lean:5846-5854` | `LocalDegree.SeparatedNeighborhoods` (`Hopf/SphereTopology.lean`) |
| `LocalDegree.SeparatedNeighborhoods.componentConnecting_singlePoint` | `Hopf/Recognition.lean:5856-5875` | `LocalDegree.SeparatedNeighborhoods.open_cover` (`Hopf/SphereTopology.lean`) |
| `LocalDegree.SeparatedNeighborhoods.sphereConnecting_component` | `Hopf/Recognition.lean:5877-5923` | `LocalDegree.SeparatedNeighborhoods.open_cover` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapseLocalClass_singlePoint` | `Hopf/Recognition.lean:5925-5935` | `LocalDegree.NativeNeighborhood.sphereConnecting` (`Hopf/SphereTopology.lean`) |
| `SphereNormalCoordinates.localBoundary_homology_outward` | `Hopf/Recognition.lean:5937-5965` | `SphereNormalCoordinates.normalJacobian` (`Hopf/SingularHomology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapseLocalBoundary_homology_sign_of_transverse` | `Hopf/Recognition.lean:5967-6021` | `ManifoldMorse.MorseSurgeryData.beltIntersectionSign` (`Hopf/SingularHomology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapseLocalClass_eq_outward` | `Hopf/Recognition.lean:6027-6045` | `SpherePoint.outwardClass` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapseLocalBoundary_outward` | `Hopf/Recognition.lean:6047-6079` | `SpherePoint.outwardClass` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.beltIntersectionCount_smul` | `Hopf/Recognition.lean:6081-6096` | `ManifoldMorse.MorseSurgeryData.beltIntersectionSign` (`Hopf/SingularHomology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapseSphereConnecting_signed_count` | `Hopf/Recognition.lean:6098-6133` | `SpherePoint.outwardClass` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.collapse_homology_signed_count` | `Hopf/Recognition.lean:6135-6166` | `SpherePoint.outwardClass` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_signed_count` | `Hopf/Recognition.lean:6168-6199` | `SpherePoint.countMark_of_connecting` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_topClass_natAbs` | `Hopf/Recognition.lean:6201-6223` | `ManifoldMorse.MorseSurgeryData.upperLevelInclusion` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_transverse_natAbs` | `Hopf/Recognition.lean:6225-6242` | `ManifoldMorse.MorseSurgeryData.finite_points_of_isTransverseBeltSphere` (`Hopf/SingularHomology.lean`) |
| `MorseCancellation.last_index_two_collapse_is_primitive` | `Hopf/Recognition.lean:6244-6277` | `ManifoldMorse.SurgeryWindows.HasIndexTwoPrefix` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.exists_native_belt_cut_family` | `Hopf/Recognition.lean:6279-6357` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.exists_transverse_representative` | `Hopf/Recognition.lean:6379-6417` | `ManifoldMorse.MorseSurgeryData.IsTransverseBeltSphere` (`Hopf/SingularHomology.lean`) |
| `MorseCancellation.exists_single_intersection_of_unit_coordinate` | `Hopf/Recognition.lean:6419-6470` | `ManifoldMorse.MorseSurgeryData.exists_single_belt_intersection_of_unit_count` (`Hopf/SphereTopology.lean`) |
| `AdaptedWindows.cancel_single_basin_section_isotopy` | `Hopf/Recognition.lean:6472-6590` | `MorseCancellation.surgery_pair_inner_band_regular` (`Hopf/DifferentialTopology.lean`) |
| `MorseCancellation.cancel_from_preserved_unit_belt_cut` | `Hopf/Recognition.lean:6629-6738` | `ManifoldMorse.MorseSurgeryData.IsTransverseBeltSphere` (`Hopf/SingularHomology.lean`) |
| `MorseCancellation.cancel_from_complete_middle_family` | `Hopf/Recognition.lean:6782-6904` | `MorseCancellation.IsNativeMiddleBasinFamily` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.coreBoundary_two_injective_of_upper` | `Hopf/Recognition.lean:6907-6919` | `ManifoldMorse.MorseSurgeryData.morseConnectingMap` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.indexThreeAttaching_zsmul_eq_zero` | `Hopf/Recognition.lean:6921-6935` | `ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.MorseSurgeryData.indexThreePresentation_matrix_injective` | `Hopf/Recognition.lean:6937-6949` | `ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_surjective` (`Hopf/SphereTopology.lean`) |
| `ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_upper_third` | `Hopf/Recognition.lean:6951-6988` | `ManifoldMorse.SurgeryWindows.HasIndexTwoPrefix` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.middle_blocks_complete_of_no_four_five` | `Hopf/Recognition.lean:7009-7049` | `ManifoldMorse.SurgeryWindows.HasIndexTwoPrefix` (`Hopf/SphereTopology.lean`) |
| `MorseCancellation.critical_pair_of_surgery_count_two` | `Hopf/Recognition.lean:7052-7082` | `ManifoldMorse.SurgeryWindows.count` (`Hopf/SphereTopology.lean`) |

## Charged (34, stay)

`SixSphereCube.*` (21) and the thirteen rows `cylinderQuotient` … `Sphere.homotopic_id_of_topClass`
(`Hopf/Recognition.lean:303-514`), all mentioning `SixSphereCube` objects.


## Free by the dump but not moved in this pass (59)

No use of a stock constant outside `Hopf/Recognition.lean`; not moved for lack of time in this pass
(each needs the textual retarget check of shim-qualified names before a build). Candidates for the next
unit, in file order:

- `MorseCancellation.levelSublevelMap` (`Hopf/Recognition.lean:782-784`)
- `AdaptedWindows.level_transport_homotopic_in_sublevel` (`Hopf/Recognition.lean:786-850`)
- `MorseCancellation.sublevelMap` (`Hopf/Recognition.lean:865-867`)
- `MorseCancellation.middleSectionClass` (`Hopf/Recognition.lean:869-873`)
- `MorseCancellation.sublevelMap_trans` (`Hopf/Recognition.lean:1048-1051`)
- `MorseCancellation.sublevelHomologyMap_comp` (`Hopf/Recognition.lean:1053-1058`)
- `MorseCancellation.regular_sublevel_inclusion_bijective` (`Hopf/Recognition.lean:1060-1073`)
- `MorseCancellation.span_prefix_succ` (`Hopf/Recognition.lean:1137-1147`)
- `MorseCancellation.canonicalMiddleMatrix` (`Hopf/Recognition.lean:1339-1343`)
- `MorseCancellation.equalCutSection` (`Hopf/Recognition.lean:1526-1530`)
- `MorseCancellation.equalCutSublevelHomeomorph` (`Hopf/Recognition.lean:1532-1540`)
- `MorseCancellation.equalCutHomologyEquiv` (`Hopf/Recognition.lean:1542-1547`)
- `MorseCancellation.equalCutSection_class` (`Hopf/Recognition.lean:1549-1567`)
- `MorseCancellation.canonicalMiddleMatrix_equalCut` (`Hopf/Recognition.lean:1569-1582`)
- `MorseCancellation.native_index_order_of_equal_index_exchange` (`Hopf/Recognition.lean:1636-1680`)
- `AdaptedWindows.backward_basin_reaches_intermediate_cut` (`Hopf/Recognition.lean:1987-2003`)
- `AdaptedWindows.transported_basin_image_of_reaching` (`Hopf/Recognition.lean:2005-2039`)
- `AdaptedWindows.upper_point_not_on_belt_of_lower_orbit` (`Hopf/Recognition.lean:2076-2095`)
- `MorseCancellation.lower_backward_basins_preserved` (`Hopf/Recognition.lean:2097-2167`)
- `MorseCancellation.lower_forward_basins_preserved` (`Hopf/Recognition.lean:2169-2196`)
- `AdaptedWindows.reaches_cut_of_forward_holonomy` (`Hopf/Recognition.lean:2198-2228`)
- `AdaptedWindows.section_class_of_flow_transport` (`Hopf/Recognition.lean:2501-2523`)
- `MorseCancellation.signed_relation_of_regular_cut_transport` (`Hopf/Recognition.lean:2525-2553`)
- `MorseCancellation.exists_sheet_arc_tube_with_normal_change` (`Hopf/Recognition.lean:2658-2706`)
- `MorseCancellation.exists_clean_sheet_arc_tube_with_normal_change` (`Hopf/Recognition.lean:2708-2799`)
- `MorseCancellation.exists_relative_sheet_passages_with_normal_change` (`Hopf/Recognition.lean:2801-2908`)
- `MorseCancellation.LongitudinalTubeMotion.sheet_trace_germ_of_endpoint_germs` (`Hopf/Recognition.lean:2910-2969`)
- `MorseCancellation.exists_centered_passage_clock` (`Hopf/Recognition.lean:2971-2988`)
- `MorseCancellation.passageNormalProduct` (`Hopf/Recognition.lean:3214-3216`)
- `MorseCancellation.passageNormalProduct_det` (`Hopf/Recognition.lean:3218-3227`)
- `MorseCancellation.relative_normal_frame_det` (`Hopf/Recognition.lean:3229-3249`)
- `MorseCancellation.passage_normal_relative_det_neg` (`Hopf/Recognition.lean:3251-3262`)
- `MorseCancellation.mfderiv_normal_trace_model` (`Hopf/Recognition.lean:3264-3288`)
- `MorseCancellation.LongitudinalTubeMotion.normal_trace_mfderiv` (`Hopf/Recognition.lean:3290-3339`)
- `MorseCancellation.mfderiv_retime_unit_rate` (`Hopf/Recognition.lean:3341-3372`)
- `MorseCancellation.fderiv_retimed_trace_parameter` (`Hopf/Recognition.lean:3374-3401`)
- `MorseCancellation.exists_shared_passage_frames` (`Hopf/Recognition.lean:3403-3434`)
- `MorseCancellation.CenteredSheetPassage` (`Hopf/Recognition.lean:3436-3448`)
- `MorseCancellation.LongitudinalTubeMotion.centeredSheetPassage` (`Hopf/Recognition.lean:3450-3478`)
- `MorseCancellation.bijective_trace_normal_of_native_transverse` (`Hopf/Recognition.lean:3480-3504`)
- `MorseCancellation.hasFDerivAt_terminal_normal_factor` (`Hopf/Recognition.lean:3506-3528`)
- `MorseCancellation.regular_below_pivot_of_regular_lower_band` (`Hopf/Recognition.lean:4490-4501`)
- `MorseCancellation.lower_window_le_of_radius_le` (`Hopf/Recognition.lean:4503-4509`)
- `MorseCancellation.common_cut_band_of_smaller_radius` (`Hopf/Recognition.lean:4511-4523`)
- `MorseCancellation.higher_window_separation_of_value_order` (`Hopf/Recognition.lean:4525-4529`)
- `MorseCancellation.canonicalMiddleMatrix_single_class_addition` (`Hopf/Recognition.lean:4755-4772`)
- `MorseCancellation.SurgeryWindows.regular_before_first_middle_pivot` (`Hopf/Recognition.lean:4774-4805`)
- `MorseCancellation.low_index_cut_of_preserved_other_values` (`Hopf/Recognition.lean:4807-4831`)
- `MorseCancellation.equalCutSection_trans` (`Hopf/Recognition.lean:5108-5113`)
- `MorseCancellation.equalCutHomologyEquiv_refl` (`Hopf/Recognition.lean:5115-5131`)
- `MorseCancellation.equalCutHomologyEquiv_trans` (`Hopf/Recognition.lean:5133-5147`)
- `MorseCancellation.regularCutHomologyEquiv` (`Hopf/Recognition.lean:5463-5471`)
- `ManifoldMorse.MorseSurgeryData.instLocal1` (`Hopf/Recognition.lean:6023-6025`)
- `SupportedDiffeomorph.IsotopicToIdentity.homotopic` (`Hopf/Recognition.lean:6359-6370`)
- `SupportedDiffeomorph.IsotopicToIdentity.comp_homotopic` (`Hopf/Recognition.lean:6372-6377`)
- `MorseCancellation.conjugate_level_isotopy` (`Hopf/Recognition.lean:6592-6613`)
- `MorseCancellation.intersection_count_under_injective_map` (`Hopf/Recognition.lean:6615-6627`)
- `MorseCancellation.consecutive_last_two_first_three` (`Hopf/Recognition.lean:6740-6780`)
- `MorseCancellation.native_index_excluded_of_count_zero` (`Hopf/Recognition.lean:6991-7007`)

## Build (unit 1)

```
start Mon Sep 14 00:54:17 CEST 2026
✔ [8816/8819] Built Lib.AlgebraicTopology.Hurewicz.DegreeSix (6.0s)
✔ [8817/8819] Built Lib.AlgebraicTopology.SingularHomology.LocalContributionsNaturality (6.3s)
✔ [8818/8819] Built Lib (6.5s)
Build completed successfully (8819 jobs).
✔ [8854/8858] Built Hopf.Recognition (106s)
✔ [8855/8858] Built Hopf.Proof.Recognition (18s)
✔ [8856/8858] Built Hopf.Proof.Final (11s)
ℹ [8857/8858] Built Solution (7.7s)
info: Solution.lean:61:0: 'Mathoverflow1973.mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8858 jobs).
exit 0 Mon Sep 14 00:57:06 CEST 2026
```

`python3 scripts/lib_stock_census.py --check`: `ratchet PASS: 1558 <= baseline 1648`
(`Hopf/Recognition.lean` 213 -> 185).

