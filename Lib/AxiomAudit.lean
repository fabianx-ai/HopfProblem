import Lib

/-!
# Per-export axiom audit for the reusable library

Compile this file directly. It deliberately is not imported by `Lib.lean`, because `#print axioms`
is an evidence command rather than library content.
-/

#print axioms Module.End.cyclicAverage
#print axioms Module.End.mul_sum_powers_eq_sum_powers
#print axioms Module.End.sum_powers_mul_eq_sum_powers
#print axioms Module.End.mul_cyclicAverage
#print axioms Module.End.cyclicAverage_mul
#print axioms Module.End.cyclicAverage_apply_of_fixed
#print axioms Module.End.isProj_cyclicAverage
#print axioms Module.End.isIdempotentElem_cyclicAverage
#print axioms Module.End.range_cyclicAverage
#print axioms Module.End.comp_cyclicAverage

#print axioms exteriorPower.finBasis
#print axioms exteriorPower.finBasis_map_coefficient
#print axioms exteriorPower.finMatrix
#print axioms exteriorPower.toMatrix_map
#print axioms exteriorPower.finCoordinates
#print axioms exteriorPower.finCoordinates_apply
#print axioms exteriorPower.finCoordinates_map

#print axioms Matrix.natAbs_det_eq_natCard_quotient_range_toLin'
#print axioms Matrix.quotientRangeToLin'EquivZModOfIsCoprime
#print axioms Matrix.quotientRangeToLinEquivZModOfIsCoprime

#print axioms Module.End.oneAddSMul
#print axioms Module.End.oneAddSMul_zero
#print axioms Module.End.oneAddSMul_apply
#print axioms Module.End.oneAddSMul_mul_oneAddSMul
#print axioms Module.End.oneAddSMulEquiv
#print axioms Module.End.oneAddSMulEquiv_toLinearMap
#print axioms Module.End.oneAddSMulEquiv_apply
#print axioms Module.End.oneAddSMulEquiv_symm_toLinearMap
#print axioms Module.End.quadratic_term_eq_zero
#print axioms Module.End.oneAddSMul_preserves_bilin
#print axioms Module.End.oneAddSMul_preserves_bilin_of_isSkewAdjoint

#print axioms Abelianization.mapMulAut
#print axioms SemidirectProduct.abelianizationRepresentation
#print axioms SemidirectProduct.AbelianizationCoinvariants
#print axioms SemidirectProduct.coinvariantsMk
#print axioms SemidirectProduct.coinvariantsMk_action
#print axioms SemidirectProduct.abelianizationMulEquiv
#print axioms SemidirectProduct.abelianizationMulEquiv_apply_of_inl
#print axioms SemidirectProduct.abelianizationMulEquiv_apply_of_inr
#print axioms SemidirectProduct.abelianizationMulEquiv_symm_apply_inl
#print axioms SemidirectProduct.abelianizationMulEquiv_symm_apply_inr
#print axioms GroupExtension.Splitting.abelianizationMulEquiv

#print axioms Subgroup.isMulCommutative_of_closure_eq_top
#print axioms AddSubgroup.isAddCommutative_of_closure_eq_top
#print axioms AddSubgroup.eq_of_le_of_quotient_subsingleton
#print axioms AddSubgroup.eq_top_of_le_of_quotient_subsingleton

-- Lane A (singular homology core)
#print axioms SingularMayerVietoris.exact_at_ambient
#print axioms SphereHomology.unitSphere_homology_subsingleton
#print axioms LinearSphereAction.homology_eq_sign_smul

-- Lane D1 (Morse theory I)
#print axioms ManifoldMorse.exists_morse_function
#print axioms SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn
#print axioms ManifoldMorse.SignedMorseChart.exists_attachingUnionHomeomorph_with_level_and_orbits
#print axioms ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points

-- Lane H (complex analysis)
#print axioms RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero
#print axioms HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution
#print axioms AnalyticRootCover.exists_analytic_square_root
#print axioms AnalyticRootCover.exists_analytic_square_root_ball

-- Lane D2 (Whitney embedding, projection bundle, collar, cells)
#print axioms exists_tubularNeighborhood_in_open_of_embedded_closedBall

-- Lane I (quotients, mapping torus, split extensions)
#print axioms SplitGroupExtension.mulEquiv
#print axioms MappingTorusHomology.monodromyHomologyMap

-- Lane C (Hurewicz theorem, higher degrees and sphere connectivity)
#print axioms Hurewicz.hurewiczLinearEquiv
#print axioms Hurewicz.hurewiczLinearEquivOfTwoLE
#print axioms Hurewicz.pi_subsingleton_of_homology_vanishing
#print axioms Hurewicz.sphere_pi_subsingleton_of_lt
#print axioms Hurewicz.sphere_homotopicRel_of_topClass_eq
#print axioms Hurewicz.sphere_homotopic_id_of_topClass
#print axioms Hurewicz.right_inverse_is_left_inverse
#print axioms Hurewicz.exists_basepoint_adjustment
#print axioms Hurewicz.hurewiczLinearEquivOfTwoLE_natural
#print axioms Hurewicz.subsingleton_singularHomology_of_lt
#print axioms DiskCube.homeomorph
#print axioms DiskCube.boundary_iff

#print axioms MorseCancellation.cancel_of_transverse_level_isotopy
#print axioms MorseRearrangement.exists_morse_rearrangement_of_no_connection
#print axioms MorseCancellation.exists_excellent_indexed_morse_birth
#print axioms simplyConnectedSpace_of_open_cover
#print axioms MorseCells.built_of_compact_smooth_manifold
#print axioms AnalyticRootCover.exists_analytic_square_root_on_of_even_zeros
