"""Cut plan for wave 1 / morse-d: OrderedCancellation and SurgeryCollapse.

PIECES: ordered list of (module name, class, source module, declaration short names, module docstring).
class 'lib'  -> Lib/<path>.lean            (stays in Lib, gets docstrings)
class 'hopf' -> Hopf/Proof/<path>.lean     (project material)
Names are the user-facing names as written in the source; a private name is matched by suffix.
"""

OC = 'Lib.Geometry.Manifold.Morse.OrderedCancellation'
SC = 'Lib.Geometry.Manifold.Morse.SurgeryCollapse'

PIECES = [
# ---------------------------------------------------------------- OrderedCancellation
('Lib.Geometry.Manifold.Morse.OrderedCancellation.TwoSphereDegree', 'lib', OC, [
  'IntLinearAutomorphism.apply_eq_mul',
  'IntLinearAutomorphism.apply_one_eq_one_or_neg_one',
  'MorseCancellation.two_sphere_map_unit_of_homology_bijective',
], """/-!
# Self-maps of the two-sphere with bijective `H₂` act by a unit

An automorphism of `ℤ` as a `ℤ`-module is multiplication by `1` or by `-1`
(`IntLinearAutomorphism.apply_one_eq_one_or_neg_one`).  Consequently, if `g : S² → Y` induces a
bijection on `H₂` and `Y` is homeomorphic to `S²` via `e`, then `H₂(g) = ±H₂(e)`
(`MorseCancellation.two_sphere_map_unit_of_homology_bijective`): the degree of a homology
isomorphism of `S²` is a unit, cf. Hatcher, *Algebraic Topology*, §2.2 (degree).
-/"""),

('Lib.Geometry.Manifold.Morse.OrderedCancellation.BeltTube', 'lib', OC, [
  'MorseCancellation.nativeBeltTubeSource',
  'MorseCancellation.nativeBeltTubeInComplement',
  'MorseCancellation.nativeBeltTubeMeridian',
  'MorseCancellation.parameterBallBoundary',
  'MorseCancellation.parameterBallCenter',
  'MorseCancellation.parameterBallContraction',
  'MorseCancellation.parameterBall_boundary_nullhomotopic',
  'MorseCancellation.normalized_pos_smul',
  'MorseCancellation.beltBallCoordinates',
  'MorseCancellation.beltBallCoordinates_normal',
  'MorseCancellation.beltBallBoundaryNormal',
  'MorseCancellation.beltBallBoundaryInComplement',
  'MorseCancellation.beltBallBoundaryInComplement_coe',
  'MorseCancellation.beltBallBoundary_normalized_coe',
  'MorseCancellation.exists_small_native_belt_neighborhood',
], """/-!
# The tubular neighbourhood of a belt sphere and its meridians

For a Morse surgery datum `d` at a critical point of index `λ` in an `n`-manifold the belt
sphere `S^{n-λ-1}` in the upper level has a tubular neighbourhood parametrised by
`S^{n-λ-1} × (punctured λ-ball)` (`MorseCancellation.nativeBeltTubeSource`,
`nativeBeltTubeInComplement`); the *meridian* through a point `v` of the belt sphere is the
`(λ-1)`-sphere of radius `r` in the normal ball (`nativeBeltTubeMeridian`).  A map of a small
parameter ball into the belt neighbourhood is described by its `(v, normal)` coordinates
(`beltBallCoordinates`), and the restriction to the boundary of the parameter ball is
null-homotopic (`parameterBall_boundary_nullhomotopic`).  This is the local structure of the
belt sphere used in the cancellation theorem, cf. Milnor, *Lectures on the h-cobordism theorem*,
§5.
-/"""),

('Lib.Geometry.Manifold.Morse.OrderedCancellation.PrescribedFlow', 'lib', OC, [
  'MorseCancellation.exists_morseSurgeryData_of_field_germ_lt',
  'MorseCancellation.exists_adapted_windows_with_prescribed_flow',
  'MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt',
  'MorseCancellation.exists_signed_morse_chart_of_germ_preserving_field',
  'MorseCancellation.exists_signed_morse_chart_of_shift_germ_preserving_field',
], """/-!
# Adapted windows with a prescribed gradient-like flow

A gradient-like vector field `V` for a Morse function `f` on a compact manifold which agrees near
every critical point with the descent field of a signed Morse chart determines an
`AdaptedWindows E f` package whose field and flow are `V` and its flow
(`MorseCancellation.exists_adapted_windows_with_prescribed_flow`), with surgery radii below any
prescribed bound (`exists_adapted_windows_with_prescribed_flow_lt`).  The construction is local:
`exists_morseSurgeryData_of_field_germ_lt` builds the surgery datum at one critical point.
A signed Morse chart survives replacing `f` by a function with the same germ, or the germ
shifted by a constant (`exists_signed_morse_chart_of_germ_preserving_field`,
`exists_signed_morse_chart_of_shift_germ_preserving_field`).
Cf. Milnor, *Lectures on the h-cobordism theorem*, §3 (gradient-like vector fields).
-/"""),

('Lib.Geometry.Manifold.Morse.OrderedCancellation.CircleParametrization', 'lib', OC, [
  'MorseCancellation.standardCircleParametrization',
  'MorseCancellation.contMDiff_comp_standardCircle',
  'MorseCancellation.injective_comp_standardCircle',
  'MorseCancellation.injective_derivative_comp_standardCircle',
], """/-!
# The standard diffeomorphism `S¹ ≃ Circle`

`MorseCancellation.standardCircleParametrization` is the smooth diffeomorphism from the unit
sphere `Hemisphere.Sphere 1` of `ℝ²` to Mathlib's `Circle ⊆ ℂ`; precomposition with it preserves
smoothness, injectivity and injectivity of the differential of a curve `Circle → N`.
-/"""),

('Lib.Geometry.Manifold.Morse.OrderedCancellation.ValueExchange', 'lib', OC, [
  'MorseCancellation.injOn_of_exchanged_values',
  'MorseCancellation.nativeMorseCount_eq_of_preserved_indices',
  'MorseCancellation.adapted_surgery_system_after_value_exchange',
  'MorseCancellation.exists_flow_preserving_value_exchange',
  'MorseCancellation.exists_flow_preserving_consecutive_pair',
  'MorseCancellation.nativeIndexDisorder',
  'MorseCancellation.nativeIndexDisorder_eq_of_finite',
  'MorseCancellation.nativeIndexDisorder_transport',
  'MorseCancellation.nativeIndexDisorder_exchange_lt',
], """/-!
# Exchanging the critical values of two consecutive critical points

The rearrangement step of Milnor, *Lectures on the h-cobordism theorem*, Theorem 4.1: if two
critical points `p < q` of a Morse function are consecutive in value and no flow line of a
gradient-like field runs from `q` down to `p`, the critical values can be exchanged by a new Morse
function with the same critical points, the same indices and the same gradient-like field
(`MorseCancellation.exists_flow_preserving_value_exchange`).  Iterating the exchange makes any
two given critical points consecutive while keeping the flow
(`exists_flow_preserving_consecutive_pair`).  The measure that decreases along the iteration is
the *index disorder* `MorseCancellation.nativeIndexDisorder` (the number of value-ordered pairs
with inverted indices), cf. `Lib.Combinatorics.IndexDisorder`.
-/"""),

('Lib.Geometry.Manifold.Morse.OrderedCancellation.PairCancellation', 'lib', OC, [
  'MorseCancellation.isOpen_forward_basin_of_native_index_zero',
  'MorseCancellation.cancel_unique_zero_one_connection',
  'MorseCancellation.exists_transverse_sheet_of_circle_placement',
  'MorseCancellation.exists_embedded_avoidance_into_level_basin',
  'MorseCancellation.isotopicToIdentity_conj',
  'MorseCancellation.unit_level_count_of_circle_placement',
  'MorseCancellation.no_other_connections_of_two_level_endpoints',
  'MorseCancellation.cancel_transverse_pair_after_flow_preserving_descent',
], """/-!
# Cancelling a pair of critical points joined by a single flow line

The first cancellation theorem (Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4):
two critical points `p`, `q` of consecutive indices `λ`, `λ + 1` joined by exactly one
trajectory of a gradient-like field, transverse along that trajectory, can be removed together,
by a Morse function which agrees with the old one outside a band around the two critical values
(`MorseCancellation.cancel_transverse_pair_after_flow_preserving_descent`, and the index `0`/`1`
case `cancel_unique_zero_one_connection`, where transversality is automatic because the forward
basin of a minimum is open, `isOpen_forward_basin_of_native_index_zero`).  The auxiliary
statements count connections through a regular level (`unit_level_count_of_circle_placement`,
`no_other_connections_of_two_level_endpoints`), transport transverse sheets and isotopies through
a diffeomorphism (`exists_transverse_sheet_of_circle_placement`, `isotopicToIdentity_conj`), and
push a compact family off the critical set into the basin of a level
(`exists_embedded_avoidance_into_level_basin`).
-/"""),

('Lib.Geometry.Manifold.Morse.OrderedCancellation.PathComponents', 'lib', OC, [
  'MorseCancellation.componentChainWeight',
  'MorseCancellation.componentChainWeight_point',
  'MorseCancellation.componentChainWeight_boundary',
  'MorseCancellation.pointClass_eq_iff_joined',
  'MorseCancellation.joined_iff_of_homologyZero_injective',
  'MorseCancellation.pathConnectedSpace_of_homologyZero_injective',
  'MorseCancellation.pathConnectedSpace_of_homotopyEquiv',
  'MorseCancellation.cell_old_empty_of_empty_boundary',
  'MorseCancellation.zeroChainCycle',
  'MorseCancellation.zeroChainClass',
  'MorseCancellation.zeroChainClass_surjective',
  'MorseCancellation.homologyZero_linearMap_ext',
], """/-!
# `H₀` detects path components

Two points of a space `X` have the same class in `H₀(X; ℤ)` if and only if they are joined by a
path (`MorseCancellation.pointClass_eq_iff_joined`; Hatcher, *Algebraic Topology*,
Proposition 2.7).  The proof evaluates the *component weight* `componentChainWeight x`, the
linear functional on `0`-chains counting the simplices in the component of `x`, which vanishes on
boundaries.  Consequences: a map injective on `H₀` reflects path-connectedness
(`pathConnectedSpace_of_homologyZero_injective`), a homotopy equivalence preserves it
(`pathConnectedSpace_of_homotopyEquiv`), a linear map out of `H₀` is determined by its values on
point classes (`homologyZero_linearMap_ext`), and a cell attached along an empty sphere to a
preconnected space leaves nothing of the old part (`cell_old_empty_of_empty_boundary`).
-/"""),

('Lib.Geometry.Manifold.Morse.OrderedCancellation.Negation', 'lib', OC, [
  'MorseCancellation.isMorseAt_neg',
  'MorseCancellation.isMorse_neg',
  'MorseCancellation.negative_finrank_neg_chart',
  'MorseCancellation.nativeMorseIndex_neg_add',
  'MorseCancellation.nativeMorseCount_neg',
  'MorseCancellation.distinct_critical_values_neg',
], """/-!
# The Morse function `-f`

`-f` is Morse when `f` is (`MorseCancellation.isMorse_neg`), with the same critical points,
distinct critical values when `f` has them (`distinct_critical_values_neg`), and index
`n - index_f p` at each critical point (`nativeMorseIndex_neg_add`); hence the number of critical
points of `-f` of index `n - k` equals the number of critical points of `f` of index `k`
(`nativeMorseCount_neg`).  Cf. Milnor, *Morse Theory*, §2.
-/"""),

('Lib.Geometry.Manifold.Morse.OrderedCancellation.MinimalSystem', 'lib', OC, [
  'MorseCancellation.exists_minimal_excellent_morse_system',
  'MorseCancellation.minimal_excellent_morse_forbids_pair_removal',
  'MorseCancellation.minimal_excellent_morse_neg',
], """/-!
# Morse functions with the least number of critical points

On a compact manifold there is a Morse function with distinct critical values (an *excellent*
Morse function) and the least number of critical points among all such, together with an
`AdaptedWindows` package for it (`MorseCancellation.exists_minimal_excellent_morse_system`).
Minimality is preserved by `f ↦ -f` (`minimal_excellent_morse_neg`) and forbids the removal of a
pair of critical points (`minimal_excellent_morse_forbids_pair_removal`).  This is the starting
point of Smale's minimal Morse function programme, cf. Milnor, *Lectures on the h-cobordism
theorem*, §8.
-/"""),

('Lib.Geometry.Manifold.Morse.OrderedCancellation.IndexCounts', 'lib', OC, [
  'MorseCancellation.unitSphere_isEmpty_of_finrank_zero',
  'MorseCancellation.ordered_upper_pathConnected_of_later_transfers',
  'MorseCancellation.native_index_zero_point_unique',
  'MorseCancellation.native_index_one_excluded',
  'MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one',
  'MorseCancellation.indexed_criticalPoints_removed_of_index_eq',
  'MorseCancellation.nativeMorseCount_removed_of_index_eq',
  'MorseCancellation.nativeMorseCount_adjacent_removed_of_index_eq',
  'MorseCancellation.native_indices_monotone',
], """/-!
# Counting critical points by index

Bookkeeping for the numbers `nativeMorseCount E f k` of critical points of index `k`: removing a
pair of critical points of indices `k`, `k + 1` lowers the two counts by one and keeps the others
(`MorseCancellation.nativeMorseCount_adjacent_removed_of_index_eq`); when exactly one critical
point has index `0` it is the first window of a surgery system
(`native_index_zero_point_unique`); when index `1` does not occur no critical point has it
(`native_index_one_excluded`); indices along the value-ordered windows are monotone when the
function is index-ordered (`native_indices_monotone`); and the sublevel set below a window is
path-connected when all later windows transfer path-connectedness downward
(`ordered_upper_pathConnected_of_later_transfers`).  The attaching sphere of an index-`0` handle
is empty and that of an index-`1` handle has two points
(`unitSphere_isEmpty_of_finrank_zero`, `exists_distinct_unitSphere_points_of_finrank_one`).
-/"""),

('Lib.Geometry.Manifold.Morse.OrderedCancellation.BirthPreservation', 'lib', OC, [
  'MorseCancellation.superlevel_bound_of_critical_bound',
  'MorseCancellation.birth_preserves_lower_levels',
  'MorseCancellation.equalLevelDiffeomorph',
  'MorseCancellation.regular_level_of_retained_critical_germs',
  'MorseCancellation.birth_preserves_lower_index_bound',
  'MorseCancellation.birth_first_new_value_gap',
  'MorseCancellation.birth_preserves_unique_index_zero',
], """/-!
# What the birth of a critical pair preserves below the birth level

When a Morse function `g` differs from `f` only above a level `l` and has at most two new critical
points `p`, `q` (a *birth*, cf. Milnor, *Lectures on the h-cobordism theorem*, §8, Lemma 8.2), the
sublevel sets below `l` are unchanged: `g` and `f` have the same level set at every `a < l`
(`MorseCancellation.birth_preserves_lower_levels`), that level is regular for `g`
(`regular_level_of_retained_critical_germs`) and diffeomorphic to the level of `f`
(`equalLevelDiffeomorph`), index bounds below `a` persist (`birth_preserves_lower_index_bound`),
and a unique minimum stays unique (`birth_preserves_unique_index_zero`).  The bound
`superlevel_bound_of_critical_bound` is the minimum-principle argument behind these statements.
-/"""),

('Hopf.Proof.Geometry.Manifold.Morse.OrderedCancellation.MiddleIndexBlocks', 'hopf', OC, [
  'MorseCancellation.nativeIndexThreeAttachingSphere',
  'MorseCancellation.IsNativeMiddleBasinFamily',
  'MorseCancellation.outer_index_minimality_neg',
  'MorseCancellation.exists_middle_index_blocks',
  'MorseCancellation.nativeMiddleBlockPoint',
], """/-!
# Middle index blocks of a six-dimensional ordered Morse system (proof-specific)

Proof-specific material of the six-sphere formalization; not library mathematics and not
registered in `Lib.lean`.  Every statement is pinned to dimension `6` or to the indices `2`, `3`
of the W4W1 argument: the attaching `2`-sphere of an index-`3` window
(`MorseCancellation.nativeIndexThreeAttachingSphere`), families of such spheres in a regular level
(`IsNativeMiddleBasinFamily`), the index-`2` prefix / index-`3` block decomposition of an
index-ordered system with one minimum and no index `1` (`exists_middle_index_blocks`,
`nativeMiddleBlockPoint`), and the invariance of the secondary count `c₁ + c₅` under `f ↦ -f`
(`outer_index_minimality_neg`).

Moved from `Lib.Geometry.Manifold.Morse.OrderedCancellation`; statements unchanged.
-/"""),

# ---------------------------------------------------------------- SurgeryCollapse
('Lib.Geometry.Manifold.Morse.SurgeryCollapse.PuncturedBall', 'lib', SC, [
  'PuncturedBall.toSphere_fromSphere',
  'PuncturedBall.deformation',
  'PuncturedBall.sphereHomotopyEquiv',
], """/-!
# The punctured ball deformation retracts onto a sphere

The punctured open ball `PuncturedBall.Space E R = {x | 0 < ‖x‖ < R}` deformation retracts onto
the sphere of radius `r < R` (`PuncturedBall.deformation`), so the unit sphere is homotopy
equivalent to the punctured ball (`PuncturedBall.sphereHomotopyEquiv`), cf. Hatcher, *Algebraic
Topology*, Example 0.2 / Proposition 2.22 (`ℝⁿ ∖ 0 ≃ Sⁿ⁻¹`).
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.BeltTubeMeridian', 'lib', SC, [
  'MorseCancellation.nativeBeltTube_homotopic_meridian',
  'MorseCancellation.nativeBeltTubeMeridian_eq',
  'MorseCancellation.beltBallBoundary_homotopic_meridian',
  'MorseCancellation.normal_boundary_homotopic_native_meridian',
], """/-!
# Loops in the belt tube are homotopic to meridians

A map into the tubular neighbourhood of a belt sphere whose belt-sphere component is
null-homotopic is homotopic to a meridian composed with the normalised normal component
(`MorseCancellation.nativeBeltTube_homotopic_meridian`); in particular the boundary of a small
parameter ball mapped into the belt tube is homotopic to a meridian
(`beltBallBoundary_homotopic_meridian`, `normal_boundary_homotopic_native_meridian`).  The
meridian of `Lib.Geometry.Manifold.Morse.OrderedCancellation.BeltTube` agrees with the upper
meridian of an adapted window (`nativeBeltTubeMeridian_eq`).
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelTransport', 'lib', SC, [
  'AdaptedWindows.exists_embedded_level_transport',
  'MorseCancellation.transverse_comp_standardCircle',
  'AdaptedWindows.exists_attaching_circle_lower_transport',
  'AdaptedWindows.realize_one_handle_minimum_branches',
  'AdaptedWindows.exists_native_family_level_transport',
  'AdaptedWindows.exists_native_attaching_lower_cut',
  'AdaptedWindows.exists_regular_band_family_transport',
  'MorseCancellation.unique_connection_of_distinct_minimum_branches',
], """/-!
# Transport of embedded spheres between regular levels along the flow

The gradient-like flow of an `AdaptedWindows` package carries a compact embedded submanifold of a
regular level `f = a`, lying in the basin of a lower regular level `f = b`, to an embedded
submanifold of that level (`AdaptedWindows.exists_embedded_level_transport`, families:
`exists_native_family_level_transport`, `exists_regular_band_family_transport`); attaching
spheres are transported below their critical point (`exists_native_attaching_lower_cut`,
`exists_attaching_circle_lower_transport`).  For an index-`1` critical point whose two attaching
points lie in different path components a flow with two distinct minima at the ends of the
attaching arc is realised (`realize_one_handle_minimum_branches`), and the flow line from the
`1`-handle to the higher minimum is unique (`unique_connection_of_distinct_minimum_branches`).
Cf. Milnor, *Lectures on the h-cobordism theorem*, §4.
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence', 'lib', SC, [
  'EmbeddedCellAttachment.overlapHomologyEquiv',
  'EmbeddedCellAttachment.cellConnectingMap',
  'EmbeddedCellAttachment.coverLeft_old',
  'EmbeddedCellAttachment.coverLeft_formula',
  'EmbeddedCellAttachment.cellConnecting_eq_zero_iff',
  'EmbeddedCellAttachment.cell_exact_at_old',
  'EmbeddedCellAttachment.cell_exact_at_ambient',
  'EmbeddedCellAttachment.mem_range_cellConnecting',
  'EmbeddedCellAttachment.coverLeft_eq_zero_iff',
  'EmbeddedCellAttachment.cell_exact_at_sphere',
  'EmbeddedCellAttachment.cellConnecting_zero_apply',
  'MorseCancellation.cell_oldHomologyMap_zero_injective',
  'MorseCancellation.cell_oldHomologyMap_zero_surjective',
  'MorseCancellation.cell_oldHomologyMap_zero_bijective',
  'MorseCancellation.cellDiskBoundaryHomologyMap',
  'MorseCancellation.cell_oldHomologyMap_zero_iff',
  'MorseCancellation.cell_oldHomologyMap_injective_of_attaching_component',
  'MorseCancellation.cell_old_pathConnected_of_attaching_component',
], """/-!
# The long exact sequence of an attached cell

For a cell `Dᵏ` embedded in `X` and attached to `A = X ∖ int Dᵏ` along its boundary sphere
(`EmbeddedCellAttachment N X`), Mayer–Vietoris for the cover by a neighbourhood of `A` and the
open cell gives the exact sequence
`… → H_{k+1}(X) → H_k(S) → H_k(A) → H_k(X) → …` with connecting map
`EmbeddedCellAttachment.cellConnectingMap` (`cell_exact_at_old`, `cell_exact_at_ambient`,
`cell_exact_at_sphere`); this is the homology sequence of the pair `(X, A)` with
`H_*(X, A) ≅ H̃_{*-1}(S)`, cf. Hatcher, *Algebraic Topology*, Example 2.43 / Proposition 2.22.
In degree `0` the inclusion `A → X` induces a bijection on `H₀` when the sphere is
path-connected (`MorseCancellation.cell_oldHomologyMap_zero_bijective`), and an injection when
the attaching sphere lies in one path component of `A`
(`cell_oldHomologyMap_injective_of_attaching_component`), so `A` is path-connected when `X` is
(`cell_old_pathConnected_of_attaching_component`).
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleExactSequence', 'lib', SC, [
  'ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv',
  'ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv',
  'ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap',
  'ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap',
  'ManifoldMorse.MorseSurgeryData.morseConnectingMap',
  'ManifoldMorse.MorseSurgeryData.cellAttachingHomology_compare',
  'ManifoldMorse.MorseSurgeryData.cellOldHomology_compare',
  'ManifoldMorse.MorseSurgeryData.morseConnecting_compare',
  'ManifoldMorse.MorseSurgeryData.morse_exact_at_lower',
  'ManifoldMorse.MorseSurgeryData.morse_exact_at_upper',
  'ManifoldMorse.MorseSurgeryData.morse_exact_at_attachingSphere',
  'ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_sphere',
  'ManifoldMorse.MorseSurgeryData.morseConnecting_zero_apply',
  'ManifoldMorse.MorseSurgeryData.lowerRealization_one_surjective',
  'ManifoldMorse.MorseSurgeryData.upperHomologyOne_subsingleton',
  'MorseCancellation.native_lowerRealization_zero_bijective',
  'MorseCancellation.native_lower_pathConnected_of_upper',
  'MorseCancellation.native_zero_handle_lower_isEmpty',
  'MorseCancellation.native_lower_pathConnected_of_attaching_component',
  'MorseCancellation.native_attaching_component_of_pairwise_joined',
  'ManifoldMorse.SurgeryWindows.BandData.homologyEquiv',
  'ManifoldMorse.SurgeryWindows.lower_homologyOne_subsingleton_of_indices',
  'ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_index',
], """/-!
# The homology exact sequence of passing a critical point

Passing a critical point of index `λ` attaches a `λ`-cell to the sublevel set (Milnor, *Morse
Theory*, Theorem 3.2); the cell exact sequence of
`Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence` transported along the core-cell
presentation of a Morse surgery datum gives the exact sequence
`… → H_{k+1}(M_{upper}) → H_k(S^{λ-1}) → H_k(M_{lower}) → H_k(M_{upper}) → …`
(`ManifoldMorse.MorseSurgeryData.morse_exact_at_lower`, `morse_exact_at_upper`,
`morse_exact_at_attachingSphere`, with connecting map `morseConnectingMap`).  Consequences for
`λ ≥ 2`: `H₀` and `H₁` do not change (`MorseCancellation.native_lowerRealization_zero_bijective`,
`lowerRealization_one_surjective`), path-connectedness passes downward
(`native_lower_pathConnected_of_upper`), and `H₁` of a sublevel set vanishes when all handles
below have index `≥ 2` (`ManifoldMorse.SurgeryWindows.lower_homologyOne_subsingleton_of_indices`);
below an index-`0` handle the sublevel set is empty when the upper one is path-connected
(`native_zero_handle_lower_isEmpty`).
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.MinimumReduction', 'lib', SC, [
  'MorseCancellation.native_minimum_count_one_of_one_handle_components',
  'MorseCancellation.exists_native_one_handle_joining_components',
  'MorseCancellation.cancel_realized_higher_minimum',
  'MorseCancellation.exists_excellent_morse_reduction_of_multiple_minima',
  'MorseCancellation.minimal_excellent_morse_minimum_count_one',
  'MorseCancellation.minimal_excellent_morse_extreme_counts_one',
], """/-!
# A minimal Morse function on a connected manifold has one minimum and one maximum

If a Morse function on a compact path-connected manifold has more than one local minimum, some
`1`-handle joins two path components of the sublevel set below it
(`MorseCancellation.exists_native_one_handle_joining_components`); cancelling that `1`-handle
against the higher of the two minima (`cancel_realized_higher_minimum`, by the index-`0`/`1`
cancellation theorem) removes two critical points
(`exists_excellent_morse_reduction_of_multiple_minima`).  Hence a Morse function with the least
number of critical points among those with distinct critical values has exactly one minimum
(`minimal_excellent_morse_minimum_count_one`) and, applying this to `-f`, exactly one maximum
(`minimal_excellent_morse_extreme_counts_one`).  Cf. Milnor, *Lectures on the h-cobordism
theorem*, Theorem 8.1 and its corollary.
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.IndexOrdering', 'lib', SC, [
  'AdaptedWindows.remove_connections_of_index_le',
  'AdaptedWindows.remove_connections_of_nonincreasing_indices',
  'AdaptedWindows.exchange_nonincreasing_native_indices',
  'MorseCancellation.exists_index_ordered_morse_system_preserving_critical_points',
], """/-!
# Rearrangement: ordering the critical values by index

Milnor, *Lectures on the h-cobordism theorem*, Theorem 4.8: every Morse function on a compact
manifold can be replaced by a *self-indexing* one with the same critical points and indices, whose
critical values increase with the index.  For two consecutive critical points with
`index q ≤ index p` a general-position isotopy of the intermediate level separates the descending
sphere of `q` from the ascending sphere of `p` (`AdaptedWindows.remove_connections_of_index_le`,
`remove_connections_of_nonincreasing_indices`; Milnor Theorem 4.4), after which the two critical
values may be exchanged (`exchange_nonincreasing_native_indices`).  Decreasing the index disorder
gives the index-ordered system
(`MorseCancellation.exists_index_ordered_morse_system_preserving_critical_points`).
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskFilling', 'lib', SC, [
  'SublevelDisk.circle_nullhomotopies',
  'SphereBoundary.exists_extension_immersive_on_sphere',
  'exists_embedded_disk_extension_of_smooth_extension',
  'RadialFilling.contMDiffAt_direction',
  'RadialFilling.contMDiff_filling',
  'MorseCancellation.circle_nullhomotopy_of_disk',
  'MorseCancellation.exists_smooth_embedded_disk_of_continuous_filling',
], """/-!
# Filling a null-homotopic embedded circle by a smoothly embedded disk

A null-homotopy of a smooth embedded circle `γ : S¹ → N` in a manifold of dimension `≥ 5` with
collars in the time variable yields a smooth map of the plane extending `γ` radially
(`RadialFilling.contMDiff_filling`); the Whitney embedding argument in dimension `≥ 5` (general
position for a `2`-disk) makes it an embedding of the closed disk
(`exists_embedded_disk_extension_of_smooth_extension`,
`MorseCancellation.exists_smooth_embedded_disk_of_continuous_filling`).  Conversely a continuous
disk with boundary `γ` gives the null-homotopy (`circle_nullhomotopy_of_disk`), and in a sublevel
disk of dimension `≥ 3` every circle in the boundary sphere is null-homotopic
(`SublevelDisk.circle_nullhomotopies`).  Cf. Milnor, *Lectures on the h-cobordism theorem*,
Theorem 6.6 (Whitney's lemma), embedding part.
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelIsotopy', 'lib', SC, [
  'AdaptedWindows.realize_unit_level_isotopy',
  'AdaptedWindows.realize_unit_transverse_level_isotopy',
  'AdaptedWindows.place_one_handle_in_unique_minimum_basin',
  'AdaptedWindows.realize_unique_minimum_one_handle_branches',
], """/-!
# Realising an isotopy of a regular level by a gradient-like flow

An isotopy `P` of a regular level `f = a` between two critical points is realised by a new
gradient-like field whose flow through the level is the old flow composed with `P`
(`AdaptedWindows.realize_unit_level_isotopy`, Milnor, *Lectures on the h-cobordism theorem*,
Lemma 4.7); if the descending sphere of `p` and the ascending sphere of `q` meet in one point after
the isotopy, the new flow has a unique trajectory from `p` to `q`, transverse along it when the
sheets are (`realize_unit_transverse_level_isotopy`).  For an index-`1` critical point on a
manifold with a unique minimum both attaching points are moved into the basin of that minimum
(`place_one_handle_in_unique_minimum_basin`, `realize_unique_minimum_one_handle_branches`).
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.OnePointCover', 'lib', SC, [
  'OnePointCover.instLocal1',
  'OnePointCover.spherePunctureHomeomorph',
  'OnePointCover.punctureHomeomorph',
  'OnePointCover.oldPatch_contractible',
  'OnePointCover.finitePatch_contractible',
  'OnePointCover.overlap_subset_range',
  'OnePointCover.overlap_preimage',
  'OnePointCover.overlapHomeomorph',
  'OnePointCover.overlapHomeomorph_apply',
  'OnePointCover.overlapSphereEquiv',
  'OnePointCover.overlapHomologyEquiv',
  'OnePointCover.sphereConnecting',
  'OnePointCover.sphereConnecting_injective',
  'OnePointCover.sphereHomologyEquiv',
], """/-!
# The one-point compactification of `ℝⁿ` covered by two contractible patches

The one-point compactification `OnePoint N` of a finite-dimensional normed space is a sphere;
removing a point leaves a space homeomorphic to `ℝⁿ` (`OnePointCover.punctureHomeomorph`, via
Mathlib's stereographic projection `stereographic'`), so the two patches
`OnePoint N ∖ {0}` and `OnePoint N ∖ {∞}` of `Lib.AlgebraicTopology.SingularHomology.OnePointCover`
are contractible (`oldPatch_contractible`, `finitePatch_contractible`) and their overlap
`N ∖ {0}` is homotopy equivalent to the unit sphere (`overlapHomeomorph`, `overlapSphereEquiv`).
Mayer–Vietoris then gives the suspension isomorphism
`H_{k+2}(OnePoint N) ≅ H_{k+1}(S(N))` (`sphereHomologyEquiv`) with an injective connecting map
`sphereConnecting`, cf. Hatcher, *Algebraic Topology*, Exercise 2.2.
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskCollapse', 'lib', SC, [
  'DiskOnePointCollapse.collapse',
  'DiskOnePointCollapse.collapse_boundary',
  'DiskOnePointCollapse.collapse_interior',
  'DiskOnePointCollapse.collapse_eq_iff',
  'DiskOnePointCollapse.collapse_compress',
  'DiskOnePointCollapse.collapse_eq_coe_iff',
  'DiskOnePointCollapse.collapse_eq_zero_iff',
  'DiskOnePointCollapse.collapse_eq_infty_iff',
  'ClosedHandleCore.collapseMaps_agree',
  'ClosedHandleCore.collapseMap',
  'ClosedHandleCore.collapseMap_old',
  'ClosedHandleCore.collapseMap_handle',
  'EmbeddedCellAttachment.collapseMaps_agree',
  'EmbeddedCellAttachment.collapseMap',
  'EmbeddedCellAttachment.collapseMap_old',
  'EmbeddedCellAttachment.collapseMap_cell',
  'EmbeddedCellAttachment.collapseMap_infty_iff',
  'EmbeddedCellAttachment.collapseMap_eq_zero_iff',
  'EmbeddedCellAttachment.collapseMaps_oldNeighborhood',
  'EmbeddedCellAttachment.collapseMaps_diskPatch',
  'EmbeddedCellAttachment.collapseOverlapMap',
  'EmbeddedCellAttachment.collapseOverlap_sphere',
  'EmbeddedCellAttachment.collapseOverlap_comp_sphere',
  'EmbeddedCellAttachment.collapse_overlapHomology_compare',
  'EmbeddedCellAttachment.collapse_connecting_compare',
], """/-!
# Collapsing the complement of an attached cell to a point

The quotient of the closed unit disk of `N` by its boundary is the one-point compactification
`OnePoint N` (`DiskOnePointCollapse.collapse`, Hatcher, *Algebraic Topology*, Example 0.2 /
Proposition 2.22).  For a cell attached to `A` along its boundary, or a handle
`Dᵏ × Dⁿ⁻ᵏ` attached along `∂Dᵏ × Dⁿ⁻ᵏ`, collapsing `A` to the point at infinity gives a
continuous map `X → OnePoint N` (`EmbeddedCellAttachment.collapseMap`,
`ClosedHandleCore.collapseMap`) which carries the Mayer–Vietoris cover of the cell attachment to
the two-patch cover of `OnePoint N` and is compatible with the connecting homomorphisms
(`EmbeddedCellAttachment.collapse_connecting_compare`).
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.LocalDegreeConnecting', 'lib', SC, [
  'LocalDegree.NativeNeighborhood.overlapSphereEquiv',
  'LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv',
  'LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv_apply',
  'LocalDegree.SeparatedNeighborhoods.overlapMap_sphereEquiv',
  'LinearSphereAction.sphereHomotopyEquiv',
  'LinearSphereAction.sphereHomotopyEquiv_toFun',
  'LinearSphereAction.homologyEquiv',
  'LinearSphereAction.homologyEquiv_apply',
  'LocalDegree.NativeNeighborhood.sphereConnecting',
  'LocalDegree.NativeNeighborhood.sphereHomologyEquiv',
  'LocalDegree.BoundaryData.normalized_homology_compare',
  'LocalDegree.BoundaryData.normalized_homology_eq_sign_smul',
  'LocalDegree.PointTransition.coordinateMap',
  'LocalDegree.PointTransition.coordinateMap_coe',
  'LocalDegree.PointTransition.connecting_naturality',
  'LocalDegree.NativeNeighborhood.coordinateMap_restrictRadius',
  'LocalDegree.NativeNeighborhood.sphereConnecting_restrictRadius',
  'LocalDegree.NativeNeighborhood.sphereConnecting_eq',
  'LocalDegree.PointTransition.coordinateMap_eq_boundary',
  'LocalDegree.PointTransition.coordinateMap_homology',
  'LocalDegree.PointTransition.connecting_derivative_naturality',
  'LocalDegree.pointConnecting_diffeomorph',
], """/-!
# The connecting homomorphism at a point of a manifold and its naturality

For a point `x` of a manifold `M` with a chart neighbourhood `U` (`LocalDegree.NeighborhoodData`),
Mayer–Vietoris for the cover `{M ∖ x, U}` gives the connecting homomorphism
`H_{k+1}(M) → H_k(S(E))` to the homology of the unit sphere of the model space
(`LocalDegree.NativeNeighborhood.sphereConnecting`), independent of the chart radius
(`sphereConnecting_eq`) and an isomorphism `H_{k+2}(M) ≅ H_{k+1}(S(E))` when `M ∖ x` is
contractible (`sphereHomologyEquiv`).  Under a homeomorphism `e` with `e x = y` the connecting maps
correspond through the sphere map of the derivative of the chart transition
(`LocalDegree.PointTransition.connecting_naturality`, `pointConnecting_diffeomorph`); a linear
isomorphism `B` acts on sphere homology through `LinearSphereAction.homologyEquiv`, and the
normalised boundary map of a `BoundaryData` acts by the sign of the relative determinant
(`LocalDegree.BoundaryData.normalized_homology_eq_sign_smul`).  Cf. Hatcher, *Algebraic
Topology*, §2.2 (local degree).
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.SphereOrientation', 'lib', SC, [
  'SphereNormalCoordinates.normalJacobian_smul_mul_pow',
  'SphereNormalCoordinates.sign_normalJacobian_smul_pos',
  'SpherePoint.chart_radial_frame_comp',
  'SphereNormalCoordinates.chartJacobian',
  'SphereNormalCoordinates.chartJacobian_ne_zero',
  'SphereNormalCoordinates.chartJacobian_factor',
  'SphereNormalCoordinates.chartJacobian_sign_factor',
  'SpherePoint.chart_radial_frame_det',
  'SpherePoint.chartJacobian_transport',
  'SpherePoint.chartJacobian_transport_sign',
  'SpherePoint.instLocal1',
  'SpherePoint.pointDiffeomorph',
  'SpherePoint.pointDiffeomorph_apply',
  'SpherePoint.pointChartLinear',
  'SpherePoint.pointClass_sign_compare',
  'SpherePoint.punctureHomeomorph',
  'SpherePoint.puncture_contractible',
  'SpherePoint.connectingHomologyEquiv',
  'SpherePoint.outwardPointClass',
  'SpherePoint.outwardPointClass_eq',
  'SpherePoint.chartSign_mul_self',
  'SpherePoint.connecting_eq_sign_outward',
  'SpherePoint.outwardPointClassEquiv',
  'SpherePoint.outwardClass',
  'SpherePoint.outwardClassEquiv',
  'SpherePoint.outwardPointClass_eq_global',
  'SpherePoint.pointConnecting_eq_outward',
  'SpherePoint.sourceCountMark',
  'SpherePoint.overlapCountMark',
  'SpherePoint.targetCountMark',
  'SpherePoint.overlapCountMark_linear',
  'SpherePoint.countMark_of_connecting',
], """/-!
# Orientation of the point connecting map on a sphere

The connecting homomorphism `H_{k+2}(Sⁿ⁺¹) → H_{k+1}(Sⁿ)` at a point `x` of the sphere
(`Lib.Geometry.Manifold.Morse.SurgeryCollapse.LocalDegreeConnecting`) depends on the chart at
`x` only through a sign, the sign of the *chart Jacobian*
`SphereNormalCoordinates.chartJacobian` (the determinant of the radial frame of the chart against
a fixed splitting `ℝ × F ≃ V`).  Transporting `x` to `y` by a rotation of determinant `1`
transports the Jacobian sign (`SpherePoint.chartJacobian_transport_sign`), so the sign-corrected
map `SpherePoint.outwardPointClass` is independent of the point and the chart
(`outwardPointClass_eq`, `outwardPointClass_eq_global`) and defines a canonical isomorphism
`SpherePoint.outwardClassEquiv : H_{k+2}(Sⁿ⁺²) ≃ H_{k+1}(Sⁿ⁺¹)`.  The *count marks*
(`sourceCountMark`, `overlapCountMark`, `targetCountMark`) identify the top homology groups of
the sphere, of `S(N)` and of `OnePoint N` with `ℤ` compatibly with the connecting maps
(`countMark_of_connecting`).  Cf. Hatcher, *Algebraic Topology*, §2.2 (local degree and
orientation).
-/"""),

('Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleCollapse', 'lib', SC, [
  'ManifoldMorse.MorseSurgeryData.attachmentCollapseMap',
  'ManifoldMorse.MorseSurgeryData.upperCollapseMap',
  'ManifoldMorse.MorseSurgeryData.upperCollapse_realization',
  'ManifoldMorse.MorseSurgeryData.upperCollapse_old',
  'ManifoldMorse.MorseSurgeryData.upperCollapse_handle',
  'ManifoldMorse.MorseSurgeryData.levelCollapseMap',
  'ManifoldMorse.MorseSurgeryData.levelCollapse_realized',
  'ManifoldMorse.MorseSurgeryData.levelCollapse_newExterior',
  'ManifoldMorse.MorseSurgeryData.levelCollapse_newPiece',
  'ManifoldMorse.MorseSurgeryData.levelCollapse_zero_iff',
  'ManifoldMorse.MorseSurgeryData.upperCollapse_coreCell',
  'ManifoldMorse.MorseSurgeryData.upperCollapseHomology_coreCell',
  'ManifoldMorse.MorseSurgeryData.upperCollapse_connecting_compare',
  'ManifoldMorse.MorseSurgeryData.upperCollapse_homology_equiv_compare',
  'ManifoldMorse.MorseSurgeryData.upperCollapse_homology_kernel',
  'ManifoldMorse.MorseSurgeryData.morseConnecting_surjective_of_lower',
  'ManifoldMorse.MorseSurgeryData.upperCollapse_surjective_of_lower',
  'ManifoldMorse.MorseSurgeryData.levelCollapse_beltClosedDiskMap',
  'ManifoldMorse.MorseSurgeryData.levelCollapse_eq_coe_collapseNormal',
  'ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign',
  'ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign_of_transverse',
  'ManifoldMorse.MorseSurgeryData.isInvertible_collapseNormal_comp_of_transverse',
  'ManifoldMorse.MorseSurgeryData.CollapseNeighborhoods',
  'ManifoldMorse.MorseSurgeryData.nonempty_collapseNeighborhoods',
  'ManifoldMorse.MorseSurgeryData.attachingCollapse',
  'ManifoldMorse.MorseSurgeryData.attachingCollapse_zero_iff',
  'ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_old',
  'ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_neighborhood',
  'ManifoldMorse.MorseSurgeryData.collapseOverlapMap',
  'ManifoldMorse.MorseSurgeryData.collapseOverlapMap_eq',
  'ManifoldMorse.MorseSurgeryData.collapseOverlapMap_sphereEquiv',
], """/-!
# Collapsing the lower sublevel set of a Morse surgery to a point

For a Morse surgery datum `d` at a critical point of index `λ`, collapsing the lower sublevel set
`{f ≤ f p - r²}` to the point at infinity of the core disk gives
`ManifoldMorse.MorseSurgeryData.upperCollapseMap : {f ≤ f p + r²} → OnePoint (ℝ^λ)`, and its
restriction `levelCollapseMap` to the upper level, which sends the belt sphere to `0`
(`levelCollapse_zero_iff`) and is the normalised belt normal `collapseNormal` on the new piece
(`levelCollapse_eq_coe_collapseNormal`).  On homology the collapse map composed with the
suspension isomorphism of `OnePoint (ℝ^λ)` is the Morse connecting map
(`upperCollapse_connecting_compare`), its kernel is the image of the lower sublevel set
(`upperCollapse_homology_kernel`), and it is onto in degree `k + 2` when
`H_{k+1}` of the lower set vanishes (`upperCollapse_surjective_of_lower`).  For a sphere `g` in
the upper level transverse to the belt sphere, the intersection points carry separated
neighbourhoods (`CollapseNeighborhoods`, `nonempty_collapseNeighborhoods`) on which the collapse is
the belt normal, and the local Jacobian sign of the collapse equals the intersection sign
(`collapseNormal_comp_sign_of_transverse`).  This is the Morse-theoretic form of the degree
computation of Milnor, *Lectures on the h-cobordism theorem*, §7 (intersection numbers via
`H_*(M_{upper}, M_{lower})`).
-/"""),

('Hopf.Proof.Geometry.Manifold.Morse.SurgeryCollapse.MiddleFamilies', 'hopf', SC, [
  'AdaptedWindows.exists_middle_family_descent',
  'AdaptedWindows.exists_middle_family_step',
  'AdaptedWindows.exists_regular_band_middle_basin_family',
  'AdaptedWindows.exists_middle_basin_family_step',
  'AdaptedWindows.exists_middle_block_realization',
  'AdaptedWindows.exists_ordered_middle_family',
], """/-!
# Families of attaching two-spheres of an index-three block (proof-specific)

Proof-specific material of the six-sphere formalization; not library mathematics and not
registered in `Lib.lean`.  Every statement carries `Module.finrank ℝ E = 6` or a
`Hemisphere.Sphere 2` family: the descent of a family of attaching `2`-spheres of index-`3`
windows through one window (`AdaptedWindows.exists_middle_family_descent`,
`exists_middle_family_step`, `exists_middle_basin_family_step`,
`exists_regular_band_middle_basin_family`) and its iteration over an index-`3` block
(`exists_middle_block_realization`, `exists_ordered_middle_family`), producing a
`MorseCancellation.IsNativeMiddleBasinFamily` in a regular level below the block.

Moved from `Lib.Geometry.Manifold.Morse.SurgeryCollapse`; statements unchanged.
-/"""),

('Hopf.Proof.Geometry.Manifold.Morse.SurgeryCollapse.BeltIntersections', 'hopf', SC, [
  'ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices',
  'MorseCancellation.lower_circle_nullhomotopies_of_ordered_native_indices',
  'ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step',
  'ManifoldMorse.MorseSurgeryData.exists_finite_belt_reduction',
  'ManifoldMorse.MorseSurgeryData.exists_minimal_signed_belt_sphere',
  'ManifoldMorse.MorseSurgeryData.exists_single_belt_intersection_of_unit_count',
  'AdaptedWindows.exists_transverse_middle_belt_loop',
], """/-!
# Belt-sphere intersections of an index-two window in dimension six (proof-specific)

Proof-specific material of the six-sphere formalization; not library mathematics and not
registered in `Lib.lean`.  Every statement carries `Module.finrank ℝ E = 6` and the index `2`:
circles in the lower level of an index-`2` window are null-homotopic when all earlier windows have
index `2` or `3` (`ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices`,
`MorseCancellation.lower_circle_nullhomotopies_of_ordered_native_indices`); the Whitney trick
cancels pairs of opposite intersection points of a transverse `2`-sphere with the belt `3`-sphere
of an index-`2` window (`ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step`,
`exists_finite_belt_reduction`, `exists_minimal_signed_belt_sphere`,
`exists_single_belt_intersection_of_unit_count`); and a transverse loop through the belt sphere
of an index-`1` window is placed in a regular level (`AdaptedWindows.exists_transverse_middle_belt_loop`).

Moved from `Lib.Geometry.Manifold.Morse.SurgeryCollapse`; statements unchanged.
-/"""),

('Hopf.Proof.Geometry.Manifold.Morse.SurgeryCollapse.OuterIndexMinimal', 'hopf', SC, [
  'MorseCancellation.exists_outer_index_minimal_ordered_morse_system',
], """/-!
# The outer-index-minimal ordered Morse system (proof-specific)

Proof-specific material of the six-sphere formalization; not library mathematics and not
registered in `Lib.lean`.  `MorseCancellation.exists_outer_index_minimal_ordered_morse_system`
combines the minimal excellent Morse system, the index ordering and the one-minimum/one-maximum
counts of `Lib.Geometry.Manifold.Morse.SurgeryCollapse` with the project's secondary minimality
of the count `c₁ + c₅` of critical points of the outer indices `1` and `5` of the six-dimensional
argument.

Moved from `Lib.Geometry.Manifold.Morse.SurgeryCollapse`; statement unchanged.
-/"""),

('Hopf.Proof.Geometry.Manifold.Morse.SurgeryCollapse.MiddlePresentation', 'hopf', SC, [
  'ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate',
  'ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_surjective',
  'ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_kernel',
  'ManifoldMorse.MorseSurgeryData.lowerRealization_two_injective',
  'ManifoldMorse.MorseSurgeryData.exists_indexTwoHomology_split',
  'ManifoldMorse.MorseSurgeryData.exists_indexTwoBasis_extension',
  'ManifoldMorse.SurgeryWindows.indexTwoBasis_step',
  'ManifoldMorse.SurgeryWindows.indexTwoBasis',
  'ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass',
  'ManifoldMorse.MorseSurgeryData.coreBoundary_two_eq_smul',
  'ManifoldMorse.MorseSurgeryData.coreBoundary_two_range',
  'ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_surjective',
  'ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_kernel',
  'ManifoldMorse.MorseSurgeryData.indexThreePresentation',
  'ManifoldMorse.SurgeryWindows.middlePresentation',
  'ManifoldMorse.SurgeryWindows.middleMatrix',
], """/-!
# The index-two basis and the index-three presentation of `H₂` (proof-specific)

Proof-specific material of the six-sphere formalization; not library mathematics and not
registered in `Lib.lean`.  Every statement is pinned to the indices `2` and `3` of the W4W1
argument: each index-`2` window adds a free generator to `H₂` of the sublevel set, read off by the
collapse coordinate (`ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate`,
`ManifoldMorse.SurgeryWindows.indexTwoBasis`), and each index-`3` window adds one relation, the
class of its attaching sphere (`indexThreeAttachingClass`, `indexThreePresentation`); over an
index-`2` prefix followed by an index-`3` block this yields the integer presentation
`ManifoldMorse.SurgeryWindows.middlePresentation` with matrix `middleMatrix`.

Moved from `Lib.Geometry.Manifold.Morse.SurgeryCollapse`; statements unchanged.
-/"""),
]

FACADE_DOC = {
OC: """/-!
# Ordered Morse systems and cancellation steps

Facade module: it imports the pieces of the former monolith and declares nothing.

* `OrderedCancellation.TwoSphereDegree` — a homology isomorphism of `S²` acts by `±1`;
* `OrderedCancellation.BeltTube` — the tubular neighbourhood of a belt sphere and its meridians;
* `OrderedCancellation.PrescribedFlow` — adapted windows with a prescribed gradient-like flow;
* `OrderedCancellation.CircleParametrization` — the diffeomorphism `S¹ ≃ Circle`;
* `OrderedCancellation.ValueExchange` — exchanging consecutive critical values (Milnor 4.1);
* `OrderedCancellation.PairCancellation` — the first cancellation theorem (Milnor 5.4);
* `OrderedCancellation.PathComponents` — `H₀` detects path components (Hatcher 2.7);
* `OrderedCancellation.Negation` — the Morse function `-f` and its indices;
* `OrderedCancellation.MinimalSystem` — Morse functions with the least number of critical points;
* `OrderedCancellation.IndexCounts` — counting critical points by index;
* `OrderedCancellation.BirthPreservation` — what a birth of a critical pair preserves below.

The dimension-`6` and index-`2`/`3` statements of the former file live in
`Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean`.
-/""",
SC: """/-!
# Surgery collapse

Facade module: it imports the pieces of the former monolith and declares nothing.

* `SurgeryCollapse.PuncturedBall` — the punctured ball retracts onto a sphere;
* `SurgeryCollapse.BeltTubeMeridian` — loops in the belt tube are homotopic to meridians;
* `SurgeryCollapse.LevelTransport` — transport of embedded spheres between regular levels;
* `SurgeryCollapse.CellExactSequence` — the long exact sequence of an attached cell;
* `SurgeryCollapse.HandleExactSequence` — the homology exact sequence of passing a critical point;
* `SurgeryCollapse.MinimumReduction` — a minimal Morse function has one minimum and one maximum;
* `SurgeryCollapse.IndexOrdering` — rearrangement by index (Milnor 4.8);
* `SurgeryCollapse.DiskFilling` — filling a null-homotopic circle by an embedded disk;
* `SurgeryCollapse.LevelIsotopy` — realising an isotopy of a regular level by a flow;
* `SurgeryCollapse.OnePointCover` — the two-patch cover of `OnePoint N` and its suspension isomorphism;
* `SurgeryCollapse.DiskCollapse` — collapsing the complement of an attached cell to a point;
* `SurgeryCollapse.LocalDegreeConnecting` — the point connecting map and its naturality;
* `SurgeryCollapse.SphereOrientation` — the orientation sign of the point connecting map;
* `SurgeryCollapse.HandleCollapse` — collapsing the lower sublevel set of a Morse surgery.

The dimension-`6`, `Hemisphere.Sphere 2` and index-`2`/`3` statements of the former file live
under `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/` (`MiddleFamilies`,
`BeltIntersections`, `OuterIndexMinimal`, `MiddlePresentation`).
-/""",
}

def path_of(module):
    return module.replace('.', '/') + '.lean'
