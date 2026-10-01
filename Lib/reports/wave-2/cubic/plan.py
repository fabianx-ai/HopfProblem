"""Cut plan for wave 2 / cubic.  PIECES: (stem, [line ranges of the base file], extra sibling imports,
keep_lib_imports (None = the original five), import_all, docstring)."""
MOD = 'Lib.Geometry.Manifold.Morse.Cubic'
ORIG = ['Lib.Geometry.Manifold.Morse.Existence', 'Lib.Geometry.Manifold.RegularLevel',
        'Lib.Geometry.Manifold.WhitneyEmbedding', 'Lib.Geometry.Manifold.Collar',
        'Lib.Geometry.Manifold.Morse.SurgeryWindows']
PIECES = [
('SurgeryWindowsExistence', [(49, 109)], [], None, True, """/-!
# Existence of adapted surgery windows

A Morse function `f` on a compact Hausdorff manifold whose critical values are pairwise distinct
admits an `AdaptedWindows E f` package (`MorseCancellation.nonempty_adaptedSurgeryWindows`): Morse
surgery data of small radius around every critical point, with pairwise disjoint value windows, and a
complete gradient-like field which is the model descent field in every surgery block.  This is the
existence of a gradient-like vector field adapted to Morse charts, cf. Milnor, *Lectures on the
h-cobordism theorem*, §3.
-/"""),
('BasinBlock', [(111, 711)], [], None, True, """/-!
# The Morse block of a gradient-like flow near a critical point

Let `c` be a signed Morse chart of `f` at `p` and `V` a vector field with flow `F` which agrees
with the descent field of `c` near `p`.  In the split coordinates `(z₋, z₊)` of the chart the flow
is the linear model `MorseHandle.descentFlow`, and on a small box `‖z₋‖, ‖z₊‖ ≤ r`:

* a point with `z₋ ≠ 0` leaves the box forwards through a level below `f p`, a point with
  `z₊ ≠ 0` leaves it backwards through a level above `f p`
  (`MorseCancellation.exists_forward_morse_model_exit`, `exists_native_forward_morse_exit` and the
  backward twins);
* points of the plane `z₋ = 0` converge to `p` as `t → ∞`, points of `z₊ = 0` as `t → -∞`
  (`native_morse_positive_plane_limit`, `native_morse_negative_plane_limit`);
* hence, if `f` is non-increasing along the flow, the forward (backward) basin of `p` meets the
  box exactly in the plane `z₋ = 0` (`z₊ = 0`): `exists_native_morse_basin_block`,
  `exists_descending_morse_basin_block`;
* the attaching sphere and the belt sphere of radius `r` flow by the linear model and converge to
  `p` backwards, respectively forwards (`native_attaching_core_flow`,
  `native_attaching_core_backward_limit`, `native_belt_core_flow`, `native_belt_core_forward_limit`).

These are the local stable and unstable discs of a critical point, cf. Milnor, *Lectures on the
h-cobordism theorem*, §3–§4 (the discs `D_L`, `D_R` of a gradient-like field).
-/"""),
('SublevelFlow', [(715, 839)], [], ['Lib.Geometry.Manifold.Flow.HeightTranslating'], False, """/-!
# Flows that cross a level set strictly downwards

Let `F : Flow ℝ X` be a flow on a topological space and `f : X → ℝ` a continuous function whose
derivative along the flow is a continuous function `D`, i.e. `d/ds f (F s x) = D (F t x)` at
`s = t`.  If `D < 0` on the level set `f = c`, then

* `f` is strictly decreasing along the orbit of a point where `D < 0`, for small times
  (`FlowCancellation.exists_local_strict_flow_descent`);
* the sublevel set `{f ≤ c}` is forward invariant and is mapped into `{f < c}` by every positive
  time (`forwardInvariant_sublevel_of_boundary`, `strict_sublevel_entry_of_boundary`);
* the interior of `{f ≤ c}` is `{f < c}` (`interior_sublevel_eq_of_boundary`);
* every orbit meets the level `f = c` at most once (`flow_level_time_unique`).

This is the elementary transversality of a flow to a regular level, cf. Milnor, *Morse Theory*, §3.
-/"""),
('LevelOrbit', [(843, 873)], ['SublevelFlow'], None, True, """/-!
# Orbits of a vector field crossing a level set

The derivative `x ↦ df_x (V x)` of a smooth function `f` along a smooth vector field `V` on a
manifold is smooth (`MorseCancellation.contMDiff_directionalDerivative`).  If it is negative on the
level set `f = c`, an orbit of the flow of `V` meets that level in at most one point
(`MorseCancellation.native_same_level_orbit_points`); cf. Milnor, *Morse Theory*, §3.
-/"""),
('Model', [(877, 981)], [], [], False, """/-!
# The cubic birth–death model

On `MorseCancellation.Model m = ℝ × (Fin m → ℝ)` the one-parameter family
`MorseCancellation.cubic σ t (x, y) = x³/3 + t x + ∑ i, σ i * y i ^ 2` is the standard model of the
birth or cancellation of a pair of nondegenerate critical points (cf. Milnor, *Lectures on the
h-cobordism theorem*, §5; the birth–death singularity).  For `σ i ≠ 0`:

* its derivative is `MorseCancellation.differential` (`hasFDerivAt_cubic`, `fderiv_cubic`), and a
  point is critical iff `x² + t = 0` and `y = 0` (`critical_iff`);
* for `t > 0` there is no critical point (`positive_parameter_no_critical`), for `t = 0` exactly
  the origin (`cubic_zero_unique_critical`), and for `t = -a²` exactly `(±a, 0)`
  (`negative_parameter_critical_iff`), with critical values `∓ 2a³/3` (`cubic_critical_values`).
-/"""),
('EndpointChart', [(985, 1093)], ['Model'], ['Lib.Geometry.Manifold.Morse.Existence'], True, """/-!
# Morse charts at the two critical points of the cubic model

At the critical point `(e a, 0)`, `e = ±1`, `a > 0`, of `cubic σ (-a²)` the substitution
`u = (s - e a) √(a + e (s - e a) / 3)` (`MorseCancellation.endpointCoordinate`, defined on
`endpointDomain a e`) turns the cubic into its Morse normal form
`cubic σ (-a²) (s, y) = (critical value) + e u² + ∑ i, σ i * y i ^ 2` (`cubic_endpoint_square`).
The substitution is a local diffeomorphism of `ℝ` near `e a` (`exists_endpoint_scalar_chart`),
and its product with the identity (`scalarProductChart`) is a Morse chart of the model at the
critical point (`exists_endpoint_product_chart`).  This is the explicit Morse lemma for
`x³/3 - a² x`, cf. Milnor, *Morse Theory*, Lemma 2.2.
-/"""),
('LocalReplacement', [(1097, 1216)], [], [], True, """/-!
# Replacing a function inside a chart

For a partial diffeomorphism `Φ : E → M` and functions `f : M → ℝ`, `b : E → ℝ`,
`LocalFunctionReplacement.replace Φ f b` is `b ∘ Φ⁻¹` on the image of `Φ` and `f` elsewhere.  If
`f ∘ Φ = b₀` on the source of `Φ` and `b₁ = b₀` outside a compact subset `K` of the source, then
`replace Φ f b₁` agrees with `f` outside `Φ '' K` (`replace_eq_off_support`), is smooth when `f` and
`b₁` are (`contMDiff_replace`), and its critical points inside the chart are the images of those of
`b₁` (`replace_critical_iff`).  This is the standard way to alter a function on a coordinate
neighbourhood, as in Milnor, *Lectures on the h-cobordism theorem*, §2 and §4.
-/"""),
('DescentField', [(1220, 1485)], ['Model', 'EndpointChart'], None, True, """/-!
# The descent field of the cubic model and its linearisation at the critical points

`MorseCancellation.cubicDescent σ t (x, y) = (-(x² + t), -σ i * y i)` is a gradient-like field for
the cubic model: the derivative of `cubic σ t` along it is negative away from the critical points
(`cubicDescent_strict`) and it vanishes at them (`cubicDescent_zero_of_critical`).  Its transport
to a manifold by a chart is `nativeCubicDescent`.

At the critical point `(e a, 0)` of `cubic σ (-a²)` the Möbius substitution
`u = (s - e a) / (a + e s)` (`endpointFieldCoordinate`, on `endpointFieldDomain a e`) conjugates the
axis component `a² - s²` of the field to the linear field `-2 e a u`
(`endpointFieldCoordinate_pushforward`); with the identity on the transverse coordinates
(`endpointFieldProduct`) it conjugates `cubicDescent` to the linear field `endpointLinearField`
(`fderiv_endpointFieldProduct_cubic`, `exists_endpoint_field_product_chart`).  Hence a field which
is `endpointLinearField` in a chart `Q` is the cubic descent field in the chart
`Q ∘ endpointFieldProduct` (`partialChartField_of_model_conjugacy`,
`exists_native_cubic_field_endpoint`).  Cf. Milnor, *Lectures on the h-cobordism theorem*, §5
(the gradient-like field of the cancellation model).
-/"""),
('SplitCoordinates', [(1489, 1934)], ['Model', 'DescentField'], None, True, """/-!
# Aligning the cubic model with a Morse chart

A bijection `ρ : Option (Fin m) ≃ Fin n` gives the linear equivalence
`MorseCancellation.splitEquiv ρ : ℝ × (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)` placing the axis coordinate
at `ρ none`.  Composed with the splitting of a signed Morse chart `c` into negative and positive
coordinates it gives `selectedMorseFieldEquiv c ρ`, which conjugates the linear endpoint field of
the cubic model to the model descent field of the chart (`selectedMorseFieldEquiv_descent`).
Changing it by block isometries (`exists_positive_ray_alignment`, `morse_block_change_descent`,
`transverseFieldChange`, `splitTransverseChange`) one can moreover send the model axis onto a
prescribed ray of the unstable or of the stable plane (`exists_selected_outgoing_axis`,
`exists_selected_incoming_axis`).  The resulting charts in which a given field is the cubic descent
field near a critical point are `exists_cubic_field_endpoint_with_alignment`,
`exists_original_field_endpoint_with_alignment` and `exists_controlled_morse_field_endpoint`.
Cf. Milnor, *Lectures on the h-cobordism theorem*, §5.
-/"""),
('AlignedRays', [(1938, 2330)], ['Model', 'DescentField', 'SplitCoordinates'], None, True, """/-!
# Orbits converging to a critical point, in Morse coordinates and on the cubic axis

For a field `V` with flow `F` that is the descent field of a signed Morse chart `c` near `p`:
an orbit is given by the linear model flow in the chart as long as it stays where `V` is the model
(`MorseCancellation.eventually_morse_coordinate_flow`, `flow_formula_of_local_shifts`,
`morse_coordinates_of_actual_trajectory`); an orbit converging to `p` as `t → ∞` eventually lies
in the plane `z₋ = 0`, one converging as `t → -∞` in the plane `z₊ = 0`
(`exists_incoming_morse_tail`, `exists_outgoing_morse_tail`).  If the chart is aligned with a cubic
model chart `Φ` so that this ray is the image of the model axis
(`descentFlow_outgoing_aligned_ray`, `descentFlow_incoming_aligned_ray`,
`cubic_axis_of_aligned_morse_ray`), the tail of the orbit lies on the axis `Φ (s, 0)`, `|s| < a`
(`incoming_tail_on_cubic_axis`, `outgoing_tail_on_cubic_axis`), and such a chart exists for every
non-constant orbit converging to `p` (`exists_actual_incoming_cubic_endpoint`,
`exists_actual_outgoing_cubic_endpoint`).  Cf. Milnor, *Lectures on the h-cobordism theorem*, §5.
-/"""),
('CoreBasins', [(2333, 2513)], ['BasinBlock', 'LevelOrbit', 'AlignedRays'], None, True, """/-!
# The attaching sphere and the belt sphere as level sets of the basins

For a field `V` with flow `F` that is the model descent field in the block of radius `2r` of a
signed Morse chart at `p`, and which crosses the level `f = f p - r²` strictly downwards, a point
`x` of that level satisfies `F t x → p` as `t → -∞` iff it lies on the attaching sphere of radius
`r` (`MorseCancellation.native_attaching_core_basin_iff`); dually, on the level `f = f p + r²` the
points with `F t x → p` as `t → ∞` are exactly the belt sphere
(`MorseCancellation.native_belt_core_basin_iff`).  These are the left-hand and right-hand spheres
`S_L`, `S_R` of Milnor, *Lectures on the h-cobordism theorem*, §3, described as
traces of the unstable and stable manifolds.
-/"""),
('Tanh', [(2517, 2542), (2641, 2648)], [], [], False, """/-!
# Calculus of `Real.tanh` and `Real.artanh`

The derivative of `tanh` is `1 - tanh²`, `tanh` is strictly increasing with limits `±1` at `±∞`,
and `artanh` is smooth on `(-1, 1)`.  These complement
`Mathlib/Analysis/SpecialFunctions/Artanh.lean` (`Real.tanh_bijOn`, `Real.artanh_tanh`) and are
candidates for upstreaming.
-/"""),
('AxisParameter', [(2544, 2639), (2650, 2689)], ['Model', 'DescentField', 'Tanh'], [], False, """/-!
# The connecting orbit of the cubic model

For `a > 0` the axis `{(s, 0) | -a < s < a}` of the cubic model `cubic σ (-a²)` is the orbit of the
descent field `cubicDescent` joining the two critical points: the solution of `s' = a² - s²` with
`s 0 = 0` is `MorseCancellation.cubicAxisParameter a t = a * tanh (a * t)`
(`hasDerivAt_cubicAxisParameter`), a smooth bijection of `ℝ` onto `(-a, a)`
(`range_cubicAxisParameter`, `contDiff_cubicAxisParameter`) with limits `±a`, whose inverse is
`cubicAxisClock a s = artanh (s / a) / a` (`cubicAxisClock_parameter`, `cubicAxisParameter_clock`,
`contDiffOn_cubicAxisClock`).  `cubicModelOrbit a t = (cubicAxisParameter a t, 0)` is the
corresponding integral curve of `cubicDescent σ (-a²)` (`hasDerivAt_cubicModelOrbit`).  This is the
single trajectory from the critical point of index `λ + 1` to that of index `λ` in the
cancellation model, cf. Milnor, *Lectures on the h-cobordism theorem*, §5.
-/"""),
]
FACADE_DOC = """/-!
# The cubic model of a cancelling pair

Facade module: it imports the pieces of the former monolith and declares nothing.  The subject is
the chart-level cubic birth–death model behind Morse cancellation (cf. Milnor, *Lectures on the
h-cobordism theorem*, §5) together with the local flow lemmas it is used with.

* `Cubic.SurgeryWindowsExistence` — existence of adapted surgery windows;
* `Cubic.BasinBlock` — the Morse block of a gradient-like flow near a critical point;
* `Cubic.SublevelFlow` — flows crossing a level set strictly downwards;
* `Cubic.LevelOrbit` — orbits of a vector field crossing a level set;
* `Cubic.Model` — the cubic family `x³/3 + t x + ∑ σᵢ yᵢ²` and its critical points;
* `Cubic.EndpointChart` — Morse charts at the two critical points of the model;
* `Cubic.LocalReplacement` — replacing a function inside a chart;
* `Cubic.DescentField` — the descent field of the model and its linearisation;
* `Cubic.SplitCoordinates` — aligning the model with a Morse chart;
* `Cubic.AlignedRays` — orbits converging to a critical point, on the cubic axis;
* `Cubic.CoreBasins` — attaching and belt spheres as level sets of the basins;
* `Cubic.Tanh` — calculus of `Real.tanh` and `Real.artanh`;
* `Cubic.AxisParameter` — the connecting orbit `a tanh (a t)` of the model.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, §3–§5.
* [milnor63] J. Milnor, *Morse Theory*, §2–§3.

## Tags

morse-theory, cancellation, cubic-model, h-cobordism
-/"""
