/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Geometry.Manifold.Morse.Rearrangement.TransverseChart
public import Lib.Geometry.Manifold.Morse.Rearrangement.HeightCoordinates
public import Lib.Geometry.Manifold.Morse.Rearrangement.IntervalTranslation
public import Lib.Geometry.Manifold.Morse.Rearrangement.LongitudinalBlend
public import Lib.Geometry.Manifold.Morse.Rearrangement.SmoothTransition
public import Lib.Geometry.Manifold.Morse.Rearrangement.TubeMotion
public import Lib.Geometry.Manifold.Morse.Rearrangement.LevelTime
public import Lib.Geometry.Manifold.Morse.Rearrangement.BasinImages
public import Lib.Geometry.Manifold.Morse.Rearrangement.LevelConnectedness
public import Lib.Geometry.Manifold.Morse.Rearrangement.AmbientTransversality

/-!
# Rearrangement of Morse functions: the toolbox

Facade module: it imports the pieces below and declares nothing itself. The pieces are the
tools with which a Morse function is modified inside a band — the machinery of the
rearrangement theorem (Milnor, *Lectures on the h-cobordism theorem*, Theorem 4.1 and §4; the
theorem itself is `MorseRearrangement.exists_morse_rearrangement_of_no_connection` in
`Lib.Geometry.Manifold.Morse.RearrangementTheorem`) together with the local models of the
Whitney trick (§6) and the general-position lemmas both use.

* `Rearrangement.HeightCoordinates` — the height map `(t, z) ↦ (F (t, z), z)` and the
  diffeomorphism `RegularHeightCoordinates.longitudinalDiffeomorph` of `ℝ × V` given by a
  compactly supported displacement with positive longitudinal derivative.
* `Rearrangement.IntervalTranslation` — `MorseRearrangement.IntervalTranslation`: increasing
  diffeomorphisms of `ℝ` supported in `(a, b)` moving `x` to `y`
  (`exists_increasing_interval_translation_with_exterior_germs`), and the convex blend
  `blendHeight` of two heights.
* `Rearrangement.LongitudinalBlend` — `MorseCancellation.longitudinalBlend`: the isotopy of
  `ℝ × V` pushing along the axis, every slice a diffeomorphism.
* `Rearrangement.SmoothTransition` — positive derivative and strict monotonicity of
  `Real.smoothTransition`.
* `Rearrangement.TransverseChart` — linear transverse corrections of tube charts and the
  restriction of a tube to a clean neighbourhood of an axis segment.
* `Rearrangement.TubeMotion` — `MorseCancellation.LongitudinalTubeMotion`: the supported isotopy
  of a manifold moving a point along the axis of a tube, and the single transverse crossing of
  two sheets it produces.
* `Rearrangement.LevelTime` — agreement of flows along half orbits, level crossings, the
  implicit-function germ of a scalar time, the smooth signed level time and the flow cylinder
  `{f = c} × ℝ ≃ levelBasin` (`FlowCancellation.exists_native_level_flow_cylinder`).
* `Rearrangement.BasinImages` — the basins of the critical points of an adapted window as
  countable unions of smooth images of Euclidean balls; the endpoint obstruction
  `forwardHighBasins ∪ backwardLowBasins` as the complement of a level basin.
* `Rearrangement.LevelConnectedness` — joining in sublevels and basins; a regular level is path
  connected under the index bounds `coindex, index ≤ d`, `1 + d < dim M`
  (`AdaptedWindows.pathConnectedSpace_regular_level_of_endpoint_dimensions`).
* `Rearrangement.AmbientTransversality` — `NativeTransversality.Patch` and the ambient
  diffeomorphism making a map transverse to, or disjoint from, another
  (`NativeTransversality.exists_ambient_transverse_diffeomorph`,
  `MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension`).

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, §4 and §6.

## Tags

morse-theory, rearrangement, h-cobordism
-/
