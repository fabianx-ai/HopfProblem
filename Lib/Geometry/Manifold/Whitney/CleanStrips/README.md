# Clean crossing charts and strip patches

Local normal forms along the two sheets of a Whitney pair, in general dimension. The module only
imports its pieces:

* `CleanStrips.CrossingChart` : simultaneous charts at a transverse crossing of two submanifolds of
  complementary dimension, and finiteness of transverse intersections (Guillemin–Pollack,
  *Differential topology*, §§1.5, 2.3).
* `CleanStrips.SphereNormal` : the defining function of the unit sphere, the adapted normal frame
  and the normal Jacobian.
* `CleanStrips.BeltIntersection` : local signs and intersection numbers of a sphere with the belt
  sphere of a Morse surgery (Milnor, *Lectures on the h-cobordism theorem*, §6).
  (moved: now `Lib.Geometry.Manifold.Morse.BeltIntersection`)
* `CleanStrips.NormalCoordinate` : the normal coordinate of a product chart.
* `CleanStrips.StripModel` : the linear model `(ℝ × A) × B` of a strip chart, blending and the
  detector map.
* `CleanStrips.StripNormalData` : strip charts along a sheet and their normal frames.
* `CleanStrips.CornerPatch` : clean corner patches at a transverse crossing.
* `CleanStrips.BigonStripCoordinates` : the strip coordinates of the planar Whitney bigon.
* `CleanStrips.StripPatch` : clean strip patches along an arc.
* `CleanStrips.BigonBoundary` : a clean embedded neighbourhood of the boundary of the Whitney bigon
  (Milnor, *Lectures on the h-cobordism theorem*, §§5–6).

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Whitney.CleanStrips` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Whitney.CleanStrips.BigonBoundary`
* `Lib.Geometry.Manifold.Whitney.CleanStrips.BigonStripCoordinates`
* `Lib.Geometry.Manifold.Whitney.CleanStrips.CornerPatch`
* `Lib.Geometry.Manifold.Whitney.CleanStrips.CrossingChart`
* `Lib.Geometry.Manifold.Whitney.CleanStrips.NormalCoordinate`
* `Lib.Geometry.Manifold.Whitney.CleanStrips.SphereNormal`
* `Lib.Geometry.Manifold.Whitney.CleanStrips.StripModel`
* `Lib.Geometry.Manifold.Whitney.CleanStrips.StripNormalData`
* `Lib.Geometry.Manifold.Whitney.CleanStrips.StripPatch`
