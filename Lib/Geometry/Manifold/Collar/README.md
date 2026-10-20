# Tubular neighbourhoods, collars and level transport

Facade module: it imports the pieces below and declares nothing itself.

* `Collar.Tubular` — the normal bundle of a compact manifold embedded in Euclidean space, the
  tubular neighbourhood theorem `NativeEuclideanEmbedding.exists_tubularNeighborhood` and the
  smooth retraction `NativeEuclideanEmbedding.SmoothRetraction` onto the embedded manifold
  (Lee, *Introduction to Smooth Manifolds*, Thm 6.24, Prop. 6.25).
* `Collar.RangeTransport` — `DiskFraming.SmoothRangeTransportOn`: smooth transport between the
  ranges of two projection families, and smooth frames of a range bundle near a star-convex
  compact set (`DiskFraming.exists_smooth_frame_near_starConvex`).
* `Collar.DiskTubular` — the tubular neighbourhood of an embedded closed ball
  (`exists_tubularNeighborhood_in_open_of_embedded_closedBall`).
* `Collar.HeightCollar` — collars of a regular level adapted to the height
  (`RegularLevel.exists_heightCollar`; cf. Lee, Thm 9.25).
* `Collar.SmallPerturbation` — `x ↦ x + u x` with `u` smooth and `k`-Lipschitz, `k < 1`, is a
  diffeomorphism; bump translations.
* `Collar.SupportedDiffeomorph` — `SupportedDiffeomorph.extension`: a compactly supported
  diffeomorphism in the source of a partial diffeomorphism, extended by the identity.
* `Collar.LevelTransport` — ambient diffeomorphisms carrying one regular level and sublevel to
  another across a band without critical values
  (`RegularLevel.exists_ambient_regularBand_transport`; Milnor, *Morse Theory*, Thm 3.1).
* `Collar.SphereCoordinates` — the diffeomorphism of unit spheres induced by a linear isometry.
  (moved: now `Lib.Geometry.Manifold.Morse.SurgeryWindows.SurgeryData`)

## References

* [John M. Lee, *Introduction to Smooth Manifolds*][lee13], Thm 6.24, Thm 9.25
* [milnor63] J. Milnor, *Morse Theory*, §3

## Tags

collar, tubular neighbourhood, supported diffeomorphism, level transport

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Collar` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Collar.DiskTubular`
* `Lib.Geometry.Manifold.Collar.HeightCollar`
* `Lib.Geometry.Manifold.Collar.LevelTransport`
* `Lib.Geometry.Manifold.Collar.RangeTransport`
* `Lib.Geometry.Manifold.Collar.SmallPerturbation`
* `Lib.Geometry.Manifold.Collar.SupportedDiffeomorph`
* `Lib.Geometry.Manifold.Collar.Tubular`
