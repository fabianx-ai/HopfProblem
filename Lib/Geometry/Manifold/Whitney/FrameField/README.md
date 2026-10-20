# Frame fields along tubular bigons

The Whitney trick needs a field of frames over the Whitney disc restricting on the two boundary
arcs to the normal frames of the two sheets; such a field exists when the two intersection points
have opposite signs. This module re-exports the pieces:

* `Whitney.FrameField.BlockDeterminant`: determinants of block frames `G ⊞ C`, frames on a line,
  constancy of the determinant sign along a path of invertible maps.
* `Whitney.FrameField.Complement`: smooth orthogonal complements of a smooth family of injective
  maps near a compact star-shaped set.
* `Whitney.FrameField.FrameExtension`: nowhere-zero curves with prescribed endpoint germs, and
  nowhere-zero fields and one-column frames extended relative to a closed set.
* `Whitney.FrameField.PlanarFrame`: linear algebra of the plane and the two path components of
  `GL₂(ℝ)`.
* `Whitney.FrameField.InvertibleJoin`: smooth joins of invertible germs of the same determinant
  sign in dimension one or two, and complements with prescribed endpoint germs.
* `Whitney.FrameField.IntersectionCoordinates`: the joint block of two sheet frames, whose
  determinant is the intersection sign, and the transport of complements.
* `Whitney.FrameField.BoundaryArcs`: the two boundary arcs of a tubular bigon and the normal frames
  of the sheets along them.
* `Whitney.FrameField.BoundaryField`: one smooth field on a neighbourhood of the boundary of the
  bigon from fields along the two arcs.
* `Whitney.FrameField.RankThreeFrame`: the adapted frame over a bigon of normal rank three, from
  opposite corner intersection signs
  (`TubularBigon.exists_rankThree_adapted_frame_of_opposite_corner_signs`).
* `Whitney.FrameField.SheetNormal`: sheet frames, sheet complements and normal detectors along a
  strip.
* `Whitney.FrameField.RankThreeCorners`: the corner intersection signs computed from a defining
  map of one sheet, and the case of a belt sphere of a Morse surgery.
* `Whitney.FrameField.SheetCoordinates`: the chart induced on a sheet by a clean ambient chart.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6 (the Whitney trick and the
  framing of the Whitney disc).

## Tags

Morse theory, Whitney trick, handle cancellation

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Whitney.FrameField` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Whitney.FrameField.BlockDeterminant`
* `Lib.Geometry.Manifold.Whitney.FrameField.BoundaryArcs`
* `Lib.Geometry.Manifold.Whitney.FrameField.BoundaryField`
* `Lib.Geometry.Manifold.Whitney.FrameField.Complement`
* `Lib.Geometry.Manifold.Whitney.FrameField.FrameExtension`
* `Lib.Geometry.Manifold.Whitney.FrameField.IntersectionCoordinates`
* `Lib.Geometry.Manifold.Whitney.FrameField.InvertibleJoin`
* `Lib.Geometry.Manifold.Whitney.FrameField.PlanarFrame`
* `Lib.Geometry.Manifold.Whitney.FrameField.RankThreeCorners`
* `Lib.Geometry.Manifold.Whitney.FrameField.RankThreeFrame`
* `Lib.Geometry.Manifold.Whitney.FrameField.SheetCoordinates`
* `Lib.Geometry.Manifold.Whitney.FrameField.SheetNormal`
