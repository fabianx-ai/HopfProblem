# The immersion chain: plane, curve and manifold immersions in charts

Existence of immersions and embeddings in relative form, for maps of a plane or of a line into a
manifold, and the perturbation, tubular-neighbourhood and frame machinery they rest on: Whitney's
weak embedding theorem (Whitney, *Differentiable manifolds*, Thm 5) and the immersion and
embedding theorems of Hirsch, *Differential Topology*, Ch. 2 §2 and Ch. 3 §2. This module is a
facade: it imports the pieces below and declares nothing.

## Pieces

* `Lib.Geometry.Manifold.Immersion.Relative.PointMoving` — homogeneity of a manifold: points of a
  path-connected open set are exchanged by supported diffeomorphisms isotopic to the identity.
* `Lib.Geometry.Manifold.Immersion.Relative.ImmersionLocus` — the immersion locus is open; the local
  immersion theorem; compactness of the double-point set.
* `Lib.Geometry.Manifold.Immersion.Relative.ChartPerturbation` — the Sard-type count for
  chart-supported perturbations (`ChartMapPerturbation`).
* `Lib.Geometry.Manifold.Immersion.Relative.Embedding` — the relative embedding theorem for a
  general source in the range `2 dim E < dim N`, with avoidance of a closed image.
* `Lib.Geometry.Manifold.Immersion.Relative.AffinePerturbation` — affine perturbations of maps of the
  plane and their bad parameters (`PlaneImmersion`).
* `Lib.Geometry.Manifold.Immersion.Relative.Plane` — the relative immersion and embedding theorems
  for a two-dimensional source into a manifold of dimension at least `5`.
* `Lib.Geometry.Manifold.Immersion.Relative.Curve` — the same chain in dimension one
  (`WeightedPerturbation`, `CurveImmersion`).
* `Lib.Geometry.Manifold.Immersion.Relative.Arc` — embedded arcs with prescribed endpoint germs,
  clean of a finite set or of a closed image.
* `Lib.Geometry.Manifold.Immersion.Relative.TubularNeighborhood` — tubular neighbourhoods of an
  embedded star-convex compact set (Hirsch, Ch. 4 §5), clean form.
* `Lib.Geometry.Manifold.Immersion.Relative.TwoSheetArc` — clean charts along an arc joining two
  embedded surfaces in a five-manifold.
* `Lib.Geometry.Manifold.Immersion.Relative.FrameField` — frame fields, sheared blocks and axis
  coordinates (`FrameField`, `AxisCoordinates`, `TransverseCoordinates`).
* `Lib.Geometry.Manifold.Immersion.Relative.AxisChart` — axis charts with prescribed endpoint germs
  (`LinearFramePaths`).

## References

* [hirsch76] M. Hirsch, *Differential Topology*, Ch. 2, Ch. 3, Ch. 4 §5.
* [whitney36] H. Whitney, *Differentiable manifolds*, Thm 5.

## Tags

immersion, whitney, tubular-neighborhood, relative-form

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Immersion.Relative` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Immersion.Relative.AffinePerturbation`
* `Lib.Geometry.Manifold.Immersion.Relative.Arc`
* `Lib.Geometry.Manifold.Immersion.Relative.AxisChart`
* `Lib.Geometry.Manifold.Immersion.Relative.ChartPerturbation`
* `Lib.Geometry.Manifold.Immersion.Relative.Curve`
* `Lib.Geometry.Manifold.Immersion.Relative.Embedding`
* `Lib.Geometry.Manifold.Immersion.Relative.FrameField`
* `Lib.Geometry.Manifold.Immersion.Relative.ImmersionLocus`
* `Lib.Geometry.Manifold.Immersion.Relative.Plane`
* `Lib.Geometry.Manifold.Immersion.Relative.PointMoving`
* `Lib.Geometry.Manifold.Immersion.Relative.TubularNeighborhood`
* `Lib.Geometry.Manifold.Immersion.Relative.TwoSheetArc`
