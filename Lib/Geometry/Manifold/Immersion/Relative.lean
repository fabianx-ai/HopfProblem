/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Geometry.Manifold.Immersion.Relative.PointMoving
public import Lib.Geometry.Manifold.Immersion.Relative.ImmersionLocus
public import Lib.Geometry.Manifold.Immersion.Relative.ChartPerturbation
public import Lib.Geometry.Manifold.Immersion.Relative.Embedding
public import Lib.Geometry.Manifold.Immersion.Relative.AffinePerturbation
public import Lib.Geometry.Manifold.Immersion.Relative.Plane
public import Lib.Geometry.Manifold.Immersion.Relative.Curve
public import Lib.Geometry.Manifold.Immersion.Relative.Arc
public import Lib.Geometry.Manifold.Immersion.Relative.TubularNeighborhood
public import Lib.Geometry.Manifold.Immersion.Relative.TwoSheetArc
public import Lib.Geometry.Manifold.Immersion.Relative.FrameField
public import Lib.Geometry.Manifold.Immersion.Relative.AxisChart

/-!
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
-/
