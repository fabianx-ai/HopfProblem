/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Geometry.Manifold.Transversality.Diffeomorph
public import Lib.Geometry.Manifold.Transversality.RegularValues
public import Lib.Geometry.Manifold.Transversality.Transverse
public import Lib.Geometry.Manifold.Transversality.Parametric
public import Lib.Geometry.Manifold.Transversality.MorseBelt
public import Lib.Geometry.Manifold.Transversality.CenteredChart
public import Lib.Geometry.Manifold.Transversality.SupportedIsotopy
public import Lib.Geometry.Manifold.Transversality.LinearFramePaths
public import Lib.Geometry.Manifold.Transversality.GermLinearization
public import Lib.Geometry.Manifold.Transversality.GermRealization
public import Lib.Geometry.Manifold.Transversality.DiskShrinking
public import Lib.Geometry.Manifold.Transversality.DiscTheorem
public import Lib.Geometry.Manifold.Transversality.Homogeneity

/-!
# Transversality, supported isotopies and the disc theorem

This module only re-exports its pieces:

* `Transversality.Diffeomorph` : diffeomorphisms with definitional underlying maps.
* `Transversality.RegularValues` : submersions are a chart-independent open condition; Sard's
  theorem in equal dimension.
* `Transversality.Transverse` : the transversality relation `f ⋔ g` at a pair of points
  (Guillemin–Pollack, §2.3), its chart description, openness, and invariance.
* `Transversality.Parametric` : transversality after a generic translation (Hirsch, Ch. 3).
* `Transversality.MorseBelt` : belt-sphere neighbourhood coordinates of a Morse chart.
* `Transversality.CenteredChart` : translations and charts centred at a point.
* `Transversality.SupportedIsotopy` : compactly supported isotopies, isotopy extension through a
  chart, bump translations and shears.
* `Transversality.LinearFramePaths` : `SL(n, ℝ)` is path connected and `GL(n, ℝ)` has two path
  components.
* `Transversality.GermLinearization` : linearisation of germs by compactly supported isotopies.
* `Transversality.GermRealization` : germs realised by compactly supported diffeomorphisms, and the
  alignment of two charts with the same centre.
* `Transversality.DiskShrinking` : radial diffeomorphisms and the disc-shrinking isotopy.
* `Transversality.DiscTheorem` : the disc theorem (Hirsch, Thm 8.3.1; Palais).
* `Transversality.Homogeneity` : homogeneity of manifolds.
-/
