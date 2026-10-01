/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Geometry.Manifold.Morse.Existence.AttachingUnion
public import Lib.Geometry.Manifold.Morse.Existence.RegularLocus
public import Lib.Geometry.Manifold.Morse.Existence.DistinctCriticalValues
public import Lib.Geometry.Manifold.Morse.Existence.LevelSurgery
public import Lib.Geometry.Manifold.Morse.Existence.PartialChart
public import Lib.Geometry.Manifold.Morse.Existence.BeltCore
public import Lib.Geometry.Manifold.Morse.Existence.HomotopyCollars
public import Lib.Geometry.Manifold.Morse.Existence.HomotopicRelWithin
public import Lib.Geometry.Manifold.Morse.Existence.ChartPerturbation
public import Lib.Geometry.Manifold.Morse.Existence.SmoothApproximation

/-!
# Morse functions with distinct critical values, handle attachment, and smoothing

This module only re-exports its pieces, which treat three subjects.

* Morse functions: `Existence.RegularLocus` (openness of the regular locus of a smooth family)
  and `Existence.DistinctCriticalValues` (every Morse function on a compact manifold can be
  perturbed to have distinct critical values; cf. Milnor, *Lectures on the h-cobordism
  theorem*, §2).
* Handle attachment along a signed Morse chart: `Existence.AttachingUnion` (the sublevel set
  above an isolated critical level is the one below with a handle attached; Milnor,
  *Morse theory*, §3), `Existence.LevelSurgery` (the two level sets form a surgery
  pair), `Existence.BeltCore` (attaching and belt spheres as smooth embeddings), and
  `Existence.PartialChart` (restrictions of partial diffeomorphisms).
* Whitney approximation: `Existence.HomotopicRelWithin`, `Existence.ChartPerturbation`,
  `Existence.HomotopyCollars` and `Existence.SmoothApproximation` (every continuous map from a
  compact manifold to a boundaryless manifold is homotopic to a smooth one; Hirsch,
  *Differential Topology*, §2.2; Lee, *Introduction to Smooth Manifolds*, Ch. 6).

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65]
-/
