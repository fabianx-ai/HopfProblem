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

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Morse.Existence` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Morse.Existence.AttachingUnion`
* `Lib.Geometry.Manifold.Morse.Existence.BeltCore`
* `Lib.Geometry.Manifold.Morse.Existence.ChartPerturbation`
* `Lib.Geometry.Manifold.Morse.Existence.DistinctCriticalValues`
* `Lib.Geometry.Manifold.Morse.Existence.HomotopicRelWithin`
* `Lib.Geometry.Manifold.Morse.Existence.HomotopyCollars`
* `Lib.Geometry.Manifold.Morse.Existence.LevelSurgery`
* `Lib.Geometry.Manifold.Morse.Existence.PartialChart`
* `Lib.Geometry.Manifold.Morse.Existence.RegularLocus`
* `Lib.Geometry.Manifold.Morse.Existence.SmoothApproximation`
