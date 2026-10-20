# Ordered Morse systems and cancellation steps

Facade module: it imports the pieces of the former monolith and declares nothing.

* `OrderedCancellation.TwoSphereDegree` — a homology isomorphism of `S²` acts by `±1`;
* `OrderedCancellation.BeltTube` — the tubular neighbourhood of a belt sphere and its meridians;
* `OrderedCancellation.PrescribedFlow` — adapted windows with a prescribed gradient-like flow;
* `OrderedCancellation.CircleParametrization` — the diffeomorphism `S¹ ≃ Circle`;
* `OrderedCancellation.ValueExchange` — exchanging consecutive critical values (Milnor 4.1);
* `OrderedCancellation.PairCancellation` — the first cancellation theorem (Milnor 5.4);
* `OrderedCancellation.PathComponents` — `H₀` detects path components (Hatcher 2.7);
  (moved: now `Lib.AlgebraicTopology.SingularHomology.PathComponents`)
* `OrderedCancellation.Negation` — the Morse function `-f` and its indices;
* `OrderedCancellation.MinimalSystem` — Morse functions with the least number of critical points;
* `OrderedCancellation.IndexCounts` — counting critical points by index;
* `OrderedCancellation.BirthPreservation` — what a birth of a critical pair preserves below.

The dimension-`6` and index-`2`/`3` statements of the former file live in
`Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean`.

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Morse.OrderedCancellation` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Morse.OrderedCancellation.BeltTube`
* `Lib.Geometry.Manifold.Morse.OrderedCancellation.BirthPreservation`
* `Lib.Geometry.Manifold.Morse.OrderedCancellation.CircleParametrization`
* `Lib.Geometry.Manifold.Morse.OrderedCancellation.IndexCounts`
* `Lib.Geometry.Manifold.Morse.OrderedCancellation.MinimalSystem`
* `Lib.Geometry.Manifold.Morse.OrderedCancellation.Negation`
* `Lib.Geometry.Manifold.Morse.OrderedCancellation.PairCancellation`
* `Lib.Geometry.Manifold.Morse.OrderedCancellation.PrescribedFlow`
* `Lib.Geometry.Manifold.Morse.OrderedCancellation.TwoSphereDegree`
* `Lib.Geometry.Manifold.Morse.OrderedCancellation.ValueExchange`
