/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.Geometry.Manifold.Morse.OrderedCancellation.TwoSphereDegree
import Lib.Geometry.Manifold.Morse.OrderedCancellation.BeltTube
import Lib.Geometry.Manifold.Morse.OrderedCancellation.PrescribedFlow
import Lib.Geometry.Manifold.Morse.OrderedCancellation.CircleParametrization
import Lib.Geometry.Manifold.Morse.OrderedCancellation.ValueExchange
import Lib.Geometry.Manifold.Morse.OrderedCancellation.PairCancellation
import Lib.Geometry.Manifold.Morse.OrderedCancellation.PathComponents
import Lib.Geometry.Manifold.Morse.OrderedCancellation.Negation
import Lib.Geometry.Manifold.Morse.OrderedCancellation.MinimalSystem
import Lib.Geometry.Manifold.Morse.OrderedCancellation.IndexCounts
import Lib.Geometry.Manifold.Morse.OrderedCancellation.BirthPreservation

/-!
# Ordered Morse systems and cancellation steps

Facade module: it imports the pieces of the former monolith and declares nothing.

* `OrderedCancellation.TwoSphereDegree` — a homology isomorphism of `S²` acts by `±1`;
* `OrderedCancellation.BeltTube` — the tubular neighbourhood of a belt sphere and its meridians;
* `OrderedCancellation.PrescribedFlow` — adapted windows with a prescribed gradient-like flow;
* `OrderedCancellation.CircleParametrization` — the diffeomorphism `S¹ ≃ Circle`;
* `OrderedCancellation.ValueExchange` — exchanging consecutive critical values (Milnor 4.1);
* `OrderedCancellation.PairCancellation` — the first cancellation theorem (Milnor 5.4);
* `OrderedCancellation.PathComponents` — `H₀` detects path components (Hatcher 2.7);
* `OrderedCancellation.Negation` — the Morse function `-f` and its indices;
* `OrderedCancellation.MinimalSystem` — Morse functions with the least number of critical points;
* `OrderedCancellation.IndexCounts` — counting critical points by index;
* `OrderedCancellation.BirthPreservation` — what a birth of a critical pair preserves below.

The dimension-`6` and index-`2`/`3` statements of the former file live in
`Hopf/Proof/Geometry/Manifold/Morse/OrderedCancellation/MiddleIndexBlocks.lean`.
-/
