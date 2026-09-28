/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.PuncturedBall
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.BeltTubeMeridian
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelTransport
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleExactSequence
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.MinimumReduction
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.IndexOrdering
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskFilling
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelIsotopy
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.OnePointCover
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskCollapse
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.LocalDegreeConnecting
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.SphereOrientation
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleCollapse

/-!
# Surgery collapse

Facade module: it imports the pieces of the former monolith and declares nothing.

* `SurgeryCollapse.PuncturedBall` — the punctured ball retracts onto a sphere;
* `SurgeryCollapse.BeltTubeMeridian` — loops in the belt tube are homotopic to meridians;
* `SurgeryCollapse.LevelTransport` — transport of embedded spheres between regular levels;
* `SurgeryCollapse.CellExactSequence` — the long exact sequence of an attached cell;
* `SurgeryCollapse.HandleExactSequence` — the homology exact sequence of passing a critical point;
* `SurgeryCollapse.MinimumReduction` — a minimal Morse function has one minimum and one maximum;
* `SurgeryCollapse.IndexOrdering` — rearrangement by index (Milnor 4.8);
* `SurgeryCollapse.DiskFilling` — filling a null-homotopic circle by an embedded disk;
* `SurgeryCollapse.LevelIsotopy` — realising an isotopy of a regular level by a flow;
* `SurgeryCollapse.OnePointCover` — the two-patch cover of `OnePoint N` and its suspension isomorphism;
* `SurgeryCollapse.DiskCollapse` — collapsing the complement of an attached cell to a point;
* `SurgeryCollapse.LocalDegreeConnecting` — the point connecting map and its naturality;
* `SurgeryCollapse.SphereOrientation` — the orientation sign of the point connecting map;
* `SurgeryCollapse.HandleCollapse` — collapsing the lower sublevel set of a Morse surgery.

The dimension-`6`, `Hemisphere.Sphere 2` and index-`2`/`3` statements of the former file live
under `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/` (`MiddleFamilies`,
`BeltIntersections`, `OuterIndexMinimal`, `MiddlePresentation`).
-/
