# Surgery collapse

Facade module: it imports the pieces of the former monolith and declares nothing.

* `SurgeryCollapse.PuncturedBall` — the punctured ball retracts onto a sphere;
  (moved: now `Lib.AlgebraicTopology.SingularHomology.PuncturedBall`)
* `SurgeryCollapse.BeltTubeMeridian` — loops in the belt tube are homotopic to meridians;
* `SurgeryCollapse.LevelTransport` — transport of embedded spheres between regular levels;
* `SurgeryCollapse.CellExactSequence` — the long exact sequence of an attached cell;
* `SurgeryCollapse.HandleExactSequence` — the homology exact sequence of passing a critical point;
* `SurgeryCollapse.MinimumReduction` — a minimal Morse function has one minimum and one maximum;
* `SurgeryCollapse.IndexOrdering` — rearrangement by index (Milnor 4.8);
* `SurgeryCollapse.DiskFilling` — filling a null-homotopic circle by an embedded disk;
* `SurgeryCollapse.LevelIsotopy` — realising an isotopy of a regular level by a flow;
* `SurgeryCollapse.OnePointCover` — the two-patch cover of `OnePoint N` and its suspension isomorphism;
  (moved: now in `Lib.AlgebraicTopology.SingularHomology.OnePointCover`)
* `SurgeryCollapse.DiskCollapse` — collapsing the complement of an attached cell to a point;
* `SurgeryCollapse.LocalDegreeConnecting` — the point connecting map and its naturality;
* `SurgeryCollapse.SphereOrientation` — the orientation sign of the point connecting map;
* `SurgeryCollapse.HandleCollapse` — collapsing the lower sublevel set of a Morse surgery.

The dimension-`6`, `Hemisphere.Sphere 2` and index-`2`/`3` statements of the former file live
under `Hopf/Proof/Geometry/Manifold/Morse/SurgeryCollapse/` (`MiddleFamilies`,
`BeltIntersections`, `OuterIndexMinimal`, `MiddlePresentation`).

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Morse.SurgeryCollapse` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.BeltTubeMeridian`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskCollapse`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.DiskFilling`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleCollapse`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleExactSequence`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.IndexOrdering`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelIsotopy`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.LevelTransport`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.LocalDegreeConnecting`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.MinimumReduction`
* `Lib.Geometry.Manifold.Morse.SurgeryCollapse.SphereOrientation`
