# The transverse connection of a cancelling pair

Facade module: it imports the pieces below and declares nothing itself, so that every consumer
of `Lib.Geometry.Manifold.Morse.Connection` keeps working unchanged.

Two critical points of adjacent index joined by a single transverse trajectory of a
gradient-like field can be given coordinates along the trajectory in which the field is the
cubic model field (the first step of the first cancellation theorem, Milnor, *Lectures on the
h-cobordism theorem*, Theorem 5.4). The pieces, in dependency order:

* `Connection.CubicEndpoints`: endpoint slices and clocks of the cubic model along an orbit;
* `Connection.MinimumBasins`: density of the forward basins of the minima, belt branches;
* `Connection.NoReturn`: no-return neighbourhoods of an isolated connecting orbit;
* `Connection.BeltArc`: belt arcs and meridians of a handle;
* `Connection.TimeChange`: time changes and band normalisation of a descent flow;
* `Connection.Suspension`: the suspended flow of a level diffeomorphism, level flow cylinders;
* `Connection.LevelHolonomy`: realising an isotopy of a regular level by the flow;
* `Connection.TransverseTimeLifts`: transversality of flow sheets through transverse level maps;
* `Connection.PhaseCylinder`: flow-box charts of a connecting orbit with a phase;
* `Connection.TransitionPhase`: transition maps between flow-box charts;
* `Connection.TransportedCorrections`: transport of supported isotopies through transverse charts;
* `Connection.SignEnumerations`: sign vectors, coordinate enumerations, split coordinates;
* `Connection.EndpointBasins`: stable and unstable planes at the cubic endpoints,
  `MorseCancellation.NativeEndpointSliceData`;
* `Connection.TransverseBlocks`: linearising a transverse germ by supported isotopies;
* `Connection.CylinderHolonomy`: holonomy corrections of a flow cylinder;
* `Connection.PhaseFlow`: phase clocks and the phase-corrected cylinder;
* `Connection.FieldChartGluing`: gluing flow-box charts along an axis;
* `Connection.CubicFieldChart`: the cubic field chart along a unique connecting orbit,
  `MorseCancellation.exists_full_cubic_chart_from_corrected_cylinder`.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4.

## Tags

morse-theory, cancellation, gradient-like-flow, h-cobordism

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Morse.Connection` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Morse.Connection.BeltArc`
* `Lib.Geometry.Manifold.Morse.Connection.CubicEndpoints`
* `Lib.Geometry.Manifold.Morse.Connection.CubicFieldChart`
* `Lib.Geometry.Manifold.Morse.Connection.CylinderHolonomy`
* `Lib.Geometry.Manifold.Morse.Connection.EndpointBasins`
* `Lib.Geometry.Manifold.Morse.Connection.FieldChartGluing`
* `Lib.Geometry.Manifold.Morse.Connection.LevelHolonomy`
* `Lib.Geometry.Manifold.Morse.Connection.MinimumBasins`
* `Lib.Geometry.Manifold.Morse.Connection.NoReturn`
* `Lib.Geometry.Manifold.Morse.Connection.PhaseCylinder`
* `Lib.Geometry.Manifold.Morse.Connection.PhaseFlow`
* `Lib.Geometry.Manifold.Morse.Connection.SignEnumerations`
* `Lib.Geometry.Manifold.Morse.Connection.Suspension`
* `Lib.Geometry.Manifold.Morse.Connection.TimeChange`
* `Lib.Geometry.Manifold.Morse.Connection.TransitionPhase`
* `Lib.Geometry.Manifold.Morse.Connection.TransportedCorrections`
* `Lib.Geometry.Manifold.Morse.Connection.TransverseBlocks`
* `Lib.Geometry.Manifold.Morse.Connection.TransverseTimeLifts`
