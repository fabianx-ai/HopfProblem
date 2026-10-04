# The cubic model of a cancelling pair

Facade module: it imports the pieces of the former monolith and declares nothing.  The subject is
the chart-level cubic birth–death model behind Morse cancellation (cf. Milnor, *Lectures on the
h-cobordism theorem*, §5) together with the local flow lemmas it is used with.

* `Cubic.SurgeryWindowsExistence` — existence of adapted surgery windows;
* `Cubic.BasinBlock` — the Morse block of a gradient-like flow near a critical point;
* `Cubic.SublevelFlow` — flows crossing a level set strictly downwards;
* `Cubic.LevelOrbit` — orbits of a vector field crossing a level set;
* `Cubic.Model` — the cubic family `x³/3 + t x + ∑ σᵢ yᵢ²` and its critical points;
* `Cubic.EndpointChart` — Morse charts at the two critical points of the model;
* `Cubic.LocalReplacement` — replacing a function inside a chart;
* `Cubic.DescentField` — the descent field of the model and its linearisation;
* `Cubic.SplitCoordinates` — aligning the model with a Morse chart;
* `Cubic.AlignedRays` — orbits converging to a critical point, on the cubic axis;
* `Cubic.CoreBasins` — attaching and belt spheres as level sets of the basins;
* `Cubic.Tanh` — calculus of `Real.tanh` and `Real.artanh`;
* `Cubic.AxisParameter` — the connecting orbit `a tanh (a t)` of the model.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, §3–§5.
* [milnor63] J. Milnor, *Morse Theory*, §2–§3.

## Tags

morse-theory, cancellation, cubic-model, h-cobordism

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Morse.Cubic` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Morse.Cubic.AlignedRays`
* `Lib.Geometry.Manifold.Morse.Cubic.AxisParameter`
* `Lib.Geometry.Manifold.Morse.Cubic.BasinBlock`
* `Lib.Geometry.Manifold.Morse.Cubic.CoreBasins`
* `Lib.Geometry.Manifold.Morse.Cubic.DescentField`
* `Lib.Geometry.Manifold.Morse.Cubic.EndpointChart`
* `Lib.Geometry.Manifold.Morse.Cubic.LevelOrbit`
* `Lib.Geometry.Manifold.Morse.Cubic.LocalReplacement`
* `Lib.Geometry.Manifold.Morse.Cubic.Model`
* `Lib.Geometry.Manifold.Morse.Cubic.SplitCoordinates`
* `Lib.Geometry.Manifold.Morse.Cubic.SublevelFlow`
* `Lib.Geometry.Manifold.Morse.Cubic.SurgeryWindowsExistence`
* `Lib.Geometry.Manifold.Morse.Cubic.Tanh`
