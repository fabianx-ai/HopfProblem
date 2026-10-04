# Morse surgery windows

The data structures for the surgeries of a Morse function and the general-position and
homotopy tools they use (Milnor, *Lectures on the h-cobordism theorem*, §3-4; Milnor,
*Morse Theory*, §3). This module only re-exports its pieces:

* `SurgeryWindows.HausdorffDimension` — smooth images of lower dimension have dense complement.
* `SurgeryWindows.Avoidance` — a smooth map can be moved, rel a closed set, off the image of a
  map of complementary low dimension.
* `SurgeryWindows.DiskDouble` — the double of a disk along a boundary homeomorphism.
* `SurgeryWindows.Hemisphere` — the unit sphere as two hemisphere graphs over the ball.
* `SurgeryWindows.ImageComplement` — homotopies and nullhomotopies in the complement of a
  compact smooth image.
* `SurgeryWindows.NewInterior` — the interior of the new piece of a surgery boundary pair.
* `SurgeryWindows.OpenHomotopyExtension` — extending a homotopy on an open set that is
  stationary off a closed subset.
* `SurgeryWindows.ZeroAvoidanceCutoff` — nonvanishing approximations of maps into higher
  dimension.
* `SurgeryWindows.BeltComplement` — loops in the level after a surgery are nullhomotopic.
* `SurgeryWindows.SurgeryData` — `ManifoldMorse.MorseSurgeryData`, the surgery at one critical
  point.
* `SurgeryWindows.Windows` — `ManifoldMorse.SurgeryWindows` and `AdaptedWindows`.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, §3-4.
* [milnor63] J. Milnor, *Morse Theory*, §3.

## Tags

morse-theory, surgery, h-cobordism, handle-decomposition

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Morse.SurgeryWindows` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Morse.SurgeryWindows.Avoidance`
* `Lib.Geometry.Manifold.Morse.SurgeryWindows.BeltComplement`
* `Lib.Geometry.Manifold.Morse.SurgeryWindows.DiskDouble`
* `Lib.Geometry.Manifold.Morse.SurgeryWindows.HausdorffDimension`
* `Lib.Geometry.Manifold.Morse.SurgeryWindows.Hemisphere`
* `Lib.Geometry.Manifold.Morse.SurgeryWindows.ImageComplement`
* `Lib.Geometry.Manifold.Morse.SurgeryWindows.NewInterior`
* `Lib.Geometry.Manifold.Morse.SurgeryWindows.OpenHomotopyExtension`
* `Lib.Geometry.Manifold.Morse.SurgeryWindows.SurgeryData`
* `Lib.Geometry.Manifold.Morse.SurgeryWindows.Windows`
* `Lib.Geometry.Manifold.Morse.SurgeryWindows.ZeroAvoidanceCutoff`
