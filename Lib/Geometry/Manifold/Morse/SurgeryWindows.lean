/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Geometry.Manifold.Morse.SurgeryWindows.HausdorffDimension
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.Avoidance
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.DiskDouble
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.Hemisphere
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.ImageComplement
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.NewInterior
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.OpenHomotopyExtension
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.ZeroAvoidanceCutoff
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.BeltComplement
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.SurgeryData
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.Windows

/-!
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
-/
