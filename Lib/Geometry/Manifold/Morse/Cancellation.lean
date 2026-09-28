/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Geometry.Manifold.Morse.Cancellation.CubicModel
import Lib.Geometry.Manifold.Morse.Cancellation.LyapunovResidence
import Lib.Geometry.Manifold.Morse.Cancellation.LevelExit
import Lib.Geometry.Manifold.Morse.Cancellation.CriticalGerms
import Lib.Geometry.Manifold.Morse.Cancellation.LogarithmicCutoff
import Lib.Geometry.Manifold.Morse.Cancellation.TransverseGerms
import Lib.Geometry.Manifold.Morse.Cancellation.BandHeight
import Lib.Geometry.Manifold.Morse.Cancellation.BandReplacement
import Lib.Geometry.Manifold.Morse.Cancellation.CubicConnection
import Lib.Geometry.Manifold.Morse.Cancellation.ConnectionData
import Lib.Geometry.Manifold.Morse.Cancellation.BasinSheets
import Lib.Geometry.Manifold.Morse.Cancellation.LevelIsotopy

/-!
# Cancellation along a transverse connection

The cancellation theorems of Morse theory (Milnor, *Lectures on the
h-cobordism theorem*, Theorem 5.4). This module re-exports the pieces:

* `Morse.Cancellation.CubicModel`: the cubic local model, its cancelled descent
  field, Lyapunov function and Hessian.
* `Morse.Cancellation.LyapunovResidence`: residence bounds for a flow in a
  compact set where a Lyapunov function decreases; uniform band crossings.
* `Morse.Cancellation.LevelExit`: exits of the Morse model flow through the
  levels `f p ± r ^ 2` near the belt and attaching spheres.
* `Morse.Cancellation.CriticalGerms`: surviving critical germs, the Morse index
  as a germ invariant, the Morse count after removing a pair.
* `Morse.Cancellation.LogarithmicCutoff`: one-variable cutoffs with
  `|t χ'(t)|` small.
* `Morse.Cancellation.BandHeight`: the smooth band height between two regular
  levels and its boundary germ corrections.
* `Morse.Cancellation.BandReplacement`: replacing a Morse function on a band;
  removal of a critical pair (`FlowCancellation.remove_morse_band_pair`).
* `Morse.Cancellation.CubicConnection`: cancellation of a unique connection in
  the cubic model (`MorseCancellation.cancel_unique_native_cubic_connection`).
* `Morse.Cancellation.TransverseGerms`: transversality through sheet
  factorisations.
* `Morse.Cancellation.ConnectionData`: the cancellation datum
  `MorseCancellation.NativeConnectionCancellationData`, its transversality and
  its cancellation.
* `Morse.Cancellation.BasinSheets`: the stable and unstable sheets of the datum;
  transversality from maps into the basins.
* `Morse.Cancellation.LevelIsotopy`: the First Cancellation Theorem
  `MorseCancellation.cancel_of_transverse_level_isotopy`.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4.

## Tags

morse-theory, cancellation, gradient-like-flow, h-cobordism
-/
