/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.SphereNormalCoordinates
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.InnerBigon
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.WhitneyDisc
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.ImmersionRepair
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.Arcs
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.CornerCharts
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.TransverseCoordinates
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.StripInterpolation
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.StripAlongArc
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.StripPair
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.BeltBigon
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.FiberRestriction
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.SmallPerturbation

/-!
# Embedded arcs and clean strip pairs

The geometric preparation of the Whitney trick: embedded arcs joining two intersection points of
two sheets, clean charts and strips along them, and the filling of the resulting bigon boundary by
an embedded Whitney disc with a tubular neighbourhood. This module re-exports the pieces:

* `Whitney.EmbeddedArcs.SphereNormalCoordinates`: radial frames and normal Jacobians along an
  embedded sphere.
* `Whitney.EmbeddedArcs.InnerBigon`: contractions of the standard bigon and their collars.
* `Whitney.EmbeddedArcs.WhitneyDisc`: filling a clean bigon boundary by an embedded Whitney disc
  with a tubular neighbourhood.
* `Whitney.EmbeddedArcs.ImmersionRepair`: making a map immersive by small weighted perturbations;
  curves with injective differential at their endpoints.
* `Whitney.EmbeddedArcs.Arcs`: embedded arcs avoiding a finite set in dimension at least two, with
  tubular neighbourhoods.
* `Whitney.EmbeddedArcs.CornerCharts`: clean corner charts at transverse intersections and clean
  ambient charts along an arc.
* `Whitney.EmbeddedArcs.TransverseCoordinates`: the normal derivative at a transverse intersection.
* `Whitney.EmbeddedArcs.StripInterpolation`: strips with prescribed germs at the two ends.
* `Whitney.EmbeddedArcs.StripAlongArc`: a clean strip along an arc with prescribed corners.
* `Whitney.EmbeddedArcs.StripPair`: clean strip pairs along two arcs meeting at two corners.
* `Whitney.EmbeddedArcs.BeltBigon`: the specialisation to a belt sphere of an index-two surgery in a
  six-manifold.
* `Whitney.EmbeddedArcs.FiberRestriction`: restricting a fibre-preserving diffeomorphism to a
  subfibre.
* `Whitney.EmbeddedArcs.SmallPerturbation`: small weighted translations and finite composites of
  diffeomorphisms.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6 (the Whitney lemma and the
  construction of the Whitney disc).

## Tags

Morse theory, Whitney trick, handle cancellation
-/
