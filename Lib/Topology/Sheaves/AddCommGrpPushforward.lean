/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-!
# Additivity of abelian-sheaf pushforward

Pushforward of sheaves of abelian groups along a continuous map is an additive functor: it
preserves the addition of sheaf morphisms.  This is the additivity used whenever the pushforward
is fed to a derived functor.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.4 (direct images of sheaves)
* R. Hartshorne, *Algebraic Geometry*, II.1 and III.8 (`f_*` on sheaves of abelian groups)
-/

@[expose] public section

open CategoryTheory

namespace TopCat.Sheaf

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- Pushforward of sheaves of abelian groups is an additive functor. -/
instance pushforwardAdditive :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).Additive where
  map_add := by intros; rfl

end TopCat.Sheaf
