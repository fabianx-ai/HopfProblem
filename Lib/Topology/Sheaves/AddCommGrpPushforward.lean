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

Pushforward along a continuous map is additive on sheaves of abelian groups.  This unconditional
instance is owned here so that generic sheaf and derived-functor developments share one canonical
typeclass declaration.
-/

@[expose] public section

open CategoryTheory

namespace TopCat.Sheaf

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- Pushforward of sheaves of abelian groups is an additive functor. -/
instance pushforwardAdditive :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).Additive where
  map_add := by intros; rfl

end TopCat.Sheaf
