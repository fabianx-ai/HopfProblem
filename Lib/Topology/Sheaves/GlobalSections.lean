/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Topology.Sheaves.Abelian

/-!
# The global-sections functor on abelian sheaves

Evaluation on the top open is the global-sections functor `Γ(X, -)` of sheaves of abelian
groups on a topological space, and it is additive.  This module owns that single declaration
so that every sheaf-cohomology development in `Lib` speaks about the same functor; it is the
functor whose right derived functors are sheaf cohomology.

## References

* R. Hartshorne, *Algebraic Geometry*, II.1 and III.2
* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.2
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Sheaf

universe u

/-- The global-sections functor `Γ(X, -) : F ↦ F(⊤)` on sheaves of abelian groups
(Hartshorne, *Algebraic Geometry*, II.1). -/
def globalSectionsFunctor (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op (⊤ : Opens X))

/-- The global-sections functor on abelian sheaves is additive. -/
instance globalSectionsFunctor_additive (X : TopCat.{u}) :
    (globalSectionsFunctor X).Additive where
  map_add := by intros; rfl

end TopCat.Sheaf
