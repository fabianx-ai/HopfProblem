/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Additive groups on sheaf cohomology

The Ext definition of integral sheaf cohomology carries a canonical additive-group structure.
This module owns that unconditional instance for small sheaves of abelian groups on topological
spaces, so generic sheaf-cohomology developments share one discoverable declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace CategoryTheory.Sheaf

/-- The canonical additive group on Ext-defined cohomology of a small topological sheaf. -/
instance cohomologyAddCommGroup {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} F n) :=
  Ext.instAddCommGroup

end CategoryTheory.Sheaf
