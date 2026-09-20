/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Sheafification of presheaves of abelian groups on a space

Sheafification is the left adjoint of the forgetful functor from sheaves to presheaves; on the
site of open subsets of a topological space this module fixes one name for it, together with
its additivity, so that every development in `Lib` speaks about the same functor.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.1.2
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, II.2
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

universe u

/-- Sheafification of presheaves of abelian groups on the open-set site of `X`
(Godement, *Topologie algébrique et théorie des faisceaux*, II.1.2). -/
abbrev sheafification (X : TopCat.{u}) :
    TopCat.Presheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- Sheafification of presheaves of abelian groups is additive. -/
instance sheafification_additive (X : TopCat.{u}) : (sheafification X).Additive :=
  inferInstanceAs
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive

end TopCat.Sheaf
