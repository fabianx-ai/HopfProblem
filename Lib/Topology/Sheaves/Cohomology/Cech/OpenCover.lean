/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sets.OpenCover

/-!
# The fixed-cover Čech complex of an open cover

This file connects an indexed topological open cover to Mathlib's fixed-family Čech construction.
It provides the alternating Čech complex and its degreewise cohomology as functors on presheaves
and sheaves.

This is the Čech complex of Godement, *Topologie algébrique et théorie des faisceaux*, II.5.1,
wrapped around Mathlib's `CategoryTheory.cechComplexFunctor` for topological open covers.

Mathlib's `CategoryTheory.cechComplexFunctor` is the all-tuples alternating complex: in degree
`n`, its factors are indexed by all maps `Fin (n + 1) → ι`, including maps with repeated values.
Thus the definitions here are deliberately not called normalized complexes and require no order
on `ι`. Comparing this complex with the strictly-increasing-index normalized Čech complex is a
separate theorem.

These are fixed-cover constructions. Nothing in this file claims that one open cover computes
derived sheaf cohomology, and no refinement or direct-limit construction is introduced here.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace TopologicalSpace.IsOpenCover

variable {X : TopCat.{u}} {ι : Type u} {U : ι → TopologicalSpace.Opens X}
variable (A : Type v) [Category.{w} A] [Preadditive A] [HasProducts.{u} A]

/-- The fixed-cover Čech complex functor of an indexed open cover, acting on presheaves.

The cover hypothesis records the topological meaning of `U`; Mathlib's underlying fixed-family
construction itself is defined for an arbitrary family of objects. -/
noncomputable def presheafCechComplexFunctor
    (_hU : TopologicalSpace.IsOpenCover U) :
    TopCat.Presheaf A X ⥤ CochainComplex A ℕ :=
  CategoryTheory.cechComplexFunctor U

/-- The fixed-cover Čech complex functor of an indexed open cover, acting on sheaves by forgetting
the sheaf condition. -/
noncomputable def sheafCechComplexFunctor
    (hU : TopologicalSpace.IsOpenCover U) :
    TopCat.Sheaf A X ⥤ CochainComplex A ℕ :=
  TopCat.Sheaf.forget A X ⋙ hU.presheafCechComplexFunctor A

/-- The Čech complex of a presheaf is Mathlib's fixed-family alternating complex of the cover. -/
@[simp]
theorem presheafCechComplexFunctor_obj
    (hU : TopologicalSpace.IsOpenCover U) (P : TopCat.Presheaf A X) :
    (hU.presheafCechComplexFunctor A).obj P =
      (CategoryTheory.cechComplexFunctor U).obj P :=
  rfl

/-- The Čech complex of a sheaf is the Čech complex of its underlying presheaf. -/
@[simp]
theorem sheafCechComplexFunctor_obj
    (hU : TopologicalSpace.IsOpenCover U) (F : TopCat.Sheaf A X) :
    (hU.sheafCechComplexFunctor A).obj F =
      (CategoryTheory.cechComplexFunctor U).obj F.presheaf :=
  rfl

variable [CategoryWithHomology A]

/-- Degree-`n` fixed-cover Čech cohomology as a functor on presheaves. -/
noncomputable def presheafCechCohomologyFunctor
    (hU : TopologicalSpace.IsOpenCover U) (n : ℕ) :
    TopCat.Presheaf A X ⥤ A :=
  hU.presheafCechComplexFunctor A ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n

/-- Degree-`n` fixed-cover Čech cohomology as a functor on sheaves. -/
noncomputable def sheafCechCohomologyFunctor
    (hU : TopologicalSpace.IsOpenCover U) (n : ℕ) :
    TopCat.Sheaf A X ⥤ A :=
  TopCat.Sheaf.forget A X ⋙ hU.presheafCechCohomologyFunctor A n

/-- Degree-`n` Čech cohomology of a presheaf is the degree-`n` homology of its Čech complex. -/
@[simp]
theorem presheafCechCohomologyFunctor_obj
    (hU : TopologicalSpace.IsOpenCover U) (P : TopCat.Presheaf A X) (n : ℕ) :
    (hU.presheafCechCohomologyFunctor A n).obj P =
      ((CategoryTheory.cechComplexFunctor U).obj P).homology n :=
  rfl

/-- Degree-`n` Čech cohomology of a sheaf is computed from its underlying presheaf. -/
@[simp]
theorem sheafCechCohomologyFunctor_obj
    (hU : TopologicalSpace.IsOpenCover U) (F : TopCat.Sheaf A X) (n : ℕ) :
    (hU.sheafCechCohomologyFunctor A n).obj F =
      ((CategoryTheory.cechComplexFunctor U).obj F.presheaf).homology n :=
  rfl

end TopologicalSpace.IsOpenCover
