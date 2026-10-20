/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.CohomologySystem
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Cech cohomology as a refinement-directed colimit

For a coefficient presheaf and a degree, Cech cohomology `Ȟⁿ(X, P)` is the colimit of normalized
ordered Cech cohomology over the filtered preorder of set-valued open covers.  This file defines
that colimit and exposes the canonical map from each fixed cover, its compatibility with
refinement, and the colimit universal property.

For concrete target categories whose forgetful functor preserves this filtered colimit, the final
section records the elementwise description of a filtered colimit: two classes from a fixed cover
have the same image precisely when they agree after a refinement, and for abelian-group
coefficients a class maps to zero precisely when it dies after a refinement.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.5.8
* G. E. Bredon, *Sheaf Theory*, III.4
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w t s

namespace TopologicalSpace.OpenCover.SetOpenCover

variable {X : TopCat.{u}}
variable {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{u} A]
variable [CategoryWithHomology A] [HasColimitsOfShape (SetOpenCover X) A]

/-- Degree-`n` Cech cohomology, defined as the refinement-directed colimit of normalized
fixed-cover Cech cohomology. -/
noncomputable def cechCohomology (P : TopCat.Presheaf A X) (n : ℕ) : A :=
  colimit (normalizedCechCohomologyFunctor P n)

/-- The canonical map from normalized Cech cohomology on one cover to direct-limit Cech
cohomology. -/
noncomputable def toCechCohomology (P : TopCat.Presheaf A X) (n : ℕ)
    (U : SetOpenCover X) :
    normalizedCechCohomology P U n ⟶ cechCohomology P n :=
  colimit.ι (normalizedCechCohomologyFunctor P n) U

/-- The canonical maps to Cech cohomology are compatible with refinement. -/
@[reassoc (attr := simp)]
theorem normalizedCechCohomologyMap_comp_toCechCohomology
    (P : TopCat.Presheaf A X) (n : ℕ) {U V : SetOpenCover X} (h : U ≤ V) :
    normalizedCechCohomologyMap P h n ≫ toCechCohomology P n V =
      toCechCohomology P n U := by
  exact colimit.w (normalizedCechCohomologyFunctor P n) (homOfLE h)

/-- A compatible family of maps out of fixed-cover Cech cohomology forms a cocone over the
refinement-directed system. -/
noncomputable def cechCohomologyCocone (P : TopCat.Presheaf A X) (n : ℕ) (Q : A)
    (f : ∀ U : SetOpenCover X, normalizedCechCohomology P U n ⟶ Q)
    (hf : ∀ {U V : SetOpenCover X} (h : U ≤ V),
      normalizedCechCohomologyMap P h n ≫ f V = f U) :
    Cocone (normalizedCechCohomologyFunctor P n) where
  pt := Q
  ι :=
    { app := f
      naturality := by
        intro U V g
        simpa using hf (leOfHom g) }

/-- The map out of direct-limit Cech cohomology induced by a compatible family on fixed covers. -/
noncomputable def cechCohomologyDesc (P : TopCat.Presheaf A X) (n : ℕ) (Q : A)
    (f : ∀ U : SetOpenCover X, normalizedCechCohomology P U n ⟶ Q)
    (hf : ∀ {U V : SetOpenCover X} (h : U ≤ V),
      normalizedCechCohomologyMap P h n ≫ f V = f U) :
    cechCohomology P n ⟶ Q :=
  colimit.desc (normalizedCechCohomologyFunctor P n)
    (cechCohomologyCocone P n Q f hf)

/-- The induced map from the colimit restricts to the original map on every fixed cover. -/
@[reassoc (attr := simp)]
theorem toCechCohomology_comp_cechCohomologyDesc
    (P : TopCat.Presheaf A X) (n : ℕ) (Q : A)
    (f : ∀ U : SetOpenCover X, normalizedCechCohomology P U n ⟶ Q)
    (hf : ∀ {U V : SetOpenCover X} (h : U ≤ V),
      normalizedCechCohomologyMap P h n ≫ f V = f U)
    (U : SetOpenCover X) :
    toCechCohomology P n U ≫ cechCohomologyDesc P n Q f hf = f U := by
  exact colimit.ι_desc (cechCohomologyCocone P n Q f hf) U

/-- Maps out of Cech cohomology are determined by their restrictions to all fixed covers. -/
theorem cechCohomology_hom_ext (P : TopCat.Presheaf A X) (n : ℕ) {Q : A}
    {f g : cechCohomology P n ⟶ Q}
    (h : ∀ U : SetOpenCover X,
      toCechCohomology P n U ≫ f = toCechCohomology P n U ≫ g) :
    f = g :=
  colimit.hom_ext h

/-- The extension of a compatible family is the unique map with the prescribed restrictions. -/
theorem cechCohomologyDesc_unique (P : TopCat.Presheaf A X) (n : ℕ) (Q : A)
    (f : ∀ U : SetOpenCover X, normalizedCechCohomology P U n ⟶ Q)
    (hf : ∀ {U V : SetOpenCover X} (h : U ≤ V),
      normalizedCechCohomologyMap P h n ≫ f V = f U)
    {g : cechCohomology P n ⟶ Q}
    (hg : ∀ U : SetOpenCover X, toCechCohomology P n U ≫ g = f U) :
    g = cechCohomologyDesc P n Q f hf := by
  apply cechCohomology_hom_ext P n
  intro U
  rw [hg U, toCechCohomology_comp_cechCohomologyDesc]

section Elements

variable {FC : A → A → Type t} {CC : A → Type s}
variable [∀ Y Z : A, FunLike (FC Y Z) (CC Y) (CC Z)] [ConcreteCategory A FC]

/-- Every element of direct-limit Cech cohomology is represented on some fixed open cover. -/
theorem cechCohomology_exists_rep (P : TopCat.Presheaf A X) (n : ℕ)
    [PreservesColimit (normalizedCechCohomologyFunctor P n) (forget A)]
    (x : ToType (cechCohomology P n)) :
    ∃ (U : SetOpenCover X) (y : ToType (normalizedCechCohomology P U n)),
      toCechCohomology P n U y = x := by
  exact Concrete.colimit_exists_rep (normalizedCechCohomologyFunctor P n) x

/-- Two fixed-cover classes have the same image in Cech cohomology precisely when their images
agree on a common refinement. -/
theorem toCechCohomology_apply_eq_iff (P : TopCat.Presheaf A X) (n : ℕ)
    [PreservesColimit (normalizedCechCohomologyFunctor P n) (forget A)]
    {U V : SetOpenCover X} (x : ToType (normalizedCechCohomology P U n))
    (y : ToType (normalizedCechCohomology P V n)) :
    toCechCohomology P n U x = toCechCohomology P n V y ↔
      ∃ (W : SetOpenCover X) (f : U ⟶ W) (g : V ⟶ W),
        normalizedCechCohomologyMap P (leOfHom f) n x =
          normalizedCechCohomologyMap P (leOfHom g) n y := by
  exact Concrete.colimit_rep_eq_iff_exists
    (normalizedCechCohomologyFunctor P n) x y

/-- Two classes represented on the same cover agree in Cech cohomology precisely when they agree
after one refinement of that cover. -/
theorem toCechCohomology_apply_eq_iff_exists_refinement
    (P : TopCat.Presheaf A X) (n : ℕ)
    [PreservesColimit (normalizedCechCohomologyFunctor P n) (forget A)]
    {U : SetOpenCover X} (x y : ToType (normalizedCechCohomology P U n)) :
    toCechCohomology P n U x = toCechCohomology P n U y ↔
      ∃ (V : SetOpenCover X) (h : U ≤ V),
        normalizedCechCohomologyMap P h n x = normalizedCechCohomologyMap P h n y := by
  rw [toCechCohomology_apply_eq_iff]
  constructor
  · rintro ⟨V, f, g, hfg⟩
    have hfg' : f = g := Subsingleton.elim _ _
    subst g
    exact ⟨V, leOfHom f, hfg⟩
  · rintro ⟨V, h, hxy⟩
    exact ⟨V, homOfLE h, homOfLE h, hxy⟩

section Zero

variable [∀ Y : A, Zero (CC Y)]
variable [∀ Y Z : A, ZeroHomClass (FC Y Z) (CC Y) (CC Z)]

/-- In a concrete category whose morphisms preserve zero, a fixed-cover class is zero in
direct-limit Cech cohomology if and only if it becomes zero after some refinement. -/
theorem toCechCohomology_apply_eq_zero_iff (P : TopCat.Presheaf A X) (n : ℕ)
    [PreservesColimit (normalizedCechCohomologyFunctor P n) (forget A)]
    {U : SetOpenCover X} (x : ToType (normalizedCechCohomology P U n)) :
    toCechCohomology P n U x = 0 ↔
      ∃ (V : SetOpenCover X) (h : U ≤ V),
        normalizedCechCohomologyMap P h n x = 0 := by
  rw [← map_zero (ConcreteCategory.hom (toCechCohomology P n U)),
    toCechCohomology_apply_eq_iff_exists_refinement]
  simp

/-- A class which dies after a refinement maps to zero in direct-limit Cech cohomology. -/
theorem toCechCohomology_apply_eq_zero_of_refinement (P : TopCat.Presheaf A X) (n : ℕ)
    {U V : SetOpenCover X} (h : U ≤ V)
    (x : ToType (normalizedCechCohomology P U n))
    (hx : normalizedCechCohomologyMap P h n x = 0) :
    toCechCohomology P n U x = 0 := by
  calc
    toCechCohomology P n U x =
        (normalizedCechCohomologyMap P h n ≫ toCechCohomology P n V) x :=
      ConcreteCategory.congr_hom
        (normalizedCechCohomologyMap_comp_toCechCohomology P n h).symm x
    _ = toCechCohomology P n V (normalizedCechCohomologyMap P h n x) :=
      ConcreteCategory.comp_apply _ _ x
    _ = toCechCohomology P n V 0 := by rw [hx]
    _ = 0 := map_zero (ConcreteCategory.hom (toCechCohomology P n V))

end Zero

end Elements

end TopologicalSpace.OpenCover.SetOpenCover
