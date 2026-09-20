/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

import Lib.CategoryTheory.Sites.Leray.SheafificationNeighborhoodGerm
public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.CanonicalPositive
public import Lib.Topology.Sheaves.SheafificationLocal

/-!
# Canonical actual sections representing positive-degree Ext neighborhood germs

A normalized Ext class over an inverse-image neighborhood first gives a resolution-homology
class.  Applying the sheafification unit and the inverse higher-direct-image resolution
comparison produces a canonical section of the actual higher-direct-image sheaf on the same
base neighborhood.  Its ordinary sheaf germ is exactly the normalized derived Ext germ.

This is a generic positive-degree sheafification construction. It neither asserts proper base
change nor identifies a higher-direct-image stalk with the cohomology of a geometric fibre.

The underlying textbook fact is that `Rⁱf_*F` is the sheaf associated to the presheaf
`V ↦ Hⁱ(f⁻¹V, F)`: Hartshorne, *Algebraic Geometry* III.8.1; Godement II.4.11.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace

namespace CategoryTheory.Sheaf.Leray.FibreStalkEvaluation

variable {X Y : TopCat.{0}} {F : AbelianSheaf X}

/-- The actual higher-direct-image section canonically represented by a normalized positive-
degree Ext class on one neighborhood. -/
def canonicalDerivedNeighborhoodSectionPositive
    (f : X ⟶ Y) (I : InjectiveResolution F) (n : ℕ) (U : Opens Y) :
    (sourceCohomologyPresheaf (F := F) f (n + 1)).obj (op U) ⟶
      (higherDirectImageSheaf f F (n + 1)).obj.obj (op U) :=
  let ρ := canonicalResolutionCohomologyNormalizationPositive f I n
  let P := homologyPresheaf (pushedResolution f I) (n + 1)
  ρ.inv.app (op U) ≫
    (TopCat.SheafificationLocal.unit P).app (op U) ≫
    (higherDirectImageResolutionSheafificationIso f F I (n + 1)).inv.hom.app (op U)

set_option backward.isDefEq.respectTransparency false in
/-- The germ of the canonical actual section is the normalized positive-degree Ext neighborhood
germ. -/
theorem canonicalDerivedNeighborhoodSectionPositive_comp_germ
    (f : X ⟶ Y) (y : Y) (I : InjectiveResolution F) (n : ℕ)
    (U : Opens Y) (hy : y ∈ U) :
    canonicalDerivedNeighborhoodSectionPositive f I n U ≫
        (higherDirectImageSheaf f F (n + 1)).presheaf.germ U y hy =
      canonicalDerivedNeighborhoodGermPositive f y I n U hy := by
  ext a
  let ρ := canonicalResolutionCohomologyNormalizationPositive f I n
  let P := homologyPresheaf (pushedResolution f I) (n + 1)
  let ι := TopCat.SheafificationLocal.unit P
  let e := higherDirectImageResolutionSheafificationIso f F I (n + 1)
  let eP := (TopCat.Sheaf.forget AddCommGrpCat Y).mapIso e
  let t := ρ.inv.app (op U) a
  let s := e.inv.hom.app (op U) (ι.app (op U) t)
  have ha : ρ.hom.app (op U) t = a := by
    change ρ.hom.app (op U) (ρ.inv.app (op U) a) = a
    rw [← ConcreteCategory.comp_apply, ρ.inv_hom_id_app]
    rfl
  have he :
      e.inv.hom.app (op U) ≫ e.hom.hom.app (op U) = 𝟙 _ := by
    change eP.inv.app (op U) ≫ eP.hom.app (op U) = 𝟙 _
    exact eP.inv_hom_id_app (op U)
  have he_apply :
      e.hom.hom.app (op U) (e.inv.hom.app (op U) (ι.app (op U) t)) =
        ι.app (op U) t := by
    have he' := ConcreteCategory.congr_hom he (ι.app (op U) t)
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using he'
  have hrep :
      ι.app (op U) t =
        (TopCat.SheafificationLocal.sheaf P).obj.map (homOfLE (le_refl U)).op
          (e.hom.hom.app (op U) s) := by
    dsimp only [s]
    rw [he_apply]
    simp
  have hlocal :=
    CategoryTheory.Sheaf.Leray.derivedNeighborhoodGerm_eq_germ_of_localRepresentative
      f F I (n + 1) ρ (le_refl U) s t hrep y hy
  rw [ha] at hlocal
  exact hlocal.symm

end CategoryTheory.Sheaf.Leray.FibreStalkEvaluation
