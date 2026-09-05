/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Abelian.Projective.DimensionEquivalence
public import Lib.Topology.Sheaves.ConstantPushforward.GlobalSections
public import Lib.Topology.Sheaves.Cohomology.AcyclicResolutionH1

/-!
# Sheaf projective dimension under homeomorphism

Homeomorphic spaces have equivalent categories of additive sheaves, and hence the same
projective-dimension bound for their integral unit sheaves.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.Sheaf

/-- A homeomorphism induces an equivalence of the corresponding sheaf categories. -/
def equivalenceOfIso {X Y : TopCat.{0}} (H : X ≅ Y) :
    TopCat.Sheaf AddCommGrpCat.{0} X ≌ TopCat.Sheaf AddCommGrpCat.{0} Y := by
  let E := TopCat.Presheaf.presheafEquivOfIso AddCommGrpCat.{0} H
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (CategoryTheory.Presheaf.IsSheaf
        (Opens.grothendieckTopology Y) :
          ObjectProperty (TopCat.Presheaf AddCommGrpCat.{0} Y)) :=
    { of_iso := fun e h => (TopCat.Presheaf.isSheaf_iso_iff e).mp h }
  apply E.congrFullSubcategory
  ext F
  constructor
  · intro hEF
    have hback := pushforward_sheaf_of_sheaf H.inv hEF
    change TopCat.Presheaf.IsSheaf (E.inverse.obj (E.functor.obj F)) at hback
    exact (TopCat.Presheaf.isSheaf_iso_iff (E.unitIso.app F)).mpr hback
  · intro hF
    exact pushforward_sheaf_of_sheaf H.hom hF

instance equivalenceOfIso_functor_additive {X Y : TopCat.{0}} (H : X ≅ Y) :
    (equivalenceOfIso H).functor.Additive where
  map_add := by
    intros
    rfl

instance equivalenceOfIso_inverse_additive {X Y : TopCat.{0}} (H : X ≅ Y) :
    (equivalenceOfIso H).inverse.Additive where
  map_add := by
    intros
    rfl

/-- On a locally connected target, the integral unit sheaf is identified with the image of the
integral unit sheaf under the sheaf equivalence induced by a homeomorphism. -/
def unitSheafEquivImageIso {X Y : TopCat.{0}} [LocallyConnectedSpace Y] (H : X ≅ Y) :
    TopCat.SheafH1.unitSheaf Y ≅
      (equivalenceOfIso H).functor.obj (TopCat.SheafH1.unitSheaf X) := by
  let f := TopCat.ConstantSheaf.pushforwardHom
    (AddCommGrpCat.of (ULift.{0} ℤ)) H.hom
  letI : IsIso f := TopCat.ConstantSheaf.pushforwardHom_isIso
    (AddCommGrpCat.of (ULift.{0} ℤ)) H.hom (fun U hU =>
      (TopCat.homeoOfIso H).isConnected_preimage.mpr hU)
  change TopCat.ConstantSheaf.integralSheaf Y ≅
    (pushforward AddCommGrpCat.{0} H.hom).obj (TopCat.ConstantSheaf.integralSheaf X)
  exact asIso f

/-- The projective dimension of the integral unit sheaf is invariant under homeomorphism. -/
theorem unitSheaf_hasProjectiveDimensionLT_iff_of_iso
    {X Y : TopCat.{0}} [LocallyConnectedSpace Y] (H : X ≅ Y) (n : ℕ) :
    HasProjectiveDimensionLT (TopCat.SheafH1.unitSheaf X) n ↔
      HasProjectiveDimensionLT (TopCat.SheafH1.unitSheaf Y) n := by
  let E := equivalenceOfIso H
  let e := unitSheafEquivImageIso H
  constructor
  · intro hX
    have hImage : HasProjectiveDimensionLT
        (E.functor.obj (TopCat.SheafH1.unitSheaf X)) n :=
      CategoryTheory.Equivalence.hasProjectiveDimensionLT_functor_obj
        E (TopCat.SheafH1.unitSheaf X) n hX
    let _ : HasProjectiveDimensionLT
      (E.functor.obj (TopCat.SheafH1.unitSheaf X)) n := hImage
    exact hasProjectiveDimensionLT_of_iso e.symm n
  · intro hY
    let _ : HasProjectiveDimensionLT (TopCat.SheafH1.unitSheaf Y) n := hY
    have hImage : HasProjectiveDimensionLT
        (E.functor.obj (TopCat.SheafH1.unitSheaf X)) n :=
      hasProjectiveDimensionLT_of_iso e n
    exact (CategoryTheory.Equivalence.hasProjectiveDimensionLT_functor_obj_iff
      E (TopCat.SheafH1.unitSheaf X) n).mp hImage

end TopCat.Sheaf
