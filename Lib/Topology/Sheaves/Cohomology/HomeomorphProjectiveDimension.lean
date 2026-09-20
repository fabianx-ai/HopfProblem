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

The underlying statement is that the sheaf category is invariant under homeomorphism, the
equivalence being pushforward along the homeomorphism (Godement, *Topologie algébrique et théorie
des faisceaux*, II.1).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

section Equivalence

variable {X Y : TopCat.{u}}

/-- A homeomorphism induces an equivalence of the corresponding sheaf categories. -/
def equivalenceOfIso (H : X ≅ Y) :
    TopCat.Sheaf AddCommGrpCat.{u} X ≌ TopCat.Sheaf AddCommGrpCat.{u} Y := by
  let E := TopCat.Presheaf.presheafEquivOfIso AddCommGrpCat.{u} H
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (CategoryTheory.Presheaf.IsSheaf
        (Opens.grothendieckTopology Y) :
          ObjectProperty (TopCat.Presheaf AddCommGrpCat.{u} Y)) :=
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

/-- The sheaf equivalence induced by a homeomorphism is additive. -/
instance equivalenceOfIso_functor_additive (H : X ≅ Y) :
    (equivalenceOfIso H).functor.Additive where
  map_add := by
    intros
    rfl

/-- The inverse of the sheaf equivalence induced by a homeomorphism is additive. -/
instance equivalenceOfIso_inverse_additive (H : X ≅ Y) :
    (equivalenceOfIso H).inverse.Additive where
  map_add := by
    intros
    rfl

end Equivalence

/-- On a locally connected target, the integral unit sheaf is identified with the image of the
integral unit sheaf under the sheaf equivalence induced by a homeomorphism. -/
def integralSheafEquivImageIso {X Y : TopCat.{0}} [LocallyConnectedSpace Y] (H : X ≅ Y) :
    TopCat.ConstantSheaf.integralSheaf Y ≅
      (equivalenceOfIso H).functor.obj (TopCat.ConstantSheaf.integralSheaf X) := by
  let f := TopCat.ConstantSheaf.pushforwardHom
    (AddCommGrpCat.of (ULift.{0} ℤ)) H.hom
  letI : IsIso f := TopCat.ConstantSheaf.pushforwardHom_isIso
    (AddCommGrpCat.of (ULift.{0} ℤ)) H.hom (fun U hU =>
      (TopCat.homeoOfIso H).isConnected_preimage.mpr hU)
  change TopCat.ConstantSheaf.integralSheaf Y ≅
    (pushforward AddCommGrpCat.{0} H.hom).obj (TopCat.ConstantSheaf.integralSheaf X)
  exact asIso f

/-- The projective dimension of the integral unit sheaf is invariant under homeomorphism. -/
theorem integralSheaf_hasProjectiveDimensionLT_iff_of_iso
    {X Y : TopCat.{0}} [LocallyConnectedSpace Y] (H : X ≅ Y) (n : ℕ) :
    HasProjectiveDimensionLT (TopCat.ConstantSheaf.integralSheaf X) n ↔
      HasProjectiveDimensionLT (TopCat.ConstantSheaf.integralSheaf Y) n := by
  let E := equivalenceOfIso H
  let e := integralSheafEquivImageIso H
  constructor
  · intro hX
    have hImage : HasProjectiveDimensionLT
        (E.functor.obj (TopCat.ConstantSheaf.integralSheaf X)) n :=
      CategoryTheory.Equivalence.hasProjectiveDimensionLT_functor_obj
        E (TopCat.ConstantSheaf.integralSheaf X) n hX
    let _ : HasProjectiveDimensionLT
      (E.functor.obj (TopCat.ConstantSheaf.integralSheaf X)) n := hImage
    exact hasProjectiveDimensionLT_of_iso e.symm n
  · intro hY
    let _ : HasProjectiveDimensionLT (TopCat.ConstantSheaf.integralSheaf Y) n := hY
    have hImage : HasProjectiveDimensionLT
        (E.functor.obj (TopCat.ConstantSheaf.integralSheaf X)) n :=
      hasProjectiveDimensionLT_of_iso e n
    exact (CategoryTheory.Equivalence.hasProjectiveDimensionLT_functor_obj_iff
      E (TopCat.ConstantSheaf.integralSheaf X) n).mp hImage

end TopCat.Sheaf
