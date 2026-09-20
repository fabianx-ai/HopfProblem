/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.PrimitivesH1
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Injectivity of the singular-cochain augmentation

The augmentation `A_X ⟶ 𝒮^0(X; A)` from the constant sheaf into the degree-zero singular-cochain
sheaf is a monomorphism (Bredon, *Sheaf Theory*, III §1; Warner 5.31): a locally constant section
is determined by its value, so the map is injective on stalks.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

private theorem presheafAugmentation_stalk_injective (x : X) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (presheafAugmentation X A)) := by
  let P := TopCat.ConstantSheaf.presheaf X A
  let Q := presheaf X A 0
  intro a b hab
  obtain ⟨U, hxU, s, rfl⟩ := P.exists_germ_eq a
  obtain ⟨V, hxV, t, rfl⟩ := P.exists_germ_eq b
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at hab
  obtain ⟨W, hxW, iWU, iWV, he⟩ := Q.germ_eq x hxU hxV _ _ hab
  change (AlgebraicTopology.SingularCochains.pullback A
      ((Opens.toTopCat X).map iWU).hom).f 0 (constantCochain U A s) =
    (AlgebraicTopology.SingularCochains.pullback A
      ((Opens.toTopCat X).map iWV).hom).f 0 (constantCochain V A t) at he
  have hconst : constantCochain W A s = constantCochain W A t :=
    (pullback_constant A ((Opens.toTopCat X).map iWU).hom s).symm.trans
      (he.trans (pullback_constant A ((Opens.toTopCat X).map iWV).hom t))
  let : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hst : s = t := constantCochain_injective W A hconst
  calc
    P.germ U x hxU s = P.germ W x hxW (P.map iWU.op s) :=
      (P.germ_res_apply iWU x hxW s).symm
    _ = P.germ W x hxW (P.map iWV.op t) := by
      congr 1
    _ = P.germ V x hxV t := P.germ_res_apply iWV x hxW t

/-- The augmentation `A_X ⟶ 𝒮^0(X; A)` of the constant sheaf into the degree-zero
singular-cochain sheaf is a monomorphism (Bredon III §1). -/
theorem sheafAugmentation_mono : Mono (sheafAugmentation X A) := by
  apply (TopCat.Presheaf.mono_iff_stalk_mono (sheafAugmentation X A)).mpr
  intro x
  let K := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let e₁ : K.obj (TopCat.ConstantSheaf.presheaf X A) ≅
      K.obj (TopCat.ConstantSheaf.sheaf X A).obj :=
    @asIso AddCommGrpCat.{0} _ _ _
      (K.map (TopCat.ConstantSheaf.unit X A))
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (TopCat.ConstantSheaf.presheaf X A))
  let e₂ : K.obj (presheaf X A 0) ≅ K.obj (sheaf X A 0).obj :=
    @asIso AddCommGrpCat.{0} _ _ _ (K.map (unit X A 0))
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (presheaf X A 0))
  have : Mono (K.map (presheafAugmentation X A)) :=
    (AddCommGrpCat.mono_iff_injective _).mpr
      (presheafAugmentation_stalk_injective X A x)
  have hsquare : e₁.hom ≫ K.map (sheafAugmentation X A).hom =
      K.map (presheafAugmentation X A) ≫ e₂.hom := by
    change K.map (TopCat.ConstantSheaf.unit X A) ≫
        K.map ((sheafification X).map (presheafAugmentation X A)).hom =
      K.map (presheafAugmentation X A) ≫ K.map (unit X A 0)
    calc
      _ = K.map (TopCat.ConstantSheaf.unit X A ≫
          ((sheafification X).map (presheafAugmentation X A)).hom) :=
        (K.map_comp _ _).symm
      _ = K.map (presheafAugmentation X A ≫ unit X A 0) :=
        congrArg K.map (toSheafify_naturality (Opens.grothendieckTopology X)
          (presheafAugmentation X A)).symm
      _ = _ := K.map_comp _ _
  have hbottom : K.map (sheafAugmentation X A).hom =
      e₁.inv ≫ K.map (presheafAugmentation X A) ≫ e₂.hom := by
    rw [← cancel_epi e₁.hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hsquare
  rw [hbottom]
  infer_instance

end TopCat.SingularCochainSheaf
