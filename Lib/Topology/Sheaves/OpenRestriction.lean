/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Over

/-!
# Exact restriction of additive sheaves to an open subspace

Restriction along an open inclusion is exact and preserves injective objects.  The proof builds
extension by zero as sheafified left Kan extension and proves that the presheaf Kan extension
preserves monomorphisms by separating opens contained in the subspace from opens outside it.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{0}} (U : Opens X)

/-- The open-subspace inclusion. -/
def inclusion : TopCat.of U ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem inclusion_isOpenEmbedding : Topology.IsOpenEmbedding (inclusion U) :=
  U.isOpenEmbedding

instance inclusion_mono : Mono (inclusion U) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

/-- Direct image of open sets along the open inclusion. -/
abbrev openImage : Opens U ⥤ Opens X := (inclusion_isOpenEmbedding U).functor

instance openImage_full : (openImage U).Full :=
  @IsOpenMap.functorFullOfMono (TopCat.of U) X (inclusion U)
    (inclusion_isOpenEmbedding U).isOpenMap (inclusion_mono U)

/-- Preimage of an ambient open in the open subspace. -/
abbrev preimageOpen (V : Opens X) : Opens U := (Opens.map (inclusion U)).obj V

theorem openImage_obj_le (V : Opens U) : (openImage U).obj V ≤ U := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem openImage_preimage {V : Opens X} (hV : V ≤ U) :
    (openImage U).obj (preimageOpen U V) = V := by
  apply Opens.ext
  change (inclusion U) '' ((inclusion U) ⁻¹' (V : Set X)) = (V : Set X)
  apply Set.image_preimage_eq_of_subset
  intro x hx
  exact ⟨⟨x, hV hx⟩, rfl⟩

/-- Outside the open subspace, the pointwise extension diagram is empty. -/
theorem costructuredArrow_isEmpty (V : Opens X) (hV : ¬ V ≤ U) :
    IsEmpty (CostructuredArrow (openImage U).op (op V)) :=
  ⟨fun a ↦ hV (a.hom.unop.le.trans (openImage_obj_le U a.left.unop))⟩

/-- Left Kan extension along the open inclusion is zero off opens contained in the subspace. -/
theorem lan_obj_isZero_of_not_le (F : (Opens U)ᵒᵖ ⥤ AddCommGrpCat)
    (V : Opens X) (hV : ¬ V ≤ U) :
    IsZero (((openImage U).op.lan.obj F).obj (op V)) := by
  let := costructuredArrow_isEmpty U V hV
  let D := CostructuredArrow.proj (openImage U).op (op V) ⋙ F
  have hz : IsZero (colimit D) :=
    ((isColimitEquivIsInitialOfIsEmpty AddCommGrpCat (colimit.cocone D))
      (colimit.isColimit D)).isZero
  exact hz.of_iso ((openImage U).op.leftKanExtensionObjIsoColimit F (op V))

/-- Presheaf extension by zero preserves monomorphisms. -/
instance lan_preservesMonomorphisms :
    ((openImage U).op.lan : ((Opens U)ᵒᵖ ⥤ AddCommGrpCat) ⥤
      ((Opens X)ᵒᵖ ⥤ AddCommGrpCat)).PreservesMonomorphisms where
  preserves {F G} f _ := by
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro V
    by_cases hV : V.unop ≤ U
    · let W := op (preimageOpen U V.unop)
      have hv : (openImage U).op.obj W = V :=
        congrArg op (openImage_preimage U hV)
      rw [← hv]
      let ηF := ((openImage U).op.lanUnit.app F).app W
      let ηG := ((openImage U).op.lanUnit.app G).app W
      have : IsIso ηF := by dsimp [ηF]; infer_instance
      have : IsIso ηG := by dsimp [ηG]; infer_instance
      have he : ((openImage U).op.lan.map f).app ((openImage U).op.obj W) =
          inv ηF ≫ f.app W ≫ ηG := by
        apply (cancel_epi ηF).mp
        rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        exact (NatTrans.congr_app ((openImage U).op.lanUnit.naturality f) W).symm
      rw [he]
      infer_instance
    · exact (lan_obj_isZero_of_not_le U F V.unop hV).mono _

instance openImage_continuous :
    (openImage U).IsContinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) :=
  (inclusion_isOpenEmbedding U).functor_isContinuous

/-- Covers lift along an open inclusion. -/
instance openImage_cocontinuous :
    (openImage U).IsCocontinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) where
  cover_lift {V S} hS := by
    intro x hx
    obtain ⟨W, i, hi, hxW⟩ := hS x.val ⟨x, hx, rfl⟩
    let W' := preimageOpen U W
    have hW'V : W' ≤ V := by
      intro y hy
      obtain ⟨z, hz, he⟩ := i.le hy
      have hzy : z = y := Subtype.ext he
      exact hzy ▸ hz
    let k : (openImage U).obj W' ⟶ W := homOfLE (by
      rintro y ⟨z, hz, rfl⟩
      exact hz)
    refine ⟨W', homOfLE hW'V, ?_, hxW⟩
    exact S.downward_closed hi k

/-- Restriction of additive sheaves to the open subspace. -/
abbrev restriction : TopCat.Sheaf AddCommGrpCat.{0} X ⥤
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of U) :=
  (openImage U).sheafPushforwardContinuous AddCommGrpCat
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)

theorem restriction_eq_sheafRestrict : restriction U = U.sheafRestrict := rfl

instance restriction_additive : (restriction U).Additive where
  map_add := by intros; rfl

instance restriction_rightAdjoint : (restriction U).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (openImage U)
    AddCommGrpCat (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).isRightAdjoint

instance restriction_leftAdjoint : (restriction U).IsLeftAdjoint :=
  ((openImage U).sheafAdjunctionCocontinuous AddCommGrpCat
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).isLeftAdjoint

theorem restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction U) := by
  infer_instance

theorem restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction U) := by
  infer_instance

/-- Sheafified extension by zero from the open subspace. -/
abbrev extension : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of U) ⥤
    TopCat.Sheaf AddCommGrpCat.{0} X :=
  Functor.sheafPullbackConstruction.sheafPullback (openImage U) AddCommGrpCat
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)

instance extension_preservesMonomorphisms : (extension U).PreservesMonomorphisms := by
  have : (sheafToPresheaf (Opens.grothendieckTopology U)
      AddCommGrpCat).PreservesMonomorphisms := by infer_instance
  have : ((openImage U).op.lan : ((Opens U)ᵒᵖ ⥤ AddCommGrpCat) ⥤
      ((Opens X)ᵒᵖ ⥤ AddCommGrpCat)).PreservesMonomorphisms := by infer_instance
  have : (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat).PreservesMonomorphisms := by infer_instance
  change (sheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat ⋙
    (openImage U).op.lan ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).PreservesMonomorphisms
  infer_instance

/-- Open restriction preserves injective additive sheaves. -/
instance restriction_preservesInjectiveObjects : (restriction U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (openImage U)
      AddCommGrpCat (Opens.grothendieckTopology U) (Opens.grothendieckTopology X))

end TopCat.Sheaf.OpenRestriction
