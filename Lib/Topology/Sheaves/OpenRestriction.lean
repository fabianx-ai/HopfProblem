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
# Exact restriction of sheaves of abelian groups to an open subspace

Restriction `F ↦ F|_U` along the inclusion of an open subspace is exact and preserves injective
objects (Hartshorne, *Algebraic Geometry*, III Lemma 6.1; Iversen, *Cohomology of Sheaves*, II.6;
Godement II.4).  Both facts come from the left adjoint, extension by zero `j_!`, which is exact and
in particular preserves monomorphisms.

## Main results

* `restriction_preservesFiniteLimits`, `restriction_preservesFiniteColimits`: restriction to an
  open subspace is exact.
* `extension_preservesMonomorphisms`: extension by zero preserves monomorphisms.
* `restriction_preservesInjectiveObjects`: restriction to an open subspace preserves injective
  sheaves (Hartshorne III Lemma 6.1).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace TopCat.Sheaf.OpenRestriction

universe u

variable {X : TopCat.{u}} (U : Opens X)

/-- The inclusion of an open subspace `U ⊆ X` as a map of topological spaces. -/
def inclusion : TopCat.of U ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of an open subspace is an open embedding. -/
theorem inclusion_isOpenEmbedding : Topology.IsOpenEmbedding (inclusion U) :=
  U.isOpenEmbedding

/-- The inclusion of an open subspace is a monomorphism of spaces. -/
instance inclusion_mono : Mono (inclusion U) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The functor taking an open of the subspace `U` to the corresponding open of `X`. -/
abbrev openImage : Opens U ⥤ Opens X := (inclusion_isOpenEmbedding U).functor

/-- The direct-image functor on opens along an open inclusion is full: an inclusion between image
opens comes from an inclusion of opens of `U`. -/
instance openImage_full : (openImage U).Full :=
  @IsOpenMap.functorFullOfMono (TopCat.of U) X (inclusion U)
    (inclusion_isOpenEmbedding U).isOpenMap (inclusion_mono U)

/-- The trace `V ∩ U` of an open `V ⊆ X` on the subspace `U`. -/
abbrev preimageOpen (V : Opens X) : Opens U := (Opens.map (inclusion U)).obj V

/-- An open of the subspace `U` has image contained in `U`. -/
theorem openImage_obj_le (V : Opens U) : (openImage U).obj V ≤ U := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- An open `V ⊆ U` of the ambient space is recovered from its trace on `U`. -/
theorem openImage_preimage {V : Opens X} (hV : V ≤ U) :
    (openImage U).obj (preimageOpen U V) = V := by
  apply Opens.ext
  change (inclusion U) '' ((inclusion U) ⁻¹' (V : Set X)) = (V : Set X)
  apply Set.image_preimage_eq_of_subset
  intro x hx
  exact ⟨⟨x, hV hx⟩, rfl⟩

/-- For an open `V` not contained in `U` there is no open of `U` whose image contains `V`, so the
diagram computing extension by zero at `V` is empty. -/
theorem costructuredArrow_isEmpty (V : Opens X) (hV : ¬ V ≤ U) :
    IsEmpty (CostructuredArrow (openImage U).op (op V)) :=
  ⟨fun a ↦ hV (a.hom.unop.le.trans (openImage_obj_le U a.left.unop))⟩

/-- Presheaf extension by zero vanishes on every open not contained in `U`. -/
theorem lan_obj_isZero_of_not_le (F : (Opens U)ᵒᵖ ⥤ AddCommGrpCat)
    (V : Opens X) (hV : ¬ V ≤ U) :
    IsZero (((openImage U).op.lan.obj F).obj (op V)) := by
  let := costructuredArrow_isEmpty U V hV
  let D := CostructuredArrow.proj (openImage U).op (op V) ⋙ F
  have hz : IsZero (colimit D) :=
    ((isColimitEquivIsInitialOfIsEmpty AddCommGrpCat (colimit.cocone D))
      (colimit.isColimit D)).isZero
  exact hz.of_iso ((openImage U).op.leftKanExtensionObjIsoColimit F (op V))

/-- Presheaf extension by zero `j_!` preserves monomorphisms: on opens inside `U` it is the given
map, and outside `U` it is a map out of the zero group. -/
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

/-- The direct-image functor on opens along an open inclusion is continuous for the open-cover
topologies. -/
instance openImage_continuous :
    (openImage U).IsContinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) :=
  (inclusion_isOpenEmbedding U).functor_isContinuous

/-- The direct-image functor on opens along an open inclusion is cocontinuous: every cover of an
image open is refined by the image of a cover of an open of `U`. -/
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

/-- Restriction `F ↦ F|_U` of sheaves of abelian groups to the open subspace `U`. -/
abbrev restriction : TopCat.Sheaf AddCommGrpCat.{u} X ⥤
    TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of U) :=
  (openImage U).sheafPushforwardContinuous AddCommGrpCat
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)

/-- This restriction functor is Mathlib's `Opens.sheafRestrict`. -/
theorem restriction_eq_sheafRestrict : restriction U = U.sheafRestrict := rfl

/-- Restriction to an open subspace is an additive functor. -/
instance restriction_additive : (restriction U).Additive where
  map_add := by intros; rfl

/-- Restriction to an open subspace is a right adjoint, namely of extension by zero `j_!`. -/
instance restriction_rightAdjoint : (restriction U).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (openImage U)
    AddCommGrpCat (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).isRightAdjoint

/-- Restriction to an open subspace is also a left adjoint, namely of the pushforward `j_*`. -/
instance restriction_leftAdjoint : (restriction U).IsLeftAdjoint :=
  ((openImage U).sheafAdjunctionCocontinuous AddCommGrpCat
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).isLeftAdjoint

/-- Restriction to an open subspace is left exact (Iversen II.6). -/
theorem restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction U) := by
  infer_instance

/-- Restriction to an open subspace is right exact (Iversen II.6). -/
theorem restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction U) := by
  infer_instance

/-- Extension by zero `j_!` from the open subspace `U`, the left adjoint of restriction. -/
abbrev extension : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of U) ⥤
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  Functor.sheafPullbackConstruction.sheafPullback (openImage U) AddCommGrpCat
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)

set_option synthInstance.maxHeartbeats 80000 in
/-- Extension by zero preserves monomorphisms. -/
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

/-- Restriction to an open subspace preserves injective sheaves, because its left adjoint
`j_!` preserves monomorphisms (Hartshorne III Lemma 6.1). -/
instance restriction_preservesInjectiveObjects : (restriction U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (openImage U)
      AddCommGrpCat (Opens.grothendieckTopology U) (Opens.grothendieckTopology X))

end TopCat.Sheaf.OpenRestriction
