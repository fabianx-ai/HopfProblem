/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.ConstantCohomologyPullback
public import Lib.Topology.Sheaves.OpenEmbeddingCohomology

/-!
# Factoring finite-closed pullback through an open embedding

Suppose a map `f : T ⟶ X` factors as `f = s ≫ h` with `s : T ⟶ V` a finite closed map and
`h : V ⟶ X` an open embedding.  Then `(f_*F)|_V = s_*F`, because restriction to an open subspace
commutes with pushforward along a map into that subspace (Hartshorne, *Algebraic Geometry*, II §1;
Iversen, *Cohomology of Sheaves*, II).  Consequently pullback `f^*` on constant-coefficient sheaf
cohomology is restriction to `V` followed by `s^*`; this is the functoriality
`(s ≫ h)^* = s^* ∘ h^*` of constant-coefficient pullback, in every degree and for every
coefficient group.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf.OpenFiniteClosedFactorization

variable {T V X : TopCat.{u}}
  (f : T ⟶ X)
  (h : V ⟶ X) (hh : Topology.IsOpenEmbedding h)
  (s : T ⟶ V) (hcomp : s ≫ h = f)

include hcomp in
/-- The inverse image of the open image of `W` under `f` is its inverse image under the
factoring map `s`. -/
theorem openImage_preimage_obj (W : Opens V) :
    ((OpenEmbeddingCohomology.openImage h hh ⋙ Opens.map f).obj W) =
      (Opens.map s).obj W := by
  ext x
  change (∃ v : V, v ∈ W ∧ h v = f x) ↔ s x ∈ W
  constructor
  · rintro ⟨v, hv, hvx⟩
    have he : v = s x := hh.injective
      (hvx.trans (ConcreteCategory.congr_hom hcomp x).symm)
    simpa [he] using hv
  · intro hx
    exact ⟨s x, hx, ConcreteCategory.congr_hom hcomp x⟩

include hcomp in
/-- Functorial form of `openImage_preimage_obj`. -/
theorem openImage_preimage :
    OpenEmbeddingCohomology.openImage h hh ⋙ Opens.map f = Opens.map s :=
  CategoryTheory.Functor.ext (openImage_preimage_obj f h hh s hcomp)
    (fun _ _ _ ↦ Subsingleton.elim _ _)

include hcomp in
/-- Restricting pushforward along `f` to the open image of `h` is pushforward along `s`. -/
def restrictionPushforwardIso :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
        OpenEmbeddingCohomology.restriction h hh ≅
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} s := by
  let _ : (Opens.map s).IsContinuous
      (Opens.grothendieckTopology V)
      (Opens.grothendieckTopology T) := by
    exact CategoryTheory.Functor.isContinuous_of_coverPreserving
      (compatiblePreserving_opens_map s) (coverPreserving_opens_map s)
  exact CategoryTheory.Functor.sheafPushforwardContinuousComp'
    (eqToIso (openImage_preimage f h hh s hcomp)) AddCommGrpCat
    (Opens.grothendieckTopology V)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology T)

include hcomp in
/-- On sections over an open `W ⊆ V`, the comparison `(f_*F)|_V ≅ s_*F` is the identification of
`F(f⁻¹ h(W))` with `F(s⁻¹ W)`. -/
@[simp]
theorem restrictionPushforwardIso_hom_app
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (W : Opens V) :
    (((restrictionPushforwardIso f h hh s hcomp).hom.app F).hom.app (op W)) =
      F.obj.map (eqToHom (openImage_preimage_obj f h hh s hcomp W).symm).op := by
  let _ : (Opens.map s).IsContinuous
      (Opens.grothendieckTopology V)
      (Opens.grothendieckTopology T) := by
    exact CategoryTheory.Functor.isContinuous_of_coverPreserving
      (compatiblePreserving_opens_map s) (coverPreserving_opens_map s)
  exact (CategoryTheory.Functor.sheafPushforwardContinuousComp'_hom_app_hom_app
    (eqToIso (openImage_preimage f h hh s hcomp)) AddCommGrpCat
    (Opens.grothendieckTopology V)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology T) F (op W)).trans
      (congrArg F.obj.map (Subsingleton.elim _ _))

include hcomp in
/-- The comparison `(f_*F)|_V ≅ s_*F` carries the canonical morphism `A_V ⟶ (f_*A_T)|_V` of
constant sheaves to the canonical morphism `A_V ⟶ s_*A_T`. -/
theorem restrictionPushforwardIso_restrictionHom (A : AddCommGrpCat.{u}) :
    OpenEmbeddingCohomology.restrictionHom h hh A ≫
        (OpenEmbeddingCohomology.restriction h hh).map
          (TopCat.ConstantSheaf.pushforwardHom A f) ≫
        (restrictionPushforwardIso f h hh s hcomp).hom.app
          (TopCat.ConstantSheaf.sheaf T A) =
      TopCat.ConstantSheaf.pushforwardHom A s := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology V) _ _
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} s).obj
      (TopCat.ConstantSheaf.sheaf T A)).property (by
      apply NatTrans.ext
      funext W
      apply ConcreteCategory.hom_ext
      intro a
      change (((restrictionPushforwardIso f h hh s hcomp).hom.app
          (TopCat.ConstantSheaf.sheaf T A)).hom.app (op W.unop))
          ((TopCat.ConstantSheaf.pushforwardHom A f).hom.app
            (op ((OpenEmbeddingCohomology.openImage h hh).obj W.unop))
            ((OpenEmbeddingCohomology.restrictionHom h hh A).hom.app (op W.unop)
              ((TopCat.ConstantSheaf.unit V A).app (op W.unop) a))) =
        (TopCat.ConstantSheaf.pushforwardHom A s).hom.app (op W.unop)
          ((TopCat.ConstantSheaf.unit V A).app (op W.unop) a)
      let r := (eqToHom
        (openImage_preimage_obj f h hh s hcomp W.unop).symm).op
      have hd := (congrArg
        ((TopCat.ConstantSheaf.pushforwardHom A f).hom.app
          (op ((OpenEmbeddingCohomology.openImage h hh).obj W.unop)))
        (OpenEmbeddingCohomology.restrictionHom_app_unit h hh A W.unop a)).trans
          (TopCat.ConstantSheaf.pushforwardHom_app_unit A f
            ((OpenEmbeddingCohomology.openImage h hh).obj W.unop) a)
      exact (ConcreteCategory.congr_hom
        (restrictionPushforwardIso_hom_app f h hh s hcomp
          (TopCat.ConstantSheaf.sheaf T A) W.unop) _).trans
        ((congrArg ((TopCat.ConstantSheaf.sheaf T A).obj.map r) hd).trans
          ((ConcreteCategory.congr_hom
            ((TopCat.ConstantSheaf.unit T A).naturality r) a).symm.trans
              (TopCat.ConstantSheaf.pushforwardHom_app_unit A s W.unop a).symm)))

variable [T2Space T]
  (hf : IsClosedMap f) (hff : ∀ x : X, (f ⁻¹' ({x} : Set X)).Finite)
  (hs : IsClosedMap s) (hsf : ∀ v : V, (s ⁻¹' ({v} : Set V)).Finite)

include hcomp in
/-- The finite-map cohomology comparison commutes with restriction to the open subspace `V`, in
every degree. -/
theorem cohomologyForward_openRestriction
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{u} F n) :
    CategoryTheory.Sheaf.H.map
        ((restrictionPushforwardIso f h hh s hcomp).hom.app F) n
      (OpenEmbeddingCohomology.cohomologyMap h hh
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n
        (TopCat.FiniteClosedPushforward.cohomologyForward f hf hff F n a)) =
      TopCat.FiniteClosedPushforward.cohomologyForward s hs hsf F n a := by
  let _ := (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
    f hf hff).1
  let _ := TopCat.FiniteClosedPushforward.pushforward_preservesFiniteColimits f hf hff
  let _ := (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
    s hs hsf).1
  let _ := TopCat.FiniteClosedPushforward.pushforward_preservesFiniteColimits s hs hsf
  exact @Ext.ExactFunctorComparison.comp_natTrans
    (TopCat.Sheaf AddCommGrpCat.{u} T) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{u} V) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.Sheaf.pushforwardAdditive f)
    (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
      f hf hff).1
    (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteColimits f hf hff)
    (OpenEmbeddingCohomology.restriction h hh)
    (OpenEmbeddingCohomology.restriction_additive h hh)
    (OpenEmbeddingCohomology.restriction_preservesFiniteLimits h hh)
    (OpenEmbeddingCohomology.restriction_preservesFiniteColimits h hh)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} s)
    (TopCat.Sheaf.pushforwardAdditive s)
    (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
      s hs hsf).1
    (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteColimits s hs hsf)
    (restrictionPushforwardIso f h hh s hcomp).hom inferInstance
    (TopCat.ConstantSheaf.sheaf T (AddCommGrpCat.of (ULift.{u} ℤ))) F
    (TopCat.ConstantSheaf.sheaf X (AddCommGrpCat.of (ULift.{u} ℤ)))
    (TopCat.ConstantSheaf.sheaf V (AddCommGrpCat.of (ULift.{u} ℤ)))
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f)
    (OpenEmbeddingCohomology.restrictionHom h hh
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) s)
    (restrictionPushforwardIso_restrictionHom f h hh s hcomp
      (AddCommGrpCat.of (ULift.{u} ℤ))) n a

include hcomp in
omit [T2Space T] in
/-- After identifying `A_V` with `(A_X)|_V` on a locally connected `V`, the remaining coefficient
morphism is the canonical `A_V ⟶ s_*A_T`. -/
theorem normalizedCoefficient [LocallyConnectedSpace V]
    (A : AddCommGrpCat.{u}) :
    inv (OpenEmbeddingCohomology.restrictionHom h hh A)
        (I := OpenEmbeddingCohomology.restrictionHom_isIso h hh A) ≫
      TopCat.ConstantSheaf.pushforwardHom A s =
    (OpenEmbeddingCohomology.restriction h hh).map
        (TopCat.ConstantSheaf.pushforwardHom A f) ≫
      (restrictionPushforwardIso f h hh s hcomp).hom.app
        (TopCat.ConstantSheaf.sheaf T A) := by
  let e := OpenEmbeddingCohomology.restrictionHom h hh A
  let ie : IsIso e := OpenEmbeddingCohomology.restrictionHom_isIso h hh A
  let C := (OpenEmbeddingCohomology.restriction h hh).map
      (TopCat.ConstantSheaf.pushforwardHom A f) ≫
    (restrictionPushforwardIso f h hh s hcomp).hom.app
      (TopCat.ConstantSheaf.sheaf T A)
  have he : e ≫ C = TopCat.ConstantSheaf.pushforwardHom A s := by
    exact restrictionPushforwardIso_restrictionHom f h hh s hcomp A
  exact (congrArg (fun q ↦ inv e (I := ie) ≫ q) he.symm).trans
    (IsIso.inv_hom_id_assoc e C (I := ie))

include hcomp in
/-- Restriction to `V` followed by the pullback `s^*` is computed by the finite-map comparison
for `s`, in every degree. -/
theorem normalizedOpenPullback_forward [LocallyConnectedSpace V]
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{u} (TopCat.ConstantSheaf.sheaf X A) n) :
    TopCat.FiniteClosedPushforward.cohomologyForward s hs hsf
        (TopCat.ConstantSheaf.sheaf T A) n
        (TopCat.ConstantSheafCohomology.pullback s hs hsf A n
          (OpenEmbeddingCohomology.constantPullback h hh A n a)) =
      CategoryTheory.Sheaf.H.map
        ((OpenEmbeddingCohomology.restriction h hh).map
            (TopCat.ConstantSheaf.pushforwardHom A f) ≫
          (restrictionPushforwardIso f h hh s hcomp).hom.app
            (TopCat.ConstantSheaf.sheaf T A)) n
        (OpenEmbeddingCohomology.cohomologyMap h hh
          (TopCat.ConstantSheaf.sheaf X A) n a) := by
  let e := OpenEmbeddingCohomology.restrictionHom h hh A
  let ie : IsIso e := OpenEmbeddingCohomology.restrictionHom_isIso h hh A
  have hpS := ConcreteCategory.congr_hom
    (TopCat.ConstantSheafCohomology.pullback_forward s hs hsf A n)
    (OpenEmbeddingCohomology.constantPullback h hh A n a)
  change TopCat.FiniteClosedPushforward.cohomologyForward s hs hsf
      (TopCat.ConstantSheaf.sheaf T A) n
      (TopCat.ConstantSheafCohomology.pullback s hs hsf A n
        (OpenEmbeddingCohomology.constantPullback h hh A n a)) =
    CategoryTheory.Sheaf.H.map (TopCat.ConstantSheaf.pushforwardHom A s) n
      (OpenEmbeddingCohomology.constantPullback h hh A n a) at hpS
  rw [hpS]
  change CategoryTheory.Sheaf.H.map (TopCat.ConstantSheaf.pushforwardHom A s) n
      (CategoryTheory.Sheaf.H.map (inv e (I := ie)) n
        (OpenEmbeddingCohomology.cohomologyMap h hh
          (TopCat.ConstantSheaf.sheaf X A) n a)) = _
  exact (CategoryTheory.Sheaf.H.map_comp_apply
      (inv e (I := ie)) (TopCat.ConstantSheaf.pushforwardHom A s)
      (OpenEmbeddingCohomology.cohomologyMap h hh
        (TopCat.ConstantSheaf.sheaf X A) n a)).symm.trans
    (congrArg (fun q ↦ CategoryTheory.Sheaf.H.map q n
      (OpenEmbeddingCohomology.cohomologyMap h hh
        (TopCat.ConstantSheaf.sheaf X A) n a))
      (normalizedCoefficient f h hh s hcomp A))

include hcomp in
/-- The pullback `f^*` along the composite is computed by the finite-map comparison for `f`,
read through the open factorization. -/
theorem directPullback_forward_open
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{u} (TopCat.ConstantSheaf.sheaf X A) n) :
    TopCat.FiniteClosedPushforward.cohomologyForward s hs hsf
        (TopCat.ConstantSheaf.sheaf T A) n
        (TopCat.ConstantSheafCohomology.pullback f hf hff A n a) =
      CategoryTheory.Sheaf.H.map
        ((OpenEmbeddingCohomology.restriction h hh).map
            (TopCat.ConstantSheaf.pushforwardHom A f) ≫
          (restrictionPushforwardIso f h hh s hcomp).hom.app
            (TopCat.ConstantSheaf.sheaf T A)) n
        (OpenEmbeddingCohomology.cohomologyMap h hh
          (TopCat.ConstantSheaf.sheaf X A) n a) := by
  have hpF := ConcreteCategory.congr_hom
    (TopCat.ConstantSheafCohomology.pullback_forward f hf hff A n) a
  have hmixed := cohomologyForward_openRestriction f h hh s hcomp hf hff hs hsf
    (TopCat.ConstantSheaf.sheaf T A) n
    (TopCat.ConstantSheafCohomology.pullback f hf hff A n a)
  change TopCat.FiniteClosedPushforward.cohomologyForward f hf hff
      (TopCat.ConstantSheaf.sheaf T A) n
      (TopCat.ConstantSheafCohomology.pullback f hf hff A n a) =
    CategoryTheory.Sheaf.H.map (TopCat.ConstantSheaf.pushforwardHom A f) n a at hpF
  rw [hpF] at hmixed
  have hnat := OpenEmbeddingCohomology.cohomologyMap_naturality h hh
    (TopCat.ConstantSheaf.pushforwardHom A f) n a
  rw [hnat] at hmixed
  exact hmixed.symm.trans
    (CategoryTheory.Sheaf.H.map_comp_apply
      ((OpenEmbeddingCohomology.restriction h hh).map
        (TopCat.ConstantSheaf.pushforwardHom A f))
      ((restrictionPushforwardIso f h hh s hcomp).hom.app
        (TopCat.ConstantSheaf.sheaf T A))
      (OpenEmbeddingCohomology.cohomologyMap h hh
        (TopCat.ConstantSheaf.sheaf X A) n a)).symm

set_option linter.style.haveILetI false in
include hcomp in
/-- Constant-coefficient pullback along `f = s ≫ h` is restriction to the open subspace `V`
followed by pullback along `s`: `(s ≫ h)^* = s^* ∘ h^*` in every degree. -/
theorem constantPullback_factorization [LocallyConnectedSpace V]
    (A : AddCommGrpCat.{u}) (n : ℕ) :
    OpenEmbeddingCohomology.constantPullback h hh A n ≫
        TopCat.ConstantSheafCohomology.pullback s hs hsf A n =
      TopCat.ConstantSheafCohomology.pullback f hf hff A n := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply (TopCat.FiniteClosedPushforward.cohomologyForward_bijective
    s hs hsf (TopCat.ConstantSheaf.sheaf T A) n).injective
  exact (normalizedOpenPullback_forward f h hh s hcomp hs hsf A n a).trans
    (directPullback_forward_open f h hh s hcomp hf hff hs hsf A n a).symm

end TopCat.Sheaf.OpenFiniteClosedFactorization
