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
# Finite closed pushforward and open restriction

This file proves the elementary Beck--Chevalley comparison obtained by restricting the
pushforward along an injective map to an open subset of its image.  It also records the resulting
compatibility of native Ext-defined cohomology maps and constant-coefficient pullbacks.

No base-change theorem for higher direct images is used or asserted here.

References: Kashiwara--Schapira, *Sheaves on Manifolds*, II (base change along an open
embedding), and Iversen, *Cohomology of Sheaves*, II.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace TopCat.Sheaf.FiniteClosedOpenRestriction

variable {K U V : TopCat.{0}}
  (j : K ⟶ U) (hj : Function.Injective j)
  (h : V ⟶ U) (hh : Topology.IsOpenEmbedding h)
  (v : V ⟶ K) (hv : Topology.IsOpenEmbedding v)
  (hcomp : v ≫ j = h)

include hj hcomp in
/-- The inverse image under `j` of the open image of `W` under `h` is the open image of `W`
under `v`. -/
theorem openImage_preimage_obj (W : Opens V) :
    ((OpenEmbeddingCohomology.openImage h hh ⋙ Opens.map j).obj W) =
      (OpenEmbeddingCohomology.openImage v hv).obj W := by
  ext x
  change (∃ t : V, t ∈ W ∧ h t = j x) ↔ ∃ t : V, t ∈ W ∧ v t = x
  constructor
  · rintro ⟨t, ht, htx⟩
    refine ⟨t, ht, hj ?_⟩
    exact (ConcreteCategory.congr_hom hcomp t).trans htx
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (ConcreteCategory.congr_hom hcomp t).symm⟩

include hj hcomp in
/-- Functorial form of `openImage_preimage_obj`. -/
theorem openImage_preimage :
    OpenEmbeddingCohomology.openImage h hh ⋙ Opens.map j =
      OpenEmbeddingCohomology.openImage v hv :=
  CategoryTheory.Functor.ext (openImage_preimage_obj j hj h hh v hv hcomp)
    (fun _ _ _ ↦ Subsingleton.elim _ _)

include hj hcomp in
/-- Restricting a pushforward through the ambient open embedding agrees with direct restriction
through the induced open embedding. -/
def restrictionPushforwardIso :
    TopCat.Sheaf.pushforward AddCommGrpCat.{0} j ⋙
        OpenEmbeddingCohomology.restriction h hh ≅
      OpenEmbeddingCohomology.restriction v hv := by
  letI := OpenEmbeddingCohomology.openImage_continuous h hh
  letI := OpenEmbeddingCohomology.openImage_continuous v hv
  exact CategoryTheory.Functor.sheafPushforwardContinuousComp'
    (eqToIso (openImage_preimage j hj h hh v hv hcomp))
    AddCommGrpCat (Opens.grothendieckTopology V)
      (Opens.grothendieckTopology U) (Opens.grothendieckTopology K)

include hj hcomp in
/-- The Beck--Chevalley isomorphism is given on sections by the canonical identification of the
two open images. -/
@[simp]
theorem restrictionPushforwardIso_hom_app
    (F : TopCat.Sheaf AddCommGrpCat.{0} K) (W : Opens V) :
    (((restrictionPushforwardIso j hj h hh v hv hcomp).hom.app F).hom.app (op W)) =
      F.obj.map (eqToHom (openImage_preimage_obj j hj h hh v hv hcomp W).symm).op := by
  exact (CategoryTheory.Functor.sheafPushforwardContinuousComp'_hom_app_hom_app
    (eqToIso (openImage_preimage j hj h hh v hv hcomp))
    AddCommGrpCat (Opens.grothendieckTopology V)
      (Opens.grothendieckTopology U) (Opens.grothendieckTopology K) F (op W)).trans
    (congrArg F.obj.map (Subsingleton.elim _ _))

include hj hcomp in
/-- The Beck--Chevalley isomorphism carries the composite constant-coefficient endpoint to the
direct open-restriction endpoint. -/
theorem restrictionPushforwardIso_restrictionHom
    (A : AddCommGrpCat.{0}) :
    OpenEmbeddingCohomology.restrictionHom h hh A ≫
        (OpenEmbeddingCohomology.restriction h hh).map
          (TopCat.ConstantSheaf.pushforwardHom A j) ≫
        (restrictionPushforwardIso j hj h hh v hv hcomp).hom.app
          (TopCat.ConstantSheaf.sheaf K A) =
      OpenEmbeddingCohomology.restrictionHom v hv A := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology V) _ _
    ((OpenEmbeddingCohomology.restriction v hv).obj
      (TopCat.ConstantSheaf.sheaf K A)).property (by
      apply NatTrans.ext
      funext W
      apply ConcreteCategory.hom_ext
      intro a
      change (((restrictionPushforwardIso j hj h hh v hv hcomp).hom.app
          (TopCat.ConstantSheaf.sheaf K A)).hom.app (op W.unop))
          ((TopCat.ConstantSheaf.pushforwardHom A j).hom.app
            (op ((OpenEmbeddingCohomology.openImage h hh).obj W.unop))
            ((OpenEmbeddingCohomology.restrictionHom h hh A).hom.app (op W.unop)
              ((TopCat.ConstantSheaf.unit V A).app (op W.unop) a))) =
        (OpenEmbeddingCohomology.restrictionHom v hv A).hom.app (op W.unop)
          ((TopCat.ConstantSheaf.unit V A).app (op W.unop) a)
      let r := (eqToHom
        (openImage_preimage_obj j hj h hh v hv hcomp W.unop).symm).op
      have hd := (congrArg
        ((TopCat.ConstantSheaf.pushforwardHom A j).hom.app
          (op ((OpenEmbeddingCohomology.openImage h hh).obj W.unop)))
        (OpenEmbeddingCohomology.restrictionHom_app_unit h hh A W.unop a)).trans
          (TopCat.ConstantSheaf.pushforwardHom_app_unit A j
            ((OpenEmbeddingCohomology.openImage h hh).obj W.unop) a)
      exact (ConcreteCategory.congr_hom
        (restrictionPushforwardIso_hom_app j hj h hh v hv hcomp
          (TopCat.ConstantSheaf.sheaf K A) W.unop) _).trans
        ((congrArg ((TopCat.ConstantSheaf.sheaf K A).obj.map r) hd).trans
          ((ConcreteCategory.congr_hom
            ((TopCat.ConstantSheaf.unit K A).naturality r) a).symm.trans
              (OpenEmbeddingCohomology.restrictionHom_app_unit v hv A W.unop a).symm)))

variable [T2Space K]
  (hjclosed : IsClosedMap j) (hjfinite : ∀ u : U, (j ⁻¹' ({u} : Set U)).Finite)

include hj hcomp in
/-- Finite-closed pushforward followed by open restriction agrees, in every cohomological degree,
with direct open restriction through the induced open embedding. -/
theorem cohomologyForward_openRestriction
    (F : TopCat.Sheaf AddCommGrpCat.{0} K) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} F n) :
    CategoryTheory.Sheaf.H.map
        ((restrictionPushforwardIso j hj h hh v hv hcomp).hom.app F) n
      (OpenEmbeddingCohomology.cohomologyMap h hh
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} j).obj F) n
        (TopCat.FiniteClosedPushforward.cohomologyForward
          j hjclosed hjfinite F n a)) =
      OpenEmbeddingCohomology.cohomologyMap v hv F n a := by
  let _ := (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
    j hjclosed hjfinite).1
  let _ := TopCat.FiniteClosedPushforward.pushforward_preservesFiniteColimits
    j hjclosed hjfinite
  exact @Ext.ExactFunctorComparison.comp_natTrans
    (TopCat.Sheaf AddCommGrpCat.{0} K) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{0} U) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{0} V) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} j)
    (TopCat.Sheaf.pushforwardAdditive j)
    (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
      j hjclosed hjfinite).1
    (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteColimits
      j hjclosed hjfinite)
    (OpenEmbeddingCohomology.restriction h hh)
    (OpenEmbeddingCohomology.restriction_additive h hh)
    (OpenEmbeddingCohomology.restriction_preservesFiniteLimits h hh)
    (OpenEmbeddingCohomology.restriction_preservesFiniteColimits h hh)
    (OpenEmbeddingCohomology.restriction v hv)
    (OpenEmbeddingCohomology.restriction_additive v hv)
    (OpenEmbeddingCohomology.restriction_preservesFiniteLimits v hv)
    (OpenEmbeddingCohomology.restriction_preservesFiniteColimits v hv)
    (restrictionPushforwardIso j hj h hh v hv hcomp).hom
    inferInstance
    (TopCat.ConstantSheaf.sheaf K (AddCommGrpCat.of (ULift.{0} ℤ))) F
    (TopCat.ConstantSheaf.sheaf U (AddCommGrpCat.of (ULift.{0} ℤ)))
    (TopCat.ConstantSheaf.sheaf V (AddCommGrpCat.of (ULift.{0} ℤ)))
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{0} ℤ)) j)
    (OpenEmbeddingCohomology.restrictionHom h hh
      (AddCommGrpCat.of (ULift.{0} ℤ)))
    (OpenEmbeddingCohomology.restrictionHom v hv
      (AddCommGrpCat.of (ULift.{0} ℤ)))
    (restrictionPushforwardIso_restrictionHom j hj h hh v hv hcomp
      (AddCommGrpCat.of (ULift.{0} ℤ))) n a

include hj hcomp in
/-- The coefficient morphism in the finite-closed/open sandwich. -/
def sandwichCoefficient (A : AddCommGrpCat.{0}) :
    (OpenEmbeddingCohomology.restriction h hh).obj
        (TopCat.ConstantSheaf.sheaf U A) ⟶
      (OpenEmbeddingCohomology.restriction v hv).obj
        (TopCat.ConstantSheaf.sheaf K A) :=
  (OpenEmbeddingCohomology.restriction h hh).map
      (TopCat.ConstantSheaf.pushforwardHom A j) ≫
    (restrictionPushforwardIso j hj h hh v hv hcomp).hom.app
      (TopCat.ConstantSheaf.sheaf K A)

include hj hcomp in
/-- Open restriction followed by the sandwich coefficient. -/
def openRestrictionThenCoefficient (A : AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (TopCat.ConstantSheaf.sheaf U A) n) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        ((OpenEmbeddingCohomology.restriction v hv).obj
          (TopCat.ConstantSheaf.sheaf K A)) n) :=
  AddCommGrpCat.ofHom (OpenEmbeddingCohomology.cohomologyMap h hh
      (TopCat.ConstantSheaf.sheaf U A) n) ≫
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology V) n).map
      (sandwichCoefficient j hj h hh v hv hcomp A)

/-- Finite-closed pullback followed by open restriction. -/
def closedPullbackThenRestriction (A : AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (TopCat.ConstantSheaf.sheaf U A) n) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        ((OpenEmbeddingCohomology.restriction v hv).obj
          (TopCat.ConstantSheaf.sheaf K A)) n) :=
  TopCat.ConstantSheafCohomology.pullback j hjclosed hjfinite A n ≫
    AddCommGrpCat.ofHom (OpenEmbeddingCohomology.cohomologyMap v hv
      (TopCat.ConstantSheaf.sheaf K A) n)

include hj hcomp in
/-- The native constant-coefficient finite-closed pullback commutes with open restriction through
the coefficient-level Beck--Chevalley isomorphism, in every degree. -/
theorem pullback_openRestriction (A : AddCommGrpCat.{0}) (n : ℕ) :
    openRestrictionThenCoefficient j hj h hh v hv hcomp A n =
      closedPullbackThenRestriction (j := j) (v := v) hv hjclosed hjfinite A n := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  let p := TopCat.ConstantSheafCohomology.pullback j hjclosed hjfinite A n
  let k := TopCat.ConstantSheaf.pushforwardHom A j
  let rho := restrictionPushforwardIso j hj h hh v hv hcomp
  let c := sandwichCoefficient j hj h hh v hv hcomp A
  have hfwd : TopCat.FiniteClosedPushforward.cohomologyForward j hjclosed hjfinite
        (TopCat.ConstantSheaf.sheaf K A) n (p a) =
      CategoryTheory.Sheaf.H.map k n a :=
    ConcreteCategory.congr_hom
      (TopCat.ConstantSheafCohomology.pullback_forward
        j hjclosed hjfinite A n) a
  have hmix := cohomologyForward_openRestriction j hj h hh v hv hcomp
    hjclosed hjfinite (TopCat.ConstantSheaf.sheaf K A) n (p a)
  rw [hfwd] at hmix
  have hnat := OpenEmbeddingCohomology.cohomologyMap_naturality
    h hh k n a
  rw [hnat] at hmix
  change CategoryTheory.Sheaf.H.map c n
      (OpenEmbeddingCohomology.cohomologyMap h hh
        (TopCat.ConstantSheaf.sheaf U A) n a) =
    OpenEmbeddingCohomology.cohomologyMap v hv
      (TopCat.ConstantSheaf.sheaf K A) n (p a)
  change CategoryTheory.Sheaf.H.map
      ((OpenEmbeddingCohomology.restriction h hh).map k ≫
        rho.hom.app (TopCat.ConstantSheaf.sheaf K A)) n
      (OpenEmbeddingCohomology.cohomologyMap h hh
        (TopCat.ConstantSheaf.sheaf U A) n a) = _
  exact (CategoryTheory.Sheaf.H.map_comp_apply
    ((OpenEmbeddingCohomology.restriction h hh).map k)
    (rho.hom.app (TopCat.ConstantSheaf.sheaf K A)) _).trans hmix

set_option linter.style.haveILetI false in
include hj hcomp in
/-- After the canonical constant-sheaf normalizations, open restriction through the ambient space
is the finite-closed pullback followed by restriction inside the closed subspace. -/
theorem constantPullback_sandwich [LocallyConnectedSpace V]
    (A : AddCommGrpCat.{0}) (n : ℕ) :
    OpenEmbeddingCohomology.constantPullback h hh A n =
      TopCat.ConstantSheafCohomology.pullback j hjclosed hjfinite A n ≫
        OpenEmbeddingCohomology.constantPullback v hv A n := by
  let rh := OpenEmbeddingCohomology.restrictionHom h hh A
  let rv := OpenEmbeddingCohomology.restrictionHom v hv A
  let c := sandwichCoefficient j hj h hh v hv hcomp A
  letI irh : IsIso rh := OpenEmbeddingCohomology.restrictionHom_isIso h hh A
  letI irv : IsIso rv := OpenEmbeddingCohomology.restrictionHom_isIso v hv A
  have hc0 : rh ≫ c = rv := by
    exact restrictionPushforwardIso_restrictionHom j hj h hh v hv hcomp A
  have hc : c ≫ inv rv (I := irv) = inv rh (I := irh) :=
    (IsIso.comp_inv_eq rv).2 ((IsIso.eq_inv_comp rh).2 hc0)
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  have hs := ConcreteCategory.congr_hom
    (pullback_openRestriction j hj h hh v hv hcomp hjclosed hjfinite A n) a
  change CategoryTheory.Sheaf.H.map (inv rh (I := irh)) n
      (OpenEmbeddingCohomology.cohomologyMap h hh
        (TopCat.ConstantSheaf.sheaf U A) n a) =
    CategoryTheory.Sheaf.H.map (inv rv (I := irv)) n
      (OpenEmbeddingCohomology.cohomologyMap v hv
        (TopCat.ConstantSheaf.sheaf K A) n
        (TopCat.ConstantSheafCohomology.pullback j hjclosed hjfinite A n a))
  change CategoryTheory.Sheaf.H.map c n
      (OpenEmbeddingCohomology.cohomologyMap h hh
        (TopCat.ConstantSheaf.sheaf U A) n a) =
    OpenEmbeddingCohomology.cohomologyMap v hv
      (TopCat.ConstantSheaf.sheaf K A) n
      (TopCat.ConstantSheafCohomology.pullback j hjclosed hjfinite A n a) at hs
  rw [← hs]
  exact ((CategoryTheory.Sheaf.H.map_comp_apply c (inv rv (I := irv)) _).symm.trans
    (congrArg (fun q ↦ CategoryTheory.Sheaf.H.map q n
      (OpenEmbeddingCohomology.cohomologyMap h hh
        (TopCat.ConstantSheaf.sheaf U A) n a)) hc)).symm

end TopCat.Sheaf.FiniteClosedOpenRestriction
