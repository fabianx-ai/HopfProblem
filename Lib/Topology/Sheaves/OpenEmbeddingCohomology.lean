/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.ExactFunctorComparison
public import Lib.Topology.Sheaves.Cohomology.AddCommGroup
public import Lib.Topology.Sheaves.ConstantPushforward
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-!
# Constant coefficients and cohomology along open embeddings

Restriction along an open embedding is exact.  This file constructs the canonical morphism from
the constant sheaf on the source to the restriction of the constant sheaf on the target and the
resulting native Ext-defined cohomology map.  On a locally connected source the coefficient
morphism is an isomorphism, giving the normalized constant-coefficient pullback.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace TopCat.Sheaf.OpenEmbeddingCohomology

variable {T X : TopCat.{0}} (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)

/-- The functor taking an open of the source to its open image in the target. -/
abbrev openImage : Opens T ⥤ Opens X := hf.functor

instance openImage_continuous :
    (openImage f hf).IsContinuous (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology X) :=
  hf.functor_isContinuous

/-- Restriction of additive sheaves along an open embedding. -/
abbrev restriction : TopCat.Sheaf AddCommGrpCat.{0} X ⥤
    TopCat.Sheaf AddCommGrpCat.{0} T :=
  (openImage f hf).sheafPushforwardContinuous AddCommGrpCat
    (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)

instance restriction_additive : (restriction f hf).Additive where
  map_add := by intros; rfl

instance openImage_cocontinuous :
    (openImage f hf).IsCocontinuous (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology X) where
  cover_lift {V S} hS := by
    intro t ht
    obtain ⟨W, i, hi, htW⟩ := hS (f t) ⟨t, ht, rfl⟩
    let W' : Opens T := (Opens.map f).obj W
    have hW'V : W' ≤ V := by
      intro s hs
      obtain ⟨u, hu, hus⟩ := i.le hs
      exact hf.injective hus ▸ hu
    let k : (openImage f hf).obj W' ⟶ W := homOfLE (by
      rintro x ⟨s, hs, rfl⟩
      exact hs)
    refine ⟨W', homOfLE hW'V, ?_, htW⟩
    exact S.downward_closed hi k

instance restriction_rightAdjoint : (restriction f hf).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (openImage f hf)
    AddCommGrpCat (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology X)).isRightAdjoint

instance restriction_leftAdjoint : (restriction f hf).IsLeftAdjoint :=
  ((openImage f hf).sheafAdjunctionCocontinuous AddCommGrpCat
    (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology X)).isLeftAdjoint

theorem restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction f hf) := by
  infer_instance

theorem restriction_preservesFiniteColimits :
    PreservesFiniteColimits (restriction f hf) := by
  infer_instance

/-- Before sheafification, a coefficient value is sent to the same constant section on the
corresponding image open. -/
def rawRestrictionHom (A : AddCommGrpCat.{0}) :
    TopCat.ConstantSheaf.presheaf T A ⟶
      ((restriction f hf).obj (TopCat.ConstantSheaf.sheaf X A)).obj where
  app U := (TopCat.ConstantSheaf.unit X A).app (op ((openImage f hf).obj U.unop))
  naturality U V g := by
    change (TopCat.ConstantSheaf.presheaf X A).map
          ((openImage f hf).map g.unop).op ≫
        (TopCat.ConstantSheaf.unit X A).app
          (op ((openImage f hf).obj V.unop)) =
      (TopCat.ConstantSheaf.unit X A).app
          (op ((openImage f hf).obj U.unop)) ≫
        (TopCat.ConstantSheaf.sheaf X A).obj.map
          ((openImage f hf).map g.unop).op
    exact (TopCat.ConstantSheaf.unit X A).naturality
      ((openImage f hf).map g.unop).op

/-- Canonical restriction of a constant sheaf along an open embedding. -/
def restrictionHom (A : AddCommGrpCat.{0}) :
    TopCat.ConstantSheaf.sheaf T A ⟶
      (restriction f hf).obj (TopCat.ConstantSheaf.sheaf X A) where
  hom := CategoryTheory.sheafifyLift (Opens.grothendieckTopology T)
    (rawRestrictionHom f hf A)
    ((restriction f hf).obj (TopCat.ConstantSheaf.sheaf X A)).property

/-- The restriction morphism is characterized by the constant-presheaf unit. -/
theorem unit_restrictionHom (A : AddCommGrpCat.{0}) :
    TopCat.ConstantSheaf.unit T A ≫ (restrictionHom f hf A).hom =
      rawRestrictionHom f hf A :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology T)
    (rawRestrictionHom f hf A)
    ((restriction f hf).obj (TopCat.ConstantSheaf.sheaf X A)).property

@[simp]
theorem restrictionHom_app_unit (A : AddCommGrpCat.{0})
    (U : Opens T) (a : A) :
    (restrictionHom f hf A).hom.app (op U)
        ((TopCat.ConstantSheaf.unit T A).app (op U) a) =
      (TopCat.ConstantSheaf.unit X A).app
        (op ((openImage f hf).obj U)) a := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (unit_restrictionHom f hf A) (op U)) a
  exact h

/-- A locally connected source sees the same locally constant coefficient sheaf after open
restriction. -/
theorem restrictionHom_isIso [LocallyConnectedSpace T]
    (A : AddCommGrpCat.{0}) : IsIso (restrictionHom f hf A) := by
  let B : Set (Opens T) := {U | IsConnected (U : Set T)}
  let basis : B → Opens T := fun U ↦ U.1
  have hbasis : Opens.IsBasis (Set.range basis) := by
    rw [Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨S, ⟨hSopen, hxS, hSconnected⟩, hSU⟩ :=
      (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp (U.2.mem_nhds hx)
    refine ⟨⟨S, hSopen⟩, ?_, hxS, hSU⟩
    exact ⟨⟨⟨S, hSopen⟩, hSconnected⟩, rfl⟩
  apply TopCat.Sheaf.isIso_iff_isIso_basis hbasis
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  have hsource := TopCat.ConstantSheaf.unit_app_bijective T A (basis U) U.2
  have himage : IsConnected (((openImage f hf).obj (basis U) : Set X)) := by
    change IsConnected (f '' (basis U : Set T))
    exact U.2.image f f.hom.continuous.continuousOn
  have htarget := TopCat.ConstantSheaf.unit_app_bijective X A
    ((openImage f hf).obj (basis U)) himage
  constructor
  · intro s t hst
    obtain ⟨a, rfl⟩ := hsource.surjective s
    obtain ⟨b, rfl⟩ := hsource.surjective t
    exact congrArg ((TopCat.ConstantSheaf.unit T A).app (op (basis U)))
      (htarget.injective
        ((restrictionHom_app_unit f hf A (basis U) a).symm.trans
          (hst.trans (restrictionHom_app_unit f hf A (basis U) b))))
  · intro t
    obtain ⟨a, rfl⟩ := htarget.surjective t
    exact ⟨(TopCat.ConstantSheaf.unit T A).app (op (basis U)) a,
      restrictionHom_app_unit f hf A (basis U) a⟩

/-- Native Ext-defined cohomology restriction along an open embedding. -/
def cohomologyMap (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} F n →+
      CategoryTheory.Sheaf.H.{0} ((restriction f hf).obj F) n := by
  let _ := restriction_preservesFiniteLimits f hf
  let _ := restriction_preservesFiniteColimits f hf
  exact Ext.ExactFunctorComparison.map (restriction f hf)
    (restrictionHom f hf (AddCommGrpCat.of (ULift.{0} ℤ))) F n

/-- Open restriction commutes with coefficient morphisms. -/
theorem cohomologyMap_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (g : F ⟶ G) (n : ℕ) (a : CategoryTheory.Sheaf.H.{0} F n) :
    cohomologyMap f hf G n (CategoryTheory.Sheaf.H.map g n a) =
      CategoryTheory.Sheaf.H.map ((restriction f hf).map g) n
        (cohomologyMap f hf F n a) := by
  let _ := restriction_preservesFiniteLimits f hf
  let _ := restriction_preservesFiniteColimits f hf
  exact @Ext.ExactFunctorComparison.map_naturality
    (TopCat.Sheaf AddCommGrpCat.{0} X) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{0} T) _ _ (IsGrothendieckAbelian.hasExt _)
    (restriction f hf) (restriction_additive f hf)
    (restriction_preservesFiniteLimits f hf)
    (restriction_preservesFiniteColimits f hf)
    _ _ _ _
    (restrictionHom f hf (AddCommGrpCat.of (ULift.{0} ℤ))) g n a

/-- The normalized constant-coefficient pullback along an open embedding. -/
def constantPullback [LocallyConnectedSpace T]
    (A : AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (TopCat.ConstantSheaf.sheaf X A) n) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (TopCat.ConstantSheaf.sheaf T A) n) :=
  AddCommGrpCat.ofHom (cohomologyMap f hf (TopCat.ConstantSheaf.sheaf X A) n) ≫
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology T) n).map
      (inv (restrictionHom f hf A)
        (I := restrictionHom_isIso f hf A))

end TopCat.Sheaf.OpenEmbeddingCohomology
