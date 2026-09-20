/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.ConstantPushforward
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Integral constant sheaves and pushforward global sections

Morphisms from the integral constant sheaf are global sections. Since the inverse image of the
top open is the top open, postcomposition with the native constant-sheaf pushforward map gives an
additive equivalence on these morphism groups for every continuous map.

This is the degree-zero corepresentability `Hom(ℤ_X, F) ≅ Γ(X, F)` (Hartshorne, *Algebraic
Geometry*, III.2; Godement, *Topologie algébrique et théorie des faisceaux*, II.4), together with
its compatibility with pushforward.  It makes no higher-cohomology or proper-base-change claim.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat.ConstantSheaf

/-- The integral constant sheaf `ℤ_X`. -/
abbrev integralSheaf (X : TopCat.{u}) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheaf X (AddCommGrpCat.of (ULift.{u} ℤ))

/-- Morphisms from the integral constant sheaf are additive-equivalent to global sections. -/
def integralHomGlobalEquiv (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (integralSheaf X ⟶ F) ≃+ F.obj.obj (op (⊤ : Opens X)) := by
  let K : AddCommGrpCat.{u} ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let Γ : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op (⊤ : Opens X))
  let adj : K ⊣ Γ := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)
  let _ : Γ.Additive := ⟨by intros; rfl⟩
  let _ : K.Additive := adj.left_adjoint_additive
  exact (adj.homAddEquiv _ F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- The global-section representation is natural in the sheaf. -/
theorem integralHomGlobalEquiv_naturality (X : TopCat.{u})
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (h : integralSheaf X ⟶ F) (g : F ⟶ G) :
    integralHomGlobalEquiv X G (h ≫ g) =
      g.hom.app (op (⊤ : Opens X)) (integralHomGlobalEquiv X F h) := by
  simp only [integralHomGlobalEquiv]
  rfl

/-- The identity of the integral sheaf represents its unit global section. -/
theorem integralHomGlobalEquiv_id (X : TopCat.{u}) :
    integralHomGlobalEquiv X (integralSheaf X) (𝟙 _) =
      (unit X (AddCommGrpCat.of (ULift.{u} ℤ))).app
        (op (⊤ : Opens X)) (ULift.up 1) := by
  rfl

/-- Global sections of a pushforward are literally the source global sections. -/
def integralGlobalSectionsEquiv {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).obj.obj
        (op (⊤ : Opens Y)) ≃+ F.obj.obj (op (⊤ : Opens X)) :=
  AddEquiv.refl _

/-- Pushforward identifies the morphism group out of the integral sheaf with the original
morphism group, through their literal global sections. -/
def integralHomPushforwardEquiv {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (integralSheaf X ⟶ F) ≃+
      (integralSheaf Y ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) :=
  (integralHomGlobalEquiv X F).trans
    ((integralGlobalSectionsEquiv f F).symm.trans
      (integralHomGlobalEquiv Y
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)).symm)

/-- The pushforward morphism equivalence preserves the represented global section. -/
theorem integralHomPushforwardEquiv_global {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (h : integralSheaf X ⟶ F) :
    integralHomGlobalEquiv Y ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
        (integralHomPushforwardEquiv f F h) =
      integralHomGlobalEquiv X F h :=
  (integralHomGlobalEquiv Y
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)).apply_symm_apply _

/-- The pushforward morphism equivalence is natural in the target sheaf. -/
theorem integralHomPushforwardEquiv_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (h : integralSheaf X ⟶ F) (g : F ⟶ G) :
    integralHomPushforwardEquiv f G (h ≫ g) =
      integralHomPushforwardEquiv f F h ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g := by
  apply (integralHomGlobalEquiv Y
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj G)).injective
  exact (integralHomPushforwardEquiv_global f G (h ≫ g)).trans
    ((integralHomGlobalEquiv_naturality X h g).trans
      ((congrArg (g.hom.app (op (⊤ : Opens X)))
        (integralHomPushforwardEquiv_global f F h).symm).trans
        (integralHomGlobalEquiv_naturality Y (integralHomPushforwardEquiv f F h)
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g)).symm))

/-- The native integral constant-sheaf pushforward map preserves the distinguished global
section. -/
theorem integralPushforwardHom_global {X Y : TopCat.{u}} (f : X ⟶ Y) :
    integralHomGlobalEquiv Y
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (integralSheaf X))
        (pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f) =
      integralHomGlobalEquiv X (integralSheaf X) (𝟙 _) := by
  have hnat := integralHomGlobalEquiv_naturality Y
    (𝟙 (integralSheaf Y)) (pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f)
  rw [Category.id_comp] at hnat
  rw [hnat]
  rw [integralHomGlobalEquiv_id, integralHomGlobalEquiv_id]
  exact pushforwardHom_app_unit (AddCommGrpCat.of (ULift.{u} ℤ)) f
    (⊤ : Opens Y) (ULift.up 1)

/-- Postcomposition by the native integral constant-sheaf pushforward map is exactly the global-
section pushforward equivalence. -/
theorem integralPushforwardHom_comp {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (h : integralSheaf X ⟶ F) :
    pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map h =
      integralHomPushforwardEquiv f F h := by
  apply (integralHomGlobalEquiv Y
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)).injective
  rw [integralHomGlobalEquiv_naturality, integralPushforwardHom_global,
    integralHomPushforwardEquiv_global]
  exact (integralHomGlobalEquiv_naturality X (𝟙 _) h).symm.trans
    (congrArg (integralHomGlobalEquiv X F) (Category.id_comp h))

/-- Postcomposition by the native integral constant-sheaf pushforward map is bijective on
morphism groups. -/
theorem integralPushforwardHom_comp_bijective {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Bijective (fun h : integralSheaf X ⟶ F ↦
      pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map h) := by
  have heq : (fun h : integralSheaf X ⟶ F ↦
      pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map h) =
      integralHomPushforwardEquiv f F := funext (integralPushforwardHom_comp f)
  rw [heq]
  exact (integralHomPushforwardEquiv f F).bijective

end TopCat.ConstantSheaf
