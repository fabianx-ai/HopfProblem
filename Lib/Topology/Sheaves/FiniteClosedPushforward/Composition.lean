/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.ConstantCohomologyPullback

/-!
# Composition of finite-closed constant-sheaf cohomology maps

The canonical morphism `A_Y → f_*A_X` of constant sheaves is functorial in `f`, and hence so are
the finite-map cohomology comparison `H^n(X, F) → H^n(Y, f_*F)` and the induced contravariant
pullback on constant-sheaf cohomology (the composition half of Hartshorne, *Algebraic Geometry*,
III Ex. 8.2).  All statements hold in every degree.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace

universe u

namespace TopCat.ConstantSheaf

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism `A_Z → g_*A_Y → g_*f_*A_X` of constant sheaves agrees with the one for
the composite `f ≫ g`: `A_• → f_*` is functorial in the map of spaces. -/
theorem pushforwardHom_comp {X Y Z : TopCat.{u}} (A : AddCommGrpCat.{u})
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardHom A g ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map (pushforwardHom A f) =
      pushforwardHom A (f ≫ g) := by
  let adj := sheafificationAdjunction
    (Opens.grothendieckTopology Z) AddCommGrpCat.{u}
  apply (adj.homEquiv (presheaf Z A)
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g)).obj (sheaf X A))).injective
  change unit Z A ≫ (pushforwardHom A g).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map (pushforwardHom A f)).hom =
    unit Z A ≫ (pushforwardHom A (f ≫ g)).hom
  rw [← Category.assoc, unit_pushforwardHom]
  rw [unit_pushforwardHom]
  change rawPushforwardHom A g ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} g).map (unit Y A) ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} g).map (pushforwardHom A f).hom = _
  rw [← Functor.map_comp, unit_pushforwardHom]
  rfl

end TopCat.ConstantSheaf

namespace TopCat.FiniteClosedPushforward

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {X Y Z : TopCat.{u}} [T2Space X] [T2Space Y]

/-- The finite-map cohomology comparisons for `f` and `g` compose to the comparison for `f ≫ g`,
in every degree. -/
theorem cohomologyForward_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsClosedMap f) (hff : ∀ y : Y, (f ⁻¹' ({y} : Set Y)).Finite)
    (hg : IsClosedMap g) (hgf : ∀ z : Z, (g ⁻¹' ({z} : Set Z)).Finite)
    (hfg : IsClosedMap (f ≫ g))
    (hfgf : ∀ z : Z, ((f ≫ g) ⁻¹' ({z} : Set Z)).Finite)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{u} F n) :
    cohomologyForward g hg hgf
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n
        (cohomologyForward f hf hff F n a) =
      cohomologyForward (f ≫ g) hfg hfgf F n a := by
  let _ : HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
    IsGrothendieckAbelian.hasExt _
  let _ : HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} Y) :=
    IsGrothendieckAbelian.hasExt _
  let _ : HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} Z) :=
    IsGrothendieckAbelian.hasExt _
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hff).1
  let _ := pushforward_preservesFiniteColimits f hf hff
  let _ := (pushforward_preservesFiniteLimitsAndColimits g hg hgf).1
  let _ := pushforward_preservesFiniteColimits g hg hgf
  let _ := (pushforward_preservesFiniteLimitsAndColimits (f ≫ g) hfg hfgf).1
  let _ := pushforward_preservesFiniteColimits (f ≫ g) hfg hfgf
  change Ext.ExactFunctorComparison.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g)
      (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) g)
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n
      (Ext.ExactFunctorComparison.map
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
        (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f)
        F n a) =
    Ext.ExactFunctorComparison.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g))
      (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) (f ≫ g))
      F n a
  rw [← TopCat.ConstantSheaf.pushforwardHom_comp
    (AddCommGrpCat.of (ULift.{u} ℤ)) f g]
  exact @Ext.ExactFunctorComparison.comp
    (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{u} Y) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{u} Z) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.Sheaf.pushforwardAdditive f)
    (pushforward_preservesFiniteLimitsAndColimits f hf hff).1
    (pushforward_preservesFiniteColimits f hf hff)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g)
    (TopCat.Sheaf.pushforwardAdditive g)
    (pushforward_preservesFiniteLimitsAndColimits g hg hgf).1
    (pushforward_preservesFiniteColimits g hg hgf)
    inferInstance
    (TopCat.ConstantSheaf.integralSheaf X) F
    (TopCat.ConstantSheaf.integralSheaf Y)
    (TopCat.ConstantSheaf.integralSheaf Z)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) g)
    n a

end TopCat.FiniteClosedPushforward

namespace TopCat.ConstantSheafCohomology

variable {X Y Z : TopCat.{u}} [T2Space X] [T2Space Y]

/-- Pullback on constant-sheaf cohomology is contravariantly functorial for finite closed maps:
`g^* ≫ f^* = (f ≫ g)^*` in every degree. -/
theorem pullback_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsClosedMap f) (hff : ∀ y : Y, (f ⁻¹' ({y} : Set Y)).Finite)
    (hg : IsClosedMap g) (hgf : ∀ z : Z, (g ⁻¹' ({z} : Set Z)).Finite)
    (hfg : IsClosedMap (f ≫ g))
    (hfgf : ∀ z : Z, ((f ≫ g) ⁻¹' ({z} : Set Z)).Finite)
    (A : AddCommGrpCat.{u}) (n : ℕ) :
    pullback g hg hgf A n ≫ pullback f hf hff A n =
      pullback (f ≫ g) hfg hfgf A n := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply (TopCat.FiniteClosedPushforward.cohomologyForward_bijective
    (f ≫ g) hfg hfgf (TopCat.ConstantSheaf.sheaf X A) n).injective
  let pF := pullback f hf hff A n
  let pG := pullback g hg hgf A n
  let pFG := pullback (f ≫ g) hfg hfgf A n
  let cX := TopCat.ConstantSheaf.sheaf X A
  let cY := TopCat.ConstantSheaf.sheaf Y A
  let kF := TopCat.ConstantSheaf.pushforwardHom A f
  let kG := TopCat.ConstantSheaf.pushforwardHom A g
  let kFG := TopCat.ConstantSheaf.pushforwardHom A (f ≫ g)
  have hcomp := (TopCat.FiniteClosedPushforward.cohomologyForward_comp
    f g hf hff hg hgf hfg hfgf cX n (pF (pG a))).symm
  have hpF : TopCat.FiniteClosedPushforward.cohomologyForward f hf hff cX n
      (pF (pG a)) = CategoryTheory.Sheaf.H.map kF n (pG a) :=
    ConcreteCategory.congr_hom (pullback_forward f hf hff A n) (pG a)
  have hpF' := congrArg
    (TopCat.FiniteClosedPushforward.cohomologyForward g hg hgf
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj cX) n) hpF
  have hnat := TopCat.FiniteClosedPushforward.cohomologyForward_naturality
    g hg hgf kF n (pG a)
  have hpG : TopCat.FiniteClosedPushforward.cohomologyForward g hg hgf cY n (pG a) =
      CategoryTheory.Sheaf.H.map kG n a :=
    ConcreteCategory.congr_hom (pullback_forward g hg hgf A n) a
  have hpG' := congrArg
    (CategoryTheory.Sheaf.H.map
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map kF) n) hpG
  have hmap : CategoryTheory.Sheaf.H.map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map kF) n
        (CategoryTheory.Sheaf.H.map kG n a) =
      CategoryTheory.Sheaf.H.map kFG n a := by
    exact (CategoryTheory.Sheaf.H.map_comp_apply kG
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map kF) a).symm.trans
      (congrArg (fun k ↦ CategoryTheory.Sheaf.H.map k n a)
        (TopCat.ConstantSheaf.pushforwardHom_comp A f g))
  have hpFG : CategoryTheory.Sheaf.H.map kFG n a =
      TopCat.FiniteClosedPushforward.cohomologyForward
        (f ≫ g) hfg hfgf cX n (pFG a) :=
    (ConcreteCategory.congr_hom (pullback_forward (f ≫ g) hfg hfgf A n) a).symm
  rw [show (pG ≫ pF) a = pF (pG a) from rfl]
  exact hcomp.trans (hpF'.trans (hnat.trans (hpG'.trans (hmap.trans hpFG))))

end TopCat.ConstantSheafCohomology
