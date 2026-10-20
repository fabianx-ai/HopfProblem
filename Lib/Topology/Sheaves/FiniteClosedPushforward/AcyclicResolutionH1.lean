/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolutionH1ExactFunctor
public import Lib.Topology.Sheaves.Cohomology.AcyclicResolutionH1
public import Lib.Topology.Sheaves.FiniteClosedPushforward.Cohomology

/-!
# H¹ acyclic resolutions under finite closed pushforward

Finite closed pushforward carries a low-degree acyclic resolution to another such resolution.
The native Ext comparison commutes with the canonical H¹/global-sections comparison.  This is the
degree-one case of `Lib.Topology.Sheaves.FiniteClosedPushforward.AcyclicResolution`; see
Hartshorne, *Algebraic Geometry*, III.1.2A.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

universe u

namespace TopCat.FiniteClosedPushforward

variable {X Y : TopCat.{u}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' ({y} : Set Y)).Finite)

/-- Mathlib's degree-zero cohomology equivalence agrees with the explicit integral-sheaf
global-section equivalence on degree-zero Ext classes. -/
private theorem h0GlobalIso_mk₀ {Z : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} Z)
    (g : TopCat.ConstantSheaf.integralSheaf Z ⟶ F) :
    CategoryTheory.Sheaf.H.equiv₀ F
        (show IsTerminal (⊤ : Opens Z) from isTerminalTop) (Ext.mk₀ g) =
      TopCat.ConstantSheaf.integralHomGlobalEquiv Z F g :=
  congrArg (TopCat.ConstantSheaf.integralHomGlobalEquiv Z F)
    ((Ext.addEquiv₀ (X := TopCat.ConstantSheaf.integralSheaf Z) (Y := F)).apply_symm_apply g)

/-- The exact finite closed pushforward of a low-degree acyclic resolution. -/
def mapResolution
    (R : Ext.AcyclicResolutionH1 (C := TopCat.Sheaf AddCommGrpCat.{u} X)) :
    Ext.AcyclicResolutionH1 (C := TopCat.Sheaf AddCommGrpCat.{u} Y) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)

/-- Degree-one acyclicity is preserved by finite closed pushforward. -/
theorem mapResolution_h1_subsingleton
    (R : Ext.AcyclicResolutionH1 (C := TopCat.Sheaf AddCommGrpCat.{u} X))
    [Subsingleton (CategoryTheory.Sheaf.H.{u} R.complex.X₁ 1)] :
    Subsingleton (CategoryTheory.Sheaf.H.{u} (mapResolution f hf hfinite R).complex.X₁ 1) :=
  ⟨fun _ _ => (cohomologyEquiv f hf hfinite R.complex.X₁ 1).injective
    (Subsingleton.elim _ _)⟩

/-- In degree zero the exact-functor Ext comparison preserves the literal global section. -/
private theorem h0Global_forward (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    AddCommGrpCat.ofHom (cohomologyForward f hf hfinite F 0) ≫
        (TopCat.SheafH1.h0GlobalIso ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)).hom =
      (TopCat.SheafH1.h0GlobalIso F).hom := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro e
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (TopCat.ConstantSheaf.integralSheaf X) F).surjective e
  change CategoryTheory.Sheaf.H.equiv₀
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
      (show IsTerminal (⊤ : Opens Y) from isTerminalTop)
      (Ext.ExactFunctorComparison.map
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
        (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f)
        F 0 (Ext.mk₀ g)) =
    CategoryTheory.Sheaf.H.equiv₀ F
      (show IsTerminal (⊤ : Opens X) from isTerminalTop) (Ext.mk₀ g)
  have hmk := Ext.ExactFunctorComparison.map_mk₀
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f) g
  conv_lhs => rw [hmk]
  have hy := h0GlobalIso_mk₀
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g)
  have hx := h0GlobalIso_mk₀ F g
  exact hy.trans
    ((congrArg
      (TopCat.ConstantSheaf.integralHomGlobalEquiv Y
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F))
      (TopCat.ConstantSheaf.integralPushforwardHom_comp f g)).trans
        ((TopCat.ConstantSheaf.integralHomPushforwardEquiv_global f F g).trans hx.symm))

/-- The termwise endpoint comparison for a finite closed pushforward. -/
private def extZeroForwardMap
    (R : Ext.AcyclicResolutionH1 (C := TopCat.Sheaf AddCommGrpCat.{u} X)) :
    R.extZeroComplex (TopCat.ConstantSheaf.integralSheaf X) ⟶
      (mapResolution f hf hfinite R).extZeroComplex (TopCat.ConstantSheaf.integralSheaf Y) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact Ext.AcyclicResolutionH1.extZeroMap
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f) R

/-- The termwise degree-zero Ext comparison preserves the literal global short complex. -/
private theorem extZeroGlobal_forward
    (R : Ext.AcyclicResolutionH1 (C := TopCat.Sheaf AddCommGrpCat.{u} X)) :
    extZeroForwardMap f hf hfinite R ≫
      (TopCat.SheafH1.AcyclicResolutionH1.extZeroGlobalIso
        (mapResolution f hf hfinite R)).hom =
      (TopCat.SheafH1.AcyclicResolutionH1.extZeroGlobalIso R).hom := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  apply ShortComplex.hom_ext
  · exact h0Global_forward f hf hfinite R.complex.X₁
  · exact h0Global_forward f hf hfinite R.complex.X₂
  · exact h0Global_forward f hf hfinite R.complex.X₃

/-- The H¹/global-sections comparison for the pushed resolution, with acyclicity transferred
from the source. -/
def pushedH1GlobalIso
    (R : Ext.AcyclicResolutionH1 (C := TopCat.Sheaf AddCommGrpCat.{u} X))
    [Subsingleton (CategoryTheory.Sheaf.H.{u} R.complex.X₁ 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u}
      (mapResolution f hf hfinite R).F 1) ≅
      (TopCat.SheafH1.AcyclicResolutionH1.globalComplex
        (mapResolution f hf hfinite R)).homology := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{u}
      (mapResolution f hf hfinite R).complex.X₁ 1) :=
    mapResolution_h1_subsingleton f hf hfinite R
  exact TopCat.SheafH1.AcyclicResolutionH1.h1GlobalIso
    (mapResolution f hf hfinite R)

/-- Native finite-pushforward H¹ commutes with the H¹/global-sections comparison. -/
theorem h1Global_forward
    (R : Ext.AcyclicResolutionH1 (C := TopCat.Sheaf AddCommGrpCat.{u} X))
    [Subsingleton (CategoryTheory.Sheaf.H.{u} R.complex.X₁ 1)] :
    AddCommGrpCat.ofHom (cohomologyForward f hf hfinite R.F 1) ≫
        (pushedH1GlobalIso f hf hfinite R).hom =
      (TopCat.SheafH1.AcyclicResolutionH1.h1GlobalIso R).hom := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  let : Subsingleton (Ext.{u} (TopCat.ConstantSheaf.integralSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{u} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{u} (TopCat.ConstantSheaf.integralSheaf Y)
      (R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).complex.X₁ 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj R.complex.X₁) 1)
    exact ⟨fun _ _ => (cohomologyEquiv f hf hfinite R.complex.X₁ 1).injective
      (Subsingleton.elim _ _)⟩
  let : Subsingleton (Ext.{u}
      (TopCat.ConstantSheaf.sheaf X (AddCommGrpCat.of (ULift.{u} ℤ)))
      R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{u} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{u}
      (TopCat.ConstantSheaf.sheaf Y (AddCommGrpCat.of (ULift.{u} ℤ)))
      (R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).complex.X₁ 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj R.complex.X₁) 1)
    exact ⟨fun _ _ => (cohomologyEquiv f hf hfinite R.complex.X₁ 1).injective
      (Subsingleton.elim _ _)⟩
  let : Subsingleton (Ext.{u} (TopCat.ConstantSheaf.integralSheaf Y)
      (R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).complex.X₁ 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj R.complex.X₁) 1)
    exact ⟨fun _ _ => (cohomologyEquiv f hf hfinite R.complex.X₁ 1).injective
      (Subsingleton.elim _ _)⟩
  have hext := Ext.AcyclicResolutionH1.extOneIso_naturality
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f) R
  have hglobalRaw :
      ShortComplex.homologyMap
          (extZeroForwardMap f hf hfinite R ≫
            (TopCat.SheafH1.AcyclicResolutionH1.extZeroGlobalIso
              (R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))).hom) =
        ShortComplex.homologyMap
          (TopCat.SheafH1.AcyclicResolutionH1.extZeroGlobalIso R).hom :=
    congrArg (fun k => ShortComplex.homologyMap k)
      (extZeroGlobal_forward f hf hfinite R)
  have hglobal :
      ShortComplex.homologyMap
          (extZeroForwardMap f hf hfinite R) ≫
        ShortComplex.homologyMap
          (TopCat.SheafH1.AcyclicResolutionH1.extZeroGlobalIso
            (R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))).hom =
      ShortComplex.homologyMap
        (TopCat.SheafH1.AcyclicResolutionH1.extZeroGlobalIso R).hom :=
    (ShortComplex.homologyMap_comp _ _).symm.trans hglobalRaw
  have hforward :
      AddCommGrpCat.ofHom (cohomologyForward f hf hfinite R.F 1) =
        Ext.AcyclicResolutionH1.comparisonHom
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
          (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f)
          R.F 1 := rfl
  have hext' := hext
  rw [← hforward] at hext'
  change AddCommGrpCat.ofHom (cohomologyForward f hf hfinite R.F 1) ≫
      ((R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).extOneIso
        (TopCat.ConstantSheaf.integralSheaf Y)).hom =
    (R.extOneIso (TopCat.ConstantSheaf.integralSheaf X)).hom ≫
      ShortComplex.homologyMap (extZeroForwardMap f hf hfinite R) at hext'
  change AddCommGrpCat.ofHom (cohomologyForward f hf hfinite R.F 1) ≫
      (((R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).extOneIso
          (TopCat.ConstantSheaf.integralSheaf Y)).hom ≫
        ShortComplex.homologyMap
          (TopCat.SheafH1.AcyclicResolutionH1.extZeroGlobalIso
            (R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))).hom) =
    (R.extOneIso (TopCat.ConstantSheaf.integralSheaf X)).hom ≫
      ShortComplex.homologyMap
        (TopCat.SheafH1.AcyclicResolutionH1.extZeroGlobalIso R).hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ ShortComplex.homologyMap
      (TopCat.SheafH1.AcyclicResolutionH1.extZeroGlobalIso
        (R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))).hom) hext').trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => (R.extOneIso (TopCat.ConstantSheaf.integralSheaf X)).hom ≫ k) hglobal)))

end TopCat.FiniteClosedPushforward
