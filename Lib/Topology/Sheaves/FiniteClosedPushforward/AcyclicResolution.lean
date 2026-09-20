/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolutionExactFunctor
public import Lib.Topology.Sheaves.Cohomology.AcyclicResolution
public import Lib.Topology.Sheaves.FiniteClosedPushforward.Cohomology

/-!
# Indexed acyclic resolutions under finite closed pushforward

Finite closed pushforward carries an indexed acyclic resolution to an indexed acyclic resolution.
The native Ext comparison commutes in every positive degree with the corresponding comparison to
literal global sections.

This is the general fact that an exact functor preserving injectives carries an acyclic
resolution to an acyclic resolution; see Hartshorne, *Algebraic Geometry*, III.1.2A and
III Ex. 8.1.
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

/-- The exact finite closed pushforward of an indexed acyclic resolution. -/
def mapIndexedResolution
    (R : TopCat.SheafCohomology.AcyclicResolution.Resolution (X := X)) :
    TopCat.SheafCohomology.AcyclicResolution.Resolution (X := Y) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact R.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)

set_option backward.isDefEq.respectTransparency false in
/-- The differential of the pushed indexed resolution is the pushforward of the original
differential. -/
theorem mapIndexedResolution_d
    (R : TopCat.SheafCohomology.AcyclicResolution.Resolution (X := X)) (n : ℕ) :
    (mapIndexedResolution f hf hfinite R).d n =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (R.d n) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact CategoryTheory.Abelian.Ext.AcyclicResolution.map_d
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) R n

/-- Positive-degree acyclicity is preserved by finite closed pushforward. -/
theorem mapIndexedResolution_isAcyclic
    (R : TopCat.SheafCohomology.AcyclicResolution.Resolution (X := X))
    (hR : TopCat.SheafCohomology.AcyclicResolution.IsAcyclic R) :
    TopCat.SheafCohomology.AcyclicResolution.IsAcyclic
      (mapIndexedResolution f hf hfinite R) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact CategoryTheory.Abelian.Ext.AcyclicResolution.isAcyclicFor_map_of_surjective
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f)
    R (TopCat.SheafCohomology.AcyclicResolution.isAcyclicFor R hR)
    (fun i q _hq ↦
      (cohomologyForward_bijective f hf hfinite (R.X i) q).surjective)

/-- Mathlib's degree-zero cohomology equivalence agrees with the explicit integral-sheaf
global-section equivalence on degree-zero Ext classes. -/
private theorem h0GlobalIso_mk₀ {Z : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} Z)
    (g : TopCat.ConstantSheaf.integralSheaf Z ⟶ F) :
    CategoryTheory.Sheaf.H.equiv₀ F
        (show IsTerminal (⊤ : Opens Z) from isTerminalTop) (Ext.mk₀ g) =
      TopCat.ConstantSheaf.integralHomGlobalEquiv Z F g :=
  congrArg (TopCat.ConstantSheaf.integralHomGlobalEquiv Z F)
    ((Ext.addEquiv₀ (X := TopCat.ConstantSheaf.integralSheaf Z) (Y := F)).apply_symm_apply g)

/-- In degree zero the finite-pushforward Ext comparison preserves the literal global section. -/
private theorem h0Global_forward (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    AddCommGrpCat.ofHom (cohomologyForward f hf hfinite F 0) ≫
        (TopCat.SheafH1.h0GlobalIso
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)).hom =
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

/-- The termwise Ext comparison from a resolution to its finite closed pushforward. -/
def indexedEvaluatedComplexForwardMap
    (R : TopCat.SheafCohomology.AcyclicResolution.Resolution (X := X)) :
    R.evaluatedComplex (TopCat.ConstantSheaf.integralSheaf X) ⟶
      (mapIndexedResolution f hf hfinite R).evaluatedComplex
        (TopCat.ConstantSheaf.integralSheaf Y) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact CategoryTheory.Abelian.Ext.AcyclicResolution.evaluatedComplexMap
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f) R

set_option backward.isDefEq.respectTransparency false in
/-- Global sections of a pushed indexed resolution are canonically the original global-section
complex. -/
def indexedGlobalComplexIso
    (R : TopCat.SheafCohomology.AcyclicResolution.Resolution (X := X)) :
    TopCat.SheafCohomology.AcyclicResolution.globalComplex
        (mapIndexedResolution f hf hfinite R) ≅
      TopCat.SheafCohomology.AcyclicResolution.globalComplex R := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ by
      change (TopCat.Sheaf.globalSectionsFunctor X).obj (R.X n) ≅
        (TopCat.Sheaf.globalSectionsFunctor X).obj (R.X n)
      exact Iso.refl _)
    (fun i j hij ↦ by
      subst j
      simp only [Functor.mapHomologicalComplex_obj_d,
        CategoryTheory.Abelian.Ext.AcyclicResolution.complex_d]
      rw [show (mapIndexedResolution f hf hfinite R).d i =
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (R.d i) by
        exact CategoryTheory.Abelian.Ext.AcyclicResolution.map_d
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) R i]
      rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The termwise degree-zero Ext comparison preserves the literal global cochain complex. -/
theorem indexedExtZeroGlobal_forward
    (R : TopCat.SheafCohomology.AcyclicResolution.Resolution (X := X)) :
    (indexedEvaluatedComplexForwardMap f hf hfinite R ≫
        (TopCat.SheafCohomology.AcyclicResolution.extZeroGlobalIso
          (mapIndexedResolution f hf hfinite R)).hom) ≫
        (indexedGlobalComplexIso f hf hfinite R).hom =
      (TopCat.SheafCohomology.AcyclicResolution.extZeroGlobalIso R).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  change (AddCommGrpCat.ofHom (cohomologyForward f hf hfinite (R.X n) 0) ≫
      (TopCat.SheafH1.h0GlobalIso
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (R.X n))).hom) ≫
      𝟙 _ = (TopCat.SheafH1.h0GlobalIso (R.X n)).hom
  rw [Category.comp_id]
  exact h0Global_forward f hf hfinite (R.X n)

/-- The pushed indexed resolution comparison, normalized to the original literal global-section
complex. -/
def pushedIndexedGlobalIso
    (R : TopCat.SheafCohomology.AcyclicResolution.Resolution (X := X))
    (hR : TopCat.SheafCohomology.AcyclicResolution.IsAcyclic R) (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u}
        ((mapIndexedResolution f hf hfinite R).Z 0) (n + 1)) ≅
      (TopCat.SheafCohomology.AcyclicResolution.globalComplex R).homology (n + 1) :=
  Iso.trans
    (TopCat.SheafCohomology.AcyclicResolution.extIsoGlobalHomology
      (mapIndexedResolution f hf hfinite R)
      (mapIndexedResolution_isAcyclic f hf hfinite R hR) n)
    (HomologicalComplex.homologyMapIso
      (indexedGlobalComplexIso f hf hfinite R) (n + 1))

set_option backward.isDefEq.respectTransparency false in
/-- Native finite-pushforward cohomology commutes in every positive degree with the indexed
resolution comparison to literal global sections. -/
theorem indexedGlobal_forward
    (R : TopCat.SheafCohomology.AcyclicResolution.Resolution (X := X))
    (hR : TopCat.SheafCohomology.AcyclicResolution.IsAcyclic R) (n : ℕ) :
    AddCommGrpCat.ofHom (cohomologyForward f hf hfinite (R.Z 0) (n + 1)) ≫
        (pushedIndexedGlobalIso f hf hfinite R hR n).hom =
      (TopCat.SheafCohomology.AcyclicResolution.extIsoGlobalHomology R hR n).hom := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  let a := AddCommGrpCat.ofHom (cohomologyForward f hf hfinite (R.Z 0) (n + 1))
  let r := (R.extIsoHomology (TopCat.ConstantSheaf.integralSheaf X)
    (TopCat.SheafCohomology.AcyclicResolution.isAcyclicFor R hR) n).hom
  let s := ((mapIndexedResolution f hf hfinite R).extIsoHomology
    (TopCat.ConstantSheaf.integralSheaf Y)
    (TopCat.SheafCohomology.AcyclicResolution.isAcyclicFor
      (mapIndexedResolution f hf hfinite R)
      (mapIndexedResolution_isAcyclic f hf hfinite R hR)) n).hom
  let b := HomologicalComplex.homologyMap
    (indexedEvaluatedComplexForwardMap f hf hfinite R) (n + 1)
  let eR := (HomologicalComplex.homologyMapIso
    (TopCat.SheafCohomology.AcyclicResolution.extZeroGlobalIso R) (n + 1)).hom
  let eS := (HomologicalComplex.homologyMapIso
    (TopCat.SheafCohomology.AcyclicResolution.extZeroGlobalIso
      (mapIndexedResolution f hf hfinite R)) (n + 1)).hom
  let q := (HomologicalComplex.homologyMapIso
    (indexedGlobalComplexIso f hf hfinite R) (n + 1)).hom
  change a ≫ ((s ≫ eS) ≫ q) = r ≫ eR
  have hext : a ≫ s = r ≫ b :=
    CategoryTheory.Abelian.Ext.AcyclicResolution.extIsoHomology_naturality
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
      (TopCat.ConstantSheaf.pushforwardHom (AddCommGrpCat.of (ULift.{u} ℤ)) f)
      R (TopCat.SheafCohomology.AcyclicResolution.isAcyclicFor R hR)
      (TopCat.SheafCohomology.AcyclicResolution.isAcyclicFor
        (mapIndexedResolution f hf hfinite R)
        (mapIndexedResolution_isAcyclic f hf hfinite R hR)) n
  have hglobal : (b ≫ eS) ≫ q = eR := by
    dsimp only [b, eS, eR, q]
    simpa only [HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMapIso_hom] using
      congrArg (fun k ↦ HomologicalComplex.homologyMap k (n + 1))
        (indexedExtZeroGlobal_forward f hf hfinite R)
  calc
    a ≫ ((s ≫ eS) ≫ q) = ((a ≫ s) ≫ eS) ≫ q := by
      simp only [Category.assoc]
    _ = ((r ≫ b) ≫ eS) ≫ q :=
      congrArg (fun k ↦ (k ≫ eS) ≫ q) hext
    _ = r ≫ ((b ≫ eS) ≫ q) := by
      simp only [Category.assoc]
    _ = r ≫ eR := congrArg (fun k ↦ r ≫ k) hglobal

end TopCat.FiniteClosedPushforward
