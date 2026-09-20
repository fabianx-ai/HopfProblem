/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.AddCommGroup
public import Lib.Topology.Sheaves.ConstantPushforward.GlobalSections
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Flasque sheaves are acyclic in degree one

A flasque sheaf of abelian groups on a topological space has vanishing first cohomology
(Hartshorne, *Algebraic Geometry*, III Prop. 2.5; Godement, *Topologie algébrique et théorie des
faisceaux*, II §§3–4), here in the degree-one case and for the `Ext`-defined cohomology.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian

universe u

namespace TopCat.SheafH1

variable {X : TopCat.{u}}

private instance abelianSheaf_hasExt :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  IsGrothendieckAbelian.hasExt _

private theorem hom_surjective_of_global_surjective
    {G Q : TopCat.Sheaf AddCommGrpCat.{u} X} (π : G ⟶ Q)
    (hπ : Function.Surjective (π.hom.app (op (⊤ : Opens X)))) :
    Function.Surjective (fun f : (TopCat.ConstantSheaf.integralSheaf X) ⟶ G => f ≫ π) := by
  intro f
  let x : CategoryTheory.Sheaf.H.{u} Q 0 := Ext.mk₀.{u} f
  let eG := CategoryTheory.Sheaf.H.equiv₀.{u} G
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)
  let eQ := CategoryTheory.Sheaf.H.equiv₀.{u} Q
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)
  obtain ⟨y, hy⟩ := hπ (eQ x)
  let z : CategoryTheory.Sheaf.H.{u} G 0 := eG.symm y
  have hz : CategoryTheory.Sheaf.H.map.{u} π 0 z = x := by
    apply eQ.injective
    calc
      eQ (CategoryTheory.Sheaf.H.map.{u} π 0 z) =
          π.hom.app (op (⊤ : Opens X)) (eG z) :=
        (CategoryTheory.Sheaf.H.equiv₀_naturality
          (hT := (show IsTerminal (⊤ : Opens X) from isTerminalTop)) π z).symm
      _ = eQ x := (congrArg (π.hom.app (op (⊤ : Opens X)))
        (eG.apply_symm_apply y)).trans hy
  refine ⟨Ext.addEquiv₀.{u} (C := TopCat.Sheaf AddCommGrpCat.{u} X) z, ?_⟩
  calc
    Ext.addEquiv₀.{u} (C := TopCat.Sheaf AddCommGrpCat.{u} X) z ≫ π =
      Ext.addEquiv₀.{u} (C := TopCat.Sheaf AddCommGrpCat.{u} X)
        (CategoryTheory.Sheaf.H.map.{u} π 0 z) :=
      (CategoryTheory.Sheaf.H.addEquiv₀_map π z).symm
    _ = Ext.addEquiv₀.{u} (C := TopCat.Sheaf AddCommGrpCat.{u} X) x :=
      congrArg (Ext.addEquiv₀.{u} (C := TopCat.Sheaf AddCommGrpCat.{u} X)) hz
    _ = f := (Ext.addEquiv₀.{u} (C := TopCat.Sheaf AddCommGrpCat.{u} X)
      (X := (TopCat.ConstantSheaf.integralSheaf X)) (Y := Q)).apply_symm_apply f

private theorem subsingleton_ext_one_of_shortExact
    (X₀ : TopCat.Sheaf AddCommGrpCat.{u} X)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [Injective S.X₂]
    (hsurj : Function.Surjective (fun f : X₀ ⟶ S.X₂ => f ≫ S.g)) :
    Subsingleton (Ext.{u} X₀ S.X₁ 1) := by
  refine subsingleton_of_forall_eq 0 ?_
  intro e
  obtain ⟨e₀, he₀⟩ := Ext.covariant_sequence_exact₁ X₀ hS e
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X₀ S.X₃).surjective e₀
  obtain ⟨g, rfl⟩ := hsurj f
  rw [← he₀, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

private def GlobalLifting (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ {G Q : TopCat.Sheaf AddCommGrpCat.{u} X}
    (ι : F ⟶ G) (π : G ⟶ Q) (h : ι ≫ π = 0),
    (ShortComplex.mk ι π h).ShortExact →
      Function.Surjective (π.hom.app (op (⊤ : Opens X)))

private theorem subsingleton_h1_of_globalLifting
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hlift : GlobalLifting F) :
    Subsingleton (CategoryTheory.Sheaf.H.{u} F 1) := by
  let p : InjectivePresentation F := Classical.arbitrary _
  have hS := p.shortExact_shortComplex
  have hglobal := hlift p.f (cokernel.π p.f) (cokernel.condition p.f) hS
  have hhom := hom_surjective_of_global_surjective (cokernel.π p.f) hglobal
  exact subsingleton_ext_one_of_shortExact (TopCat.ConstantSheaf.integralSheaf X) hS hhom

private theorem globalLifting_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [TopCat.Sheaf.IsFlasque F] :
    GlobalLifting F := by
  intro G Q ι π h hS
  have hepi := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) hS
  exact (AddCommGrpCat.epi_iff_surjective _).mp hepi

/-- A flasque sheaf of abelian groups is acyclic in degree one: `H¹(X, F) = 0`
(Hartshorne III Prop. 2.5). -/
theorem subsingleton_h1_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [TopCat.Sheaf.IsFlasque F] :
    Subsingleton (CategoryTheory.Sheaf.H.{u} F 1) :=
  subsingleton_h1_of_globalLifting F (globalLifting_of_isFlasque F)

end TopCat.SheafH1
