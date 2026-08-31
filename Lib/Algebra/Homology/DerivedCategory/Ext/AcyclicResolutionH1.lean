/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Lib.Algebra.Homology.ShortComplex.LeftHomologyData

/-!
# Degree-one Ext from a length-two acyclic resolution

This is the degree-one part of the standard acyclic-resolution comparison.  It works in an
arbitrary abelian category with small Ext groups.  Given an augmented complex
`0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ K²` exact through degree one, it identifies `Ext¹(P,F)` with the homology of the degree-zero
`Ext` complex, assuming only `Ext¹(P,K⁰) = 0`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

section Ext

variable [HasExt.{w} C]

/-- The connecting homomorphism in the covariant long exact Ext sequence. -/
def connecting (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    Ext P S.X₃ n →+ Ext P S.X₁ (n + 1) :=
  hS.extClass.postcomp P rfl

@[simp]
theorem connecting_apply (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) (x : Ext P S.X₃ n) :
    connecting P hS n x = x.comp hS.extClass rfl := rfl

/-- Vanishing of the next Ext group of the middle term makes the connecting map surjective. -/
theorem connecting_surjective (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) [Subsingleton (Ext P S.X₂ (n + 1))] :
    Function.Surjective (connecting P hS n) := by
  intro x
  exact covariant_sequence_exact₁ P hS x (Subsingleton.elim _ _) rfl

/-- Exactness immediately before the connecting map. -/
theorem connecting_exact (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((mk₀ S.g).postcomp P (add_zero n)) (connecting P hS n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (covariant_sequence_exact₃' P hS n (n + 1) rfl)

end Ext

/-- An augmented complex exact through degree one. -/
structure AcyclicResolutionH1 where
  F : C
  complex : ShortComplex C
  ι : F ⟶ complex.X₁
  zero : ι ≫ complex.f = 0
  initial_exact : (ShortComplex.mk ι complex.f zero).Exact
  exact : complex.Exact
  mono_ι : Mono ι

namespace AcyclicResolutionH1

variable (R : AcyclicResolutionH1 (C := C))

attribute [instance] mono_ι

/-- The kernel separating an augmented length-two resolution into two short exact sequences. -/
abbrev cycles : C := kernel R.complex.g

/-- The first differential with codomain restricted to the kernel of the second. -/
def toCycles : R.complex.X₁ ⟶ R.cycles :=
  kernel.lift R.complex.g R.complex.f R.complex.zero

@[reassoc (attr := simp)]
theorem toCycles_ι : R.toCycles ≫ kernel.ι R.complex.g = R.complex.f :=
  kernel.lift_ι _ _ _

theorem augmentation_toCycles : R.ι ≫ R.toCycles = 0 := by
  apply (cancel_mono (kernel.ι R.complex.g)).mp
  simp only [Category.assoc, toCycles_ι, R.zero, Limits.zero_comp]

/-- The short exact sequence `0 ⟶ F ⟶ K⁰ ⟶ cycles ⟶ 0`. -/
abbrev first : ShortComplex C :=
  ShortComplex.mk R.ι R.toCycles R.augmentation_toCycles

theorem first_shortExact : R.first.ShortExact where
  exact := by
    let φ : R.first ⟶ ShortComplex.mk R.ι R.complex.f R.zero :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι R.complex.g
        comm₁₂ := by simp [first]
        comm₂₃ := by simp [first] }
    have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 R.F))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 R.complex.X₁))
    have : Mono φ.τ₃ := inferInstanceAs (Mono (kernel.ι R.complex.g))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr R.initial_exact
  mono_f := R.mono_ι
  epi_g := R.exact.epi_kernelLift

variable (P : C)

variable [HasExt.{w} C]

/-- The degree-zero Ext complex obtained by applying `Ext⁰(P,-)`. -/
abbrev extZeroComplex : ShortComplex AddCommGrpCat.{w} :=
  R.complex.map (extFunctorObj P 0)

/-- Left homology data exhibiting `Ext¹(P,F)` as homology of the degree-zero Ext complex. -/
def extOneHomologyData [Subsingleton (Ext P R.complex.X₁ 1)] :
    (R.extZeroComplex P).LeftHomologyData := by
  let i : AddCommGrpCat.of (Ext P R.cycles 0) ⟶ (R.extZeroComplex P).X₂ :=
    (extFunctorObj P 0).map (kernel.ι R.complex.g)
  let a : (R.extZeroComplex P).X₁ ⟶ AddCommGrpCat.of (Ext P R.cycles 0) :=
    (extFunctorObj P 0).map R.toCycles
  let p : AddCommGrpCat.of (Ext P R.cycles 0) ⟶ AddCommGrpCat.of (Ext P R.F 1) :=
    AddCommGrpCat.ofHom (connecting P R.first_shortExact 0)
  have hiMono : Mono i := mono_postcomp_mk₀_of_mono P (kernel.ι R.complex.g)
  have hpEpi : Epi p := (AddCommGrpCat.epi_iff_surjective _).mpr
    (connecting_surjective P R.first_shortExact 0)
  have wi : i ≫ (R.extZeroComplex P).g = 0 := by
    change (extFunctorObj P 0).map (kernel.ι R.complex.g) ≫
        (extFunctorObj P 0).map R.complex.g = 0
    rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
  have wa : a ≫ i = (R.extZeroComplex P).f := by
    change (extFunctorObj P 0).map R.toCycles ≫
      (extFunctorObj P 0).map (kernel.ι R.complex.g) =
        (extFunctorObj P 0).map R.complex.f
    rw [← Functor.map_comp, R.toCycles_ι]
  have wp : a ≫ p = 0 := by
    ext x
    exact (connecting_exact P R.first_shortExact 0 _).mpr ⟨x, rfl⟩
  have hi : (ShortComplex.mk i (R.extZeroComplex P).g wi).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    obtain ⟨f, rfl⟩ := addEquiv₀.symm.surjective x
    change (mk₀ f).comp (mk₀ R.complex.g) (add_zero 0) = 0 at hx
    rw [mk₀_comp_mk₀, mk₀_eq_zero_iff] at hx
    refine ⟨mk₀ (kernel.lift R.complex.g f hx), ?_⟩
    change (mk₀ (kernel.lift R.complex.g f hx)).comp
      (mk₀ (kernel.ι R.complex.g)) (add_zero 0) = mk₀ f
    rw [mk₀_comp_mk₀, kernel.lift_ι]
  exact @ShortComplex.leftHomologyDataOfExact AddCommGrpCat.{w} _ _
    (R.extZeroComplex P) (AddCommGrpCat.of (Ext P R.cycles 0))
    (AddCommGrpCat.of (Ext P R.F 1)) i a p wi wa wp
    hi
    ((ShortComplex.ab_exact_iff_function_exact _).mpr
      (connecting_exact P R.first_shortExact 0)) hiMono hpEpi

/-- The canonical degree-one acyclic-resolution comparison. -/
def extOneIso [Subsingleton (Ext P R.complex.X₁ 1)] :
    AddCommGrpCat.of (Ext P R.F 1) ≅ (R.extZeroComplex P).homology :=
  (R.extOneHomologyData P).homologyIso.symm

end AcyclicResolutionH1

end CategoryTheory.Abelian.Ext
