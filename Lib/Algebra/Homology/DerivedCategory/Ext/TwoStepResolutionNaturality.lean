/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.CochainTransgression

/-!
# Naturality of two-step resolution classes

A map between four-term exact sequences induces compatible maps between the two constituent
short exact sequences.  This file constructs those maps through the intermediate boundary
kernels and proves naturality of the resulting positive two-step Ext class.

The comparison applies to arbitrary morphisms of exact sequences; no component is required to
be an isomorphism.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.ExtTransgression.TwoStepResolution

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A commuting map between the four objects and three arrows of two two-step resolutions. -/
structure Hom (R S : TwoStepResolution (C := C)) where
  τF : R.F ⟶ S.F
  τ₁ : R.complex.X₁ ⟶ S.complex.X₁
  τ₂ : R.complex.X₂ ⟶ S.complex.X₂
  τ₃ : R.complex.X₃ ⟶ S.complex.X₃
  comm_ι : τF ≫ S.ι = R.ι ≫ τ₁ := by cat_disch
  comm_f : τ₁ ≫ S.complex.f = R.complex.f ≫ τ₂ := by cat_disch
  comm_g : τ₂ ≫ S.complex.g = R.complex.g ≫ τ₃ := by cat_disch

namespace Hom

variable {R S : TwoStepResolution (C := C)} (f : Hom R S)

/-- The map induced on the intermediate boundary kernels. -/
def boundary : R.boundary ⟶ S.boundary :=
  kernel.map R.complex.g S.complex.g f.τ₂ f.τ₃ f.comm_g.symm

@[reassoc (attr := simp)]
lemma boundary_ι : f.boundary ≫ kernel.ι S.complex.g = kernel.ι R.complex.g ≫ f.τ₂ := by
  exact kernel.lift_ι _ _ _

/-- The induced morphism between the first short exact sequences. -/
def first : R.first ⟶ S.first where
  τ₁ := f.τF
  τ₂ := f.τ₁
  τ₃ := f.boundary
  comm₁₂ := f.comm_ι
  comm₂₃ := (kernel.lift_map R.complex.f R.complex.g R.complex.zero
    S.complex.f S.complex.g S.complex.zero f.τ₁ f.τ₂ f.τ₃
    f.comm_f.symm f.comm_g.symm).symm

/-- The induced morphism between the second short exact sequences. -/
def second : R.second ⟶ S.second where
  τ₁ := f.boundary
  τ₂ := f.τ₂
  τ₃ := f.τ₃
  comm₁₂ := f.boundary_ι
  comm₂₃ := f.comm_g

variable [HasExt.{v} C]

/-- Covariantly mapping the input and output of a two-step connecting class gives the
two-step connecting class of the mapped resolution. -/
lemma connectingTwo_naturality (P : C) (x : Ext.{v} P R.complex.X₃ 0) :
    S.connectingTwo P (x.comp (Ext.mk₀ f.τ₃) (add_zero 0)) =
      (R.connectingTwo P x).comp (Ext.mk₀ f.τF) (add_zero 2) := by
  change
    (((x.comp (Ext.mk₀ f.τ₃) (add_zero 0)).comp
        S.second_shortExact.extClass rfl).comp
      S.first_shortExact.extClass rfl) =
    (((x.comp R.second_shortExact.extClass rfl).comp
      R.first_shortExact.extClass rfl).comp (Ext.mk₀ f.τF) (add_zero 2))
  have hfirst :
      R.first_shortExact.extClass.comp (Ext.mk₀ f.τF) (add_zero 1) =
        (Ext.mk₀ f.boundary).comp S.first_shortExact.extClass (zero_add 1) := by
    simpa only [first] using ShortComplex.ShortExact.extClass_naturality
      R.first_shortExact S.first_shortExact f.first
  have hsecond :
      R.second_shortExact.extClass.comp (Ext.mk₀ f.boundary) (add_zero 1) =
        (Ext.mk₀ f.τ₃).comp S.second_shortExact.extClass (zero_add 1) := by
    simpa only [second] using ShortComplex.ShortExact.extClass_naturality
      R.second_shortExact S.second_shortExact f.second
  symm
  calc
    (((x.comp R.second_shortExact.extClass rfl).comp
        R.first_shortExact.extClass rfl).comp (Ext.mk₀ f.τF) (add_zero 2)) =
      (x.comp R.second_shortExact.extClass rfl).comp
        (R.first_shortExact.extClass.comp (Ext.mk₀ f.τF) (add_zero 1)) rfl := by
          rw [Ext.comp_assoc_of_third_deg_zero]
    _ = (x.comp R.second_shortExact.extClass rfl).comp
        ((Ext.mk₀ f.boundary).comp S.first_shortExact.extClass (zero_add 1)) rfl := by
          rw [hfirst]
    _ = (((x.comp R.second_shortExact.extClass rfl).comp
        (Ext.mk₀ f.boundary) (add_zero 1)).comp
          S.first_shortExact.extClass rfl) := by
            rw [Ext.comp_assoc_of_second_deg_zero]
    _ = ((x.comp (R.second_shortExact.extClass.comp
        (Ext.mk₀ f.boundary) (add_zero 1)) rfl).comp
          S.first_shortExact.extClass rfl) := by
            rw [Ext.comp_assoc_of_third_deg_zero]
    _ = ((x.comp ((Ext.mk₀ f.τ₃).comp
        S.second_shortExact.extClass (zero_add 1)) rfl).comp
          S.first_shortExact.extClass rfl) := by
            rw [hsecond]
    _ = (((x.comp (Ext.mk₀ f.τ₃) (add_zero 0)).comp
        S.second_shortExact.extClass rfl).comp
          S.first_shortExact.extClass rfl) := by
            rw [Ext.comp_assoc_of_second_deg_zero]

end Hom

end CategoryTheory.Abelian.ExtTransgression.TwoStepResolution
