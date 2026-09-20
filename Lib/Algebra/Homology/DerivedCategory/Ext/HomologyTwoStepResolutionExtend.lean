/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Lib.Algebra.Homology.DerivedCategory.Ext.CochainTransgressionHomology
public import Lib.Algebra.Homology.DerivedCategory.Ext.TwoStepResolutionNaturality
public import Lib.Algebra.Homology.Embedding.ExtendHomologySequence

/-!
# Homology two-step resolutions under extension of a complex

The cycles, opcycles, and homology isomorphisms for extension along a complex-shape embedding
assemble into a morphism from the extended four-term homology sequence to the original one.
Naturality of two-step extension classes then compares their positive Yoneda products.

The final two declarations specialize the comparison to the standard extension of a
natural-graded cochain complex to integer degrees.  This is the grading bridge used when a
cochain transgression is compared with the Postnikov tower of its derived object.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Abelian.ExtTransgression

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The four-term homology sequence of an extended complex maps canonically to the original
sequence in any two degrees carried to the specified target degrees. -/
def homologyTwoStepResolutionExtendHom
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex C c) (e : c.Embedding c')
    {i j : ι} {i' j' : ι'} (hij : c.Rel i j) (hij' : c'.Rel i' j')
    (hi : e.f i = i') (hj : e.f j = j')
    [K.HasHomology i] [K.HasHomology j]
    [(K.extend e).HasHomology i'] [(K.extend e).HasHomology j'] :
    TwoStepResolution.Hom
      (homologyTwoStepResolutionOfRel (K.extend e) i' j' hij')
      (homologyTwoStepResolutionOfRel K i j hij) where
  τF := (K.extendHomologyIso e hi).hom
  τ₁ := (K.extendOpcyclesIso e hi).hom
  τ₂ := (K.extendCyclesIso e hj).hom
  τ₃ := (K.extendHomologyIso e hj).hom
  comm_ι := by
    exact K.extendHomologyIso_hom_homologyι e hi
  comm_f := by
    exact (K.extend_opcyclesToCycles e hi hj).symm
  comm_g := by
    exact (K.homologyπ_extendHomologyIso_hom e hj).symm

variable [HasExt.{v} C]

/-- Naturality of the positive homology two-step class under extension of a complex. -/
lemma homologyTwoStepResolutionExtend_connectingTwo
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex C c) (e : c.Embedding c')
    {i j : ι} {i' j' : ι'} (hij : c.Rel i j) (hij' : c'.Rel i' j')
    (hi : e.f i = i') (hj : e.f j = j')
    [K.HasHomology i] [K.HasHomology j]
    [(K.extend e).HasHomology i'] [(K.extend e).HasHomology j']
    (P : C) (x : Ext.{v} P ((K.extend e).homology j') 0) :
    (homologyTwoStepResolutionOfRel K i j hij).connectingTwo P
        (x.comp (Ext.mk₀ (K.extendHomologyIso e hj).hom) (add_zero 0)) =
      ((homologyTwoStepResolutionOfRel (K.extend e) i' j' hij').connectingTwo P x).comp
        (Ext.mk₀ (K.extendHomologyIso e hi).hom) (add_zero 2) := by
  exact (homologyTwoStepResolutionExtendHom K e hij hij' hi hj).connectingTwo_naturality P x

/-- The native homology two-step resolution of a natural-graded cochain complex is the target
of the corresponding resolution after extension to integer degrees. -/
def homologyTwoStepResolutionExtendUpNatHom (K : CochainComplex C ℕ) (q : ℕ) :
    TwoStepResolution.Hom
      (homologyTwoStepResolutionInt (K.extend ComplexShape.embeddingUpNat) (q : ℤ))
      (homologyTwoStepResolution K q) :=
  homologyTwoStepResolutionExtendHom K ComplexShape.embeddingUpNat
    (ComplexShape.up_mk q (q + 1) rfl)
    (ComplexShape.up_mk (q : ℤ) ((q : ℤ) + 1) (by omega))
    rfl (by simp)

/-- The positive two-step class of the integer extension agrees with the native natural-graded
class after the canonical homology transports. -/
lemma homologyTwoStepResolutionExtendUpNat_connectingTwo
    (K : CochainComplex C ℕ) (q : ℕ) (P : C)
    (x : Ext.{v} P
      ((K.extend ComplexShape.embeddingUpNat).homology ((q : ℤ) + 1)) 0) :
    (homologyTwoStepResolution K q).connectingTwo P
        (x.comp (Ext.mk₀
          (K.extendHomologyIso ComplexShape.embeddingUpNat (j := q + 1) (by simp)).hom)
          (add_zero 0)) =
      ((homologyTwoStepResolutionInt
        (K.extend ComplexShape.embeddingUpNat) (q : ℤ)).connectingTwo P x).comp
        (Ext.mk₀ (K.extendHomologyIso ComplexShape.embeddingUpNat (j := q) rfl).hom)
        (add_zero 2) := by
  exact (homologyTwoStepResolutionExtendUpNatHom K q).connectingTwo_naturality P x

end CategoryTheory.Abelian.ExtTransgression
