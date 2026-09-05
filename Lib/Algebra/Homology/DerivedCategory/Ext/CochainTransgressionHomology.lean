/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.CochainTransgression
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# The cochain transgression with a homology source

The native two-step cochain transgression lands in degree-two Ext from the cycles object.  This
file pushes that class along the homology quotient and identifies the result with the two short
exact sequences in the canonical four-term exact sequence

`0 → HⁿK → Kⁿ / BⁿK → Zⁿ⁺¹K → Hⁿ⁺¹K → 0`.

The comparison fixes the Yoneda-product orientation and introduces no sign.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Abelian.ExtTransgression

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The short complex `Kⁿ / BⁿK → Zⁿ⁺¹K → Hⁿ⁺¹K`. -/
abbrev homologyCyclesComplex (K : CochainComplex C ℕ) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.opcyclesToCycles n (n + 1)) (K.homologyπ (n + 1))
    (K.opcyclesToCycles_homologyπ n (n + 1))

/-- The canonical exact sequence
`0 → HⁿK → Kⁿ / BⁿK → Zⁿ⁺¹K → Hⁿ⁺¹K → 0` as a two-step resolution. -/
def homologyTwoStepResolution (K : CochainComplex C ℕ) (n : ℕ) :
    TwoStepResolution (C := C) where
  F := K.homology n
  complex := homologyCyclesComplex K n
  ι := K.homologyι n
  zero := K.homologyι_opcyclesToCycles n (n + 1)
  initial_exact :=
    (HomologicalComplex.HomologySequence.composableArrows₃_exact
      K n (n + 1) rfl).exact 0
  exact :=
    (HomologicalComplex.HomologySequence.composableArrows₃_exact
      K n (n + 1) rfl).exact 1
  mono_ι := inferInstanceAs (Mono (K.homologyι n))
  epi_g := inferInstanceAs (Epi (K.homologyπ (n + 1)))

/-- The first short exact sequence of `cyclesResolution` maps to the first short exact sequence
of `homologyTwoStepResolution` through the homology quotient. -/
def cyclesToHomologyFirst (K : CochainComplex C ℕ) (n : ℕ) :
    (cyclesResolution K n).first ⟶ (homologyTwoStepResolution K n).first where
  τ₁ := K.homologyπ n
  τ₂ := K.pOpcycles n
  τ₃ := 𝟙 _
  comm₁₂ := by
    dsimp [TwoStepResolution.first, cyclesResolution, homologyTwoStepResolution]
    exact K.homology_π_ι n
  comm₂₃ := by
    change K.pOpcycles n ≫
        kernel.lift (K.homologyπ (n + 1)) (K.opcyclesToCycles n (n + 1))
          (K.opcyclesToCycles_homologyπ n (n + 1)) =
      kernel.lift (K.homologyπ (n + 1)) (K.toCycles n (n + 1))
          (K.toCycles_comp_homologyπ n (n + 1)) ≫ 𝟙 _
    rw [Category.comp_id, ← cancel_mono (kernel.ι (K.homologyπ (n + 1))),
      Category.assoc, kernel.lift_ι, kernel.lift_ι]
    exact K.pOpcycles_opcyclesToCycles n (n + 1)

variable [HasExt.{v} C]

set_option backward.isDefEq.respectTransparency false

/-- Pushing the first cycles extension along `ZⁿK → HⁿK` gives the canonical first
extension in `homologyTwoStepResolution`. -/
lemma cyclesFirst_extClass_comp_homologyπ (K : CochainComplex C ℕ) (n : ℕ) :
    (cyclesResolution K n).first_shortExact.extClass.comp
        (Ext.mk₀ (K.homologyπ n)) (add_zero 1) =
      (homologyTwoStepResolution K n).first_shortExact.extClass := by
  simpa only [cyclesToHomologyFirst, Ext.mk₀_id_comp] using
    ShortComplex.ShortExact.extClass_naturality
      (cyclesResolution K n).first_shortExact
      (homologyTwoStepResolution K n).first_shortExact
      (cyclesToHomologyFirst K n)

/-- After covariantly mapping along `ZⁿK → HⁿK`, the native cochain transgression is
the positive Yoneda product of the two canonical homology short exact sequences. -/
lemma cochainTransgression_comp_homologyπ
    (K : CochainComplex C ℕ) (n : ℕ) (P : C) :
    cochainTransgression K n P ≫
        (extFunctorObj P 2).map (K.homologyπ n) =
      (Ext.addEquiv₀ (X := P) (Y := K.homology (n + 1))).toAddCommGrpIso.inv ≫
        AddCommGrpCat.ofHom ((homologyTwoStepResolution K n).connectingTwo P) := by
  ext x
  change (((Ext.addEquiv₀.symm x).comp
      (cyclesResolution K n).second_shortExact.extClass rfl).comp
      (cyclesResolution K n).first_shortExact.extClass rfl).comp
      (Ext.mk₀ (K.homologyπ n)) (add_zero 2) =
    ((Ext.addEquiv₀.symm x).comp
      (homologyTwoStepResolution K n).second_shortExact.extClass rfl).comp
      (homologyTwoStepResolution K n).first_shortExact.extClass rfl
  rw [Ext.comp_assoc, cyclesFirst_extClass_comp_homologyπ]
  all_goals omega

end CategoryTheory.Abelian.ExtTransgression
