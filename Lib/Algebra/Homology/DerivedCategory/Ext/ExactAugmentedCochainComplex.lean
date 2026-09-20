/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolution

/-!
# Exact augmented cochain complexes as indexed acyclic resolutions

This file records the standard textbook passage from an augmented cochain complex

`0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯`

which is exact in every degree to the tower of short exact sequences obtained from its cycle
objects.  The cycle objects are the actual categorical kernels of the outgoing differentials.
No injective, flasque, or sheaf-specific hypothesis occurs here.

## References

* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §2.4 (breaking a
  resolution into short exact sequences).
* [R. Hartshorne, *Algebraic geometry*][hartshorne77], Chapter III, §1.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option genSizeOf false in
/-- An exact augmented cochain complex in nonnegative degrees.

The field `positiveExact n` is exactness at `K^(n+1)`.  Keeping this in literal three-term form
makes the construction independent of any particular indexing API for `ExactAt`.
-/
structure ExactAugmentedCochainComplex where
  F : C
  complex : CochainComplex C ℕ
  ι : F ⟶ complex.X 0
  zero : ι ≫ complex.d 0 1 = 0
  initialExact : (ShortComplex.mk ι (complex.d 0 1) zero).Exact
  mono_ι : Mono ι
  positiveExact : ∀ n : ℕ,
    (ShortComplex.mk (complex.d n (n + 1)) (complex.d (n + 1) (n + 2))
      (complex.d_comp_d n (n + 1) (n + 2))).Exact

namespace ExactAugmentedCochainComplex

variable (R : ExactAugmentedCochainComplex (C := C))

/-- The augmented object in degree zero and the actual cycle object thereafter. -/
def Z : ℕ → C
  | 0 => R.F
  | n + 1 => kernel (R.complex.d (n + 1) (n + 2))

/-- Inclusion of the augmentation in degree zero and inclusion of cycles thereafter. -/
def i : ∀ n : ℕ, R.Z n ⟶ R.complex.X n
  | 0 => R.ι
  | n + 1 => kernel.ι (R.complex.d (n + 1) (n + 2))

/-- The differential with codomain restricted to the next cycle object. -/
def p (n : ℕ) : R.complex.X n ⟶ R.Z (n + 1) :=
  kernel.lift (R.complex.d (n + 1) (n + 2)) (R.complex.d n (n + 1))
    (R.complex.d_comp_d n (n + 1) (n + 2))

/-- The restricted differential followed by the cycle inclusion is the original differential. -/
@[reassoc (attr := simp)]
theorem p_i (n : ℕ) : R.p n ≫ R.i (n + 1) = R.complex.d n (n + 1) := by
  exact kernel.lift_ι _ _ _

/-- Two consecutive maps of the cycle tower compose to zero. -/
@[reassoc (attr := simp)]
theorem i_p (n : ℕ) : R.i n ≫ R.p n = 0 := by
  have hi : Mono (R.i (n + 1)) := by
    change Mono (kernel.ι (R.complex.d (n + 1) (n + 2)))
    infer_instance
  let _ : Mono (R.i (n + 1)) := hi
  apply (cancel_mono (R.i (n + 1))).mp
  rw [Category.assoc, R.p_i, Limits.zero_comp]
  cases n with
  | zero => exact R.zero
  | succ n => exact kernel.condition _

/-- Before restricting the differential's codomain, the step is exact at its middle object. -/
abbrev unfactoredStep (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (R.i n) (R.complex.d n (n + 1)) (by
    cases n with
    | zero => exact R.zero
    | succ n => exact kernel.condition _)

/-- The sequence `Zⁿ ⟶ Kⁿ ⟶ Kⁿ⁺¹` is exact at `Kⁿ`. -/
theorem unfactoredStep_exact (n : ℕ) : (R.unfactoredStep n).Exact := by
  cases n with
  | zero => exact R.initialExact
  | succ n => exact ShortComplex.exact_kernel _

/-- The short exact step after replacing the next term by its cycle object. -/
abbrev step (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (R.i n) (R.p n) (R.i_p n)

/-- The comparison from the factored step to the original differential. -/
def stepToUnfactored (n : ℕ) : R.step n ⟶ R.unfactoredStep n where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := R.i (n + 1)
  comm₁₂ := by simp
  comm₂₃ := by simp

/-- The sequence `Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹` is exact at `Kⁿ`. -/
theorem step_exact (n : ℕ) : (R.step n).Exact := by
  let φ := R.stepToUnfactored n
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 (R.Z n)))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (R.complex.X n)))
  have : Mono φ.τ₃ := by
    change Mono (kernel.ι (R.complex.d (n + 1) (n + 2)))
    infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (R.unfactoredStep_exact n)

/-- Every cycle inclusion is a monomorphism. -/
theorem mono_i (n : ℕ) : Mono (R.i n) := by
  cases n with
  | zero => exact R.mono_ι
  | succ n =>
      change Mono (kernel.ι (R.complex.d (n + 1) (n + 2)))
      infer_instance

/-- The differential with codomain restricted to the next cycle object is an epimorphism. -/
theorem epi_p (n : ℕ) : Epi (R.p n) := by
  exact (R.positiveExact n).epi_kernelLift

/-- The sequence `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0` is short exact: this is the standard
breaking-up of a resolution into short exact sequences. -/
theorem step_shortExact (n : ℕ) : (R.step n).ShortExact :=
  ShortComplex.ShortExact.mk' (R.step_exact n) (R.mono_i n) (R.epi_p n)

/-- The canonical indexed acyclic resolution carried by an exact augmented cochain complex. -/
def toAcyclicResolution : AcyclicResolution (C := C) where
  Z := R.Z
  X := R.complex.X
  i := R.i
  p := R.p
  zero := R.i_p
  shortExact := R.step_shortExact

/-- The cycle object in degree zero of the associated resolution is the augmentation object `F`. -/
@[simp]
theorem toAcyclicResolution_Z_zero : R.toAcyclicResolution.Z 0 = R.F := rfl

/-- The associated resolution has the terms of the original cochain complex. -/
@[simp]
theorem toAcyclicResolution_X (n : ℕ) : R.toAcyclicResolution.X n = R.complex.X n := rfl

/-- The degree-zero inclusion of the associated resolution is the augmentation. -/
@[simp]
theorem toAcyclicResolution_i_zero : R.toAcyclicResolution.i 0 = R.ι := rfl

/-- The differential reconstructed from the cycle tower is the original differential. -/
theorem toAcyclicResolution_d (n : ℕ) :
    R.toAcyclicResolution.d n = R.complex.d n (n + 1) := by
  exact R.p_i n

/-- The reconstructed resolution complex is canonically the original cochain complex. -/
def resolutionComplexIso : R.toAcyclicResolution.complex ≅ R.complex :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    subst j
    rw [AcyclicResolution.complex_d, R.toAcyclicResolution_d]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

end ExactAugmentedCochainComplex

end CategoryTheory.Abelian.Ext
