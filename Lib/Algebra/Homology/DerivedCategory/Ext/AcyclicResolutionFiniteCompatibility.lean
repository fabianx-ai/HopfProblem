/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolutionH2H3

/-!
# Compatibility of indexed and finite acyclic-resolution comparisons

The finite degree-two and degree-three staircases use Mathlib's chosen kernels, whereas an indexed
resolution carries coherent cycle objects.  This file constructs the canonical cycle isomorphisms
and proves that the finite comparisons are exactly the degree-two and degree-three specializations
of the indexed comparison.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace AcyclicResolution

variable (R : AcyclicResolution (C := C))

/-- Each chosen cycle inclusion is also a kernel of the corresponding literal differential. -/
def iIsKernel (n : ℕ) :
    IsLimit (KernelFork.ofι (R.i n) (R.i_d n)) := by
  let _ : Mono (R.i n) := (R.shortExact n).mono_f
  exact (R.augmentedStep_exact n).fIsKernel

/-- The coherent chosen cycle object in degree `n+1` is canonically isomorphic to the kernel
chosen by Mathlib for the differential out of `X (n+1)`. -/
def nextCycleIso (n : ℕ) : R.Z (n + 1) ≅ kernel (R.d (n + 1)) :=
  IsLimit.conePointUniqueUpToIso (R.iIsKernel (n + 1))
    (limit.isLimit (parallelPair (R.d (n + 1)) 0))

@[reassoc (attr := simp)]
theorem nextCycleIso_hom_kernel_ι (n : ℕ) :
    (R.nextCycleIso n).hom ≫ kernel.ι (R.d (n + 1)) = R.i (n + 1) := by
  simp [nextCycleIso]

/-- The degree-two finite view of an indexed resolution. -/
def toAcyclicResolutionH2 : AcyclicResolutionH2 (C := C) where
  trunc := R.trunc 0
  X₄ := R.X 3
  d₂ := R.d 2
  zero₂ := by
    change R.d 1 ≫ R.d 2 = 0
    exact R.d_comp_d 1
  exact₂ := by
    change (R.localComplex 1).Exact
    exact R.localComplex_exact 1

/-- The degree-three finite view of an indexed resolution. -/
def toAcyclicResolutionH3 : AcyclicResolutionH3 (C := C) where
  toAcyclicResolutionH2 := AcyclicResolution.toAcyclicResolutionH2 R
  X₅ := R.X 4
  d₃ := R.d 3
  zero₃ := by
    change R.d 2 ≫ R.d 3 = 0
    exact R.d_comp_d 2
  exact₃ := by
    change (R.localComplex 2).Exact
    exact R.localComplex_exact 2

/-- The kernel-chosen degree-one truncation used internally by the finite staircase. -/
def kernelTrunc (n : ℕ) : AcyclicResolutionH1 (C := C) where
  F := kernel (R.d (n + 1))
  complex := R.localComplex (n + 1)
  ι := kernel.ι (R.d (n + 1))
  zero := kernel.condition _
  initial_exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  exact := R.localComplex_exact (n + 1)
  mono_ι := inferInstance

/-- The chosen-cycle truncation maps isomorphically on its augmentation to the kernel-chosen
truncation, and identically on the three complex terms. -/
def truncToKernelTrunc (n : ℕ) :
    AcyclicResolutionH1.Hom (R.trunc (n + 1)) (R.kernelTrunc n) where
  augmentation := (R.nextCycleIso n).hom
  complex := 𝟙 _
  comm := by
    dsimp [kernelTrunc, trunc]
    rw [Category.comp_id]
    exact R.nextCycleIso_hom_kernel_ι n

/-- Restricting `p n` to the chosen kernel agrees with the kernel lift used by the finite API. -/
theorem p_nextCycleIso (n : ℕ) :
    R.p n ≫ (R.nextCycleIso n).hom = (R.trunc n).toCycles := by
  change R.p n ≫ (R.nextCycleIso n).hom =
    kernel.lift (R.d (n + 1)) (R.d n) (R.d_comp_d n)
  apply (cancel_mono (kernel.ι (R.d (n + 1)))).mp
  rw [Category.assoc, R.nextCycleIso_hom_kernel_ι, kernel.lift_ι]
  rfl

/-- The `n`th explicit short exact step maps to the first short exact sequence of the finite
kernel-based truncation. -/
def stepToFirst (n : ℕ) : R.step n ⟶ (R.trunc n).first := by
  refine
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (R.nextCycleIso n).hom
      comm₁₂ := by
        change 𝟙 _ ≫ R.i n = R.i n ≫ 𝟙 _
        simp
      comm₂₃ := ?_ }
  change 𝟙 _ ≫ (R.trunc n).toCycles = R.p n ≫ (R.nextCycleIso n).hom
  rw [Category.id_comp]
  exact (R.p_nextCycleIso n).symm

@[simp]
theorem stepToFirst_τ₁ (n : ℕ) : (R.stepToFirst n).τ₁ = 𝟙 _ := rfl

@[simp]
theorem stepToFirst_τ₃ (n : ℕ) : (R.stepToFirst n).τ₃ = (R.nextCycleIso n).hom := rfl

/-- The next explicit short exact step maps to the first sequence of the kernel-chosen tail.
Both endpoint maps are the canonical chosen-cycle-to-kernel isomorphisms. -/
def stepToKernelFirst (n : ℕ) : R.step (n + 1) ⟶ (R.kernelTrunc n).first := by
  refine
    { τ₁ := (R.nextCycleIso n).hom
      τ₂ := 𝟙 _
      τ₃ := (R.nextCycleIso (n + 1)).hom
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · change (R.nextCycleIso n).hom ≫ kernel.ι (R.d (n + 1)) = R.i (n + 1) ≫ 𝟙 _
    rw [Category.comp_id]
    exact R.nextCycleIso_hom_kernel_ι n
  · change 𝟙 _ ≫ (R.kernelTrunc n).toCycles =
      R.p (n + 1) ≫ (R.nextCycleIso (n + 1)).hom
    rw [Category.id_comp]
    exact (R.p_nextCycleIso (n + 1)).symm

@[simp]
theorem stepToKernelFirst_τ₁ (n : ℕ) :
    (R.stepToKernelFirst n).τ₁ = (R.nextCycleIso n).hom := rfl

@[simp]
theorem stepToKernelFirst_τ₃ (n : ℕ) :
    (R.stepToKernelFirst n).τ₃ = (R.nextCycleIso (n + 1)).hom := rfl

@[simp]
theorem toAcyclicResolutionH2_trunc : R.toAcyclicResolutionH2.trunc = R.trunc 0 := rfl

@[simp]
theorem toAcyclicResolutionH2_tail : R.toAcyclicResolutionH2.tail = R.kernelTrunc 0 := rfl

@[simp]
theorem toAcyclicResolutionH3_firstTail :
    R.toAcyclicResolutionH3.tail.trunc = R.kernelTrunc 0 := rfl

@[simp]
theorem toAcyclicResolutionH3_secondTail :
    R.toAcyclicResolutionH3.tail.tail = R.kernelTrunc 1 := rfl

variable [HasExt.{w} C]

/-- The legacy finite degree-two comparison, with all acyclicity instances supplied by the
indexed tower. -/
def legacyExtTwoHom (P : C) (h : R.IsAcyclicFor P) :
    AddCommGrpCat.of (Ext P (R.Z 0) 2) ⟶
      ((R.kernelTrunc 0).extZeroComplex P).homology := by
  let _ : Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₁ 1) := by
    change Subsingleton (Ext P (R.X 0) 1)
    exact h 0 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₁ 2) := by
    change Subsingleton (Ext P (R.X 0) 2)
    exact h 0 2 (by omega)
  let _ : Subsingleton (Ext P R.toAcyclicResolutionH2.trunc.complex.X₂ 1) := by
    change Subsingleton (Ext P (R.X 1) 1)
    exact h 1 1 Nat.zero_lt_one
  exact (R.toAcyclicResolutionH2.extTwoIso P).hom

/-- The legacy finite degree-three comparison, with all acyclicity instances supplied by the
indexed tower. -/
def legacyExtThreeHom (P : C) (h : R.IsAcyclicFor P) :
    AddCommGrpCat.of (Ext P (R.Z 0) 3) ⟶
      ((R.kernelTrunc 1).extZeroComplex P).homology := by
  let _ : Subsingleton
      (Ext P R.toAcyclicResolutionH3.toAcyclicResolutionH2.trunc.complex.X₁ 2) := by
    change Subsingleton (Ext P (R.X 0) 2)
    exact h 0 2 (by omega)
  let _ : Subsingleton
      (Ext P R.toAcyclicResolutionH3.toAcyclicResolutionH2.trunc.complex.X₁ 3) := by
    change Subsingleton (Ext P (R.X 0) 3)
    exact h 0 3 (by omega)
  let _ : Subsingleton
      (Ext P R.toAcyclicResolutionH3.toAcyclicResolutionH2.trunc.complex.X₂ 1) := by
    change Subsingleton (Ext P (R.X 1) 1)
    exact h 1 1 Nat.zero_lt_one
  let _ : Subsingleton
      (Ext P R.toAcyclicResolutionH3.toAcyclicResolutionH2.trunc.complex.X₂ 2) := by
    change Subsingleton (Ext P (R.X 1) 2)
    exact h 1 2 (by omega)
  let _ : Subsingleton
      (Ext P R.toAcyclicResolutionH3.toAcyclicResolutionH2.trunc.complex.X₃ 1) := by
    change Subsingleton (Ext P (R.X 2) 1)
    exact h 2 1 Nat.zero_lt_one
  exact (R.toAcyclicResolutionH3.extThreeIso P).hom

/-- The indexed and legacy degree-two comparisons commute with the canonical change from the
coherently chosen first cycle object to Mathlib's kernel. -/
theorem legacyExtTwoHom_compatibility (P : C) (h : R.IsAcyclicFor P) :
    (extFunctorObj P 2).map (R.stepToFirst 0).τ₁ ≫ R.legacyExtTwoHom P h =
      R.finiteStaircaseHomOne P h ≫
        ShortComplex.homologyMap ((R.truncToKernelTrunc 0).extZeroMap P) := by
  let _ : Subsingleton (Ext P (R.X 0) 1) := h 0 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P (R.X 0) 2) := h 0 2 (by omega)
  let _ : Subsingleton (Ext P (R.X 1) 1) := h 1 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P (R.trunc 0).first.X₂ 1) := by
    change Subsingleton (Ext P (R.X 0) 1)
    infer_instance
  let _ : Subsingleton (Ext P (R.trunc 0).first.X₂ 2) := by
    change Subsingleton (Ext P (R.X 0) 2)
    infer_instance
  let _ : Subsingleton (Ext P (R.trunc 1).complex.X₁ 1) := by
    change Subsingleton (Ext P (R.X 1) 1)
    infer_instance
  let _ : Subsingleton (Ext P (R.kernelTrunc 0).complex.X₁ 1) := by
    change Subsingleton (Ext P (R.X 1) 1)
    infer_instance
  change
    (extFunctorObj P (1 + 1)).map (R.stepToFirst 0).τ₁ ≫
        ((connectingIso P (R.trunc 0).first_shortExact 1).inv ≫
          ((R.kernelTrunc 0).extOneIso P).hom) =
      ((connectingIso P (R.shortExact 0) 1).inv ≫
        ((R.trunc 1).extOneIso P).hom) ≫
          ShortComplex.homologyMap ((R.truncToKernelTrunc 0).extZeroMap P)
  ext x
  change
    ((R.kernelTrunc 0).extOneIso P).hom
        ((connectingIso P (R.trunc 0).first_shortExact 1).inv
          ((extFunctorObj P (1 + 1)).map (R.stepToFirst 0).τ₁ x)) =
      ShortComplex.homologyMap ((R.truncToKernelTrunc 0).extZeroMap P)
        (((R.trunc 1).extOneIso P).hom
          ((connectingIso P (R.shortExact 0) 1).inv x))
  have hδx := congrArg (fun q => q x)
    (connectingIso_inv_naturality P (R.shortExact 0)
      (R.trunc 0).first_shortExact (R.stepToFirst 0) 1)
  change
    (connectingIso P (R.trunc 0).first_shortExact 1).inv
        ((extFunctorObj P (1 + 1)).map (R.stepToFirst 0).τ₁ x) =
      (extFunctorObj P 1).map (R.stepToFirst 0).τ₃
        ((connectingIso P (R.shortExact 0) 1).inv x) at hδx
  rw [hδx]
  rw [R.stepToFirst_τ₃]
  have honex := congrArg
    (fun q => q ((connectingIso P (R.shortExact 0) 1).inv x))
    ((R.truncToKernelTrunc 0).extOneIso_naturality P)
  change
    ((R.kernelTrunc 0).extOneIso P).hom
        ((extFunctorObj P 1).map (R.nextCycleIso 0).hom
          ((connectingIso P (R.shortExact 0) 1).inv x)) =
      ShortComplex.homologyMap ((R.truncToKernelTrunc 0).extZeroMap P)
        (((R.trunc 1).extOneIso P).hom
          ((connectingIso P (R.shortExact 0) 1).inv x)) at honex
  exact honex

/-- Direct degree-two endpoint square for the indexed local comparison. -/
theorem localExtIso_one_legacy_compatibility (P : C) (h : R.IsAcyclicFor P) :
    (extFunctorObj P 2).map (R.stepToFirst 0).τ₁ ≫ R.legacyExtTwoHom P h =
      (R.localExtIso P h 1).hom ≫
        ShortComplex.homologyMap ((R.truncToKernelTrunc 0).extZeroMap P) := by
  rw [R.localExtIso_hom_one]
  exact R.legacyExtTwoHom_compatibility P h

set_option maxHeartbeats 800000 in
/-- The indexed and legacy degree-three comparisons commute with the canonical changes from the
two coherently chosen cycle objects to Mathlib's two kernels. -/
theorem legacyExtThreeHom_compatibility (P : C) (h : R.IsAcyclicFor P) :
    (extFunctorObj P 3).map (R.stepToFirst 0).τ₁ ≫ R.legacyExtThreeHom P h =
      R.finiteStaircaseHomTwo P h ≫
        ShortComplex.homologyMap ((R.truncToKernelTrunc 1).extZeroMap P) := by
  let _ : Subsingleton (Ext P (R.X 0) 2) := h 0 2 (by omega)
  let _ : Subsingleton (Ext P (R.X 0) 3) := h 0 3 (by omega)
  let _ : Subsingleton (Ext P (R.X 1) 1) := h 1 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P (R.X 1) 2) := h 1 2 (by omega)
  let _ : Subsingleton (Ext P (R.X 2) 1) := h 2 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P (R.trunc 0).first.X₂ 2) := by
    change Subsingleton (Ext P (R.X 0) 2)
    infer_instance
  let _ : Subsingleton (Ext P (R.trunc 0).first.X₂ 3) := by
    change Subsingleton (Ext P (R.X 0) 3)
    infer_instance
  let _ : Subsingleton (Ext P (R.kernelTrunc 0).first.X₂ 1) := by
    change Subsingleton (Ext P (R.X 1) 1)
    infer_instance
  let _ : Subsingleton (Ext P (R.kernelTrunc 0).first.X₂ 2) := by
    change Subsingleton (Ext P (R.X 1) 2)
    infer_instance
  let _ : Subsingleton (Ext P (R.trunc 2).complex.X₁ 1) := by
    change Subsingleton (Ext P (R.X 2) 1)
    infer_instance
  let _ : Subsingleton (Ext P (R.kernelTrunc 1).complex.X₁ 1) := by
    change Subsingleton (Ext P (R.X 2) 1)
    infer_instance
  change
    (extFunctorObj P (2 + 1)).map (R.stepToFirst 0).τ₁ ≫
        (((connectingIso P (R.trunc 0).first_shortExact 2).inv ≫
          (connectingIso P (R.kernelTrunc 0).first_shortExact 1).inv) ≫
            ((R.kernelTrunc 1).extOneIso P).hom) =
      (((connectingIso P (R.shortExact 0) 2).inv ≫
        (connectingIso P (R.shortExact 1) 1).inv) ≫
          ((R.trunc 2).extOneIso P).hom) ≫
            ShortComplex.homologyMap ((R.truncToKernelTrunc 1).extZeroMap P)
  ext x
  change
    ((R.kernelTrunc 1).extOneIso P).hom
        ((connectingIso P (R.kernelTrunc 0).first_shortExact 1).inv
          ((connectingIso P (R.trunc 0).first_shortExact 2).inv
            ((extFunctorObj P (2 + 1)).map (R.stepToFirst 0).τ₁ x))) =
      ShortComplex.homologyMap ((R.truncToKernelTrunc 1).extZeroMap P)
        (((R.trunc 2).extOneIso P).hom
          ((connectingIso P (R.shortExact 1) 1).inv
            ((connectingIso P (R.shortExact 0) 2).inv x)))
  have hδ₀x := congrArg (fun q => q x)
    (connectingIso_inv_naturality P (R.shortExact 0)
      (R.trunc 0).first_shortExact (R.stepToFirst 0) 2)
  change
    (connectingIso P (R.trunc 0).first_shortExact 2).inv
        ((extFunctorObj P (2 + 1)).map (R.stepToFirst 0).τ₁ x) =
      (extFunctorObj P 2).map (R.stepToFirst 0).τ₃
        ((connectingIso P (R.shortExact 0) 2).inv x) at hδ₀x
  rw [hδ₀x, R.stepToFirst_τ₃]
  let y : Ext P (R.Z 1) 2 := (connectingIso P (R.shortExact 0) 2).inv x
  change
    ((R.kernelTrunc 1).extOneIso P).hom
        ((connectingIso P (R.kernelTrunc 0).first_shortExact 1).inv
          ((extFunctorObj P 2).map (R.nextCycleIso 0).hom y)) =
      ShortComplex.homologyMap ((R.truncToKernelTrunc 1).extZeroMap P)
        (((R.trunc 2).extOneIso P).hom
          ((connectingIso P (R.shortExact 1) 1).inv y))
  have hδ₁y := congrArg (fun q => q y)
    (connectingIso_inv_naturality P (R.shortExact 1)
      (R.kernelTrunc 0).first_shortExact (R.stepToKernelFirst 0) 1)
  change
    (connectingIso P (R.kernelTrunc 0).first_shortExact 1).inv
        ((extFunctorObj P 2).map (R.nextCycleIso 0).hom y) =
      (extFunctorObj P 1).map (R.nextCycleIso 1).hom
        ((connectingIso P (R.shortExact 1) 1).inv y) at hδ₁y
  rw [hδ₁y]
  let z := (connectingIso P (R.shortExact 1) 1).inv y
  have honez := congrArg (fun q => q z)
    ((R.truncToKernelTrunc 1).extOneIso_naturality P)
  change
    ((R.kernelTrunc 1).extOneIso P).hom
        ((extFunctorObj P 1).map (R.nextCycleIso 1).hom z) =
      ShortComplex.homologyMap ((R.truncToKernelTrunc 1).extZeroMap P)
        (((R.trunc 2).extOneIso P).hom z) at honez
  exact honez

/-- Direct degree-three endpoint square for the indexed local comparison. -/
theorem localExtIso_two_legacy_compatibility (P : C) (h : R.IsAcyclicFor P) :
    (extFunctorObj P 3).map (R.stepToFirst 0).τ₁ ≫ R.legacyExtThreeHom P h =
      (R.localExtIso P h 2).hom ≫
        ShortComplex.homologyMap ((R.truncToKernelTrunc 1).extZeroMap P) := by
  rw [R.localExtIso_hom_two]
  exact R.legacyExtThreeHom_compatibility P h

end AcyclicResolution

end CategoryTheory.Abelian.Ext
