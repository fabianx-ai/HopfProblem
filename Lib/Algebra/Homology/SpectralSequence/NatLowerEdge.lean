/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# The bottom-left `d₂` of a first-quadrant spectral sequence

This file isolates a small first-quadrant fact which does not require a global column bound.
If the source `(0,1)` and target `(2,0)` vanish on page four, then the page-two differential
between them is an isomorphism.  Indeed, both bidegrees have no incoming or outgoing
differentials on page three, so page three already equals page four there.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence.NatLowerEdge

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : E₂CohomologicalSpectralSequenceNat C)

private theorem pageTwo_zeroOne_dTo_eq_zero :
    (P.page 2).dTo (0, 1) = 0 := by
  apply (P.page 2).dTo_eq_zero
  intro h
  rw [ComplexShape.spectralSequenceNat_rel_iff] at h
  omega

private theorem pageTwo_twoZero_dFrom_eq_zero :
    (P.page 2).dFrom (2, 0) = 0 := by
  apply (P.page 2).dFrom_eq_zero
  intro h
  rw [ComplexShape.spectralSequenceNat_rel_iff] at h
  omega

private noncomputable def pageThreeZeroOneIsoPageFour :
    (P.page 3).X (0, 1) ≅ (P.page 4).X (0, 1) := by
  have hTo : (P.page 3).dTo (0, 1) = 0 := by
    apply (P.page 3).dTo_eq_zero
    intro h
    rw [ComplexShape.spectralSequenceNat_rel_iff] at h
    omega
  have hFrom : (P.page 3).dFrom (0, 1) = 0 := by
    apply (P.page 3).dFrom_eq_zero
    intro h
    rw [ComplexShape.spectralSequenceNat_rel_iff] at h
    omega
  exact
    ((ShortComplex.HomologyData.ofZeros ((P.page 3).sc (0, 1)) hTo hFrom).left.homologyIso).symm ≪≫
      P.iso 3 4 (0, 1) (by omega)

private noncomputable def pageThreeTwoZeroIsoPageFour :
    (P.page 3).X (2, 0) ≅ (P.page 4).X (2, 0) := by
  have hTo : (P.page 3).dTo (2, 0) = 0 := by
    apply (P.page 3).dTo_eq_zero
    intro h
    rw [ComplexShape.spectralSequenceNat_rel_iff] at h
    omega
  have hFrom : (P.page 3).dFrom (2, 0) = 0 := by
    apply (P.page 3).dFrom_eq_zero
    intro h
    rw [ComplexShape.spectralSequenceNat_rel_iff] at h
    omega
  exact
    ((ShortComplex.HomologyData.ofZeros ((P.page 3).sc (2, 0)) hTo hFrom).left.homologyIso).symm ≪≫
      P.iso 3 4 (2, 0) (by omega)

/-- Page-four vanishing at `(0,1)` makes the bottom-left page-two differential monic. -/
theorem mono_d₂_zeroOne_twoZero_of_isZero_pageFour
    (h : IsZero ((P.page 4).X (0, 1))) :
    Mono ((P.page 2).d (0, 1) (2, 0)) := by
  have hpage3 : IsZero ((P.page 3).X (0, 1)) :=
    IsZero.of_iso h (pageThreeZeroOneIsoPageFour P)
  have hhomology : IsZero ((P.page 2).homology (0, 1)) :=
    IsZero.of_iso hpage3 (P.iso 2 3 (0, 1) (by omega))
  have hexact : (P.page 2).ExactAt (0, 1) :=
    ((P.page 2).exactAt_iff_isZero_homology (0, 1)).2 hhomology
  have : Mono ((P.page 2).dFrom (0, 1)) :=
    hexact.mono_g (pageTwo_zeroOne_dTo_eq_zero P)
  have hrel :
      (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (0, 1) (2, 0) := by
    rw [ComplexShape.spectralSequenceNat_rel_iff]
    omega
  rw [← (P.page 2).dFrom_comp_xNextIso hrel]
  infer_instance

/-- Page-four vanishing at `(2,0)` makes the bottom-left page-two differential epic. -/
theorem epi_d₂_zeroOne_twoZero_of_isZero_pageFour
    (h : IsZero ((P.page 4).X (2, 0))) :
    Epi ((P.page 2).d (0, 1) (2, 0)) := by
  have hpage3 : IsZero ((P.page 3).X (2, 0)) :=
    IsZero.of_iso h (pageThreeTwoZeroIsoPageFour P)
  have hhomology : IsZero ((P.page 2).homology (2, 0)) :=
    IsZero.of_iso hpage3 (P.iso 2 3 (2, 0) (by omega))
  have hexact : (P.page 2).ExactAt (2, 0) :=
    ((P.page 2).exactAt_iff_isZero_homology (2, 0)).2 hhomology
  have : Epi ((P.page 2).dTo (2, 0)) :=
    hexact.epi_f (pageTwo_twoZero_dFrom_eq_zero P)
  have hrel :
      (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (0, 1) (2, 0) := by
    rw [ComplexShape.spectralSequenceNat_rel_iff]
    omega
  rw [← (P.page 2).xPrevIso_comp_dTo hrel]
  infer_instance

end CategoryTheory.SpectralSequence.NatLowerEdge
