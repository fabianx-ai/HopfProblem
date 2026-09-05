/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# The first three lower-left `d₂` arrows of a first-quadrant spectral sequence

This file isolates a small first-quadrant fact which does not require a global column bound.
If the source `(0,1)` and target `(2,0)` vanish on page four, then the page-two differential
between them is an isomorphism.  Indeed, both bidegrees have no incoming or outgoing
differentials on page three, so page three already equals page four there.

The same local argument treats `(0,2) → (2,1)` once only the two possible off-axis obstructions
`E₂^(3,0)` and `E₂^(4,0)` vanish.  Thus an application may use concrete cohomology calculations
at those two groups instead of proving a global column-support theorem.

Finally, the same bookkeeping identifies `E₂^(1,1)` with `E₃^(1,1)` as soon as its sole
outgoing target `E₂^(3,0)` vanishes.  This is another local statement and does not assume that
all columns beyond two vanish.
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

private theorem pageThree_threeZero_isZero_of_isZero_pageTwo
    (h : IsZero ((P.page 2).X (3, 0))) :
    IsZero ((P.page 3).X (3, 0)) := by
  have hhomology : IsZero ((P.page 2).homology (3, 0)) :=
    ((P.page 2).sc (3, 0)).isZero_homology_of_isZero_X₂ h
  exact IsZero.of_iso hhomology (P.iso 2 3 (3, 0) (by omega)).symm

private noncomputable def pageThreeZeroTwoIsoPageFour
    (h : IsZero ((P.page 2).X (3, 0))) :
    (P.page 3).X (0, 2) ≅ (P.page 4).X (0, 2) := by
  have hTo : (P.page 3).dTo (0, 2) = 0 := by
    apply (P.page 3).dTo_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  have hFrom : (P.page 3).dFrom (0, 2) = 0 := by
    have hrel :
        (ComplexShape.spectralSequenceNat ⟨3, 1 - 3⟩).Rel (0, 2) (3, 0) := by
      rw [ComplexShape.spectralSequenceNat_rel_iff]
      omega
    have htarget : IsZero ((P.page 3).X (3, 0)) :=
      pageThree_threeZero_isZero_of_isZero_pageTwo P h
    rw [(P.page 3).dFrom_eq hrel,
      htarget.eq_of_tgt ((P.page 3).d (0, 2) (3, 0)) 0, zero_comp]
  exact
    ((ShortComplex.HomologyData.ofZeros ((P.page 3).sc (0, 2)) hTo hFrom).left.homologyIso).symm ≪≫
      P.iso 3 4 (0, 2) (by omega)

private noncomputable def pageThreeTwoOneIsoPageFour :
    (P.page 3).X (2, 1) ≅ (P.page 4).X (2, 1) := by
  have hTo : (P.page 3).dTo (2, 1) = 0 := by
    apply (P.page 3).dTo_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  have hFrom : (P.page 3).dFrom (2, 1) = 0 := by
    apply (P.page 3).dFrom_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  exact
    ((ShortComplex.HomologyData.ofZeros ((P.page 3).sc (2, 1)) hTo hFrom).left.homologyIso).symm ≪≫
      P.iso 3 4 (2, 1) (by omega)

/-- Page-four vanishing at `(0,2)`, together with vanishing of the only possible page-three
target `(3,0)`, makes the second lower page-two differential monic.  It suffices to state the
off-axis vanishing on page two, since zero objects remain zero after taking homology. -/
theorem mono_d₂_zeroTwo_twoOne_of_isZero_pageFour
    (hthreeZero : IsZero ((P.page 2).X (3, 0)))
    (hzeroTwo : IsZero ((P.page 4).X (0, 2))) :
    Mono ((P.page 2).d (0, 2) (2, 1)) := by
  have hpage3 : IsZero ((P.page 3).X (0, 2)) :=
    IsZero.of_iso hzeroTwo (pageThreeZeroTwoIsoPageFour P hthreeZero)
  have hhomology : IsZero ((P.page 2).homology (0, 2)) :=
    IsZero.of_iso hpage3 (P.iso 2 3 (0, 2) (by omega))
  have hexact : (P.page 2).ExactAt (0, 2) :=
    ((P.page 2).exactAt_iff_isZero_homology (0, 2)).2 hhomology
  have hTo : (P.page 2).dTo (0, 2) = 0 := by
    apply (P.page 2).dTo_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  have : Mono ((P.page 2).dFrom (0, 2)) := hexact.mono_g hTo
  have hrel :
      (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (0, 2) (2, 1) := by
    rw [ComplexShape.spectralSequenceNat_rel_iff]
    omega
  rw [← (P.page 2).dFrom_comp_xNextIso hrel]
  infer_instance

/-- Page-four vanishing at `(2,1)`, together with vanishing of the only possible outgoing
page-two target `(4,0)`, makes the second lower page-two differential epic. -/
theorem epi_d₂_zeroTwo_twoOne_of_isZero_pageFour
    (hfourZero : IsZero ((P.page 2).X (4, 0)))
    (htwoOne : IsZero ((P.page 4).X (2, 1))) :
    Epi ((P.page 2).d (0, 2) (2, 1)) := by
  have hpage3 : IsZero ((P.page 3).X (2, 1)) :=
    IsZero.of_iso htwoOne (pageThreeTwoOneIsoPageFour P)
  have hhomology : IsZero ((P.page 2).homology (2, 1)) :=
    IsZero.of_iso hpage3 (P.iso 2 3 (2, 1) (by omega))
  have hexact : (P.page 2).ExactAt (2, 1) :=
    ((P.page 2).exactAt_iff_isZero_homology (2, 1)).2 hhomology
  have hFrom : (P.page 2).dFrom (2, 1) = 0 := by
    have hrel :
        (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (2, 1) (4, 0) := by
      rw [ComplexShape.spectralSequenceNat_rel_iff]
      omega
    rw [(P.page 2).dFrom_eq hrel,
      hfourZero.eq_of_tgt ((P.page 2).d (2, 1) (4, 0)) 0, zero_comp]
  have : Epi ((P.page 2).dTo (2, 1)) := hexact.epi_f hFrom
  have hrel :
      (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (0, 2) (2, 1) := by
    rw [ComplexShape.spectralSequenceNat_rel_iff]
    omega
  rw [← (P.page 2).xPrevIso_comp_dTo hrel]
  infer_instance

/-- The two local off-axis vanishings and the two page-four endpoint vanishings make the second
lower page-two differential an isomorphism. -/
theorem isIso_d₂_zeroTwo_twoOne_of_isZero_pageFour
    (hthreeZero : IsZero ((P.page 2).X (3, 0)))
    (hfourZero : IsZero ((P.page 2).X (4, 0)))
    (hzeroTwo : IsZero ((P.page 4).X (0, 2)))
    (htwoOne : IsZero ((P.page 4).X (2, 1))) :
    IsIso ((P.page 2).d (0, 2) (2, 1)) := by
  let _ : Mono ((P.page 2).d (0, 2) (2, 1)) :=
    mono_d₂_zeroTwo_twoOne_of_isZero_pageFour P hthreeZero hzeroTwo
  let _ : Epi ((P.page 2).d (0, 2) (2, 1)) :=
    epi_d₂_zeroTwo_twoOne_of_isZero_pageFour P hfourZero htwoOne
  exact isIso_of_mono_of_epi _

private theorem pageThree_threeOne_isZero_of_isZero_pageTwo
    (h : IsZero ((P.page 2).X (3, 1))) :
    IsZero ((P.page 3).X (3, 1)) := by
  have hhomology : IsZero ((P.page 2).homology (3, 1)) :=
    ((P.page 2).sc (3, 1)).isZero_homology_of_isZero_X₂ h
  exact IsZero.of_iso hhomology (P.iso 2 3 (3, 1) (by omega)).symm

private noncomputable def pageThreeZeroThreeIsoPageFour
    (h : IsZero ((P.page 2).X (3, 1))) :
    (P.page 3).X (0, 3) ≅ (P.page 4).X (0, 3) := by
  have hTo : (P.page 3).dTo (0, 3) = 0 := by
    apply (P.page 3).dTo_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  have hFrom : (P.page 3).dFrom (0, 3) = 0 := by
    have hrel :
        (ComplexShape.spectralSequenceNat ⟨3, 1 - 3⟩).Rel (0, 3) (3, 1) := by
      rw [ComplexShape.spectralSequenceNat_rel_iff]
      omega
    have htarget : IsZero ((P.page 3).X (3, 1)) :=
      pageThree_threeOne_isZero_of_isZero_pageTwo P h
    rw [(P.page 3).dFrom_eq hrel,
      htarget.eq_of_tgt ((P.page 3).d (0, 3) (3, 1)) 0, zero_comp]
  exact
    ((ShortComplex.HomologyData.ofZeros ((P.page 3).sc (0, 3)) hTo hFrom).left.homologyIso).symm ≪≫
      P.iso 3 4 (0, 3) (by omega)

private theorem pageFour_fourZero_isZero_of_isZero_pageTwo
    (h : IsZero ((P.page 2).X (4, 0))) :
    IsZero ((P.page 4).X (4, 0)) := by
  have hhomologyTwo : IsZero ((P.page 2).homology (4, 0)) :=
    ((P.page 2).sc (4, 0)).isZero_homology_of_isZero_X₂ h
  have hthree : IsZero ((P.page 3).X (4, 0)) :=
    IsZero.of_iso hhomologyTwo (P.iso 2 3 (4, 0) (by omega)).symm
  have hhomologyThree : IsZero ((P.page 3).homology (4, 0)) :=
    ((P.page 3).sc (4, 0)).isZero_homology_of_isZero_X₂ hthree
  exact IsZero.of_iso hhomologyThree (P.iso 3 4 (4, 0) (by omega)).symm

private noncomputable def pageFourZeroThreeIsoPageFive
    (h : IsZero ((P.page 2).X (4, 0))) :
    (P.page 4).X (0, 3) ≅ (P.page 5).X (0, 3) := by
  have hTo : (P.page 4).dTo (0, 3) = 0 := by
    apply (P.page 4).dTo_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  have hFrom : (P.page 4).dFrom (0, 3) = 0 := by
    have hrel :
        (ComplexShape.spectralSequenceNat ⟨4, 1 - 4⟩).Rel (0, 3) (4, 0) := by
      rw [ComplexShape.spectralSequenceNat_rel_iff]
      omega
    have htarget : IsZero ((P.page 4).X (4, 0)) :=
      pageFour_fourZero_isZero_of_isZero_pageTwo P h
    rw [(P.page 4).dFrom_eq hrel,
      htarget.eq_of_tgt ((P.page 4).d (0, 3) (4, 0)) 0, zero_comp]
  exact
    ((ShortComplex.HomologyData.ofZeros ((P.page 4).sc (0, 3)) hTo hFrom).left.homologyIso).symm ≪≫
      P.iso 4 5 (0, 3) (by omega)

/-- Page-five vanishing at `(0,3)`, together with vanishing of the only possible later
outgoing targets `(3,1)` and `(4,0)`, makes the third lower page-two differential monic.
Only these two off-axis page-two groups are required; no global column bound is assumed. -/
theorem mono_d₂_zeroThree_twoTwo_of_isZero_pageFive
    (hthreeOne : IsZero ((P.page 2).X (3, 1)))
    (hfourZero : IsZero ((P.page 2).X (4, 0)))
    (hzeroThree : IsZero ((P.page 5).X (0, 3))) :
    Mono ((P.page 2).d (0, 3) (2, 2)) := by
  have hpage4 : IsZero ((P.page 4).X (0, 3)) :=
    IsZero.of_iso hzeroThree (pageFourZeroThreeIsoPageFive P hfourZero)
  have hpage3 : IsZero ((P.page 3).X (0, 3)) :=
    IsZero.of_iso hpage4 (pageThreeZeroThreeIsoPageFour P hthreeOne)
  have hhomology : IsZero ((P.page 2).homology (0, 3)) :=
    IsZero.of_iso hpage3 (P.iso 2 3 (0, 3) (by omega))
  have hexact : (P.page 2).ExactAt (0, 3) :=
    ((P.page 2).exactAt_iff_isZero_homology (0, 3)).2 hhomology
  have hTo : (P.page 2).dTo (0, 3) = 0 := by
    apply (P.page 2).dTo_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  have : Mono ((P.page 2).dFrom (0, 3)) := hexact.mono_g hTo
  have hrel :
      (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (0, 3) (2, 2) := by
    rw [ComplexShape.spectralSequenceNat_rel_iff]
    omega
  rw [← (P.page 2).dFrom_comp_xNextIso hrel]
  infer_instance

/-- If the sole outgoing target `E₂^(3,0)` vanishes, the middle term `E₂^(1,1)` is already
unchanged on page three.  No global support condition is needed. -/
noncomputable def pageTwoOneOneIsoPageThree
    (hthreeZero : IsZero ((P.page 2).X (3, 0))) :
    (P.page 2).X (1, 1) ≅ (P.page 3).X (1, 1) := by
  have hTo : (P.page 2).dTo (1, 1) = 0 := by
    apply (P.page 2).dTo_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  have hFrom : (P.page 2).dFrom (1, 1) = 0 := by
    have hrel :
        (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (1, 1) (3, 0) := by
      rw [ComplexShape.spectralSequenceNat_rel_iff]
      omega
    rw [(P.page 2).dFrom_eq hrel,
      hthreeZero.eq_of_tgt ((P.page 2).d (1, 1) (3, 0)) 0, zero_comp]
  exact
    ((ShortComplex.HomologyData.ofZeros ((P.page 2).sc (1, 1)) hTo hFrom).left.homologyIso).symm ≪≫
      P.iso 2 3 (1, 1) (by omega)

/-- Vanishing of page three at `(1,1)` descends to page two once the only outgoing page-two
target vanishes. -/
theorem isZero_pageTwo_oneOne_of_isZero_pageThree
    (hthreeZero : IsZero ((P.page 2).X (3, 0)))
    (honeOne : IsZero ((P.page 3).X (1, 1))) :
    IsZero ((P.page 2).X (1, 1)) :=
  IsZero.of_iso honeOne (pageTwoOneOneIsoPageThree P hthreeZero)

end CategoryTheory.SpectralSequence.NatLowerEdge
