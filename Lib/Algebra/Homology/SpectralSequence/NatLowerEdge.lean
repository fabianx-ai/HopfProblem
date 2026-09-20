/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Local lower-page facts for a first-quadrant spectral sequence

This file isolates a small first-quadrant fact which does not require a global column bound.
If the source `(0,1)` and target `(2,0)` vanish on page four, then the page-two differential
between them is an isomorphism.  Indeed, both bidegrees have no incoming or outgoing
differentials on page three, so page three already equals page four there.

The same local argument treats `(0,2) → (2,1)` once only the two possible off-axis obstructions
`E₂^(3,0)` and `E₂^(4,0)` vanish.  Thus an application may use concrete cohomology calculations
at those two groups instead of proving a global column-support theorem.

For the third arrow `(0,3) → (2,2)`, the same method records both halves separately.  Vanishing
of the two later source escape routes makes it monic; vanishing of the two target escape routes
makes it epic.  Thus sufficiently sparse local data plus the actual abutment can manufacture the
target coordinate instead of requiring it as an independent calculation.

Finally, the same bookkeeping identifies `E₂^(1,1)` with `E₃^(1,1)` as soon as its sole
outgoing target `E₂^(3,0)` vanishes.  This is another local statement and does not assume that
all columns beyond two vanish.

Likewise, `E₂^(1,2)` reaches page four unchanged if the two successive targets
`E₂^(3,1)` and `E₂^(4,0)` vanish.  This lets an application use a single targeted
off-axis calculation instead of constructing a separate degree-one local-coefficient complex.

## References

* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §5.2 (first-quadrant
  spectral sequences and the degrees in
  which they stabilise).

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

private theorem pageThree_fiveZero_isZero_of_isZero_pageTwo
    (h : IsZero ((P.page 2).X (5, 0))) :
    IsZero ((P.page 3).X (5, 0)) := by
  have hhomology : IsZero ((P.page 2).homology (5, 0)) :=
    ((P.page 2).sc (5, 0)).isZero_homology_of_isZero_X₂ h
  exact IsZero.of_iso hhomology (P.iso 2 3 (5, 0) (by omega)).symm

private noncomputable def pageThreeTwoTwoIsoPageFour
    (h : IsZero ((P.page 2).X (5, 0))) :
    (P.page 3).X (2, 2) ≅ (P.page 4).X (2, 2) := by
  have hTo : (P.page 3).dTo (2, 2) = 0 := by
    apply (P.page 3).dTo_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  have hFrom : (P.page 3).dFrom (2, 2) = 0 := by
    have hrel :
        (ComplexShape.spectralSequenceNat ⟨3, 1 - 3⟩).Rel (2, 2) (5, 0) := by
      rw [ComplexShape.spectralSequenceNat_rel_iff]
      omega
    have htarget : IsZero ((P.page 3).X (5, 0)) :=
      pageThree_fiveZero_isZero_of_isZero_pageTwo P h
    rw [(P.page 3).dFrom_eq hrel,
      htarget.eq_of_tgt ((P.page 3).d (2, 2) (5, 0)) 0, zero_comp]
  exact
    ((ShortComplex.HomologyData.ofZeros ((P.page 3).sc (2, 2)) hTo hFrom).left.homologyIso).symm ≪≫
      P.iso 3 4 (2, 2) (by omega)

/-- Page-four vanishing at `(2,2)`, together with vanishing of its only page-two and page-three
outgoing targets `(4,1)` and `(5,0)`, makes the third lower page-two differential epic.
Only these local groups are required; no global column bound is assumed. -/
theorem epi_d₂_zeroThree_twoTwo_of_isZero_pageFour
    (hfourOne : IsZero ((P.page 2).X (4, 1)))
    (hfiveZero : IsZero ((P.page 2).X (5, 0)))
    (htwoTwo : IsZero ((P.page 4).X (2, 2))) :
    Epi ((P.page 2).d (0, 3) (2, 2)) := by
  have hpage3 : IsZero ((P.page 3).X (2, 2)) :=
    IsZero.of_iso htwoTwo (pageThreeTwoTwoIsoPageFour P hfiveZero)
  have hhomology : IsZero ((P.page 2).homology (2, 2)) :=
    IsZero.of_iso hpage3 (P.iso 2 3 (2, 2) (by omega))
  have hexact : (P.page 2).ExactAt (2, 2) :=
    ((P.page 2).exactAt_iff_isZero_homology (2, 2)).2 hhomology
  have hFrom : (P.page 2).dFrom (2, 2) = 0 := by
    have hrel :
        (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (2, 2) (4, 1) := by
      rw [ComplexShape.spectralSequenceNat_rel_iff]
      omega
    rw [(P.page 2).dFrom_eq hrel,
      hfourOne.eq_of_tgt ((P.page 2).d (2, 2) (4, 1)) 0, zero_comp]
  have : Epi ((P.page 2).dTo (2, 2)) := hexact.epi_f hFrom
  have hrel :
      (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (0, 3) (2, 2) := by
    rw [ComplexShape.spectralSequenceNat_rel_iff]
    omega
  rw [← (P.page 2).xPrevIso_comp_dTo hrel]
  infer_instance

/-- The six local source, target, and endpoint vanishings make the third lower page-two
differential an isomorphism. -/
theorem isIso_d₂_zeroThree_twoTwo_of_isZero_pageFour_pageFive
    (hthreeOne : IsZero ((P.page 2).X (3, 1)))
    (hfourZero : IsZero ((P.page 2).X (4, 0)))
    (hfourOne : IsZero ((P.page 2).X (4, 1)))
    (hfiveZero : IsZero ((P.page 2).X (5, 0)))
    (hzeroThree : IsZero ((P.page 5).X (0, 3)))
    (htwoTwo : IsZero ((P.page 4).X (2, 2))) :
    IsIso ((P.page 2).d (0, 3) (2, 2)) := by
  let _ : Mono ((P.page 2).d (0, 3) (2, 2)) :=
    mono_d₂_zeroThree_twoTwo_of_isZero_pageFive
      P hthreeOne hfourZero hzeroThree
  let _ : Epi ((P.page 2).d (0, 3) (2, 2)) :=
    epi_d₂_zeroThree_twoTwo_of_isZero_pageFour
      P hfourOne hfiveZero htwoTwo
  exact isIso_of_mono_of_epi _

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

/-- If the first outgoing target `E₂^(3,1)` vanishes, the second middle term
`E₂^(1,2)` is unchanged on page three. -/
noncomputable def pageTwoOneTwoIsoPageThree
    (hthreeOne : IsZero ((P.page 2).X (3, 1))) :
    (P.page 2).X (1, 2) ≅ (P.page 3).X (1, 2) := by
  have hTo : (P.page 2).dTo (1, 2) = 0 := by
    apply (P.page 2).dTo_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  have hFrom : (P.page 2).dFrom (1, 2) = 0 := by
    have hrel :
        (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (1, 2) (3, 1) := by
      rw [ComplexShape.spectralSequenceNat_rel_iff]
      omega
    rw [(P.page 2).dFrom_eq hrel,
      hthreeOne.eq_of_tgt ((P.page 2).d (1, 2) (3, 1)) 0, zero_comp]
  exact
    ((ShortComplex.HomologyData.ofZeros ((P.page 2).sc (1, 2)) hTo hFrom).left.homologyIso).symm ≪≫
      P.iso 2 3 (1, 2) (by omega)

/-- If `E₂^(4,0)` vanishes, the second middle term is unchanged from page three to page
four. -/
noncomputable def pageThreeOneTwoIsoPageFour
    (hfourZero : IsZero ((P.page 2).X (4, 0))) :
    (P.page 3).X (1, 2) ≅ (P.page 4).X (1, 2) := by
  have htargetHomology : IsZero ((P.page 2).homology (4, 0)) :=
    ((P.page 2).sc (4, 0)).isZero_homology_of_isZero_X₂ hfourZero
  have htarget : IsZero ((P.page 3).X (4, 0)) :=
    IsZero.of_iso htargetHomology (P.iso 2 3 (4, 0) (by omega)).symm
  have hTo : (P.page 3).dTo (1, 2) = 0 := by
    apply (P.page 3).dTo_eq_zero
    intro hrel
    rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
    omega
  have hFrom : (P.page 3).dFrom (1, 2) = 0 := by
    have hrel :
        (ComplexShape.spectralSequenceNat ⟨3, 1 - 3⟩).Rel (1, 2) (4, 0) := by
      rw [ComplexShape.spectralSequenceNat_rel_iff]
      omega
    rw [(P.page 3).dFrom_eq hrel,
      htarget.eq_of_tgt ((P.page 3).d (1, 2) (4, 0)) 0, zero_comp]
  exact
    ((ShortComplex.HomologyData.ofZeros ((P.page 3).sc (1, 2)) hTo hFrom).left.homologyIso).symm ≪≫
      P.iso 3 4 (1, 2) (by omega)

/-- The two successive off-axis target vanishings identify `E₂^(1,2)` with
`E₄^(1,2)`, without a global support hypothesis. -/
noncomputable def pageTwoOneTwoIsoPageFour
    (hthreeOne : IsZero ((P.page 2).X (3, 1)))
    (hfourZero : IsZero ((P.page 2).X (4, 0))) :
    (P.page 2).X (1, 2) ≅ (P.page 4).X (1, 2) :=
  pageTwoOneTwoIsoPageThree P hthreeOne ≪≫
    pageThreeOneTwoIsoPageFour P hfourZero

/-- Vanishing of page four at `(1,2)` descends to page two once the two possible outgoing
targets vanish. -/
theorem isZero_pageTwo_oneTwo_of_isZero_pageFour
    (hthreeOne : IsZero ((P.page 2).X (3, 1)))
    (hfourZero : IsZero ((P.page 2).X (4, 0)))
    (honeTwo : IsZero ((P.page 4).X (1, 2))) :
    IsZero ((P.page 2).X (1, 2)) :=
  IsZero.of_iso honeTwo
    (pageTwoOneTwoIsoPageFour P hthreeOne hfourZero)

end CategoryTheory.SpectralSequence.NatLowerEdge
