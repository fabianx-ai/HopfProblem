/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.ThreeColumnPage

/-!
# Lower transfer conditions on a normalized three-column page

This file relates three equivalent forms of the low-page condition used in a three-column
spectral-sequence calculation:

* the first two normalized differentials are bijective and the third is nonzero;
* the first two normalized coefficients are units and the third is nonzero;
* over a domain, the first two differentials are bijective and the third is injective.

When a `ThreeColumnPage.FilteredAbutment` is supplied, the last condition is equivalent to
vanishing of its first three abutment groups. The filtration remains explicit input: this module
does not construct a spectral sequence, a page realization, or convergence data.
-/

@[expose] public section

namespace ThreeColumnPage

universe u

variable {R : Type u} [CommRing R]

/-- The paper-facing lower transfer condition: two isomorphisms followed by one nonzero
rank-one differential. -/
def LowerTransferCondition (P : Data R) : Prop :=
  Function.Bijective (P.differential 0) ∧
    Function.Bijective (P.differential 1) ∧
      P.differential 2 ≠ 0

namespace Data

variable (P : Data R)

/-- The lower transfer condition expressed entirely in normalized coefficients. -/
theorem lowerTransferCondition_iff_coefficients :
    LowerTransferCondition P ↔
      IsUnit (P.coefficient 0) ∧
        IsUnit (P.coefficient 1) ∧
          P.coefficient 2 ≠ 0 := by
  rw [LowerTransferCondition, P.differential_bijective_iff_isUnit 0,
    P.differential_bijective_iff_isUnit 1,
    (P.normalization 2).map_ne_zero_iff]
  rfl

/-- If all three normalized coefficients are one scalar, the lower transfer condition says
exactly that the scalar is a unit. -/
theorem lowerTransferCondition_iff_isUnit_of_coefficients_eq [Nontrivial R] (p : R)
    (hcoeff : ∀ i, P.coefficient i = p) :
    LowerTransferCondition P ↔ IsUnit p := by
  rw [P.lowerTransferCondition_iff_coefficients]
  constructor
  · intro h
    simpa [hcoeff 0] using h.1
  · intro hp
    exact ⟨by simpa [hcoeff 0] using hp,
      by simpa [hcoeff 1] using hp,
      by simpa [hcoeff 2] using hp.ne_zero⟩

/-- Over a domain, nonvanishing of the last normalized rank-one map is equivalent to the
injectivity condition used by the filtered-abutment theorem. -/
theorem lowerTransferCondition_iff_injective [IsDomain R] :
    LowerTransferCondition P ↔
      (Function.Bijective (P.differential 0) ∧
        Function.Bijective (P.differential 1) ∧
          Function.Injective (P.differential 2)) := by
  rw [LowerTransferCondition, P.differential_injective_iff_ne_zero 2]

/-- For an explicitly supplied filtered abutment over a domain, the paper-facing lower transfer
condition is equivalent to vanishing in total degrees one through three. -/
theorem lowerTransferCondition_iff_all_subsingleton [IsDomain R]
    (A : FilteredAbutment P) :
    LowerTransferCondition P ↔
      (Subsingleton (A.H 0) ∧ Subsingleton (A.H 1) ∧ Subsingleton (A.H 2)) := by
  rw [P.lowerTransferCondition_iff_injective, A.all_subsingleton_iff]

end Data

end ThreeColumnPage
