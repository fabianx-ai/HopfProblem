/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.ThreeColumnPage

/-!
# Bijectivity of the lower differentials of a normalized three-column page

For a normalized three-column page over a commutative ring, this file states the condition that
the first two differentials are bijective and the third is nonzero, and proves it equivalent to
three reformulations.

## Main results

* `ThreeColumnPage.LowerDifferentialsBijectiveAndNeZero`: the condition itself.
* `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_coefficients`: equivalently, the
  first two normalized coefficients are units and the third is nonzero.
* `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_isUnit_of_coefficients_eq`: if
  all three coefficients are one scalar, equivalently that scalar is a unit.
* `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_injective`: over a domain,
  equivalently the third differential is injective.
* `ThreeColumnPage.Data.lowerDifferentialsBijectiveAndNeZero_iff_all_subsingleton`: for an
  explicitly supplied `ThreeColumnPage.FilteredAbutment` over a domain, equivalently its first
  three abutment groups vanish.

The filtration remains explicit input: this module does not construct a spectral sequence, a page
realization, or convergence data.

## References

* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §5.2 (a spectral sequence
  supported in three columns and its edge maps).
-/

@[expose] public section

namespace ThreeColumnPage

universe u

variable {R : Type u} [CommRing R]

/-- The first two normalized differentials of a three-column page are bijective and the third
is nonzero: two isomorphisms followed by one nonzero rank-one differential. -/
def LowerDifferentialsBijectiveAndNeZero (P : Data R) : Prop :=
  Function.Bijective (P.differential 0) ∧
    Function.Bijective (P.differential 1) ∧
      P.differential 2 ≠ 0

namespace Data

variable (P : Data R)

/-- The condition expressed entirely in normalized coefficients. -/
theorem lowerDifferentialsBijectiveAndNeZero_iff_coefficients :
    LowerDifferentialsBijectiveAndNeZero P ↔
      IsUnit (P.coefficient 0) ∧
        IsUnit (P.coefficient 1) ∧
          P.coefficient 2 ≠ 0 := by
  rw [LowerDifferentialsBijectiveAndNeZero, P.differential_bijective_iff_isUnit 0,
    P.differential_bijective_iff_isUnit 1,
    (P.normalization 2).map_ne_zero_iff]
  rfl

/-- If all three normalized coefficients are one scalar, the condition says exactly that the
scalar is a unit. -/
theorem lowerDifferentialsBijectiveAndNeZero_iff_isUnit_of_coefficients_eq [Nontrivial R] (p : R)
    (hcoeff : ∀ i, P.coefficient i = p) :
    LowerDifferentialsBijectiveAndNeZero P ↔ IsUnit p := by
  rw [P.lowerDifferentialsBijectiveAndNeZero_iff_coefficients]
  constructor
  · intro h
    simpa [hcoeff 0] using h.1
  · intro hp
    exact ⟨by simpa [hcoeff 0] using hp,
      by simpa [hcoeff 1] using hp,
      by simpa [hcoeff 2] using hp.ne_zero⟩

/-- Over a domain, nonvanishing of the last normalized rank-one map is equivalent to the
injectivity condition used by the filtered-abutment theorem. -/
theorem lowerDifferentialsBijectiveAndNeZero_iff_injective [IsDomain R] :
    LowerDifferentialsBijectiveAndNeZero P ↔
      (Function.Bijective (P.differential 0) ∧
        Function.Bijective (P.differential 1) ∧
          Function.Injective (P.differential 2)) := by
  rw [LowerDifferentialsBijectiveAndNeZero, P.differential_injective_iff_ne_zero 2]

/-- For an explicitly supplied filtered abutment over a domain, the condition is equivalent to
vanishing in total degrees one through three. -/
theorem lowerDifferentialsBijectiveAndNeZero_iff_all_subsingleton [IsDomain R]
    (A : FilteredAbutment P) :
    LowerDifferentialsBijectiveAndNeZero P ↔
      (Subsingleton (A.H 0) ∧ Subsingleton (A.H 1) ∧ Subsingleton (A.H 2)) := by
  rw [P.lowerDifferentialsBijectiveAndNeZero_iff_injective, A.all_subsingleton_iff]

end Data

end ThreeColumnPage
