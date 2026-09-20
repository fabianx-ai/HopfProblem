/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib

/-!
# Finite sums of signs and cancellation of an opposite pair

Elementary `Finset`/`SignType` combinatorics, extracted from
`Lib.Geometry.Manifold.Morse.SurgeryHomology` where it was used to count belt
intersection points with signs.

`sum_sdiff_pair` says that deleting from a finite set a pair of elements carrying
opposite signs does not change the signed sum, and `sum_sdiff_pair_of_eq` is the
version in which the remaining signs are only required to agree with the old
ones.  `card_eq_natAbs_sum_of_no_opposite` says that if no two elements of `s`
carry opposite signs then `s.card` is the absolute value of the signed sum -- the
statement that makes a signed count an honest count once all cancelling pairs are
gone.

## Main declarations

* `FiniteSignedCancellation.sum_sdiff_pair`,
  `FiniteSignedCancellation.sum_sdiff_pair_of_eq`
* `FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite`

## Tags

sign, signed sum, finset, cancellation
-/

theorem FiniteSignedCancellation.opposite_signs_distinct {a b : SignType} (h : a * b = -1) :
    a ≠ b := by cases a <;> cases b <;> simp_all

theorem FiniteSignedCancellation.cast_add_eq_zero_of_opposite {a b : SignType}
    (h : a * b = -1) : (a : ℤ) + (b : ℤ) = 0 := by cases a <;> cases b <;> simp_all

theorem FiniteSignedCancellation.sum_sdiff_pair {X : Type*} [DecidableEq X] (s : Finset X)
    (σ : X → SignType) {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1) :
    ∑ z ∈ s \ { x, y }, (σ z : ℤ) = ∑ z ∈ s, (σ z : ℤ) := by
  classical
  have hne : x ≠ y := fun h => opposite_signs_distinct hxy (congrArg σ h)
  have hsub : ({ x, y } : Finset X) ⊆ s := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · exact Finset.mem_singleton.mp hz ▸ hy
  have hsum : ∑ z ∈ ({ x, y } : Finset X), (σ z : ℤ) = 0 := by
    rw [Finset.sum_pair hne]
    exact cast_add_eq_zero_of_opposite hxy
  have h := Finset.sum_sdiff (f := fun z => (σ z : ℤ)) hsub
  simpa only [hsum, add_zero] using h

theorem FiniteSignedCancellation.sum_sdiff_pair_of_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (σ τ : X → SignType) {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1)
    (heq : ∀ z ∈ s \ { x, y }, τ z = σ z) : ∑ z ∈ s \ { x, y }, (τ z : ℤ) = ∑ z ∈ s, (σ z : ℤ) := by
  calc
    _ = ∑ z ∈ s \ { x, y }, (σ z : ℤ) :=
      Finset.sum_congr rfl (fun z hz => congrArg (fun a : SignType => (a : ℤ)) (heq z hz))
    _ = _ := sum_sdiff_pair s σ hx hy hxy

theorem FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite {X : Type*}
    (s : Finset X) (σ : X → SignType) (hunit : ∀ x ∈ s, σ x = 1 ∨ σ x = -1)
    (hno : ∀ x ∈ s, ∀ y ∈ s, σ x * σ y ≠ -1) : s.card = (∑ x ∈ s, (σ x : ℤ)).natAbs := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  have heq (y : X) (hy : y ∈ s) : σ y = σ x := by
    rcases hunit x hx with hxp | hxn <;> rcases hunit y hy with hyp | hyn
    · exact hyp.trans hxp.symm
    · exact (hno x hx y hy (by rw [hxp, hyn]; simp)).elim
    · exact (hno x hx y hy (by rw [hxn, hyp]; simp)).elim
    · exact hyn.trans hxn.symm
  have hsum : (∑ y ∈ s, (σ y : ℤ)) = ∑ _ ∈ s, (σ x : ℤ) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [heq y hy]
  rw [hsum]
  rcases hunit x hx with hp | hn
  · simp [hp]
  · simp [hn]
