/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.SplitChart

/-!
# Sign vectors, coordinate enumerations and split coordinates

Combinatorics of sign vectors `w : ι → ℝ` with values `±1` (the diagonal signs of a Morse
chart; the number of `-1`s is the index):

* `positive_of_not_negative`; `exists_equiv_of_negative_card_eq`: two sign vectors on sets of
  the same cardinality with the same number of `-1`s differ by a bijection;
* `exists_coordinate_enum`, `negative_card_split`: enumerations `Option (Fin m) ≃ Fin (m + 1)`
  with a prescribed distinguished coordinate, and the count of `-1`s split off that coordinate;
* `exists_adjacent_sign_enumerations`, `exists_adjacent_sign_enumerations_of_dimension`: for
  sign vectors of index `λ` and `λ + 1` there are enumerations agreeing on `Fin m` with `w₀ = 1`
  and `w₁ = -1` on the distinguished coordinate;
* `splitCoordinates_negative_zero_iff`, `splitCoordinates_positive_zero_iff`: the negative
  (positive) part of `MorseHandle.splitCoordinates w z` vanishes iff `z` vanishes on the
  negative (positive) coordinates.

cf. Milnor, *Morse Theory*, §2 (the Morse lemma: the index is the number of negative squares).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Split coordinates -/

attribute [local instance 100] Classical.propDecidable in
/-- The negative split coordinate vanishes exactly on the positive part. -/
theorem TransverseGerms.splitCoordinates_negative_zero_iff {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → ℝ) :
    (MorseHandle.splitCoordinates w z).1 = 0 ↔ ∀ i, w i = -1 → z i = 0 := by
  constructor
  · intro h i hi
    have hh := congrArg (fun v : MorseHandle.NegativeSpace w => v ⟨i, hi⟩) h
    exact hh
  · intro h
    ext i
    exact h i.1 i.2

attribute [local instance 100] Classical.propDecidable in
/-- The positive split coordinate vanishes exactly on the negative part. -/
theorem TransverseGerms.splitCoordinates_positive_zero_iff {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    (MorseHandle.splitCoordinates w z).2 = 0 ↔ ∀ i, w i = 1 → z i = 0 := by
  constructor
  · intro h i hi
    have hn : w i ≠ -1 := by rw [hi]; norm_num
    have hh := congrArg (fun v : MorseHandle.PositiveSpace w => v ⟨i, hn⟩) h
    exact hh
  · intro h
    ext i
    exact h i.1 ((hw i.1).resolve_left i.2)

/-! ### Sign enumerations -/

/-- A non-negative coordinate is positive. -/
theorem SignedCoordinates.positive_of_not_negative {ι : Type*} {w : ι → ℝ}
    (hw : ∀ i, w i = -1 ∨ w i = 1) {i : ι} (hi : w i ≠ -1) : w i = 1 :=
  (hw i).resolve_left hi

/-- Equal negative counts give a sign equivalence. -/
theorem SignedCoordinates.exists_equiv_of_negative_card_eq {ι κ : Type*} [Fintype ι]
    [Fintype κ] (w₀ : ι → ℝ) (w₁ : κ → ℝ) (h₀ : ∀ i, w₀ i = -1 ∨ w₀ i = 1)
    (h₁ : ∀ i, w₁ i = -1 ∨ w₁ i = 1) (hcard : Fintype.card ι = Fintype.card κ)
    [Fintype { i // w₀ i = -1 }] [Fintype { i // w₁ i = -1 }]
    (hneg : Fintype.card { i // w₀ i = -1 } = Fintype.card { i // w₁ i = -1 }) :
    ∃ e : ι ≃ κ, ∀ i, w₁ (e i) = w₀ i := by
  classical
  let eN : { i // w₀ i = -1 } ≃ { i // w₁ i = -1 } := Fintype.equivOfCardEq hneg
  have hpos : Fintype.card { i // ¬w₀ i = -1 } = Fintype.card { i // ¬w₁ i = -1 } := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard, hneg]
  let eP : { i // ¬w₀ i = -1 } ≃ { i // ¬w₁ i = -1 } := Fintype.equivOfCardEq hpos
  let e₀ := Equiv.sumCompl (fun i : ι => w₀ i = -1)
  let e₁ := Equiv.sumCompl (fun i : κ => w₁ i = -1)
  let e := e₀.symm.trans ((Equiv.sumCongr eN eP).trans e₁)
  refine ⟨e, ?_⟩
  intro i
  obtain ⟨z, rfl⟩ := e₀.surjective i
  simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]
  cases z with
  | inl x =>
    change w₁ (eN x) = w₀ x
    exact (eN x).property.trans x.property.symm
  | inr x =>
    change w₁ (eP x) = w₀ x
    exact
      (positive_of_not_negative h₁ (eP x).property).trans
        (positive_of_not_negative h₀ x.property).symm

/-- A coordinate enumeration exists. -/
theorem MorseCancellation.exists_coordinate_enum {m n : ℕ} (hn : n = m + 1) (j : Fin n) :
    ∃ ρ : Option (Fin m) ≃ Fin n, ρ Option.none = j := by
  let ρ₀ : Option (Fin m) ≃ Fin n := Fintype.equivOfCardEq (by simp [hn])
  exact ⟨ρ₀.trans (Equiv.swap (ρ₀ Option.none) j), by simp⟩

attribute [local instance 100] Classical.propDecidable in
/-- The negative cardinality of the split. -/
theorem SignedCoordinates.negative_card_split {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n)
    (w : Fin n → ℝ) :
    Fintype.card { j // w j = -1 } =
      (if w (ρ Option.none) = -1 then 1 else 0) +
        Fintype.card { i : Fin m // w (ρ (Option.some i)) = -1 } := by
  have he : { i : Option (Fin m) // w (ρ i) = -1 } ≃ { j : Fin n // w j = -1 } :=
    ρ.subtypeEquiv (fun _ => Iff.rfl)
  rw [← Fintype.card_congr he]
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]

attribute [local instance 100] Classical.propDecidable in
/-- Adjacent sign enumerations exist. -/
theorem SignedCoordinates.exists_adjacent_sign_enumerations {m : ℕ}
    (w₀ w₁ : Fin (m + 1) → ℝ) (h₀ : ∀ i, w₀ i = -1 ∨ w₀ i = 1) (h₁ : ∀ i, w₁ i = -1 ∨ w₁ i = 1)
    (hindex : Fintype.card { i // w₁ i = -1 } = Fintype.card { i // w₀ i = -1 } + 1) :
    ∃ ρ₀ ρ₁ : Option (Fin m) ≃ Fin (m + 1),
      w₀ (ρ₀ Option.none) = 1 ∧
        w₁ (ρ₁ Option.none) = -1 ∧ ∀ i, w₀ (ρ₀ (Option.some i)) = w₁ (ρ₁ (Option.some i)) := by
  have hbound := Fintype.card_subtype_le (fun i : Fin (m + 1) => w₁ i = -1)
  have hNpos : 0 < Fintype.card { i // w₁ i = -1 } := by omega
  have hPpos : 0 < Fintype.card { i // ¬w₀ i = -1 } := by
    rw [Fintype.card_subtype_compl]
    omega
  let j₀ := Classical.choice (Fintype.card_pos_iff.mp hPpos)
  let j₁ := Classical.choice (Fintype.card_pos_iff.mp hNpos)
  obtain ⟨ρ₀, hρ₀⟩ := MorseCancellation.exists_coordinate_enum rfl j₀.1
  obtain ⟨ρ₁, hρ₁⟩ := MorseCancellation.exists_coordinate_enum rfl j₁.1
  have hfirst₀ : w₀ (ρ₀ Option.none) = 1 := by
    rw [hρ₀]
    exact positive_of_not_negative h₀ j₀.2
  have hfirst₁ : w₁ (ρ₁ Option.none) = -1 := by
    rw [hρ₁]
    exact j₁.2
  let σ₀ := fun i : Fin m => w₀ (ρ₀ (Option.some i))
  let σ₁ := fun i : Fin m => w₁ (ρ₁ (Option.some i))
  have hrest : Fintype.card { i // σ₀ i = -1 } = Fintype.card { i // σ₁ i = -1 } := by
    have hcount₀ := negative_card_split ρ₀ w₀
    have hcount₁ := negative_card_split ρ₁ w₁
    rw [hfirst₀] at hcount₀
    rw [hfirst₁] at hcount₁
    norm_num at hcount₀ hcount₁
    change
      Fintype.card { i // w₀ (ρ₀ (Option.some i)) = -1 } =
        Fintype.card { i // w₁ (ρ₁ (Option.some i)) = -1 }
    omega
  obtain ⟨η, hη⟩ :=
    exists_equiv_of_negative_card_eq σ₀ σ₁ (fun i => h₀ _) (fun i => h₁ _) rfl hrest
  refine ⟨ρ₀, (Equiv.optionCongr η).trans ρ₁, hfirst₀, ?_, ?_⟩
  · simpa using hfirst₁
  · intro i
    exact (hη i).symm

attribute [local instance 100] Classical.propDecidable in
/-- Adjacent sign enumerations in a dimension exist. -/
theorem SignedCoordinates.exists_adjacent_sign_enumerations_of_dimension {m n : ℕ}
    (hn : n = m + 1) (w₀ w₁ : Fin n → ℝ) (h₀ : ∀ i, w₀ i = -1 ∨ w₀ i = 1)
    (h₁ : ∀ i, w₁ i = -1 ∨ w₁ i = 1)
    (hindex : Fintype.card { i // w₁ i = -1 } = Fintype.card { i // w₀ i = -1 } + 1) :
    ∃ ρ₀ ρ₁ : Option (Fin m) ≃ Fin n,
      w₀ (ρ₀ Option.none) = 1 ∧
        w₁ (ρ₁ Option.none) = -1 ∧ ∀ i, w₀ (ρ₀ (Option.some i)) = w₁ (ρ₁ (Option.some i)) := by
  subst n
  exact exists_adjacent_sign_enumerations w₀ w₁ h₀ h₁ hindex

end
