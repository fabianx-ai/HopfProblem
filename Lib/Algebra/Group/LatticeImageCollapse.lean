/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.Algebra.Group.Basic

/-!
# Cyclic lattice images from a cusp kernel and two matrix actions

Let a homomorphism send the additive integer four-lattice into an arbitrary
group. Killing vectors with their first two coordinates zero kills w and d.
The first conjugation, together with A1*w = u-w, then kills u. The explicit
three-coordinate decomposition kills the whole first-coordinate kernel.

Writing v as gamma(v) times epsilon plus a zero-character remainder shows
that its image is the corresponding integer power, including negative powers.
The second fixed vector and the first basis vector have that same image.
The two fixed-vector equations give commutation with the two specified
conjugating elements. No commutativity, generation or triviality of the
ambient group is assumed or concluded.
-/

@[expose] public section
universe u
open Matrix
namespace LatticeImageCollapse

/-- The first integer monodromy matrix, acting on column vectors. -/
abbrev A1 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 6, 0, 1, 0; -6, -1, -1, 0; -2, 1, 0, 1]

/-- The second integer monodromy matrix, acting on column vectors. -/
abbrev A2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 0, 0, -1, 0; -6, 1, 0, 0; 3, 0, 1, 1]

/-- The first fixed vector, with first coordinate one. -/
abbrev epsilon : Fin 4 → ℤ := ![1, 2, -4, 0]

/-- The second fixed vector, with first coordinate one. -/
abbrev epsilonPrime : Fin 4 → ℤ := ![1, 3, -3, 0]

/-- The integer character recording the first lattice coordinate. -/
@[simp] abbrev gamma (v : Fin 4 → ℤ) : ℤ := v 0

theorem image_eq_one_of_gamma_eq_zero
    {G : Type u} [Group G]
    (φ : Multiplicative (Fin 4 → ℤ) →* G) (x : G)
    (hx : ∀ v : Fin 4 → ℤ,
      x * φ (Multiplicative.ofAdd v) * x⁻¹ =
        φ (Multiplicative.ofAdd (A1 *ᵥ v)))
    (hc : ∀ v : Fin 4 → ℤ, v 0 = 0 → v 1 = 0 →
      φ (Multiplicative.ofAdd v) = 1)
    (v : Fin 4 → ℤ) (hv : gamma v = 0) :
    φ (Multiplicative.ofAdd v) = 1 := by
  let u0 : Fin 4 → ℤ := ![0, 1, 0, 0]
  let w0 : Fin 4 → ℤ := ![0, 0, 1, 0]
  let d0 : Fin 4 → ℤ := ![0, 0, 0, 1]
  have hw : φ (Multiplicative.ofAdd w0) = 1 := hc w0 rfl rfl
  have hd : φ (Multiplicative.ofAdd d0) = 1 := hc d0 rfl rfl
  have hmatrix : A1 *ᵥ w0 = u0 - w0 := by decide
  have hu : φ (Multiplicative.ofAdd u0) = 1 := by
    have h := hx w0
    rw [hmatrix, ofAdd_sub, map_div, hw] at h
    simpa only [mul_one, mul_inv_cancel, div_one] using h.symm
  have hv0 : v 0 = 0 := hv
  have hdecomp : v = v 1 • u0 + v 2 • w0 + v 3 • d0 := by
    ext i
    fin_cases i <;> simp [u0, w0, d0, hv0]
  rw [hdecomp, ofAdd_add, ofAdd_add, map_mul, map_mul,
    ofAdd_zsmul, ofAdd_zsmul, ofAdd_zsmul, map_zpow, map_zpow, map_zpow,
    hu, hw, hd, one_zpow, one_zpow, one_zpow, mul_one, mul_one]

theorem image_eq_zpow_gamma
    {G : Type u} [Group G]
    (φ : Multiplicative (Fin 4 → ℤ) →* G) (x : G)
    (hx : ∀ v : Fin 4 → ℤ,
      x * φ (Multiplicative.ofAdd v) * x⁻¹ =
        φ (Multiplicative.ofAdd (A1 *ᵥ v)))
    (hc : ∀ v : Fin 4 → ℤ, v 0 = 0 → v 1 = 0 →
      φ (Multiplicative.ofAdd v) = 1)
    (v : Fin 4 → ℤ) :
    φ (Multiplicative.ofAdd v) =
      φ (Multiplicative.ofAdd epsilon) ^ gamma v := by
  let k : Fin 4 → ℤ := v - gamma v • epsilon
  have hk : gamma k = 0 := by
    simp [k, gamma, epsilon]
    exact sub_self _
  have hker := image_eq_one_of_gamma_eq_zero φ x hx hc k hk
  have hdecomp : v = gamma v • epsilon + k := by
    ext i
    fin_cases i <;> simp [k, gamma, epsilon, mul_comm] <;> rfl
  calc
    φ (Multiplicative.ofAdd v) =
        φ (Multiplicative.ofAdd (gamma v • epsilon + k)) :=
      congrArg (fun a => φ (Multiplicative.ofAdd a)) hdecomp
    _ = φ (Multiplicative.ofAdd epsilon) ^ gamma v := by
      rw [ofAdd_add, map_mul, ofAdd_zsmul, map_zpow, hker, mul_one]

/-- The second fixed vector has character one. -/
theorem gamma_epsilonPrime : gamma epsilonPrime = 1 := by rfl

theorem image_epsilonPrime_eq
    {G : Type u} [Group G]
    (φ : Multiplicative (Fin 4 → ℤ) →* G) (x : G)
    (hx : ∀ v : Fin 4 → ℤ,
      x * φ (Multiplicative.ofAdd v) * x⁻¹ =
        φ (Multiplicative.ofAdd (A1 *ᵥ v)))
    (hc : ∀ v : Fin 4 → ℤ, v 0 = 0 → v 1 = 0 →
      φ (Multiplicative.ofAdd v) = 1) :
    φ (Multiplicative.ofAdd epsilonPrime) =
      φ (Multiplicative.ofAdd epsilon) := by
  simpa only [gamma_epsilonPrime, zpow_one] using
    image_eq_zpow_gamma φ x hx hc epsilonPrime

theorem image_firstBasis_eq
    {G : Type u} [Group G]
    (φ : Multiplicative (Fin 4 → ℤ) →* G) (x : G)
    (hx : ∀ v : Fin 4 → ℤ,
      x * φ (Multiplicative.ofAdd v) * x⁻¹ =
        φ (Multiplicative.ofAdd (A1 *ᵥ v)))
    (hc : ∀ v : Fin 4 → ℤ, v 0 = 0 → v 1 = 0 →
      φ (Multiplicative.ofAdd v) = 1) :
    φ (Multiplicative.ofAdd (![1, 0, 0, 0] : Fin 4 → ℤ)) =
      φ (Multiplicative.ofAdd epsilon) := by
  simpa using image_eq_zpow_gamma φ x hx hc (![1, 0, 0, 0] : Fin 4 → ℤ)

/-- The first matrix fixes epsilon, by its four integer row calculations. -/
theorem A1_fixes_epsilon : A1 *ᵥ epsilon = epsilon := by decide

theorem image_epsilon_commute_first
    {G : Type u} [Group G]
    (φ : Multiplicative (Fin 4 → ℤ) →* G) (x : G)
    (hx : ∀ v : Fin 4 → ℤ,
      x * φ (Multiplicative.ofAdd v) * x⁻¹ =
        φ (Multiplicative.ofAdd (A1 *ᵥ v))) :
    Commute (φ (Multiplicative.ofAdd epsilon)) x := by
  have h := hx epsilon
  rw [A1_fixes_epsilon] at h
  exact ((mul_inv_eq_iff_eq_mul).mp h).symm

/-- The second matrix fixes epsilonPrime, by its four integer row calculations. -/
theorem A2_fixes_epsilonPrime : A2 *ᵥ epsilonPrime = epsilonPrime := by decide

theorem image_epsilon_commute_second
    {G : Type u} [Group G]
    (φ : Multiplicative (Fin 4 → ℤ) →* G) (x y : G)
    (hx : ∀ v : Fin 4 → ℤ,
      x * φ (Multiplicative.ofAdd v) * x⁻¹ =
        φ (Multiplicative.ofAdd (A1 *ᵥ v)))
    (hy : ∀ v : Fin 4 → ℤ,
      y * φ (Multiplicative.ofAdd v) * y⁻¹ =
        φ (Multiplicative.ofAdd (A2 *ᵥ v)))
    (hc : ∀ v : Fin 4 → ℤ, v 0 = 0 → v 1 = 0 →
      φ (Multiplicative.ofAdd v) = 1) :
    Commute (φ (Multiplicative.ofAdd epsilon)) y := by
  have h := hy epsilonPrime
  rw [A2_fixes_epsilonPrime, image_epsilonPrime_eq φ x hx hc] at h
  exact ((mul_inv_eq_iff_eq_mul).mp h).symm

end LatticeImageCollapse
