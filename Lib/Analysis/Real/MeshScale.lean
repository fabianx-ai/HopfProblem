module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# A real mesh scale with simultaneous estimates

This file formalizes the mesh choice and all inequalities (2.2) from the canonical textbook
proof, lines 1355--1366.  The Archimedean choice is made once, and the same resulting mesh and
error scales witness every estimate.
-/

namespace Real

/-- Given a positive real scale `lambda`, there is a natural mesh denominator `N`, with mesh
`h = 2 / N` and error scale `epsilon = h / 9`, satisfying the five simultaneous estimates used
in (2.2) of the canonical textbook proof. -/
public theorem exists_mesh_scale (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, 0 < N ∧ (4 / lambda : ℝ) < (N : ℝ) ∧
      ∃ h epsilon : ℝ,
        h = 2 / (N : ℝ) ∧
        epsilon = h / 9 ∧
        0 < h ∧
        0 < epsilon ∧
        h < lambda / 2 ∧
        8 * epsilon < h ∧
        2 * epsilon < h ∧
        h * √2 < lambda ∧
        h + 2 * epsilon < lambda ∧
        8 * epsilon < lambda := by
  -- Choose the single denominator `N > 4 / lambda` and record its positivity (S-01).
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / lambda)
  have hfour : 0 < (4 / lambda : ℝ) := div_pos (by norm_num) hlambda
  have hNreal : 0 < (N : ℝ) := lt_trans hfour hN
  have hN_pos : 0 < N := Nat.cast_pos.mp hNreal
  have hNreal' : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos

  -- Define the one mesh scale `h = 2 / N` and error scale `epsilon = h / 9` (S-02).
  let h : ℝ := 2 / (N : ℝ)
  let epsilon : ℝ := h / 9
  have h_value : h = 2 / (N : ℝ) := rfl
  have epsilon_value : epsilon = h / 9 := rfl
  have hh_pos : 0 < h := by
    dsimp [h]
    exact div_pos (by norm_num) hNreal'
  have hepsilon_pos : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos hh_pos (by norm_num)

  -- Clearing the positive denominators in `N > 4 / lambda` gives `h < lambda / 2` (S-03).
  have hfour_lt : (4 : ℝ) < (N : ℝ) * lambda := (div_lt_iff₀ hlambda).mp hN
  have hh_lt : h < lambda / 2 := by
    rw [h_value, div_lt_iff₀ hNreal']
    nlinarith

  -- Since `epsilon = h / 9`, its eightfold and twofold multiples are below `h` (S-04, S-05).
  have height_h : 8 * epsilon < h := by
    rw [epsilon_value]
    linarith
  have htwo_h : 2 * epsilon < h := by
    rw [epsilon_value]
    linarith

  -- The standard comparison `sqrt 2 < 2`, scaled by positive `h`, proves the radical bound (S-06).
  have hsqrt_two : √(2 : ℝ) < 2 := by
    rw [Real.sqrt_lt] <;> norm_num
  have htwo_lt : 2 * h < lambda := by linarith
  have hsqrt : h * √2 < lambda := by
    have : h * √(2 : ℝ) < h * 2 := mul_lt_mul_of_pos_left hsqrt_two hh_pos
    nlinarith

  -- The identity `h + 2 epsilon = 11h/9` places this sum below `2h < lambda` (S-07).
  have hadd : h + 2 * epsilon < lambda := by
    rw [epsilon_value]
    nlinarith

  -- Finally `8 epsilon < h < lambda / 2 < lambda` gives the last displayed estimate (S-08).
  have height_lambda : 8 * epsilon < lambda := by
    have hlambda_half : lambda / 2 < lambda := by linarith
    exact height_h.trans (hh_lt.trans hlambda_half)

  -- Package the same `N`, `h`, and `epsilon` in the canonical conjunction order (S-09).
  exact ⟨N, hN_pos, hN, h, epsilon, h_value, epsilon_value, hh_pos, hepsilon_pos,
    hh_lt, height_h, htwo_h, hsqrt, hadd, height_lambda⟩

end Real
