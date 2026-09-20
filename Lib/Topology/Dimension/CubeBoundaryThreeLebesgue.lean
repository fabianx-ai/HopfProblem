module

public import Mathlib.Analysis.Real.Sqrt
public import Lib.Topology.Dimension.CubeBoundaryThree
public import Lib.Topology.MetricSpace.LebesgueNumber

/-!
# Lebesgue and mesh scales on the boundary of the three-cube

The Lebesgue number lemma on the boundary of the three-cube, in the form used to build a brick
cover: the inherited boundary metric computes the same diameter as the ambient Euclidean metric,
and one positive Lebesgue scale can be chosen together with mesh estimates at that same scale.

## References

* J. R. Munkres, *Topology*, Lemma 27.5 (the Lebesgue number lemma)
* R. Engelking, *Dimension Theory*, Theorem 1.8.2
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

open Set

universe v

namespace TopologicalSpace.CubeBoundaryThree

/-- The boundary carries the restricted Euclidean metric, so the intrinsic diameter of a subset
equals the diameter of its image in the ambient space. -/
public theorem diam_coe_image (A : Set Boundary) :
    Metric.diam A = Metric.diam (((↑) : Boundary → Ambient) '' A) := by
  exact (isometry_subtype_coe.diam_image A).symm

/-- Given a positive real scale `lambda`, there is a natural mesh denominator `N`, with mesh
`h = 2 / N` and error scale `epsilon = h / 9`, satisfying the simultaneous estimates used by
`exists_cover_mesh_scale` below.  The constants `2 / N` and `h / 9` and the order of the
conjunction are those of that one consumer; the mathematical content is the Archimedean property
`exists_nat_gt` together with `linarith`. -/
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
        h * Real.sqrt 2 < lambda ∧
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
  have hsqrt_two : Real.sqrt (2 : ℝ) < 2 := by
    rw [Real.sqrt_lt] <;> norm_num
  have htwo_lt : 2 * h < lambda := by linarith
  have hsqrt : h * Real.sqrt 2 < lambda := by
    have : h * Real.sqrt (2 : ℝ) < h * 2 := mul_lt_mul_of_pos_left hsqrt_two hh_pos
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

/-- One positive Lebesgue scale `lambda` for a given open cover of the cube boundary, together
with a mesh denominator `N` and mesh scales `h`, `epsilon` chosen small relative to `lambda`
(Munkres, *Topology*, Lemma 27.5 for the Lebesgue clause). -/
public theorem exists_cover_mesh_scale {ι : Type v}
    (U : ι → TopologicalSpace.Opens Boundary) (hU : TopologicalSpace.IsOpenCover U) :
    ∃ lambda : ℝ, 0 < lambda ∧
      (∀ x : Boundary, ∃ i : ι, Metric.ball x lambda ⊆ U i) ∧
      (∀ A : Set Boundary, A.Nonempty → Metric.diam A < lambda → ∃ i : ι, A ⊆ U i) ∧
      Nonempty ι ∧
      ∃ N : ℕ, 0 < N ∧ (4 / lambda : ℝ) < (N : ℝ) ∧
        ∃ h epsilon : ℝ,
          h = 2 / (N : ℝ) ∧ epsilon = h / 9 ∧ 0 < h ∧ 0 < epsilon ∧
          h < lambda / 2 ∧ 8 * epsilon < h ∧ 2 * epsilon < h ∧
          h * Real.sqrt 2 < lambda ∧ h + 2 * epsilon < lambda ∧
          8 * epsilon < lambda := by
  -- Choose one positive Lebesgue scale with both cover clauses.
  rcases Metric.exists_lebesgue_number_diam U hU with ⟨lambda, hlambda, hball, hdiam⟩
  -- Choose an explicit point of the nonempty cube boundary.
  rcases boundary_nonempty with ⟨x, hx⟩
  let q : Boundary := ⟨x, hx⟩
  -- The cover supplies a member containing that point.
  rcases hU.exists_mem q with ⟨i, hi⟩
  -- Hence the index type is explicitly nonempty, without installing an instance.
  have hι : Nonempty ι := ⟨i⟩
  -- Choose the mesh package at that same `lambda`.
  rcases exists_mesh_scale lambda hlambda with
    ⟨N, hN, hNlambda, h, epsilon, hh, hepsilon, hhpos, hepsilonpos, hhhalf, heighth,
      htwoh, hsqrt, hadd, heightlambda⟩
  -- Assemble the witnesses.
  exact ⟨lambda, hlambda, hball, hdiam, hι, N, hN, hNlambda, h, epsilon, hh, hepsilon,
    hhpos, hepsilonpos, hhhalf, heighth, htwoh, hsqrt, hadd, heightlambda⟩

end TopologicalSpace.CubeBoundaryThree
