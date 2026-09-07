module

public import Lib.Analysis.Real.MeshScale
public import Lib.Topology.Dimension.CubeBoundaryThree
public import Lib.Topology.MetricSpace.LebesgueNumber

/-!
# Lebesgue and mesh scales on the boundary of the three-cube

This file translates Section 2 of the canonical textbook proof, lines 1348--1366.  It records
that the inherited boundary metric computes the same diameter as the ambient Euclidean metric,
then assembles one Lebesgue scale with the mesh estimates chosen at that same scale.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

open Set

universe v

namespace TopologicalSpace.CubeBoundaryThree

/-- Textbook Section 2, lines 1350--1351: the boundary metric is the restricted Euclidean metric,
so intrinsic diameter equals the diameter of the ambient subtype image (Q-D). -/
public theorem diam_coe_image (A : Set Boundary) :
    Metric.diam A = Metric.diam (((↑) : Boundary → Ambient) '' A) := by
  exact (isometry_subtype_coe.diam_image A).symm

/-- Textbook Section 2, lines 1348--1366: one positive Lebesgue scale for the original cover is
retained while the mesh denominator and both real mesh scales are chosen at that same scale. -/
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
  -- Lines 1349--1353: choose one positive Lebesgue scale with both retained cover clauses (Q-L).
  rcases Metric.exists_lebesgue_number_diam U hU with ⟨lambda, hlambda, hball, hdiam⟩
  -- Lines 1351--1352: choose an explicit point of the nonempty cube boundary (Q-P).
  rcases boundary_nonempty with ⟨x, hx⟩
  let q : Boundary := ⟨x, hx⟩
  -- Lines 1351--1352: the original cover supplies a member containing that point (Q-I).
  rcases hU.exists_mem q with ⟨i, hi⟩
  -- Hence the original index type is explicitly nonempty, without installing an instance (Q-N).
  have hι : Nonempty ι := ⟨i⟩
  -- Lines 1355--1366: choose the single landed mesh package at the identical lambda (Q-S).
  rcases Real.exists_mesh_scale lambda hlambda with
    ⟨N, hN, hNlambda, h, epsilon, hh, hepsilon, hhpos, hepsilonpos, hhhalf, heighth,
      htwoh, hsqrt, hadd, heightlambda⟩
  -- Assemble the same witnesses in the canonical conjunction order (Q-A).
  exact ⟨lambda, hlambda, hball, hdiam, hι, N, hN, hNlambda, h, epsilon, hh, hepsilon,
    hhpos, hepsilonpos, hhhalf, heighth, htwoh, hsqrt, hadd, heightlambda⟩

end TopologicalSpace.CubeBoundaryThree
