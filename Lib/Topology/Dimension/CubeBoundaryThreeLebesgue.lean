module

public import Lib.Analysis.Real.MeshScale
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
  rcases Real.exists_mesh_scale lambda hlambda with
    ⟨N, hN, hNlambda, h, epsilon, hh, hepsilon, hhpos, hepsilonpos, hhhalf, heighth,
      htwoh, hsqrt, hadd, heightlambda⟩
  -- Assemble the witnesses.
  exact ⟨lambda, hlambda, hball, hdiam, hι, N, hN, hNlambda, h, epsilon, hh, hepsilon,
    hhpos, hepsilonpos, hhhalf, heighth, htwoh, hsqrt, hadd, heightlambda⟩

end TopologicalSpace.CubeBoundaryThree
