/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
/-!
# Transporting charted space structures along homeomorphisms

  Transporting charted space structures along homeomorphisms: if `M` carries a
  `C^k` charted-space structure and `e : M ~= N` a homeomorphism, then `N` inherits
  one; plus the criteria for two transported structures to coincide.
-/



open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Transporting atlases along a homeomorphism -/

/-- The charted space structure on `N` transported from `M` along a homeomorphism. -/
@[instance_reducible]
def ManifoldAtlasTransport.chartedSpace {H M N : Type*} [TopologicalSpace H] [Nonempty H]
    [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M] (h : M ≃ₜ N) : ChartedSpace H N
    where
  atlas :=
    (fun e : OpenPartialHomeomorph M H => e.lift_openEmbedding h.isOpenEmbedding) '' atlas H M
  chartAt y := (chartAt H (h.symm y)).lift_openEmbedding h.isOpenEmbedding
  mem_chart_source y := ⟨h.symm y, mem_chart_source H (h.symm y), h.apply_symm_apply y⟩
  chart_mem_atlas y := ⟨chartAt H (h.symm y), chart_mem_atlas H (h.symm y), rfl⟩

/-- Transition maps of the transported atlas equal the original transition maps. -/
theorem ManifoldAtlasTransport.transition_eq {H M N : Type*} [TopologicalSpace H] [Nonempty H]
    [TopologicalSpace M] [TopologicalSpace N] (h : M ≃ₜ N) (e e' : OpenPartialHomeomorph M H) :
    (e.lift_openEmbedding h.isOpenEmbedding).symm.trans
        (e'.lift_openEmbedding h.isOpenEmbedding) =
      e.symm.trans e' :=
  e.lift_openEmbedding_trans e' h.isOpenEmbedding

/-- A manifold transported along a homeomorphism is still a manifold for the same model. -/
theorem ManifoldAtlasTransport.isManifold {H M N : Type*} [TopologicalSpace H] [Nonempty H]
    [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M] {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (h : M ≃ₜ N) [IsManifold I n M] :
    letI := chartedSpace (H := H) h
    IsManifold I n N := by
  let := chartedSpace (H := H) h
  refine { compatible := ?_ }
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  rw [transition_eq]
  exact (contDiffGroupoid n I).compatible he he'
