/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Geometry.Manifold.Morse.RadialFilling
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Whitney.AnnularExtension
import Lib.Geometry.Manifold.Whitney.CleanStrips
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs

/-!
# Filling a null-homotopic embedded circle by a smoothly embedded disk

A null-homotopy of a smooth embedded circle `γ : S¹ → N` in a manifold of dimension `≥ 5` with
collars in the time variable yields a smooth map of the plane extending `γ` radially
(`RadialFilling.contMDiff_filling`); the Whitney embedding argument in dimension `≥ 5` (general
position for a `2`-disk) makes it an embedding of the closed disk
(`exists_embedded_disk_extension_of_smooth_extension`,
`MorseCancellation.exists_smooth_embedded_disk_of_continuous_filling`).  Conversely a continuous
disk with boundary `γ` gives the null-homotopy (`circle_nullhomotopy_of_disk`), and in a sublevel
disk of dimension `≥ 3` every circle in the boundary sphere is null-homotopic
(`SublevelDisk.circle_nullhomotopies`).  Cf. Milnor, *Lectures on the h-cobordism theorem*,
Theorem 6.6 (Whitney's lemma), embedding part.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

theorem SublevelDisk.circle_nullhomotopies {M : Type*} [TopologicalSpace M] [T2Space M]
    {f : M → ℝ} {a : ℝ} {n : ℕ} (d : SublevelDisk (n + 1) f a) (hn : 1 < n) :
    ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = a }),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let e : Hemisphere.Sphere n ≃ₜ { x : M // f x = a } := d.boundaryHomeomorph
  let forward : C(Hemisphere.Sphere n, { x : M // f x = a }) := ⟨e, e.continuous⟩
  let backward : C({ x : M // f x = a }, Hemisphere.Sphere n) := ⟨e.symm, e.symm.continuous⟩
  intro g
  obtain ⟨q, hq⟩ := sphere_sphere_nullhomotopic hn (backward.comp g)
  have heq : forward.comp (backward.comp g) = g := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (g x)
  have hh : (forward.comp (backward.comp g)).Homotopic (ContinuousMap.const _ (e q)) :=
    (ContinuousMap.Homotopic.refl forward).comp hq
  exact ⟨e q, heq ▸ hh⟩

theorem SphereBoundary.exists_extension_immersive_on_sphere {E G H N : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    [Fact (Module.finrank ℝ E = n + 1)] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {γ : Metric.sphere (0 : E) 1 → N}
    (hext : ∀ x : Metric.sphere (0 : E) 1, f x.1 = γ x)
    (hγ : ∀ x, Function.Injective (mfderiv (𝓡 n) J γ x))
    (hdim : n + Module.finrank ℝ E < Module.finrank ℝ G) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ x : Metric.sphere (0 : E) 1, g x.1 = γ x) ∧
          ∀ x : Metric.sphere (0 : E) 1, Function.Injective (mfderiv 𝓘(ℝ, E) J g x.1) := by
  have hb : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val : Metric.sphere (0 : E) 1 → E) :=
    contMDiff_coe_sphere
  have hzero (x : Metric.sphere (0 : E) 1) : definingFunction x.1 = 0 :=
    (definingFunction_eq_zero_iff x.1).mpr x.property
  have hd :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + Module.finrank ℝ E < Module.finrank ℝ G := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨g, hg, hhom, hderiv⟩ :=
    ManifoldImmersion.exists_compact_boundary_derivative_repair
      (⟨f, hf.continuous⟩ : C(E, N)) hf hb contDiff_definingFunction hzero hd
      (common_kernel_of_immersive_sphere_extension hf hext hγ)
  refine ⟨g, hg, ?_, ?_⟩
  · intro x
    exact (hhom.fst_eq_snd (hzero x)).symm.trans (hext x)
  · intro x
    exact hderiv x.1 ⟨x, rfl⟩

theorem exists_embedded_disk_extension_of_smooth_extension {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : Hemisphere.Ambient 2 → N}
    (hf : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) J ∞ f) {γ : Hemisphere.Sphere 1 → N}
    (hext : ∀ x : Hemisphere.Sphere 1, f x.1 = γ x) (hγinj : Function.Injective γ)
    (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) J γ x)) (hdim : 5 ≤ Module.finrank ℝ G) :
    ∃ g : C(Hemisphere.Ambient 2, N),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) J ∞ g ∧
        (∀ x : Hemisphere.Sphere 1, g x.1 = γ x) ∧
          Topology.IsClosedEmbedding (fun x : Hemisphere.Ball 2 => g x.1) ∧
            ∀ x : Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) J g x.1) := by
  let : Fact (Module.finrank ℝ (Hemisphere.Ambient 2) = 1 + 1) :=
    ⟨by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]⟩
  have hd : 1 + Module.finrank ℝ (Hemisphere.Ambient 2) < Module.finrank ℝ G := by
    simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]
    omega
  obtain ⟨f₁, hf₁, hboundary₁, hderiv₁⟩ :=
    SphereBoundary.exists_extension_immersive_on_sphere (n := 1) hf hext hγderiv hd
  let K : Set (Hemisphere.Ambient 2) := Metric.closedBall 0 1
  let C : Set (Hemisphere.Ambient 2) := Metric.sphere 0 1
  have hK : IsCompact K := ProperSpace.isCompact_closedBall 0 1
  have hC : IsClosed C := Metric.isClosed_sphere
  have hfixed : Set.InjOn f₁ (K ∩ C) := by
    intro x hx y hy hxy
    let xs : Hemisphere.Sphere 1 := ⟨x, hx.2⟩
    let ys : Hemisphere.Sphere 1 := ⟨y, hy.2⟩
    have hboundaryeq : γ xs = γ ys := (hboundary₁ xs).symm.trans (hxy.trans (hboundary₁ ys))
    exact congrArg Subtype.val (hγinj hboundaryeq)
  have hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) J f₁ x) :=
    fun x hx => hderiv₁ ⟨x, hx.2⟩
  obtain ⟨g, hg, hhom, hemb, hderivg⟩ :=
    ManifoldImmersion.exists_relative_compact_embedding_twoDimensional f₁ hf₁
      (by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]) hdim hK hC hfixed hderiv
  refine ⟨g, hg, ?_, hemb, fun x => hderivg x.1 x.property⟩
  intro x
  exact (hhom.fst_eq_snd x.property).symm.trans (hboundary₁ x)

theorem RadialFilling.contMDiffAt_direction {n : ℕ} (b : Hemisphere.Sphere n)
    {v : Hemisphere.Ambient (n + 1)} (hv : v ≠ 0) :
    ContMDiffAt 𝓘(ℝ, Hemisphere.Ambient (n + 1)) (𝓡 n) ∞ (direction b) v := by
  let V : TopologicalSpace.Opens (Hemisphere.Ambient (n + 1)) :=
    ⟨{w | w ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩
  have : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hnorm :
    ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) 𝓘(ℝ, Hemisphere.Ambient (n + 1)) ∞
      (fun w : V => NormedSpace.normalize (w : Hemisphere.Ambient (n + 1))) :=
    contMDiff_normalize contMDiff_subtype_val (fun w => w.2)
  have hmem (w : V) :
    NormedSpace.normalize (w : Hemisphere.Ambient (n + 1)) ∈
      Metric.sphere (0 : Hemisphere.Ambient (n + 1)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize w.2
  have hsphere := hnorm.codRestrict_sphere (n := n) hmem
  have hs :
    ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) (𝓡 n) ∞ (fun w : V => direction b w.1) := by
    apply hsphere.congr
    intro w
    exact Subtype.ext (direction_coe b w.2)
  exact (contMDiffAt_subtype_iff (U := V) (f := direction b) (x := ⟨v, hv⟩)).mp (hs ⟨v, hv⟩)

theorem RadialFilling.contMDiff_filling {n : ℕ} {G K M : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace M]
    [ChartedSpace K M] {f : C(Hemisphere.Sphere n, M)} {c : M}
    (H : f.Homotopy (ContinuousMap.const _ c)) (b : Hemisphere.Sphere n)
    (hf : ContMDiff (𝓡 n) J ∞ f) (hH : ContMDiff ((𝓡∂ 1).prod (𝓡 n)) J ∞ H)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    (htop : ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c) :
    ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) J ∞ (filling H b) := by
  intro v
  by_cases hinner : ‖v‖ < 1 / 4
  · apply (contMDiffAt_const (c := c)).congr_of_eventuallyEq
    have hn : {w : Hemisphere.Ambient (n + 1) | ‖w‖ < 1 / 4} ∈ 𝓝 v :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hinner
    filter_upwards [hn] with w hw
    exact filling_eq_center H b htop (le_of_lt hw)
  · by_cases houter : 3 / 4 < ‖v‖
    · have hv : v ≠ 0 := norm_pos_iff.mp (by linarith)
      have hs := (hf (direction b v)).comp v (contMDiffAt_direction b hv)
      apply hs.congr_of_eventuallyEq
      have hn : {w : Hemisphere.Ambient (n + 1) | 3 / 4 < ‖w‖} ∈ 𝓝 v :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds houter
      filter_upwards [hn] with w hw
      exact filling_eq_boundary H b hbottom (le_of_lt hw)
    · have hv : 0 < ‖v‖ := by linarith [le_of_not_gt hinner]
      have hunit : ‖v‖ < 1 := by linarith [le_of_not_gt houter]
      exact
        (hH (radialTime v, direction b v)).comp v (f := fun w => (radialTime w, direction b w))
          ((contMDiffAt_radialTime hv hunit).prodMk
            (contMDiffAt_direction b (norm_pos_iff.mp hv)))

theorem MorseCancellation.circle_nullhomotopy_of_disk {N : Type*} [TopologicalSpace N]
    (γ : C(Hemisphere.Sphere 1, N)) (D : C(Hemisphere.Ball 2, N))
    (hboundary :
      ∀ z : Hemisphere.Sphere 1,
        D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ c : N, γ.Homotopic (ContinuousMap.const _ c) := by
  let c := D ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let H : γ.Homotopy (ContinuousMap.const _ c) :=
    { toFun := fun p => D (SphereCone.point p)
      continuous_toFun := D.continuous.comp SphereCone.continuous_point
      map_zero_left := by
        intro z
        have he :
          SphereCone.point (0, z) =
            (⟨z.val, Metric.sphere_subset_closedBall z.property⟩ : Hemisphere.Ball 2) := by
          apply Subtype.ext
          simp [SphereCone.point]
        rw [he]
        exact hboundary z
      map_one_left := by
        intro z
        have he :
          SphereCone.point (1, z) =
            (⟨0, Metric.mem_closedBall_self zero_le_one⟩ : Hemisphere.Ball 2) := by
          apply Subtype.ext
          simp [SphereCone.point]
        exact congrArg D he }
  exact ⟨c, ⟨H⟩⟩

theorem MorseCancellation.exists_smooth_embedded_disk_of_continuous_filling {G N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] (γ : C(Hemisphere.Sphere 1, N))
    (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ) (hγinj : Function.Injective γ)
    (hγderiv : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, G) γ z))
    (hdim : 5 ≤ Module.finrank ℝ G) (D : C(Hemisphere.Ball 2, N))
    (hboundary :
      ∀ z : Hemisphere.Sphere 1,
        D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ g : C(Hemisphere.Ambient 2, N),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
        (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
          Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
            ∀ z : Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) g z.val) := by
  obtain ⟨c, ⟨H⟩⟩ := circle_nullhomotopy_of_disk γ D hboundary
  obtain ⟨H', hH', hlo, hhi⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hγ contMDiff_const H
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : Hemisphere.Sphere 1 := ⟨v, hv⟩
  have hsmooth := RadialFilling.contMDiff_filling H' b hγ hH' hlo hhi
  have hext := RadialFilling.filling_on_sphere H' b hlo
  exact exists_embedded_disk_extension_of_smooth_extension hsmooth hext hγinj hγderiv hdim

end
