/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

This file is a formalization of the claim that the six-sphere admits a complex
manifold structure compatible with its standard topology.

The mathematical content is drawn from "A compact complex threefold fibred by
tori over the projective line, and the six-sphere" (https://alpo.ge/s6.pdf),
originally shared by Levent Alpöge on X:
https://x.com/__alpoge__/status/2091639597193368014

The majority of the Lean code in this formalization is written by Codex.

The statement of the final result is adapted from the Formal Conjectures
formalization of MathOverflow question 1973:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Mathoverflow/1973.lean

Parts of the complex-analysis development, including the Riemann mapping
theorem, Hurwitz's theorem, analytic factorization, normal-family arguments,
and unit-disc automorphisms, were adapted from Yury Kudryashov's Mathlib work:
https://github.com/leanprover-community/mathlib4/pull/33505
Source commit: d43061d911b1aeae0788591da437a3b115098962
Upstream files:
  Mathlib/Analysis/Complex/RiemannMapping.lean
  Mathlib/Analysis/Complex/UnitDisc/Shift.lean

Additional preliminary Riemann-mapping lemmas were adapted from
Mathlib/Analysis/Complex/RiemannMapping.lean in Mathlib v4.33.0:
https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/RiemannMapping.lean

Parts of the topology development, including simple connectedness of spheres,
the path-factorization portion of the van Kampen development, and associated
compatibility lemmas, were adapted from Sebastian Kumar's Mathlib work:
https://github.com/leanprover-community/mathlib4/pull/28246
Source commit: 037ad801e1e5a5b7aa1750957c07f7769812effc
Upstream files:
  Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnectedSphere.lean
  Mathlib/AlgebraicTopology/FundamentalGroupoid/VanKampen.lean
  Mathlib/Topology/Path.lean
  Mathlib/Logic/Equiv/PartialEquiv.lean

The reused upstream materials were released under the Apache License,
Version 2.0. They were modified, reorganized, and adapted for this
formalization; some results were also strengthened. Their copyright
and author notices are retained below.

Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Authors: Yury Kudryashov

Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Authors: Sebastian Kumar

Copyright 2025 The Formal Conjectures Authors.
-/

/-
Move-only extraction from HopfProblem Solution.lean at 9ac8a456b526527837d7082ff775213ca8bc9809.
Original source lines 62392--81182; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.SingularHomology
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Analysis.ODE.SmoothFlow
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle
import Lib.Geometry.Manifold.Collar
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection
import Mathlib
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.Topology.Homotopy.LoopSubdivision
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.Geometry.Manifold.Whitney.BigonModel
import Lib.Topology.Homotopy.CellAttachment
import Lib.Topology.Homotopy.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.Algebra.Module.IntegerPresentation
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.Topology.OnePointCollapse
import Hopf.Proof.Geometry.Manifold.Morse.MinimalSystem
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Algebra.Module.IntegerPresentation
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods
import Lib.Geometry.Manifold.Morse.RearrangementAmbient
import Lib.AlgebraicTopology.SingularHomology.OnePointCover
import Lib.Geometry.Manifold.Morse.SurgeryHomology
import Hopf.Proof.Geometry.Manifold.Morse.SurgeryHomology
import Lib.Geometry.Manifold.Morse.OrderedCancellation
import Lib.Geometry.Manifold.Morse.AdaptedWindows
import Lib.Geometry.Manifold.Morse.SurgeryCollapse

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

theorem exists_smooth_nullhomotopy_of_homotopySixSphere {E G H X M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [CompactSpace X]
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold 𝓘(ℝ, G) ∞ M] (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E < 6) (f : C(X, M)) (hf : ContMDiff I 𝓘(ℝ, G) ∞ f) :
    ∃ c : M,
      ∃ H : f.Homotopy (ContinuousMap.const X c),
        ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ, G) ∞ H ∧
          (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x) ∧
            (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c) := by
  obtain ⟨c, ⟨H⟩⟩ := manifoldMap_nullhomotopic_of_homotopySixSphere (I := I) e hdim f
  obtain ⟨H', hH', hlo, hhi⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hf contMDiff_const H
  exact ⟨c, H', hH', hlo, hhi⟩

theorem exists_smooth_disk_extension_of_homotopySixSphere {G M : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace G M]
    [IsManifold 𝓘(ℝ, G) ∞ M] (e : M ≃ₕ SixSphere) {n : ℕ} (hn : n < 6)
    (f : C(Hemisphere.Sphere n, M)) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, G) ∞ f) :
    ∃ (c : M) (F : Hemisphere.Ambient (n + 1) → M),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) 𝓘(ℝ, G) ∞ F ∧
        (∀ v : Hemisphere.Sphere n, F v.1 = f v) ∧ ∀ v, ‖v‖ ≤ 1 / 4 → F v = c := by
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) < 6 := by
    simpa only [finrank_euclideanSpace_fin] using hn
  obtain ⟨c, H, hH, hlo, hhi⟩ := exists_smooth_nullhomotopy_of_homotopySixSphere e hd f hf
  obtain ⟨v, hv⟩ : (Hemisphere.Sphere n).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : Hemisphere.Sphere n := ⟨v, hv⟩
  exact
    ⟨c, RadialFilling.filling H b, RadialFilling.contMDiff_filling H b hf hH hlo hhi,
      RadialFilling.filling_on_sphere H b hlo, fun _ hv =>
      RadialFilling.filling_eq_center H b hhi hv⟩

theorem exists_embedded_disk_of_homotopySixSphere {G M : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace M] [ChartedSpace G M]
    [IsManifold 𝓘(ℝ, G) ∞ M] [T2Space M] (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ G = 6) (γ : C(Hemisphere.Sphere 1, M))
    (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ) (hγinj : Function.Injective γ)
    (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, G) γ x)) :
    ∃ g : C(Hemisphere.Ambient 2, M),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
        (∀ x : Hemisphere.Sphere 1, g x.1 = γ x) ∧
          Topology.IsClosedEmbedding (fun x : Hemisphere.Ball 2 => g x.1) ∧
            ∀ x : Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) g x.1) := by
  obtain ⟨-, f, hf, hext, -⟩ :=
    exists_smooth_disk_extension_of_homotopySixSphere e (n := 1) (by decide) γ hγ
  exact exists_embedded_disk_extension_of_smooth_extension hf hext hγinj hγderiv (by omega)

theorem MorseCancellation.exists_disk_in_level_basin_of_index_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Function.Injective γ) (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ x))
    (hlevel : ∀ z, f (γ z) = a) :
    ∃ g : C(Hemisphere.Ambient 2, M),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, E) ∞ g ∧
        (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
          Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
            (∀ z : Hemisphere.Ball 2,
                Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, E) g z.val)) ∧
              ∀ z : Hemisphere.Ball 2,
                g z.val ∈ FlowCancellation.levelBasin S.flow f a := by
  obtain ⟨g₀, hg₀, hboundary, hemb, hderiv⟩ :=
    exists_embedded_disk_of_homotopySixSphere e hdim γ hγ hγinj hγderiv
  let K : Set (Hemisphere.Ambient 2) := Metric.closedBall 0 1
  let C : Set (Hemisphere.Ambient 2) := Metric.sphere 0 1
  have hK : IsCompact K := ProperSpace.isCompact_closedBall _ _
  have hC : IsClosed C := Metric.isClosed_sphere
  have hinj : Set.InjOn g₀ K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hfixed (z : Hemisphere.Ambient 2) (hz : z ∈ K ∩ C) :
    g₀ z ∈ FlowCancellation.levelBasin S.flow f a := by
    refine ⟨0, ?_⟩
    rw [S.flow.map_zero_apply, hboundary ⟨z, hz.2⟩, hlevel]
  have hhigh' (p : ManifoldMorse.criticalPoints E f) (hp : a ≤ f p) :
    Module.finrank ℝ E - nativeMorseIndex E f p ≤ 3 := by
    have hh := hhigh p hp
    omega
  obtain ⟨g, hg, hhom, hembg, hderg, -, hbasin⟩ :=
    exists_embedded_avoidance_into_level_basin S hf hreg hhigh' hlow g₀ hg₀
      (by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]; omega)
      (by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]; omega) hK hK hC hinj
      (fun z hz => hderiv ⟨z, hz⟩) hfixed
  refine ⟨g, hg, ?_, hembg, fun z => hderg z.val z.property, ?_⟩
  · intro z
    exact (hhom.fst_eq_snd z.property).symm.trans (hboundary z)
  · intro z
    exact hbasin z.val (Or.inr z.property)

theorem MorseCancellation.exists_actual_regular_level_disk_of_index_cut {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Function.Injective γ) (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ x))
    (hlevel : ∀ z, f (γ z) = a) :
    ∃ D : C(Hemisphere.Ball 2, { y : M // f y = a }),
      ∀ z : Hemisphere.Sphere 1,
        (D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩).val = γ z := by
  obtain ⟨g, hg, hboundary, -, -, hbasin⟩ :=
    exists_disk_in_level_basin_of_index_cut S hf e hdim hreg hhigh hlow γ hγ hγinj hγderiv hlevel
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let z₀ : { y : M // f y = a } := ⟨γ ⟨v, hv⟩, hlevel ⟨v, hv⟩⟩
  let _ := RegularLevel.chartedSpace hf hreg
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf hreg S.smooth S.flow S.integral
      (fun y hy => S.descent y (hreg y hy)) z₀
  have hcont : Continuous (fun z : Hemisphere.Ball 2 => Φ.symm (g z.val)) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous (g.continuous.comp continuous_subtype_val)
      (fun z => htarget.symm ▸ hbasin z)
  let D : C(Hemisphere.Ball 2, { y : M // f y = a }) :=
    ⟨fun z => (Φ.symm (g z.val)).1, continuous_fst.comp hcont⟩
  refine ⟨D, ?_⟩
  intro z
  let p : { y : M // f y = a } := ⟨γ z, hlevel z⟩
  have hp : (p, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
  have hφ : Φ (p, 0) = γ z := by rw [hformula, S.flow.map_zero_apply]
  have hi : Φ.symm (Φ (p, 0)) = (p, 0) := Φ.left_inv' hp
  rw [hφ] at hi
  change (Φ.symm (g z.val)).1.val = γ z
  rw [hboundary z]
  exact congrArg (fun q : { y : M // f y = a } × ℝ => q.1.val) hi

theorem MorseCancellation.exists_embedded_regular_level_disk_of_index_cut {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Function.Injective γ) (hγderiv : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ z))
    (hlevel : ∀ z, f (γ z) = a) :
    let _ := RegularLevel.chartedSpace hf hreg
    ∃ g : C(Hemisphere.Ambient 2, { y : M // f y = a }),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧
        (∀ z : Hemisphere.Sphere 1, (g z.val).val = γ z) ∧
          Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
            ∀ z : Hemisphere.Ball 2,
              Function.Injective
                (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model E) g
                  z.val) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  obtain ⟨D, hD⟩ :=
    exists_actual_regular_level_disk_of_index_cut S hf e hdim hreg hhigh hlow γ hγ hγinj hγderiv
      hlevel
  let γL : C(Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨fun z => ⟨γ z, hlevel z⟩, γ.continuous.subtype_mk _⟩
  have hγL : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γL :=
    (RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 1) γL).mpr hγ
  have hinj : Function.Injective γL := fun x y hxy => hγinj (congrArg Subtype.val hxy)
  have hderiv (z : Hemisphere.Sphere 1) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γL z) :=
    RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 1) γL z hγ.contMDiffAt
      (hγderiv z)
  have hdimL : 5 ≤ Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
    norm_num
  have hboundary (z : Hemisphere.Sphere 1) :
    D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γL z := Subtype.ext (hD z)
  obtain ⟨g, hg, hboundaryg, hemb, hderivg⟩ :=
    exists_smooth_embedded_disk_of_continuous_filling γL hγL hinj hderiv hdimL D hboundary
  exact ⟨g, hg, fun z => congrArg Subtype.val (hboundaryg z), hemb, hderivg⟩

theorem MorseCancellation.exists_native_middle_level_circle_disk {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Hemisphere.Sphere 1, { y : M // f y = a })) :
    let _ := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
          ∃ g : C(Hemisphere.Ambient 2, { y : M // f y = a }),
            ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧
              (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
                Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
                  (∀ z : Hemisphere.Ball 2,
                    Function.Injective
                      (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model E) g
                        z.val)) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) → _
  intro hγ hγi hγd
  let γM : C(Hemisphere.Sphere 1, M) :=
    ⟨Subtype.val ∘ γ, continuous_subtype_val.comp γ.continuous⟩
  have hγM : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γM :=
    (RegularLevel.contMDiff_inclusion hf hreg).comp hγ
  have hγMi : Function.Injective γM := Subtype.val_injective.comp hγi
  have hγMd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γM z) := by
    intro z
    change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (Subtype.val ∘ γ) z)
    rw [mfderiv_comp z
        ((RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))
        (hγ.mdifferentiableAt (by simp))]
    exact (RegularLevel.injective_mfderiv_inclusion hf hreg (γ z)).comp (hγd z)
  obtain ⟨g, hg, hb, hemb, hgd⟩ :=
    exists_embedded_regular_level_disk_of_index_cut S hf e hdim hreg hhigh hlow γM hγM hγMi hγMd
      (fun z => (γ z).property)
  exact ⟨g, hg, fun z => Subtype.ext (hb z), hemb, hgd⟩

theorem MorseCancellation.exists_native_middle_level_circle_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PathConnectedSpace M]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ δ : C(Hemisphere.Sphere 1, { y : M // f y = a })) :
    let _ := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) →
                ∃ P :
                  Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
                    { y : M // f y = a } { y : M // f y = a } ∞,
                  SupportedDiffeomorph.IsotopicToIdentity P ∧ ∀ z, P (γ z) = δ z := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let _ : CompactSpace { y : M // f y = a } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  obtain ⟨g, hg, hgb, hge, hgd⟩ :=
    exists_native_middle_level_circle_disk S hf e hdim hreg hhigh hlow γ hγ hγi hγd
  obtain ⟨h, hh, hhb, hhe, hhd⟩ :=
    exists_native_middle_level_circle_disk S hf e hdim hreg hhigh hlow δ hδ hδi hδd
  let _ := S.pathConnectedSpace_middle_level hf hdim hreg hhigh hlow (g 0)
  have hgi : Set.InjOn g (Metric.closedBall (0 : Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hge.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hhi : Set.InjOn h (Metric.closedBall (0 : Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hhe.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hcodim :
    Module.finrank ℝ (Hemisphere.Ambient 2) + 3 =
      Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [Hemisphere.Ambient, RegularLevel.Model, finrank_euclideanSpace_fin,
      hdim]
  have hmodel : 2 ≤ Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
    omega
  obtain ⟨P, hP, hformula⟩ :=
    DiskShrinking.exists_embedded_disk_isotopy hg hh hgi hhi (fun x hx => hgd ⟨x, hx⟩)
      (fun x hx => hhd ⟨x, hx⟩) 3 (by omega) hcodim hmodel
  refine ⟨P, hP, ?_⟩
  intro z
  rw [← hgb z, hformula z.val (Metric.sphere_subset_closedBall z.property), hhb z]

theorem MorseCancellation.exists_equal_level_circle_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ p : ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ δ : C(Hemisphere.Sphere 1, { y : M // g y = a })) :
    let _ := RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) →
                ∃ P :
                  Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
                    { y : M // g y = a } { y : M // g y = a } ∞,
                  SupportedDiffeomorph.IsotopicToIdentity P ∧ ∀ z, P (γ z) = δ z := by
  let _ := RegularLevel.chartedSpace hf hfr
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hf hfr
  let _ := RegularLevel.isManifold hg hgr
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  let L := equalLevelDiffeomorph hf hg hfr hgr heq
  let γ' : C(Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨L.symm ∘ γ, L.symm.continuous.comp γ.continuous⟩
  let δ' : C(Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨L.symm ∘ δ, L.symm.continuous.comp δ.continuous⟩
  have hγ' : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ' := L.symm.contMDiff.comp hγ
  have hδ' : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ' := L.symm.contMDiff.comp hδ
  have hderiv (κ : C(Hemisphere.Sphere 1, { y : M // g y = a }))
    (hk : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ κ)
    (hkd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) κ z)) (z) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) (L.symm ∘ κ) z) := by
    rw [mfderiv_comp z (L.symm.contMDiff.mdifferentiableAt (by simp))
        (hk.mdifferentiableAt (by simp))]
    exact (L.symm.mfderivToContinuousLinearEquiv (by simp) (κ z)).injective.comp (hkd z)
  obtain ⟨Q, hQ, hformula⟩ :=
    exists_native_middle_level_circle_isotopy S hf e hdim hfr hhigh hlow γ' δ' hγ'
      (L.symm.injective.comp hγi) (hderiv γ hγ hγd) hδ' (L.symm.injective.comp hδi)
      (hderiv δ hδ hδd)
  refine ⟨(L.symm.trans Q).trans L, isotopicToIdentity_conj L hQ, ?_⟩
  intro z
  change L (Q (γ' z)) = δ z
  rw [hformula]
  exact L.apply_symm_apply (δ z)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_new_attaching_circle_placement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}
    (S : AdaptedWindows E f) (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ q : ManifoldMorse.criticalPoints E f, a ≤ f q → 3 ≤ nativeMorseIndex E f q)
    (hlow : ∀ q : ManifoldMorse.criticalPoints E f, f q ≤ a → nativeMorseIndex E f q ≤ 3)
    (p : ManifoldMorse.criticalPoints E g)
    [Fact (Module.finrank ℝ (T.data p).chart.NegativeCoordinates = 1 + 1)] (hap : a < g p)
    (hgap : ∀ q : ManifoldMorse.criticalPoints E g, g q < g p → g q < a)
    (δ : C(Hemisphere.Sphere 1, { y : M // g y = a })) :
    let _ := RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ →
      Function.Injective δ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) →
          ∃ Γ : C(Hemisphere.Sphere 1, { y : M // g y = a }),
            ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧
              Function.Injective Γ ∧
                (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
                  (∀ x,
                      x ∈ Set.range Γ ↔
                        Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p.val)) ∧
                    ∃ P :
                      Diffeomorph 𝓘(ℝ, RegularLevel.Model E)
                        𝓘(ℝ, RegularLevel.Model E) { y : M // g y = a } { y : M // g y = a }
                        ∞,
                      SupportedDiffeomorph.IsotopicToIdentity P ∧
                        (∀ z, P (Γ z) = δ z) ∧
                          ∀ x,
                            Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p.val) ↔
                              P x ∈ Set.range δ := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.chartedSpace hg (T.data p).lower_regular
  let _ := RegularLevel.isManifold hg hgr
  let _ := RegularLevel.isManifold hg (T.data p).lower_regular
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ →
      Function.Injective δ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) → _
  intro hδ hδi hδd
  obtain ⟨σ, D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    T.exists_attaching_circle_lower_transport hg p hgr hap hgap
  have hrange (x : { y : M // g y = a }) :
    x ∈ Set.range Γ ↔ Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p.val) :=
    T.transported_attaching_range_iff hg p hgr σ σ.surjective Γ hflow x
  obtain ⟨P, hP, hformula⟩ :=
    exists_equal_level_circle_isotopy S hf hg e hdim hfr hgr heq hhigh hlow Γ δ hΓ hΓi hΓd hδ hδi
      hδd
  refine ⟨Γ, hΓ, hΓi, hΓd, hrange, P, hP, hformula, ?_⟩
  intro x
  rw [← hrange]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hformula z).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, P.injective ((hformula z).trans hz)⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_handle_trade_transverse_level_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}
    (S : AdaptedWindows E f) (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    [Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1)]
    (u : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 m.val))
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < g r)
    (hgap : ∀ z : ManifoldMorse.criticalPoints E g, g z < g r → g z < a)
    (hnewlow :
      ∀ z : ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    let _ := RegularLevel.chartedSpace hg hgr
    ∃ P :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { y : M // g y = a } { y : M // g y = a } ∞,
      SupportedDiffeomorph.IsotopicToIdentity P ∧
        {x : { y : M // g y = a } |
                Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 r.val) ∧
                  Filter.Tendsto (fun t => T.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 ∧
          ∃ (α : C(Hemisphere.Sphere 1, { y : M // g y = a })) (z₀ :
            Hemisphere.Sphere 1) (β :
            Metric.sphere (0 : (T.data q).chart.PositiveCoordinates) 1 → { y : M // g y = a }) (v
            : Metric.sphere (0 : (T.data q).chart.PositiveCoordinates) 1),
            ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ α ∧
              MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v ∧
                β v = α z₀ ∧
                  NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) α β
                      z₀ v ∧
                    (∀ z, Filter.Tendsto (fun t => T.flow t (α z).val) Filter.atBot (𝓝 r.val)) ∧
                      (∀ᶠ w in 𝓝 v,
                          Filter.Tendsto (fun t => T.flow t (P (β w)).val) Filter.atTop
                            (𝓝 q.val)) ∧
                        ∀ x : { y : M // g y = a },
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 r.val) →
                            Filter.Tendsto (fun t => T.flow t (P x).val) Filter.atTop (𝓝 m.val) ∨
                              Filter.Tendsto (fun t => T.flow t (P x).val) Filter.atTop
                                (𝓝 q.val) := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hg hgr
  let _ : Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 1 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (T.data r).chart).symm.trans hr⟩
  obtain ⟨δ, hδ, hδi, hδd, z₀, v, β₀, hβ₀, hcross₀, htrans₀, hβbasin, hsingle, hendpoints⟩ :=
    T.exists_transverse_middle_belt_loop hg hdim m q hm hq u hbranches hqa hgr hnewlow
  obtain ⟨α, hα, -, -, hrange, P, hP, hplace, hplacement⟩ :=
    exists_new_attaching_circle_placement S T hf hg e hdim hfr hgr heq hhigh hlow r har hgap δ hδ
      hδi hδd
  obtain ⟨β, hβ, hcross, htrans, hPβ⟩ :=
    exists_transverse_sheet_of_circle_placement P (hα.mdifferentiableAt (by simp)) hβ₀ hplace
      hcross₀ htrans₀
  refine
    ⟨P, hP, unit_level_count_of_circle_placement T.flow P.toEquiv δ z₀ hplacement hsingle, α, z₀,
      β, v, hα, hβ, hcross, htrans, ?_, ?_, ?_⟩
  · intro z
    exact (hrange (α z)).mp ⟨z, rfl⟩
  · filter_upwards [hβbasin] with w hw
    rw [hPβ w]
    exact hw
  · intro x hx
    obtain ⟨z, hz⟩ := (hplacement x).mp hx
    rw [← hz]
    exact hendpoints z

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.cancel_one_two_pair_at_preserved_middle_cut {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f g : M → ℝ} (S : AdaptedWindows E f) (T : AdaptedWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : ManifoldMorse.IsMorse E g) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (u : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 m.val))
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < g r)
    (hgap : ∀ z : ManifoldMorse.criticalPoints E g, g z < g r → g z < a)
    (hnewlow :
      ∀ z : ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (ManifoldMorse.criticalPoints E h) ∧
            (ManifoldMorse.criticalPoints E h).ncard + 2 =
                (ManifoldMorse.criticalPoints E g).ncard ∧
              (∀ w,
                  w ∈ ManifoldMorse.criticalPoints E h ↔
                    w ∈ ManifoldMorse.criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
                ∀ w ∈ ManifoldMorse.criticalPoints E h,
                  nativeMorseIndex E h w = nativeMorseIndex E g w := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hg hgr
  have hnegq : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  have hsplit := (T.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  obtain ⟨P, hP, hcount, α, z₀, β, v, hα, hβ, hcross, htrans, hαbasin, hβbasin, hends⟩ :=
    exists_handle_trade_transverse_level_data S T hf hg e hdim hfr hgr heq hhigh hlow m q r hm hq
      hr u hbranches hqa har hgap hnewlow
  have hqcut : g q < a := (T.toSurgeryWindows.value_lt_upper q).trans_le hqa
  obtain
    ⟨V, G, hV, hG, hzero, hdesc, hgerms, hbackr, hforwardq, hunique, hback, hforward, htubes⟩ :=
    T.realize_unit_transverse_level_isotopy hg r q har hqcut hgr P hP hcount α β z₀ v
      (hα.mdifferentiableAt (by simp)) hβ hcross htrans (Filter.Eventually.of_forall hαbasin)
      hβbasin
  have hendsG (x : { y : M // g y = a })
    (hx : Filter.Tendsto (fun t => G t x.val) Filter.atBot (𝓝 r.val)) :
    Filter.Tendsto (fun t => G t x.val) Filter.atTop (𝓝 q.val) ∨
      Filter.Tendsto (fun t => G t x.val) Filter.atTop (𝓝 m.val) := by
    have hh := hends x ((hback x r.val).mp hx)
    exact (hh.imp ((hforward x m.val).mpr) ((hforward x q.val).mpr)).symm
  have hnoconnection :=
    no_other_connections_of_two_level_endpoints G hg.continuous T.distinct r q m har hgap
      (FlowConstruction.antitone_flow_height hg G hG hzero hdesc) hendsG
  have hmodels :
    ∀ x ∈ ManifoldMorse.criticalPoints E g,
      ∃ c : ManifoldMorse.SignedMorseChart (E := E) g x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    refine ⟨(T.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, T.critical_model_germ ⟨x, hx⟩] with y hy hyt
    exact hy.trans hyt
  have hmq : g m < g q :=
    (T.forward_limit_below_regular_level hg (T.data q).lower_regular
          ((T.data q).surgery.attachingSphere u) (hbranches u)).trans
      (T.toSurgeryWindows.lower_lt_value q)
  obtain ⟨hC, hD, hC0, hD0, hCb, hDb, htransM⟩ := htubes
  exact
    cancel_transverse_pair_after_flow_preserving_descent hg hmg T.distinct (m := 5) (by omega) hV
      G hG hzero hdesc hmodels q m r hmq (hqcut.trans har) (by omega) hnoconnection hforwardq
      hbackr hunique hC hD hC0 hD0 hCb hDb htransM

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.cancel_one_two_pair_at_unchanged_cut_of_unique_minimum {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f g : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : ManifoldMorse.IsMorse E g)
    (hinjg : Set.InjOn g (ManifoldMorse.criticalPoints E g)) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (hminimum : ∀ z : ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = m)
    (hqa : g q < a) (har : a < g r)
    (hgap : ∀ z : ManifoldMorse.criticalPoints E g, g z < g r → g z < a)
    (hnewlow :
      ∀ z : ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (ManifoldMorse.criticalPoints E h) ∧
            (ManifoldMorse.criticalPoints E h).ncard + 2 =
                (ManifoldMorse.criticalPoints E g).ncard ∧
              (∀ w,
                  w ∈ ManifoldMorse.criticalPoints E h ↔
                    w ∈ ManifoldMorse.criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
                ∀ w ∈ ManifoldMorse.criticalPoints E h,
                  nativeMorseIndex E h w = nativeMorseIndex E g w := by
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨U, -, -, hbranchesU, -⟩ :=
    T₀.realize_unique_minimum_one_handle_branches hg hmg m q hq hminimum
  obtain ⟨T, -, hflow, -, hbelow, -⟩ := U.exists_same_flow_windows_avoiding_level hg hmg hgr
  have hbranches := U.attaching_branches_of_same_flow T hg m q hflow hbranchesU
  have hneg : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  obtain ⟨u, v, huv⟩ := exists_distinct_unitSphere_points_of_finrank_one hneg
  exact
    cancel_one_two_pair_at_preserved_middle_cut S T hf hg hmg e hdim hfr hgr heq hhigh hlow m q r
      hm hq hr u hbranches (hbelow q hqa).le har hgap hnewlow

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_one_to_three_handle_trade {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) (m q : ManifoldMorse.criticalPoints E f)
    (hm0 : nativeMorseIndex E f m = 0) (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m)
    {a l u : ℝ} (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ z : ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2)
    (hqa : f q < a) (hal : a < l)
    (hband : ∀ y, f y ∈ Set.Ioo a u → y ∉ ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (ManifoldMorse.criticalPoints E h) ∧
            (ManifoldMorse.criticalPoints E h).ncard =
                (ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  let U : Set M := f ⁻¹' Set.Ioo l u
  have hU : IsOpen U := isOpen_Ioo.preimage hf.continuous
  have hbirthband : ∀ y, f y ∈ Set.Ioo l u → y ∉ ManifoldMorse.criticalPoints E f :=
    fun y hy => hband y ⟨hal.trans hy.1, hy.2⟩
  obtain
    ⟨g, b₂, b₃, hg, hmg, hinjg, -, -, hi₂, hi₃, h₂₃, hv₂, hv₃, hcountbirth, hcrit, hexterior,
      hkeep, hcount₂, hcount₃, hcountOther⟩ :=
    exists_excellent_indexed_morse_birth hf hm S.distinct hbirthband hx (k := 2) (by omega) hU hx
  have hcrit' (z : M) (hz : z ∈ ManifoldMorse.criticalPoints E g) :
    z ∈ ManifoldMorse.criticalPoints E f ∨ z = b₂ ∨ z = b₃ := (hcrit z).mp hz
  have hab₂ : a < g b₂ := hal.trans hv₂.1
  have hab₃ : a < g b₃ := hal.trans hv₃.1
  obtain ⟨heq, -⟩ :=
    birth_preserves_lower_levels hf.continuous hg
      (show U ⊆ {y : M | l < f y} from fun _ hy => hy.1) hexterior hkeep hcrit' hv₂.1.le hv₃.1.le
      hal
  have hgr := regular_level_of_retained_critical_germs hreg hcrit' hkeep hab₂ hab₃
  have hgap := birth_first_new_value_gap hcrit' hkeep hreg hband hv₂.2 h₂₃
  have hnewlow := birth_preserves_lower_index_bound hcrit' hkeep hab₂ hab₃ hlow
  let mg : ManifoldMorse.criticalPoints E g :=
    ⟨m.val, (hcrit m.val).mpr (Or.inl m.property)⟩
  let qg : ManifoldMorse.criticalPoints E g :=
    ⟨q.val, (hcrit q.val).mpr (Or.inl q.property)⟩
  let rg : ManifoldMorse.criticalPoints E g := ⟨b₂, (hcrit b₂).mpr (Or.inr (Or.inl rfl))⟩
  have hmg0 : nativeMorseIndex E g mg = 0 :=
    (nativeMorseIndex_congr_germ (hkeep m.val m.property)).trans hm0
  have hqg1 : nativeMorseIndex E g qg = 1 :=
    (nativeMorseIndex_congr_germ (hkeep q.val q.property)).trans hq1
  have hminG :
    ∀ z : ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = mg := by
    intro z hz
    apply Subtype.ext
    exact
      birth_preserves_unique_index_zero m hcrit' hkeep (by rw [hi₂]; omega) (by rw [hi₃]; omega)
        hminimum z.val z.property hz
  have hqga : g qg < a := by
    change g q.val < a
    rw [(hkeep q.val q.property).self_of_nhds]
    exact hqa
  obtain ⟨h, hh, hmh, hinjh, hcountcancel, hcritcancel, hindices⟩ :=
    cancel_one_two_pair_at_unchanged_cut_of_unique_minimum S hf hg hmg hinjg e hdim hreg hgr heq
      hhigh (fun z hz => (hlow z hz).trans (by omega)) mg qg rg hmg0 hqg1 hi₂ hminG hqga hab₂ hgap
      hnewlow
  have hq₂ : qg.val ≠ rg.val := fun he => (hqga.trans hab₂).ne (congrArg g he)
  obtain ⟨hremove₁, hremove₂, hremoveOther⟩ :=
    nativeMorseCount_adjacent_removed_of_index_eq
      (ManifoldMorse.finite_criticalPoints hg hmg) qg.property rg.property hq₂ hcritcancel
      hindices hqg1 hi₂
  have htotal :
    (ManifoldMorse.criticalPoints E h).ncard =
      (ManifoldMorse.criticalPoints E f).ncard :=
    Nat.add_right_cancel (hcountcancel.trans hcountbirth)
  have hcount₁ : nativeMorseCount E g 1 = nativeMorseCount E f 1 :=
    hcountOther 1 (by omega) (by omega)
  have hcountₕ₂ : nativeMorseCount E h 2 = nativeMorseCount E f 2 :=
    Nat.add_right_cancel (hremove₂.trans hcount₂)
  refine
    ⟨h, hh, hmh, hinjh, htotal, hremove₁.trans hcount₁,
      (hremoveOther 3 (by omega) (by omega)).trans hcount₃, ?_⟩
  intro j hj1 hj3
  by_cases hj2 : j = 2
  · subst j
    exact hcountₕ₂
  · exact (hremoveOther j hj1 hj2).trans (hcountOther j hj2 hj3)

theorem MorseCancellation.exists_one_to_three_handle_trade_at_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) (m q : ManifoldMorse.criticalPoints E f)
    (hm0 : nativeMorseIndex E f m = 0) (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ z : ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2)
    (hqa : f q < a) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (ManifoldMorse.criticalPoints E h) ∧
            (ManifoldMorse.criticalPoints E h).ncard =
                (ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  have hneg : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq1
  have hsplit := (S.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  obtain ⟨v, t, ht⟩ := S.exists_belt_point_reaching_level hf q 4 hqa hlow (by omega)
  let z := S.flow t ((S.data q).surgery.beltSphere v).val
  have hz : f z = a := ht
  obtain ⟨l₀, u, hl₀, hau, hband⟩ := S.regular_interval_around_level hreg
  have hc : Continuous (fun s : ℝ => f (S.flow s z)) :=
    hf.continuous.comp (S.flow.continuous continuous_id continuous_const)
  have h0 : (fun s : ℝ => f (S.flow s z)) 0 ∈ Set.Iio u := by
    simpa only [Flow.map_zero_apply, hz, Set.mem_Iio] using hau
  obtain ⟨ε, hε, hεball⟩ :=
    Metric.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds h0))
  let x := S.flow (-ε / 2) z
  have hxu : f x < u :=
    hεball
      (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        constructor <;> linarith)
  have hax : a < f x := by
    have hh :=
      FlowConstruction.strictAnti_flow_height hf (S.smooth.of_le (by simp)) S.flow
        S.integral S.zero S.descent (hreg z hz) (show -ε / 2 < 0 by linarith)
    simpa only [Flow.map_zero_apply, hz] using hh
  exact
    exists_one_to_three_handle_trade S hf hm e hdim m q hm0 hq1 hminimum hreg hhigh hlow hqa
      (show a < (a + f x) / 2 by linarith) (fun y hy => hband y ⟨hl₀.le.trans hy.1.le, hy.2.le⟩)
      (show f x ∈ Set.Ioo ((a + f x) / 2) u from ⟨by linarith, hxu⟩)

theorem MorseCancellation.exists_one_to_three_handle_trade_of_ordered_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [PathConnectedSpace M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (m q : ManifoldMorse.criticalPoints E f) (hm0 : nativeMorseIndex E f m = 0)
    (hq1 : nativeMorseIndex E f q = 1)
    (hminimum :
      ∀ z : ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (ManifoldMorse.criticalPoints E h) ∧
            (ManifoldMorse.criticalPoints E h).ncard =
                (ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  obtain ⟨a, hreg, hqa, hhigh, hlow⟩ :=
    S.exists_ordered_index_cut horder q (show nativeMorseIndex E f q ≤ 2 by omega)
  exact
    exists_one_to_three_handle_trade_at_cut S hf hm e hdim m q hm0 hq1 hminimum hreg hhigh hlow
      hqa

theorem MorseCancellation.outer_index_minimal_index_one_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          ManifoldMorse.IsMorse E g →
            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
              (ManifoldMorse.criticalPoints E g).ncard =
                  (ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 := by
  by_contra hnot
  have hfinite :
    {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  obtain ⟨q, hqcrit, hq1⟩ := (Set.ncard_pos hfinite).mp (Nat.pos_of_ne_zero hnot)
  change
    {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0}.ncard =
      1 at hzero
  obtain ⟨m, hmset⟩ := Set.ncard_eq_one.mp hzero
  have hmem :
    m ∈ {z : M | z ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} := by
    rw [hmset]
    exact Set.mem_singleton m
  let mc : ManifoldMorse.criticalPoints E f := ⟨m, hmem.1⟩
  have hminimum (z : ManifoldMorse.criticalPoints E f) (hz : nativeMorseIndex E f z = 0) :
    z = mc := by
    apply Subtype.ext
    have hzmem :
      z.val ∈ {x : M | x ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = 0} :=
      ⟨z.property, hz⟩
    rwa [hmset, Set.mem_singleton_iff] at hzmem
  obtain ⟨g, hg, hmg, hinjg, hcount, hcount1, -, hother⟩ :=
    exists_one_to_three_handle_trade_of_ordered_indices S hf hm e hdim horder mc ⟨q, hqcrit⟩
      hmem.2 hq1 hminimum
  have hcost := hsecondary g hg hmg hinjg hcount
  have hcount5 := hother 5 (by omega) (by omega)
  omega

theorem MorseCancellation.outer_index_minimal_outer_counts_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          ManifoldMorse.IsMorse E g →
            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
              (ManifoldMorse.criticalPoints E g).ncard =
                  (ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 ∧ nativeMorseCount E f 5 = 0 := by
  refine ⟨outer_index_minimal_index_one_count_zero S hf hm e hdim horder hzero hsecondary, ?_⟩
  obtain ⟨T⟩ :=
    nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
      (distinct_critical_values_neg S.distinct)
  have horderN :
    ∀ p q : ManifoldMorse.criticalPoints E (fun x => -f x),
      -f p < -f q → nativeMorseIndex E (fun x => -f x) p ≤ nativeMorseIndex E (fun x => -f x) q :=
    by
    intro p q hpq
    let pf : ManifoldMorse.criticalPoints E f :=
      ⟨p.val, by simpa only [ManifoldMorse.criticalPoints_neg] using p.property⟩
    let qf : ManifoldMorse.criticalPoints E f :=
      ⟨q.val, by simpa only [ManifoldMorse.criticalPoints_neg] using q.property⟩
    have hrev := horder qf pf (neg_lt_neg_iff.mp hpq)
    have hp := nativeMorseIndex_neg_add (S.data pf).chart
    have hq := nativeMorseIndex_neg_add (S.data qf).chart
    change nativeMorseIndex E f q.val ≤ nativeMorseIndex E f p.val at hrev
    change nativeMorseIndex E (fun x => -f x) p.val + nativeMorseIndex E f p.val = _ at hp
    change nativeMorseIndex E (fun x => -f x) q.val + nativeMorseIndex E f q.val = _ at hq
    omega
  have hzeroN : nativeMorseCount E (fun x => -f x) 0 = 1 := by
    have hc := nativeMorseCount_neg hf hm (k := 6) (by omega)
    simpa only [hdim, Nat.sub_self, hsix] using hc
  have honeN :=
    outer_index_minimal_index_one_count_zero T hf.neg (isMorse_neg hm) e hdim horderN hzeroN
      (outer_index_minimality_neg hf hm hdim hsecondary)
  have hc := nativeMorseCount_neg hf hm (k := 5) (by omega)
  simpa only [hdim, Nat.reduceSub, honeN] using hc.symm

theorem MorseCancellation.exists_minimal_ordered_morse_system_without_outer_indices (E : Type)
    (M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q : ManifoldMorse.criticalPoints E f,
                f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f 6 = 1 ∧
                  nativeMorseCount E f 1 = 0 ∧
                    nativeMorseCount E f 5 = 0 ∧
                      ∀ g : M → ℝ,
                        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                          ManifoldMorse.IsMorse E g →
                            Set.InjOn g (ManifoldMorse.criticalPoints E g) →
                              (ManifoldMorse.criticalPoints E f).ncard ≤
                                (ManifoldMorse.criticalPoints E g).ncard := by
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hminimal, hsecondary⟩ :=
    exists_outer_index_minimal_ordered_morse_system E M
  rw [hdim] at hsix
  obtain ⟨hone, hfive⟩ :=
    outer_index_minimal_outer_counts_zero S hf hm e hdim horder hzero hsix hsecondary
  exact ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ SixSphere) (h : 0 < S.count) (k : ℕ)
    (hk : 0 < k) (hk5 : k < 5) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.last h) } k) := by
  let d := S.data (S.last h)
  have hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 5 + 1 :=
    (S.last_index_dimension hf h).trans hdim
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 5 + 1) := ⟨hindex⟩
  let : Subsingleton (SingularMayerVietoris.SingularHomology M k) :=
    homotopySixSphere_homology_subsingleton hM k hk.ne' (by omega)
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ f (S.last h) + d.radius ^ 2 } k) :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (S.lastUpperHomeomorph hf h)
        k).injective.subsingleton
  let : Subsingleton (SingularMayerVietoris.SingularHomology (Hemisphere.Sphere 5) k) :=
    SphereHomology.unitSphere_homology_subsingleton 4 k hk.ne' (by omega)
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k) :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
            5).symm.toHomeomorph
        k).injective.subsingleton
  exact d.lowerHomology_subsingleton_of_upper_and_sphere hf.continuous k hk.ne'

theorem ManifoldMorse.SurgeryWindows.upper_homology_subsingleton_of_later_indices
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ SixSphere) (j : Fin S.count)
    (hj : j.val + 1 < S.count) (k : ℕ) (hk : 0 < k) (hk5 : k < 5)
    (hindex :
      ∀ i : Fin S.count,
        j.val < i.val →
          i.val + 1 < S.count →
            2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ k + 1) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point j) } k) := by
  have hcount : 0 < S.count := by omega
  let P : ℕ → Prop := fun i =>
    ∀ hi : i < S.count,
      Subsingleton
        (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point ⟨i, hi⟩) } k)
  have hlow : P (j.val + 1) := by
    apply Nat.decreasingInduction' (P := P) (m := j.val + 1) (n := S.count - 1)
    · intro i hi hji ih hi'
      have hs : i + 1 < S.count := by omega
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨i + 1, hs⟩) - (S.data (S.point ⟨i + 1, hs⟩)).radius ^ 2 }
            k) :=
        ih hs
      obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf ⟨i, hi'⟩ ⟨i + 1, hs⟩ rfl
      let H :=
        (S.data (S.point ⟨i, hi'⟩)).bandSublevelHomeomorph (S.data (S.point ⟨i + 1, hs⟩))
          T.toHomeomorph hT
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨i, hi'⟩) + (S.data (S.point ⟨i, hi'⟩)).radius ^ 2 } k) :=
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv H k).injective.subsingleton
      obtain ⟨hlo, hne⟩ := hindex ⟨i, hi'⟩ (by change j.val < i; omega) hs
      exact
        (S.data (S.point ⟨i, hi'⟩)).lowerHomology_subsingleton_of_upper_and_index hf.continuous k
          hk.ne' hlo hne
    · omega
    · intro hi
      exact S.lastLower_homology_subsingleton hf hdim hM hcount k hk hk5
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M //
          f x ≤ f (S.point ⟨j.val + 1, hj⟩) - (S.data (S.point ⟨j.val + 1, hj⟩)).radius ^ 2 }
        k) :=
    hlow hj
  obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf j ⟨j.val + 1, hj⟩ rfl
  let H :=
    (S.data (S.point j)).bandSublevelHomeomorph (S.data (S.point ⟨j.val + 1, hj⟩)) T.toHomeomorph
      hT
  exact (PeriodTorusHigherHomology.homeomorphHomologyEquiv H k).injective.subsingleton

theorem ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_homotopySphere {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hj : r + c + 1 < S.count)
    (hafter :
      ∀ i : Fin S.count,
        r + c < i.val →
          i.val + 1 < S.count →
            2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ 3) :
    Function.Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩) }
        2) :=
    S.upper_homology_subsingleton_of_later_indices hf hdim hM ⟨r + c, hc⟩ hj 2 (by norm_num)
      (by norm_num) hafter
  exact (S.middlePresentation hf r htwo c hc hthree).matrix_surjective_of_subsingleton

theorem ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_complete_blocks {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) :
    Function.Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  apply S.middleMatrix_surjective_of_homotopySphere hf hdim hM r c htwo hc hthree (by omega)
  intro i hi hi'
  omega

end
