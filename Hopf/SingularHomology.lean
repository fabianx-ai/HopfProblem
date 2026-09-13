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
Original source lines 31128--62391; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.DifferentialTopology
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
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Morse.Rearrangement
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.Topology.Homotopy.CellAttachment
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.Topology.Homotopy.LoopSubdivision
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.Geometry.Manifold.Whitney.BigonModel
import Lib.Geometry.Manifold.Morse.MinimalSystem
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Morse.ConnectionCancellation
import Lib.Topology.MappingTorus.Wang

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973
theorem MorseCancellation.exists_native_open_curve_with_germ {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] (S : TopologicalSpace.Opens N) {a : ℝ → N} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ∈ S) :
    ∃ g : C(ℝ, S), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧ (Subtype.val ∘ g) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → S := fun t => if h : a t ∈ S then ⟨a t, h⟩ else ⟨a t₀, ha0⟩
  let V := U ∩ a ⁻¹' (S : Set N)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU S.isOpen
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hsS : a s ∈ S := hs.2
    simp only [Function.comp_apply, A, dif_pos hsS]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ A V := by
    intro t ht
    have hvalAt := (ha.contMDiffAt (hU.mem_nhds ht.1)).congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff S A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨g, hg, heq⟩ := exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨g, hg, ?_⟩
  filter_upwards [heq, hval htV] with t ht hta
  exact (congrArg Subtype.val ht).trans hta

theorem MorseCancellation.exists_embedded_native_open_arc_with_local_germs {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] [FiniteDimensional ℝ G] [J.Boundaryless]
    [IsManifold J ∞ N] [T2Space N] (S : TopologicalSpace.Opens N) {a b : ℝ → N} {U V : Set ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b V) (hU : IsOpen U)
    (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V) (ha0 : a 0 ∈ S) (hb1 : b 1 ∈ S)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1))
    (γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, S),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        ((Subtype.val ∘ g) =ᶠ[𝓝 (0 : ℝ)] a) ∧
          ((Subtype.val ∘ g) =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
              ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨a', ha', heqa⟩ := exists_native_open_curve_with_germ S ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_native_open_curve_with_germ S hb hV h1V hb1
  have hstart : a' 0 = (⟨a 0, ha0⟩ : S) := Subtype.ext heqa.eq_of_nhds
  have hend : b' 1 = (⟨b 1, hb1⟩ : S) := Subtype.ext heqb.eq_of_nhds
  have hia' : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a' 0) := by
    have hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (Subtype.val ∘ a') 0) := by
      rw [heqa.mfderiv_eq]
      exact hia
    rw [mfderiv_comp 0
        ((contMDiff_subtype_val (I := J) (U := S) (n := ∞)).mdifferentiableAt (by simp))
        (ha'.mdifferentiableAt (by simp))] at hi
    intro x y hxy
    exact hi (congrArg (mfderiv J J (Subtype.val : S → N) (a' 0)) hxy)
  have hib' : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b' 1) := by
    have hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (Subtype.val ∘ b') 1) := by
      rw [heqb.mfderiv_eq]
      exact hib
    rw [mfderiv_comp 1
        ((contMDiff_subtype_val (I := J) (U := S) (n := ∞)).mdifferentiableAt (by simp))
        (hb'.mdifferentiableAt (by simp))] at hi
    intro x y hxy
    exact hi (congrArg (mfderiv J J (Subtype.val : S → N) (b' 1)) hxy)
  have hxy' : a' 0 ≠ b' 1 := by
    intro h
    exact hxy (heqa.eq_of_nhds.symm.trans ((congrArg Subtype.val h).trans heqb.eq_of_nhds))
  obtain ⟨g, hg, hga, hgb, hemb, hi, -⟩ :=
    exists_embedded_arc_with_endpoint_germs a' b' ha' hb' hia' hib' (γ.cast hstart hend)
      hxy' hdim (S := ∅) Set.finite_empty
  refine ⟨g, hg, ?_, ?_, hemb, hi⟩
  · filter_upwards [hga, heqa] with t hta hta'
    exact (congrArg Subtype.val hta).trans hta'
  · filter_upwards [hgb, heqb] with t htb htb'
    exact (congrArg Subtype.val htb).trans htb'

theorem MorseCancellation.injective_mfderiv_curve_translate {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {α : ℝ → N} {s c : ℝ} (hα : MDifferentiableAt 𝓘(ℝ, ℝ) J α (s + c))
    (hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α (s + c))) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => α (t + c)) s) := by
  have ht : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s :=
    (contMDiff_id.add (contMDiff_const (c := c)) :
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => t + c)).mdifferentiableAt
      (by simp)
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s = ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun t : ℝ => id t + c) s = _
    rw [fderiv_add_const, fderiv_id]
  change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (α ∘ (fun t : ℝ => t + c)) s)
  rw [mfderiv_comp s hα ht]
  intro x y hxy
  apply hi
  have hdx : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s x = x :=
    congrArg (fun L : ℝ →L[ℝ] ℝ => L x) hd
  have hdy : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s y = y :=
    congrArg (fun L : ℝ →L[ℝ] ℝ => L y) hd
  change
    mfderiv 𝓘(ℝ, ℝ) J α (s + c) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s x) =
      mfderiv 𝓘(ℝ, ℝ) J α (s + c) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s y) at hxy
  rw [hdx, hdy] at hxy
  exact hxy

theorem MorseCancellation.exists_embedded_return_arc_inside_open {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N] [T2Space N]
    (S : TopologicalSpace.Opens N) {α : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hinj : Set.InjOn α (Set.Icc (-R) R))
    (hderiv : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s)) (hplus : α r ∈ S)
    (hminus : α (-r) ∈ S) (γ : Path (⟨α r, hplus⟩ : S) (⟨α (-r), hminus⟩ : S))
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, S),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        ((Subtype.val ∘ g) =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) ∧
          ((Subtype.val ∘ g) =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
              ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let a : ℝ → N := fun t => α (t + r)
  let b : ℝ → N := fun t => α (t + (-1 - r))
  let U : Set ℝ := (fun t : ℝ => t + r) ⁻¹' Set.Ioo (-R) R
  let V : Set ℝ := (fun t : ℝ => t + (-1 - r)) ⁻¹' Set.Ioo (-R) R
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_id.add continuous_const)
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_id.add continuous_const)
  have hp : r ∈ Set.Ioo (-R) R := ⟨by linarith, hrR⟩
  have hm : -r ∈ Set.Ioo (-R) R := ⟨by linarith, by linarith⟩
  have h0U : (0 : ℝ) ∈ U := by simpa only [U, Set.mem_preimage, zero_add] using hp
  have h1V : (1 : ℝ) ∈ V := by
    change 1 + (-1 - r) ∈ Set.Ioo (-R) R
    simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using hm
  have ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U :=
    hα.comp (contMDiff_id.add contMDiff_const).contMDiffOn (fun _ ht => ht)
  have hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b V :=
    hα.comp (contMDiff_id.add contMDiff_const).contMDiffOn (fun _ ht => ht)
  have ha0 : a 0 = α r := by dsimp [a]; rw [zero_add]
  have hb1 : b 1 = α (-r) := by dsimp [b]; congr 1; ring
  have hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0) := by
    apply injective_mfderiv_curve_translate
    · simpa only [zero_add] using
        (hα.contMDiffAt (Ioo_mem_nhds hp.1 hp.2)).mdifferentiableAt (by simp)
    · exact (zero_add r).symm ▸ hderiv r hp
  have hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1) := by
    apply injective_mfderiv_curve_translate
    · simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using
        (hα.contMDiffAt (Ioo_mem_nhds hm.1 hm.2)).mdifferentiableAt (by simp)
    · exact (show (1 : ℝ) + (-1 - r) = -r by ring).symm ▸ hderiv (-r) hm
  have haS : a 0 ∈ S := ha0.symm ▸ hplus
  have hbS : b 1 ∈ S := hb1.symm ▸ hminus
  have hpath : Path (⟨a 0, haS⟩ : S) (⟨b 1, hbS⟩ : S) :=
    γ.cast (Subtype.ext ha0) (Subtype.ext hb1)
  have hxy : a 0 ≠ b 1 := by
    rw [ha0, hb1]
    intro hh
    have heq := hinj ⟨hp.1.le, hp.2.le⟩ ⟨hm.1.le, hm.2.le⟩ hh
    linarith
  exact
    exists_embedded_native_open_arc_with_local_germs S ha hb hU hV h0U h1V haS hbS hia hib hpath
      hxy hdim

theorem MorseCancellation.exists_clean_return_endpoint_neighborhood {N : Type*} [TopologicalSpace N]
    {α β : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R) (hinj : Set.InjOn α (Set.Icc (-R) R))
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    ∃ C : Set ℝ,
      IsClosed C ∧
        ({0, 1} : Set ℝ) ⊆ interior C ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1 ∩ C, t ∉ ({0, 1} : Set ℝ) → β t ∉ α '' Set.Icc (-r) r := by
  have hp : r ∈ Set.Ioo (-R) R := ⟨by linarith, hrR⟩
  have hm : -r ∈ Set.Ioo (-R) R := ⟨by linarith, by linarith⟩
  have hnear0 : ∀ᶠ t in 𝓝 (0 : ℝ), β t = α (t + r) ∧ t + r ∈ Set.Ioo (-R) R := by
    have hn : ∀ᶠ t in 𝓝 (0 : ℝ), t + r ∈ Set.Ioo (-R) R :=
      ((continuous_id.add continuous_const).continuousAt.tendsto
        (show Set.Ioo (-R) R ∈ 𝓝 ((0 : ℝ) + r) by
          simpa only [zero_add] using Ioo_mem_nhds hp.1 hp.2))
    exact h0.and hn
  have hnear1 : ∀ᶠ t in 𝓝 (1 : ℝ), β t = α (t + (-1 - r)) ∧ t + (-1 - r) ∈ Set.Ioo (-R) R := by
    have hn : ∀ᶠ t in 𝓝 (1 : ℝ), t + (-1 - r) ∈ Set.Ioo (-R) R :=
      ((continuous_id.add continuous_const).continuousAt.tendsto
        (show Set.Ioo (-R) R ∈ 𝓝 ((1 : ℝ) + (-1 - r)) by
          simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using Ioo_mem_nhds hm.1 hm.2))
    exact h1.and hn
  obtain ⟨δ₀, hδ₀, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear0
  obtain ⟨δ₁, hδ₁, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear1
  let C : Set ℝ := Metric.closedBall 0 δ₀ ∪ Metric.closedBall 1 δ₁
  have h0C : C ∈ 𝓝 (0 : ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hδ₀)
      (fun _ ht => Or.inl (Metric.ball_subset_closedBall ht))
  have h1C : C ∈ 𝓝 (1 : ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 1 hδ₁)
      (fun _ ht => Or.inr (Metric.ball_subset_closedBall ht))
  refine ⟨C, Metric.isClosed_closedBall.union Metric.isClosed_closedBall, ?_, ?_⟩
  · intro t ht
    rcases ht with rfl | ht
    · exact mem_interior_iff_mem_nhds.mpr h0C
    · have ht1 : t = 1 := ht
      subst t
      exact mem_interior_iff_mem_nhds.mpr h1C
  · intro t ht htB
    rintro ⟨s, hs, heq⟩
    have hsR : s ∈ Set.Icc (-R) R := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rcases ht.2 with ht0 | ht1
    · have hg := hball0 ht0
      have hts := hinj ⟨hg.2.1.le, hg.2.2.le⟩ hsR (hg.1.symm.trans heq.symm)
      have htne : t ≠ 0 := fun h => htB (Or.inl h)
      have htpos : 0 < t := lt_of_le_of_ne ht.1.1 htne.symm
      linarith [hs.2]
    · have hg := hball1 ht1
      have hts := hinj ⟨hg.2.1.le, hg.2.2.le⟩ hsR (hg.1.symm.trans heq.symm)
      have htne : t ≠ 1 := fun h => htB (Or.inr h)
      have htlt : t < 1 := lt_of_le_of_ne ht.1.2 htne
      linarith [hs.1]

theorem ManifoldImmersion.exists_relative_embedded_avoidance_in_open_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [SecondCountableTopology Y]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (U : TopologicalSpace.Opens N) (f : C(E, U)) (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hclosed : IsClosed (Set.range g))
    (hsourceDim : Module.finrank ℝ E = 2) (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → (f x : N) ∉ Set.range g) :
    ∃ f' : C(E, U),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, (f' x : N) ∉ Set.range g := by
  have hclean' : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range (OpenObstacle.restrict g U) := by
    intro x hx hxB hmem
    exact hclean x hx hxB ((OpenObstacle.mem_range_restrict_iff g U (f x)).mp hmem)
  obtain ⟨f', hf', hhom, hemb, hderiv', havoid⟩ :=
    exists_relative_embedded_avoidance_of_clean_neighborhood_of_isClosed_range f
      (OpenObstacle.restrict g U) hf (OpenObstacle.contMDiff_restrict g U hg)
      (OpenObstacle.isClosed_range_restrict g U hclosed) hsourceDim hdim hobstacle hK hC hBC
      hinj hderiv hclean'
  refine ⟨f', hf', hhom, hemb, hderiv', ?_⟩
  intro x hx hmem
  exact havoid x hx ((OpenObstacle.mem_range_restrict_iff g U (f' x)).mpr hmem)

theorem ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood_in_open
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [SecondCountableTopology Y]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (U : TopologicalSpace.Opens N) (f : C(E, U)) (g : C(Y, N)) (A : Set Y)
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g) (hclosed : IsClosed (g '' A))
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → (f x : N) ∉ g '' A) {O : Set U} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, U),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              Set.MapsTo f' K O ∧ ∀ x ∈ K \ B, (f' x : N) ∉ g '' A := by
  let A' : Set (OpenObstacle.source g U) := Subtype.val ⁻¹' A
  have hclean' : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ OpenObstacle.restrict g U '' A' := by
    intro x hx hxB hmem
    rw [OpenObstacle.image_restrict] at hmem
    exact hclean x hx hxB hmem
  obtain ⟨f', hf', hhom, hemb, hd, hmaps', havoid⟩ :=
    exists_embedded_image_avoidance_relative_neighborhood f (OpenObstacle.restrict g U) A'
      hf (OpenObstacle.contMDiff_restrict g U hg)
      (OpenObstacle.isClosed_image_restrict g U A hclosed) hself hobstacle hK hC hBC hinj
      hderiv hclean' hO hmaps
  refine ⟨f', hf', hhom, hemb, hd, hmaps', ?_⟩
  intro x hx hmem
  apply havoid x hx
  rw [OpenObstacle.image_restrict]
  exact hmem

theorem ManifoldImmersion.exists_relative_embedded_avoidance_in_open
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] [CompactSpace Y]
    [SecondCountableTopology H'] (U : TopologicalSpace.Opens N) (f : C(E, U)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g) (hsourceDim : Module.finrank ℝ E = 2)
    (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → (f x : N) ∉ Set.range g) :
    ∃ f' : C(E, U),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, (f' x : N) ∉ Set.range g := by
  let : SecondCountableTopology Y := ChartedSpace.secondCountable_of_sigmaCompact H' Y
  exact
    exists_relative_embedded_avoidance_in_open_of_isClosed_range U f g hf hg
      (isCompact_range g.continuous).isClosed hsourceDim hdim hobstacle hK hC hBC hinj hderiv
      hclean

theorem MorseCancellation.exists_disjoint_embedded_return_arc {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (S : TopologicalSpace.Opens N) {α : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hinj : Set.InjOn α (Set.Icc (-R) R))
    (hderiv : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s)) (hplus : α r ∈ S)
    (hminus : α (-r) ∈ S) (γ : Path (⟨α r, hplus⟩ : S) (⟨α (-r), hminus⟩ : S))
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, S),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        ((Subtype.val ∘ g) =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) ∧
          ((Subtype.val ∘ g) =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t)) ∧
                ∀ t ∈ Set.Ioo (0 : ℝ) 1, (g t : N) ∉ α '' Set.Icc (-r) r := by
  obtain ⟨β, hβ, hβ0, hβ1, hemb, hβd⟩ :=
    exists_embedded_return_arc_inside_open S hr hrR hα hinj hderiv hplus hminus γ hdim
  obtain ⟨C, hC, hBC, hclean⟩ := exists_clean_return_endpoint_neighborhood hr hrR hinj hβ0 hβ1
  let Q : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-R) R, isOpen_Ioo⟩
  let q : C(Q, N) :=
    ⟨fun s => α s,
      continuous_iff_continuousAt.mpr
        (fun s =>
          (hα.continuousOn.continuousAt (isOpen_Ioo.mem_nhds s.property)).comp
            continuous_subtype_val.continuousAt)⟩
  have hq : ContMDiff 𝓘(ℝ, ℝ) J ∞ q := by
    intro s
    exact
      (hα.contMDiffAt (isOpen_Ioo.mem_nhds s.property)).comp s
        (contMDiff_subtype_val (n := ∞)).contMDiffAt
  let A : Set Q := {s | (s : ℝ) ∈ Set.Icc (-r) r}
  have hsub : Set.Icc (-r) r ⊆ Set.Ioo (-R) R := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have himage : q '' A = α '' Set.Icc (-r) r := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hsub hs⟩, hs, rfl⟩
  have hclosed : IsClosed (q '' A) := by
    rw [himage]
    exact
      (CompactIccSpace.isCompact_Icc.image_of_continuousOn (hα.continuousOn.mono hsub)).isClosed
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobstacle : Module.finrank ℝ ℝ + Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hβinj : Set.InjOn β (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hclean' : ∀ t ∈ Set.Icc (0 : ℝ) 1 ∩ C, t ∉ ({0, 1} : Set ℝ) → (β t : N) ∉ q '' A := by
    intro t ht htB
    rw [himage]
    exact hclean t ht htB
  obtain ⟨g, hg, hhom, hembg, hdg, -, havoid⟩ :=
    ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood_in_open S β q A
      hβ hq hclosed hself hobstacle CompactIccSpace.isCompact_Icc hC hBC hβinj hβd hclean'
      isOpen_univ (fun _ _ => Set.mem_univ _)
  have h0C : C ∈ 𝓝 (0 : ℝ) := mem_interior_iff_mem_nhds.mp (hBC (Or.inl rfl))
  have h1C : C ∈ 𝓝 (1 : ℝ) := mem_interior_iff_mem_nhds.mp (hBC (Or.inr rfl))
  refine ⟨g, hg, ?_, ?_, hembg, hdg, ?_⟩
  · filter_upwards [h0C, hβ0] with t ht ht0
    exact (congrArg Subtype.val (hhom.fst_eq_snd ht)).symm.trans ht0
  · filter_upwards [h1C, hβ1] with t ht ht1
    exact (congrArg Subtype.val (hhom.fst_eq_snd ht)).symm.trans ht1
  · intro t ht hmem
    have htB : t ∉ ({0, 1} : Set ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ne_of_gt ht.1, ne_of_lt ht.2⟩
    exact havoid t ⟨⟨ht.1.le, ht.2.le⟩, htB⟩ (himage.symm ▸ hmem)

def CircleGluing.periodicExtension {N : Type*} {T : ℝ} (hT : 0 < T) (f : ℝ → N) (t : ℝ) :
    N :=
  f (toIcoMod hT 0 t)

theorem CircleGluing.periodicExtension_periodic {N : Type*} {T : ℝ} (hT : 0 < T)
    (f : ℝ → N) : Function.Periodic (periodicExtension hT f) T := fun t =>
  congrArg f (toIcoMod_add_right hT 0 t)

theorem CircleGluing.periodicExtension_germ_in_fundamental_interval {N : Type*} {T : ℝ}
    (hT : 0 < T) {f : ℝ → N} (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) T) : periodicExtension hT f =ᶠ[𝓝 x] f := by
  by_cases hx0 : x = 0
  · subst x
    filter_upwards [hmatch, Ioo_mem_nhds (neg_lt_zero.mpr hT) hT] with t ht htn
    change f (toIcoMod hT 0 t) = f t
    by_cases ht0 : 0 ≤ t
    · rw [(toIcoMod_eq_self hT).mpr ⟨ht0, by simpa only [zero_add] using htn.2⟩]
    · have hmod : toIcoMod hT 0 t = t + T := by
        apply (toIcoMod_eq_iff hT).mpr
        refine ⟨⟨by linarith [htn.1], by linarith⟩, -1, ?_⟩
        simp
      rw [hmod]
      exact ht
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    filter_upwards [Ioo_mem_nhds hxpos hx.2] with t ht
    change f (toIcoMod hT 0 t) = f t
    rw [(toIcoMod_eq_self hT).mpr ⟨ht.1.le, by simpa only [zero_add] using ht.2⟩]

theorem CircleGluing.periodicExtension_germ {N : Type*} {T : ℝ} (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f) (x : ℝ) :
    ∃ c : ℝ, x + c ∈ Set.Ico (0 : ℝ) T ∧ periodicExtension hT f =ᶠ[𝓝 x] (fun t => f (t + c)) := by
  let n : ℤ := toIcoDiv hT 0 x
  let c : ℝ := -(n • T)
  have hx : x + c = toIcoMod hT 0 x := by
    change x - n • T = toIcoMod hT 0 x
    rfl
  have hxc : x + c ∈ Set.Ico (0 : ℝ) T := by
    rw [hx]
    simpa only [zero_add] using toIcoMod_mem_Ico hT 0 x
  have hg := periodicExtension_germ_in_fundamental_interval hT hmatch hxc
  have ht : Filter.Tendsto (fun t : ℝ => t + c) (𝓝 x) (𝓝 (x + c)) :=
    (continuous_id.add continuous_const).continuousAt
  refine ⟨c, hxc, ?_⟩
  filter_upwards [hg.comp_tendsto ht] with t ht
  have heq : periodicExtension hT f (t + c) = periodicExtension hT f t :=
    congrArg f (toIcoMod_sub_zsmul hT 0 t n)
  exact heq.symm.trans ht

theorem CircleGluing.periodicExtension_contMDiff {N : Type*} {T : ℝ} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f)
    (hf : ∀ t ∈ Set.Ico (0 : ℝ) T, ContMDiffAt 𝓘(ℝ, ℝ) J ∞ f t) :
    ContMDiff 𝓘(ℝ, ℝ) J ∞ (periodicExtension hT f) := by
  intro x
  obtain ⟨c, hc, heq⟩ := periodicExtension_germ hT hmatch x
  exact
    ((hf (x + c) hc).comp x (contMDiff_id.add contMDiff_const).contMDiffAt).congr_of_eventuallyEq
      heq

theorem CircleGluing.periodicExtension_derivative_injective {N : Type*} {T : ℝ}
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f)
    (hf : ∀ t ∈ Set.Ico (0 : ℝ) T, MDifferentiableAt 𝓘(ℝ, ℝ) J f t)
    (hi : ∀ t ∈ Set.Ico (0 : ℝ) T, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (x : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (periodicExtension hT f) x) := by
  obtain ⟨c, hc, heq⟩ := periodicExtension_germ hT hmatch x
  rw [heq.mfderiv_eq]
  exact MorseCancellation.injective_mfderiv_curve_translate (hf (x + c) hc) (hi (x + c) hc)

attribute [local instance 100] Classical.propDecidable in
def CircleGluing.joinedArc {N : Type*} (α β : ℝ → N) (r t : ℝ) : N :=
  if t ≤ 2 * r then α (t + (-r)) else β (t + (-2 * r))

theorem CircleGluing.joinedArc_left {N : Type*} {α β : ℝ → N} {r t : ℝ} (ht : t ≤ 2 * r) :
    joinedArc α β r t = α (t + (-r)) :=
  if_pos ht

theorem CircleGluing.joinedArc_right {N : Type*} {α β : ℝ → N} {r t : ℝ} (ht : 2 * r < t) :
    joinedArc α β r t = β (t + (-2 * r)) :=
  if_neg (not_le.mpr ht)

theorem CircleGluing.joinedArc_left_germ {N : Type*} {α β : ℝ → N} {r t : ℝ}
    (ht : t < 2 * r) : joinedArc α β r =ᶠ[𝓝 t] (fun s => α (s + (-r))) := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact joinedArc_left hs.le

theorem CircleGluing.joinedArc_right_germ {N : Type*} {α β : ℝ → N} {r t : ℝ}
    (ht : 2 * r < t) : joinedArc α β r =ᶠ[𝓝 t] (fun s => β (s + (-2 * r))) := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact joinedArc_right hs

theorem CircleGluing.joinedArc_seam_germ {N : Type*} {α β : ℝ → N} {r : ℝ}
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) :
    joinedArc α β r =ᶠ[𝓝 (2 * r)] (fun s => α (s + (-r))) := by
  have ht : Filter.Tendsto (fun t : ℝ => t + (-2 * r)) (𝓝 (2 * r)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t + (-2 * r)) := continuous_id.add continuous_const
    simpa only [show 2 * r + (-2 * r) = 0 by ring] using hc.continuousAt.tendsto (x := 2 * r)
  filter_upwards [h0.comp_tendsto ht] with t ht
  change β (t + (-2 * r)) = α (t + (-2 * r) + r) at ht
  by_cases htr : t ≤ 2 * r
  · exact joinedArc_left htr
  · rw [joinedArc_right (lt_of_not_ge htr), ht]
    congr 1
    ring

theorem CircleGluing.joinedArc_periodic_germ {N : Type*} {α β : ℝ → N} {r : ℝ} (hr : 0 < r)
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    (fun t => joinedArc α β r (t + (2 * r + 1))) =ᶠ[𝓝 (0 : ℝ)] joinedArc α β r := by
  have ht : Filter.Tendsto (fun t : ℝ => t + 1) (𝓝 (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => t + 1) := continuous_id.add continuous_const
    simpa only [zero_add] using hc.continuousAt.tendsto (x := 0)
  filter_upwards [h1.comp_tendsto ht,
    Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show 0 < 2 * r by linarith)] with t ht htn
  change β (t + 1) = α (t + 1 + (-1 - r)) at ht
  rw [joinedArc_right (by linarith [htn.1]), joinedArc_left htn.2.le,
    show t + (2 * r + 1) + (-2 * r) = t + 1 by ring, ht]
  congr 1
  ring

theorem CircleGluing.joinedArc_injOn {N : Type*} {α β : ℝ → N} {r : ℝ}
    (hα : Set.InjOn α (Set.Icc (-r) r)) (hβ : Set.InjOn β (Set.Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, β t ∉ α '' Set.Icc (-r) r) :
    Set.InjOn (joinedArc α β r) (Set.Ico (0 : ℝ) (2 * r + 1)) := by
  intro x hx y hy hxy
  have hleft {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) (hle : t ≤ 2 * r) :
    t + (-r) ∈ Set.Icc (-r) r := ⟨by linarith [ht.1], by linarith⟩
  have hright {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) (hlt : 2 * r < t) :
    t + (-2 * r) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
  by_cases hxl : x ≤ 2 * r <;> by_cases hyl : y ≤ 2 * r
  · rw [joinedArc_left hxl, joinedArc_left hyl] at hxy
    have heq := hα (hleft hx hxl) (hleft hy hyl) hxy
    linarith
  · rw [joinedArc_left hxl, joinedArc_right (lt_of_not_ge hyl)] at hxy
    exact False.elim (havoid _ (hright hy (lt_of_not_ge hyl)) ⟨_, hleft hx hxl, hxy⟩)
  · rw [joinedArc_right (lt_of_not_ge hxl), joinedArc_left hyl] at hxy
    exact False.elim (havoid _ (hright hx (lt_of_not_ge hxl)) ⟨_, hleft hy hyl, hxy.symm⟩)
  · rw [joinedArc_right (lt_of_not_ge hxl), joinedArc_right (lt_of_not_ge hyl)] at hxy
    have heq :=
      hβ (Set.Ioo_subset_Icc_self (hright hx (lt_of_not_ge hxl)))
        (Set.Ioo_subset_Icc_self (hright hy (lt_of_not_ge hyl))) hxy
    linarith

theorem CircleGluing.joinedArc_contMDiffAt {N : Type*} {G H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {α β : ℝ → N} {R r : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) :
    ContMDiffAt 𝓘(ℝ, ℝ) J ∞ (joinedArc α β r) t := by
  by_cases htle : t ≤ 2 * r
  · have htα : t + (-r) ∈ Set.Ioo (-R) R := ⟨by linarith [ht.1], by linarith⟩
    have hs :=
      (hα.contMDiffAt (Ioo_mem_nhds htα.1 htα.2)).comp t
        (contMDiff_id.add contMDiff_const).contMDiffAt
    apply hs.congr_of_eventuallyEq
    rcases htle.eq_or_lt with rfl | hlt
    · exact joinedArc_seam_germ h0
    · exact joinedArc_left_germ hlt
  · exact
      (hβ.comp (contMDiff_id.add contMDiff_const)).contMDiffAt.congr_of_eventuallyEq
        (joinedArc_right_germ (lt_of_not_ge htle))

theorem CircleGluing.joinedArc_derivative_injective {N : Type*} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] {α β : ℝ → N} {R r : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (hiα : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hiβ : ∀ s ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J β s)) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) (2 * r + 1)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (joinedArc α β r) t) := by
  by_cases htle : t ≤ 2 * r
  · have htα : t + (-r) ∈ Set.Ioo (-R) R := ⟨by linarith [ht.1], by linarith⟩
    have heq : joinedArc α β r =ᶠ[𝓝 t] (fun s => α (s + (-r))) := by
      rcases htle.eq_or_lt with rfl | hlt
      · exact joinedArc_seam_germ h0
      · exact joinedArc_left_germ hlt
    rw [heq.mfderiv_eq]
    exact
      MorseCancellation.injective_mfderiv_curve_translate
        ((hα.contMDiffAt (Ioo_mem_nhds htα.1 htα.2)).mdifferentiableAt (by simp)) (hiα _ htα)
  · have htβ : t + (-2 * r) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
    rw [(joinedArc_right_germ (α := α) (β := β) (lt_of_not_ge htle)).mfderiv_eq]
    exact
      MorseCancellation.injective_mfderiv_curve_translate (hβ.mdifferentiableAt (by simp)) (hiβ _ htβ)

def CircleGluing.joinedLoop {N : Type*} {r : ℝ} (hr : 0 < r) (α β : ℝ → N) : ℝ → N :=
  periodicExtension (show 0 < 2 * r + 1 by linarith) (joinedArc α β r)

theorem CircleGluing.joinedLoop_periodic {N : Type*} {r : ℝ} (hr : 0 < r) (α β : ℝ → N) :
    Function.Periodic (joinedLoop hr α β) (2 * r + 1) :=
  periodicExtension_periodic _ _

theorem CircleGluing.joinedLoop_left {N : Type*} {r : ℝ} (hr : 0 < r) (α β : ℝ → N) {s : ℝ}
    (hs : s ∈ Set.Icc (-r) r) : joinedLoop hr α β (s + r) = α s := by
  change joinedArc α β r (toIcoMod _ 0 (s + r)) = α s
  rw [(toIcoMod_eq_self _).mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩,
    joinedArc_left (by linarith [hs.2])]
  congr 1
  ring

theorem CircleGluing.joinedLoop_right {N : Type*} {r : ℝ} (hr : 0 < r) {α β : ℝ → N}
    (h0 : β 0 = α r) (h1 : β 1 = α (-r)) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    joinedLoop hr α β (2 * r + s) = β s := by
  by_cases hs1 : s = 1
  · subst s
    have hper := (joinedLoop_periodic hr α β) 0
    rw [zero_add] at hper
    have hz : joinedLoop hr α β 0 = α (-r) := by
      simpa only [neg_add_cancel] using joinedLoop_left hr α β (s := -r) ⟨le_rfl, by linarith⟩
    exact hper.trans (hz.trans h1.symm)
  · change joinedArc α β r (toIcoMod _ 0 (2 * r + s)) = β s
    rw [(toIcoMod_eq_self _).mpr
        ⟨by linarith [hs.1], by
          have hlt : s < 1 := lt_of_le_of_ne hs.2 hs1
          linarith⟩]
    by_cases hs0 : s = 0
    · subst s
      rw [add_zero, joinedArc_left le_rfl]
      simpa only [show 2 * r + (-r) = r by ring] using h0.symm
    · rw [joinedArc_right
          (by
            have hpos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
            linarith)]
      congr 1
      ring

theorem CircleGluing.joinedLoop_range {N : Type*} {r : ℝ} (hr : 0 < r) {α β : ℝ → N}
    (h0 : β 0 = α r) (h1 : β 1 = α (-r)) :
    Set.range (joinedLoop hr α β) = α '' Set.Icc (-r) r ∪ β '' Set.Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    let q := toIcoMod (show 0 < 2 * r + 1 by linarith) 0 t
    have hq : q ∈ Set.Ico (0 : ℝ) (2 * r + 1) := by
      simpa only [zero_add] using toIcoMod_mem_Ico (show 0 < 2 * r + 1 by linarith) 0 t
    change joinedArc α β r q ∈ _
    by_cases hqr : q ≤ 2 * r
    · rw [joinedArc_left hqr]
      exact Or.inl ⟨_, ⟨by linarith [hq.1], by linarith⟩, rfl⟩
    · rw [joinedArc_right (lt_of_not_ge hqr)]
      exact Or.inr ⟨_, ⟨by linarith, by linarith [hq.2]⟩, rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact ⟨s + r, joinedLoop_left hr α β hs⟩
    · exact ⟨2 * r + s, joinedLoop_right hr h0 h1 hs⟩

theorem CircleGluing.joinedLoop_injOn {N : Type*} {r : ℝ} (hr : 0 < r) {α β : ℝ → N}
    (hα : Set.InjOn α (Set.Icc (-r) r)) (hβ : Set.InjOn β (Set.Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, β t ∉ α '' Set.Icc (-r) r) :
    Set.InjOn (joinedLoop hr α β) (Set.Ico (0 : ℝ) (2 * r + 1)) := by
  intro x hx y hy hxy
  apply joinedArc_injOn hα hβ havoid hx hy
  change joinedArc α β r (toIcoMod _ 0 x) = joinedArc α β r (toIcoMod _ 0 y) at hxy
  rw [(toIcoMod_eq_self _).mpr (by simpa only [zero_add] using hx),
    (toIcoMod_eq_self _).mpr (by simpa only [zero_add] using hy)] at hxy
  exact hxy

theorem CircleGluing.joinedLoop_contMDiff {N : Type*} {r : ℝ} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hr : 0 < r) {α β : ℝ → N} {R : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    ContMDiff 𝓘(ℝ, ℝ) J ∞ (joinedLoop hr α β) :=
  periodicExtension_contMDiff _ (joinedArc_periodic_germ hr h1)
    (fun _ ht => joinedArc_contMDiffAt hrR hα hβ h0 ht)

theorem CircleGluing.joinedLoop_derivative_injective {N : Type*} {r : ℝ} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hr : 0 < r) {α β : ℝ → N} {R : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r))))
    (hiα : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hiβ : ∀ s ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J β s)) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (joinedLoop hr α β) t) :=
  periodicExtension_derivative_injective _ (joinedArc_periodic_germ hr h1)
    (fun _ ht => (joinedArc_contMDiffAt hrR hα hβ h0 ht).mdifferentiableAt (by simp))
    (fun _ ht => joinedArc_derivative_injective hrR hα hβ h0 hiα hiβ ht) t

theorem CircleGluing.circleExp_derivative_injective (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  have hd :
    HasDerivAt (fun s : ℝ => (Circle.exp s : ℂ)) (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)
      t := by
    simpa only [Circle.coe_exp, Complex.real_smul, id_eq, one_mul] using
      ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).cexp.comp_ofReal
  have hdne : (Complex.exp ((t : ℂ) * Complex.I) * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero
  have hi0 : Function.Injective (fderiv ℝ (fun s : ℝ => (Circle.exp s : ℂ)) t) := by
    rw [hd.hasFDerivAt.fderiv]
    exact smul_left_injective ℝ hdne
  let c : Circle → ℂ := fun z => (z : ℂ)
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ c := contMDiff_coe_sphere
  have hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (c ∘ (fun s : ℝ => Circle.exp s)) t) := by
    rw [mfderiv_eq_fderiv]
    exact hi0
  rw [mfderiv_comp t (hc.mdifferentiableAt (by simp))
      ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))] at hi
  intro x y hxy
  exact hi (congrArg (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) c (Circle.exp t)) hxy)

theorem CircleGluing.circleExp_localDiffeomorph (t : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ Circle.exp t := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t
  have hi : Function.Injective L := circleExp_derivative_injective t
  have hs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) (by simp)).mp
      hi
  apply
    isLocalDiffeomorphAt_boundaryless isOpen_univ (Set.mem_univ t)
      (contMDiff_circleExp (m := ∞)).contMDiffOn
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

theorem CircleGluing.contMDiff_of_comp_circleExp {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff 𝓘(ℝ, ℝ) J ∞ (γ ∘ Circle.exp)) :
    ContMDiff (𝓡 1) J ∞ γ := by
  intro z
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  let h := circleExp_localDiffeomorph t
  have hs : ContMDiffAt (𝓡 1) J ∞ ((γ ∘ Circle.exp) ∘ h.localInverse) (Circle.exp t) :=
    (hγ.contMDiffAt (x := h.localInverse (Circle.exp t))).comp _ h.localInverse_contMDiffAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [h.localInverse_eventuallyEq_right] with y hy
  exact (congrArg γ hy).symm

def CircleGluing.periodicCircle {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) (z : Circle) : N :=
  hper.lift ((AddCircle.homeomorphCircle hT).symm z)

theorem CircleGluing.periodicCircle_exp {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) (t : ℝ) :
    periodicCircle hT hper (Circle.exp (2 * Real.pi / T * t)) = f t := by
  have heq : Circle.exp (2 * Real.pi / T * t) = AddCircle.homeomorphCircle hT (t : AddCircle T) :=
    by rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  rw [heq, periodicCircle, Homeomorph.symm_apply_apply, Function.Periodic.lift_coe]

theorem CircleGluing.periodicCircle_comp_exp {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) :
    periodicCircle hT hper ∘ Circle.exp = (fun t => f (T / (2 * Real.pi) * t)) := by
  funext t
  have heq : 2 * Real.pi / T * (T / (2 * Real.pi) * t) = t := by field_simp [hT, Real.pi_ne_zero]
  have hh := periodicCircle_exp hT hper (T / (2 * Real.pi) * t)
  rw [heq] at hh
  exact hh

theorem CircleGluing.periodicCircle_injective {N : Type*} {T : ℝ} {f : ℝ → N} (hT : 0 < T)
    (hper : Function.Periodic f T) (hi : Set.InjOn f (Set.Ico (0 : ℝ) T)) :
    Function.Injective (periodicCircle hT.ne' hper) := by
  let _ : Fact (0 < T) := ⟨hT⟩
  let e := AddCircle.homeomorphCircle hT.ne'
  intro z w hzw
  let x := AddCircle.equivIco T 0 (e.symm z)
  let y := AddCircle.equivIco T 0 (e.symm w)
  have hx : (x.val : AddCircle T) = e.symm z := AddCircle.coe_equivIco
  have hy : (y.val : AddCircle T) = e.symm w := AddCircle.coe_equivIco
  have hval : f x.val = f y.val := by
    change hper.lift (e.symm z) = hper.lift (e.symm w) at hzw
    rw [← hx, ← hy, Function.Periodic.lift_coe, Function.Periodic.lift_coe] at hzw
    exact hzw
  have hxy : x.val = y.val :=
    hi (by simpa only [zero_add] using x.property) (by simpa only [zero_add] using y.property)
      hval
  apply e.symm.injective
  rw [← hx, ← hy, hxy]

theorem CircleGluing.periodicCircle_range {N : Type*} {T : ℝ} {f : ℝ → N} (hT : T ≠ 0)
    (hper : Function.Periodic f T) : Set.range (periodicCircle hT hper) = Set.range f := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective w
    have hh := congrFun (periodicCircle_comp_exp hT hper) t
    exact ⟨T / (2 * Real.pi) * t, hh.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Circle.exp (2 * Real.pi / T * t), periodicCircle_exp hT hper t⟩

theorem CircleGluing.periodicCircle_contMDiff {N : Type*} {T : ℝ} {f : ℝ → N} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (hT : T ≠ 0) (hper : Function.Periodic f T)
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) : ContMDiff (𝓡 1) J ∞ (periodicCircle hT hper) := by
  apply contMDiff_of_comp_circleExp
  rw [periodicCircle_comp_exp]
  exact hf.comp (contDiff_const.mul contDiff_id).contMDiff

theorem CircleGluing.injective_mfderiv_curve_const_mul {N : Type*} {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] {α : ℝ → N} {s a : ℝ} (ha : a ≠ 0)
    (hα : MDifferentiableAt 𝓘(ℝ, ℝ) J α (a * s))
    (hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α (a * s))) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => α (a * t)) s) := by
  have hd : HasDerivAt (fun t : ℝ => a * t) a s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul a
  have hmul : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => a * t) s) := by
    rw [mfderiv_eq_fderiv]
    have hh : Function.Injective (fderiv ℝ (fun t : ℝ => a * t) s) := by
      rw [hd.hasFDerivAt.fderiv]
      exact smul_left_injective ℝ ha
    exact hh
  change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (α ∘ (fun t : ℝ => a * t)) s)
  rw [mfderiv_comp s hα hd.differentiableAt.mdifferentiableAt]
  intro x y hxy
  exact hmul (hi hxy)

theorem CircleGluing.periodicCircle_derivative_injective {N : Type*} {T : ℝ} {f : ℝ → N}
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] (hT : T ≠ 0)
    (hper : Function.Periodic f T) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hi : ∀ t, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (z : Circle) :
    Function.Injective (mfderiv (𝓡 1) J (periodicCircle hT hper) z) := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  have hc : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (periodicCircle hT hper ∘ Circle.exp) t) := by
    rw [periodicCircle_comp_exp]
    exact
      injective_mfderiv_curve_const_mul
        (div_ne_zero hT (mul_ne_zero (by norm_num) Real.pi_ne_zero))
        (hf.mdifferentiableAt (by simp)) (hi _)
  rw [mfderiv_comp t ((periodicCircle_contMDiff hT hper hf).mdifferentiableAt (by simp))
      ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))] at hc
  have hs := ((circleExp_localDiffeomorph t).mfderivToContinuousLinearEquiv (by simp)).surjective
  intro x y hxy
  obtain ⟨u, hu⟩ := hs x
  obtain ⟨v, hv⟩ := hs y
  have hux : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t u = x := hu
  have hvy : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t v = y := hv
  have huv : u = v :=
    hc
      (by
        change
          mfderiv (𝓡 1) J (periodicCircle hT hper) (Circle.exp t)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t u) =
            mfderiv (𝓡 1) J (periodicCircle hT hper) (Circle.exp t)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t v)
        rw [hux, hvy]
        exact hxy)
  exact hux.symm.trans ((congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) huv).trans hvy)

theorem NativeOpenSubmanifold.injective_mfderiv_subtype_val {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] (U : TopologicalSpace.Opens M) (p : U) :
    Function.Injective (mfderiv I I (Subtype.val : U → M) p) := by
  classical
  let g : M → U := fun x => if hx : x ∈ U then ⟨x, hx⟩ else p
  have hval : (Subtype.val ∘ g) =ᶠ[𝓝 (p : M)] id := by
    apply Filter.mem_of_superset (U.isOpen.mem_nhds p.property)
    intro x hx
    change x ∈ U at hx
    change (g x : M) = x
    dsimp [g]
    rw [dif_pos hx]
  have hg : ContMDiffAt I I ∞ g (p : M) := by
    apply (ContMDiffAt.subtypeVal_comp_iff U g (p : M)).mp
    exact contMDiffAt_id.congr_of_eventuallyEq hval
  have hv : ContMDiff I I ∞ (Subtype.val : U → M) := contMDiff_subtype_val
  have hleft : g ∘ (Subtype.val : U → M) = id := by
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, g, dif_pos x.property, id_eq]
  have heq := mfderiv_comp p (hg.mdifferentiableAt (by simp)) (hv.mdifferentiableAt (by simp))
  rw [hleft, mfderiv_id] at heq
  intro v w hvw
  have hh := congrArg (mfderiv I I g (p : M)) hvw
  have hv' := congrArg (fun L => L v) heq
  have hw' := congrArg (fun L => L w) heq
  exact hv'.trans (hh.trans hw'.symm)

theorem MorseCancellation.exists_embedded_circle_through_arc {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (S : TopologicalSpace.Opens N) {α : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Set.Ioo (-R) R)) (hinj : Set.InjOn α (Set.Icc (-R) R))
    (hderiv : ∀ s ∈ Set.Ioo (-R) R, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J α s)) (hplus : α r ∈ S)
    (hminus : α (-r) ∈ S) (η : Path (⟨α r, hplus⟩ : S) (⟨α (-r), hminus⟩ : S))
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ γ : C(Circle, N),
      ContMDiff (𝓡 1) J ∞ γ ∧
        Function.Injective γ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 1) J γ z)) ∧
            (∀ s ∈ Set.Icc (-r) r, γ (Circle.exp (2 * Real.pi / (2 * r + 1) * (s + r))) = α s) ∧
              Set.range γ ⊆ α '' Set.Icc (-r) r ∪ (S : Set N) := by
  obtain ⟨b, hb, hb0, hb1, hemb, hbd, havoid⟩ :=
    exists_disjoint_embedded_return_arc S hr hrR hα hinj hderiv hplus hminus η hdim
  let β : ℝ → N := Subtype.val ∘ b
  have hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β := contMDiff_subtype_val.comp hb
  have hβi : Set.InjOn β (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hbx : b x = b y := Subtype.ext hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hbx)
  have hβd : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J β t) := by
    intro t ht
    rw [show β = Subtype.val ∘ b from rfl,
      mfderiv_comp t ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
        (hb.mdifferentiableAt (by simp))]
    exact (NativeOpenSubmanifold.injective_mfderiv_subtype_val S (b t)).comp (hbd t ht)
  have h0 : β 0 = α r := by simpa only [zero_add] using hb0.eq_of_nhds
  have h1 : β 1 = α (-r) := by
    simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using hb1.eq_of_nhds
  let F := CircleGluing.joinedLoop hr α β
  have hF : ContMDiff 𝓘(ℝ, ℝ) J ∞ F :=
    CircleGluing.joinedLoop_contMDiff hr hrR hα hβ hb0 hb1
  have hFd : ∀ t, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J F t) :=
    CircleGluing.joinedLoop_derivative_injective hr hrR hα hβ hb0 hb1 hderiv hβd
  have hsub : Set.Icc (-r) r ⊆ Set.Icc (-R) R := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hαi : Set.InjOn α (Set.Icc (-r) r) := hinj.mono hsub
  have hFi : Set.InjOn F (Set.Ico (0 : ℝ) (2 * r + 1)) :=
    CircleGluing.joinedLoop_injOn hr hαi hβi havoid
  have hT : 0 < 2 * r + 1 := by linarith
  have hper : Function.Periodic F (2 * r + 1) := CircleGluing.joinedLoop_periodic hr α β
  let Γ := CircleGluing.periodicCircle hT.ne' hper
  have hΓ : ContMDiff (𝓡 1) J ∞ Γ := CircleGluing.periodicCircle_contMDiff hT.ne' hper hF
  refine
    ⟨⟨Γ, hΓ.continuous⟩, hΓ, CircleGluing.periodicCircle_injective hT hper hFi,
      CircleGluing.periodicCircle_derivative_injective hT.ne' hper hF hFd, ?_, ?_⟩
  · intro s hs
    exact
      (CircleGluing.periodicCircle_exp hT.ne' hper (s + r)).trans
        (CircleGluing.joinedLoop_left hr α β hs)
  · intro z hz
    change z ∈ Set.range Γ at hz
    rw [CircleGluing.periodicCircle_range,
      CircleGluing.joinedLoop_range hr h0 h1] at hz
    rcases hz with hz | ⟨t, -, rfl⟩
    · exact Or.inl hz
    · exact Or.inr (b t).property

theorem MorseCancellation.dense_section_of_flow_cylinder {N X : Type*} [TopologicalSpace N]
    [TopologicalSpace X] (A : OpenPartialHomeomorph (N × ℝ) X) (hsource : A.source = Set.univ)
    (F : Flow ℝ X) (ι : N → X) (hformula : ∀ z, A z = F z.2 (ι z.1)) {B : Set X} (hB : Dense B)
    (hinv : ∀ t x, F t x ∈ B ↔ x ∈ B) : Dense (ι ⁻¹' B) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  have hdom : U ×ˢ (Set.univ : Set ℝ) ⊆ A.source := by rw [hsource]; exact Set.subset_univ _
  have hopen : IsOpen (A '' (U ×ˢ (Set.univ : Set ℝ))) :=
    A.isOpen_image_of_subset_source (hU.prod isOpen_univ) hdom
  obtain ⟨z, hz⟩ := hne
  have himage : (A '' (U ×ˢ (Set.univ : Set ℝ))).Nonempty :=
    ⟨A (z, 0), (z, 0), ⟨hz, Set.mem_univ _⟩, rfl⟩
  obtain ⟨x, hx, hxB⟩ := hB.inter_open_nonempty _ hopen himage
  obtain ⟨⟨w, t⟩, ⟨hw, -⟩, rfl⟩ := hx
  refine ⟨w, hw, ?_⟩
  apply (hinv t (ι w)).mp
  rwa [hformula] at hxB

theorem AdaptedWindows.dense_regular_level_minimum_basins {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f) :
    Dense
      {x : { y : M // f y = a } |
        ∃ p : ManifoldMorse.criticalPoints E f,
          MorseCancellation.nativeMorseIndex E f p = 0 ∧
            Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let L := { y : M // f y = a }
  rcases isEmpty_or_nonempty L with h | h
  · exact fun x => isEmptyElim x
  · let _ := RegularLevel.chartedSpace hf hreg
    obtain ⟨A, hsource, -, hformula, -⟩ :=
      FlowCancellation.exists_native_level_flow_cylinder hf hreg S.smooth S.flow S.integral
        (fun x hx => S.descent x (hreg x hx)) (Classical.arbitrary L)
    apply
      MorseCancellation.dense_section_of_flow_cylinder A.toOpenPartialHomeomorph hsource S.flow
        Subtype.val hformula (S.dense_minimum_forward_basins hf)
    intro t x
    constructor
    · rintro ⟨p, hp, hlim⟩
      exact ⟨p, hp, (MorseCancellation.flow_time_atTop_limit_iff S.flow t x p.val).mp hlim⟩
    · rintro ⟨p, hp, hlim⟩
      exact ⟨p, hp, (MorseCancellation.flow_time_atTop_limit_iff S.flow t x p.val).mpr hlim⟩

theorem MorseCancellation.unitSphere_eq_two_points_of_finrank_one {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 1)
    (u v : Metric.sphere (0 : V) 1) (huv : u ≠ v) (w : Metric.sphere (0 : V) 1) : w = u ∨ w = v :=
  by
  obtain ⟨L⟩ :=
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
      (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hdim)
  let e := UnitSphereEquiv.homeomorph L
  have hpoint (z : Metric.sphere (0 : V) 1) : (e z : ℝ) = 1 ∨ (e z : ℝ) = -1 := by
    have hz : |(e z : ℝ)| = |(1 : ℝ)| := by
      simpa only [Real.norm_eq_abs, abs_one] using mem_sphere_zero_iff_norm.mp (e z).property
    exact abs_eq_abs.mp hz
  have hne : (e u : ℝ) ≠ (e v : ℝ) := fun h => huv (e.injective (Subtype.ext h))
  have heq : (e w : ℝ) = (e u : ℝ) ∨ (e w : ℝ) = (e v : ℝ) := by
    rcases hpoint u with hu | hu <;> rcases hpoint v with hv | hv <;>
        rcases hpoint w with hw | hw <;>
      simp_all
  exact
    heq.elim (fun h => Or.inl (e.injective (Subtype.ext h)))
      (fun h => Or.inr (e.injective (Subtype.ext h)))

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_orbit_bandBridge {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    letI := RegularLevel.chartedSpace hf (S.data p).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ e :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data p).UpperLevel (S.data q).LowerLevel ∞,
        D '' {x : M | f x ≤ f p + (S.data p).radius ^ 2} =
            {x : M | f x ≤ f q - (S.data q).radius ^ 2} ∧
          (∀ x, (e x : M) = D x) ∧ ∀ x, ∃ t, S.flow t x = D x :=
  FlowTimeChange.exists_orbit_preserving_native_band_bridge hf S.smooth S.descent S.flow
    S.integral (S.separated p q hpq).le (S.toSurgeryWindows.regular_between p q hconsecutive)
    (S.data p).upper_regular (S.data q).lower_regular

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.transported_attaching_basin_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1)]
    (e : (S.data p).UpperLevel ≃ₜ (S.data q).LowerLevel)
    (horbit : ∀ x : (S.data p).UpperLevel, ∃ t, S.flow t x = (e x : M))
    (x : (S.data p).UpperLevel) :
    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ↔
      x ∈ Set.range ((S.data p).transportedAttachingSphere (S.data q) n e) := by
  rw [(S.data p).range_transportedAttachingSphere (S.data q) n e]
  change
    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ↔
      e x ∈ Set.range (S.data q).surgery.attachingSphere
  rw [← S.attaching_basin_iff hf q (e x)]
  obtain ⟨t, ht⟩ := horbit x
  rw [← ht]
  exact (MorseCancellation.flow_time_atBot_limit_iff S.flow t (x : M) q.val).symm

theorem FlowSuspension.exists_unique_connection_of_unit_level_count {M : Type*}
    [TopologicalSpace M] (F G : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {p q : M} {c : ℝ}
    (hpc : c < f p) (hqc : f q < c) (D : { x : M // f x = c } → { x : M // f x = c })
    (hback :
      ∀ x : { y : M // f y = c },
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (hforward :
      ∀ x : { y : M // f y = c },
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q) ↔
          Filter.Tendsto (fun t => F t (D x)) Filter.atTop (𝓝 q))
    (hcount :
      {x : { y : M // f y = c } |
            Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) ∧
              Filter.Tendsto (fun t => F t (D x)) Filter.atTop (𝓝 q)}.ncard =
        1) :
    ∃ z : { y : M // f y = c },
      Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 p) ∧
        Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 q) ∧
          ∀ x,
            Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) →
              Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q) → ∃ t, G t z = x := by
  let C :=
    {x : { y : M // f y = c } |
      Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) ∧
        Filter.Tendsto (fun t => F t (D x)) Filter.atTop (𝓝 q)}
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hcount
  have hmem : z ∈ C := by rw [show C = { z } from hz]; exact Set.mem_singleton z
  have hu (x : { y : M // f y = c }) (hb : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (hf' : Filter.Tendsto (fun t => F t (D x)) Filter.atTop (𝓝 q)) : x = z := by
    have hx : x ∈ C := ⟨hb, hf'⟩
    rw [show C = { z } from hz] at hx
    exact Set.mem_singleton_iff.mp hx
  exact
    ⟨z,
      unique_connection_of_level_basin_intersection F G hf hpc hqc D hback hforward z hmem.1
        hmem.2 hu⟩

theorem FlowSuspension.no_connection_of_level_basin_disjointness {M : Type*}
    [TopologicalSpace M] (F G : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {p q : M} {c : ℝ}
    (hpc : c < f p) (hqc : f q < c) (D : { x : M // f x = c } → { x : M // f x = c })
    (hback :
      ∀ x : { y : M // f y = c },
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (hforward :
      ∀ x : { y : M // f y = c },
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q) ↔
          Filter.Tendsto (fun t => F t (D x)) Filter.atTop (𝓝 q))
    (hdisjoint :
      ∀ x : { y : M // f y = c },
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) ∧
            Filter.Tendsto (fun t => F t (D x)) Filter.atTop (𝓝 q))) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q)) := by
  rintro x ⟨hxback, hxforward⟩
  obtain ⟨s, hs⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits G hf hxback hxforward hpc hqc
  let u : { y : M // f y = c } := ⟨G s x, hs⟩
  have hub : Filter.Tendsto (fun t => G t u) Filter.atBot (𝓝 p) :=
    (MorseCancellation.flow_time_atBot_limit_iff G s x p).mpr hxback
  have huf : Filter.Tendsto (fun t => G t u) Filter.atTop (𝓝 q) :=
    (MorseCancellation.flow_time_atTop_limit_iff G s x q).mpr hxforward
  exact hdisjoint u ⟨(hback u).mp hub, (hforward u).mp huf⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.surjective_beltNormal_derivative {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Function.Surjective
      (mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
        (d.surgery.beltSphere v)) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let w : d.chart.PositiveCoordinates := d.radius • (v : d.chart.PositiveCoordinates)
  let γ : d.chart.NegativeCoordinates → M := fun u => d.chart.splitChart.symm (u, w)
  let n : M → d.chart.NegativeCoordinates := fun x => (d.chart.splitChart x).1
  have hmodel : (0, w) ∈ d.chart.splitChart.target := d.belt_model_mem_target v
  have hγ : ContMDiffAt 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, E) ∞ γ 0 :=
    (d.chart.splitChart.contMDiffOn_invFun.contMDiffAt
          (d.chart.splitChart.open_target.mem_nhds hmodel)).comp
      0 (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hpoint : γ 0 = (d.surgery.beltSphere v : M) := by rw [d.belt_eq, d.chart.beltCoreMap_coe]
  have hn :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ n (d.surgery.beltSphere v : M) :=
    contDiff_fst.contMDiff.contMDiffAt.comp _
      (d.chart.splitChart.contMDiffOn_toFun.contMDiffAt
        (d.chart.splitChart.open_source.mem_nhds (d.belt_mem_normalDomain v)))
  have hnear : ∀ᶠ u : d.chart.NegativeCoordinates in 𝓝 0, (u, w) ∈ d.chart.splitChart.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (d.chart.splitChart.open_target.mem_nhds hmodel)
  have hheight :
    f ∘ γ =ᶠ[𝓝 (0 : d.chart.NegativeCoordinates)] (fun u => f p - ‖u‖ ^ 2 + ‖w‖ ^ 2) := by
    filter_upwards [hnear] with u hu
    exact d.chart.splitChart_inverse_equation hu
  have hheight₀ : mfderiv 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, ℝ) (f ∘ γ) 0 = 0 := by
    rw [hheight.mfderiv_eq, mfderiv_eq_fderiv, fderiv_add_const, fderiv_const_sub,
      fderiv_norm_sq_apply]
    simp
    rfl
  have hnormal : n ∘ γ =ᶠ[𝓝 (0 : d.chart.NegativeCoordinates)] id := by
    filter_upwards [hnear] with u hu
    exact congrArg Prod.fst (d.chart.splitChart.right_inv' hu)
  have hnormal₀ :
    mfderiv 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, d.chart.NegativeCoordinates) (n ∘ γ) 0 =
      ContinuousLinearMap.id ℝ d.chart.NegativeCoordinates := by
    rw [hnormal.mfderiv_eq, mfderiv_id]
    rfl
  let R : d.chart.NegativeCoordinates →L[ℝ] E :=
    mfderiv 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, E) γ 0
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (d.surgery.beltSphere v : M)
  let B : E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (d.surgery.beltSphere v : M)
  have hLpoint : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ 0) : E →L[ℝ] ℝ) = L := by
    rw [hpoint]
    rfl
  have hLR₀ : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ 0) : E →L[ℝ] ℝ).comp R = 0 :=
    (mfderiv_comp 0 (hf.mdifferentiableAt (by simp)) (hγ.mdifferentiableAt (by simp))).symm.trans
      hheight₀
  have hLR : L.comp R = 0 := (congrArg (fun T : E →L[ℝ] ℝ => T.comp R) hLpoint).symm.trans hLR₀
  have hnγ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (γ 0) := by
    rw [hpoint]
    exact hn.mdifferentiableAt (by simp)
  have hBpoint :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (γ 0) :
        E →L[ℝ] d.chart.NegativeCoordinates) =
      B := by rw [hpoint]
  have hBR₀ :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (γ 0) :
            E →L[ℝ] d.chart.NegativeCoordinates).comp
        R =
      ContinuousLinearMap.id ℝ d.chart.NegativeCoordinates :=
    (mfderiv_comp 0 hnγ (hγ.mdifferentiableAt (by simp))).symm.trans hnormal₀
  have hBR : B.comp R = ContinuousLinearMap.id ℝ d.chart.NegativeCoordinates :=
    (congrArg (fun T : E →L[ℝ] d.chart.NegativeCoordinates => T.comp R) hBpoint).symm.trans hBR₀
  exact
    RegularLevel.surjective_normal_derivative_of_tangent_lift hf d.upper_regular
      (d.surgery.beltSphere v) (hn.mdifferentiableAt (by simp)) R hLR hBR

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.range_belt_derivative_eq_normal_kernel {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v).range =
      (mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
          (d.surgery.beltSphere v)).ker := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  let Q : RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
      (d.surgery.beltSphere v)
  change A.range = Q.ker
  have hQA : Q.comp A = 0 := d.beltNormal_derivative_comp_belt hf n v
  have hsub : A.range ≤ Q.ker := by
    rintro _ ⟨u, rfl⟩
    change Q (A u) = 0
    exact congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] d.chart.NegativeCoordinates => T u) hQA
  have hAi : Function.Injective A := d.belt_derivative_injective hf n v
  have hArank : Module.finrank ℝ A.range = n := by
    rw [LinearMap.finrank_range_of_inj hAi]
    exact finrank_euclideanSpace_fin
  have hQ : Function.Surjective Q := d.surjective_beltNormal_derivative hf v
  have hQrank : Module.finrank ℝ Q.range = Module.finrank ℝ d.chart.NegativeCoordinates := by
    rw [LinearMap.range_eq_top.mpr hQ, finrank_top]
  have hdimQ := Q.toLinearMap.finrank_range_add_finrank_ker
  have hsplit := d.chart.finrank_negative_add_positive
  have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1 := Fact.out
  have hmodel : Module.finrank ℝ (RegularLevel.Model E) = Module.finrank ℝ E - 1 :=
    finrank_euclideanSpace_fin
  apply Submodule.eq_of_le_of_finrank_eq hsub
  rw [hArank]
  omega

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.bijective_beltNormal_comp_of_transverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (x : Hemisphere.Sphere m)
      (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates),
      d.surgery.beltSphere v = g x →
        Function.Surjective
            ((mfderiv (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) g x :
                  EuclideanSpace ℝ (Fin m) →L[ℝ] RegularLevel.Model E).coprod
              (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v :
                EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E)) →
          Function.Bijective
            (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg x v hxy ht
  let Q : RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
      (d.surgery.beltSphere v)
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) g x
  have hQ : Function.Surjective Q := d.surjective_beltNormal_derivative hf v
  have hQB : Q.comp B = 0 := d.beltNormal_derivative_comp_belt hf n v
  have hBA : Function.Surjective (B.coprod A) :=
    TransverseCoordinates.surjective_coprod_swap A B ht
  have hi : Function.Bijective (Q.comp A) :=
    TransverseCoordinates.bijective_normal_comp Q B A hQ hBA hQB
      (by simpa only [finrank_euclideanSpace_fin] using hdim.symm)
  have hx : g x ∈ d.beltNormalDomain := hxy ▸ d.belt_mem_normalDomain v
  have hnormal :=
    (d.contMDiffOn_beltNormal hf).contMDiffAt (d.isOpen_beltNormalDomain.mem_nhds hx)
  have heq : mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x = Q.comp A := by
    rw [mfderiv_comp x (hnormal.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp)), ←
      hxy]
    rfl
  rw [heq]
  exact hi

def TransverseCoordinates.sumMap {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup A] (f : D → A) (g : Z → A) (q : D × Z) : A :=
  f q.1 + g q.2 - f 0

theorem TransverseCoordinates.sumMap_left {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup Z] [NormedAddCommGroup A] (f : D → A) (g : Z → A) (hzero : g 0 = f 0)
    (x : D) : sumMap f g (x, 0) = f x := by simp [sumMap, hzero]

theorem TransverseCoordinates.sumMap_right {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup A] (f : D → A) (g : Z → A) (z : Z) : sumMap f g (0, z) = g z := by
  simp [sumMap, add_sub_cancel_left]

theorem TransverseCoordinates.contDiffOn_sumMap {D Z A : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A]
    [NormedSpace ℝ A] {f : D → A} {g : Z → A} {U : Set D} {V : Set Z} (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g V) : ContDiffOn ℝ ∞ (sumMap f g) (U ×ˢ V) :=
  ((hf.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)).add
        (hg.comp contDiff_snd.contDiffOn (fun _ hx => hx.2))).sub
    contDiffOn_const

theorem TransverseCoordinates.hasFDerivAt_sumMap_zero {D Z A : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A]
    [NormedSpace ℝ A] {f : D → A} {g : Z → A} (hf : DifferentiableAt ℝ f 0)
    (hg : DifferentiableAt ℝ g 0) :
    HasFDerivAt (sumMap f g) ((fderiv ℝ f 0).coprod (fderiv ℝ g 0)) (0, 0) := by
  have hfst := (ContinuousLinearMap.fst ℝ D Z).hasFDerivAt (x := (0, 0))
  have hsnd := (ContinuousLinearMap.snd ℝ D Z).hasFDerivAt (x := (0, 0))
  have hd :=
    ((hf.hasFDerivAt.comp (0, 0) hfst).add (hg.hasFDerivAt.comp (0, 0) hsnd)).sub
      (hasFDerivAt_const (f 0) (0, 0))
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro q
  simp [ContinuousLinearMap.coprod_apply]

def NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) : D × Z → M :=
  r.toFun ∘ TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g)

def NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinateDomain {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) (U : Set D) (V : Set Z) : Set (D × Z) :=
  (U ×ˢ V) ∩ TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) ⁻¹' r.domain

theorem NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates_left {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [NormedAddCommGroup Z] {e : NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (f : D → M) (g : Z → M) (hzero : g 0 = f 0) (x : D) :
    r.sheetCoordinates f g (x, 0) = f x := by
  have hsum :=
    TransverseCoordinates.sumMap_left (e.toFun ∘ f) (e.toFun ∘ g) (congrArg e.toFun hzero) x
  change r.toFun (TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (x, 0)) = f x
  rw [hsum]
  exact r.retract (f x)

theorem NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates_right {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) (z : Z) : r.sheetCoordinates f g (0, z) = g z := by
  rw [sheetCoordinates, Function.comp_apply, TransverseCoordinates.sumMap_right]
  exact r.retract (g z)

theorem NativeEuclideanEmbedding.SmoothRetraction.zero_mem_sheetCoordinateDomain
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedAddCommGroup Z]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) (f : D → M) (g : Z → M)
    {U : Set D} {V : Set Z} (hU : (0 : D) ∈ U) (hV : (0 : Z) ∈ V) :
    (0, 0) ∈ r.sheetCoordinateDomain f g U V := by
  refine ⟨⟨hU, hV⟩, ?_⟩
  change TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0) ∈ r.domain
  rw [TransverseCoordinates.sumMap_right]
  exact r.contains ⟨g 0, rfl⟩

theorem NativeEuclideanEmbedding.SmoothRetraction.isOpen_sheetCoordinateDomain
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U) (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) :
    IsOpen (r.sheetCoordinateDomain f g U V) :=
  (TransverseCoordinates.contDiffOn_sumMap (e.smooth.comp_contMDiffOn hf).contDiffOn
        (e.smooth.comp_contMDiffOn hg).contDiffOn).continuousOn.isOpen_inter_preimage
    (hU.prod hV) r.open_domain

theorem NativeEuclideanEmbedding.SmoothRetraction.contMDiffOn_sheetCoordinates
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) :
    ContMDiffOn 𝓘(ℝ, D × Z) 𝓘(ℝ, E) ∞ (r.sheetCoordinates f g)
      (r.sheetCoordinateDomain f g U V) :=
  r.smooth.comp
    ((TransverseCoordinates.contDiffOn_sumMap (e.smooth.comp_contMDiffOn hf).contDiffOn
          (e.smooth.comp_contMDiffOn hg).contDiffOn).contMDiffOn.mono
      Set.inter_subset_left)
    (fun _ hx => hx.2)

theorem NativeEuclideanEmbedding.SmoothRetraction.mfderiv_sheetCoordinates_zero
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {f : D → M} {g : Z → M} (hzero : g 0 = f 0) (hf : ContMDiffAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f 0)
    (hg : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g 0) :
    mfderiv 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (r.sheetCoordinates f g) (0, 0) =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) := by
  have heF := (e.smooth.contMDiffAt.comp 0 hf).contDiffAt
  have heG := (e.smooth.contMDiffAt.comp 0 hg).contDiffAt
  have hsum :=
    TransverseCoordinates.hasFDerivAt_sumMap_zero (heF.differentiableAt (by simp))
      (heG.differentiableAt (by simp))
  have hbase :
    TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0) = e.toFun (f 0) := by
    rw [TransverseCoordinates.sumMap_right]
    exact congrArg e.toFun hzero
  have hr :
    MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun
      (TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0)) := by
    rw [hbase]
    exact
      (r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨f 0, rfl⟩))).mdifferentiableAt
        (by simp)
  have hdf :
    fderiv ℝ (e.toFun ∘ f) 0 =
      (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)).comp (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0) :=
    by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp 0 (e.smooth.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  have hdg :
    fderiv ℝ (e.toFun ∘ g) 0 =
      (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)).comp (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) :=
    by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp 0 (e.smooth.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))]
    rw [hzero]
  rw [sheetCoordinates, mfderiv_comp (0, 0) hr hsum.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, hsum.fderiv, hbase, hdf, hdg]
  apply ContinuousLinearMap.ext
  intro q
  have hleft :=
    congrArg (fun L => L ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0) q.1)) (r.mfderiv_retract_comp (f 0))
  have hright :=
    congrArg (fun L => L ((mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) q.2)) (r.mfderiv_retract_comp (f 0))
  let R : EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] E :=
    mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun (f 0))
  let T : E →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
    mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)
  let F : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0
  let G : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0
  change R (T (F q.1) + T (G q.2)) = F q.1 + G q.2
  change R (T (F q.1)) = F q.1 at hleft
  change R (T (G q.2)) = G q.2 at hright
  rw [map_add, hleft, hright]

theorem TransverseCoordinates.isInvertible_coprod_of_surjective {D Z E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    [FiniteDimensional ℝ E] (F : D →L[ℝ] E) (G : Z →L[ℝ] E)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Function.Surjective (F.coprod G)) : (F.coprod G).IsInvertible := by
  have hd : Module.finrank ℝ (D × Z) = Module.finrank ℝ E := by
    simpa only [Module.finrank_prod] using hdim
  have hi : Function.Injective (F.coprod G) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr ht
  let L := (LinearEquiv.ofBijective (F.coprod G).toLinearMap ⟨hi, ht⟩).toContinuousLinearEquiv
  exact ⟨L, rfl⟩

theorem exists_simultaneous_sheetChart {E M D Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : D) ∈ U) (h0V : (0 : Z) ∈ V) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) (hzero : g 0 = f 0)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0)))
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ a : ℝ,
      0 < a ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
          Metric.closedBall (0 : D) a ×ˢ Metric.closedBall (0 : Z) a ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ V ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
                  (∀ z, (0, z) ∈ Φ.source → Φ (0, z) = g z) := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  let W₀ := r.sheetCoordinateDomain f g U V
  have hW₀ : IsOpen W₀ := r.isOpen_sheetCoordinateDomain hU hV hf hg
  have hs : ContMDiffOn 𝓘(ℝ, D × Z) 𝓘(ℝ, E) ∞ (r.sheetCoordinates f g) W₀ :=
    r.contMDiffOn_sheetCoordinates hf hg
  let W := W₀ ∩ r.sheetCoordinates f g ⁻¹' O
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hW₀ hO
  have h0W : (0, 0) ∈ W := by
    refine ⟨r.zero_mem_sheetCoordinateDomain f g h0U h0V, ?_⟩
    change r.sheetCoordinates f g (0, 0) ∈ O
    rw [r.sheetCoordinates_left f g hzero]
    exact h0O
  have hinv : (mfderiv 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (r.sheetCoordinates f g) (0, 0)).IsInvertible := by
    rw [r.mfderiv_sheetCoordinates_zero hzero (hf.contMDiffAt (hU.mem_nhds h0U))
        (hg.contMDiffAt (hV.mem_nhds h0V))]
    exact
      TransverseCoordinates.isInvertible_coprod_of_surjective (D := D) (Z := Z) (E := E) _ _ hdim
        ht
  obtain ⟨Φ, h0Φ, hΦW, heq⟩ :=
    exists_partialDiffeomorph_into_manifold hW h0W (hs.mono Set.inter_subset_left) hinv
  obtain ⟨a, ha, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds h0Φ)
  refine ⟨a, ha, Φ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [closedBall_prod_same]
    exact hball
  · intro q hq
    exact (hΦW hq).1.1
  · intro y hy
    have hq := Φ.map_target' hy
    have hmem := (hΦW hq).2
    change r.sheetCoordinates f g (Φ.invFun y) ∈ O at hmem
    rw [heq hq] at hmem
    exact (Φ.right_inv' hy) ▸ hmem
  · intro x hx
    exact (heq hx).symm.trans (r.sheetCoordinates_left f g hzero x)
  · intro z hz
    exact (heq hz).symm.trans (r.sheetCoordinates_right f g z)

theorem exists_clean_simultaneous_sheetChart {E M D Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : D) ∈ U) (h0V : (0 : Z) ∈ V) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) (hzero : g 0 = f 0)
    (hembf : Topology.IsEmbedding (fun x : U => f x))
    (hembg : Topology.IsEmbedding (fun z : V => g z))
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0)))
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ b : ℝ,
      0 < b ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
          Metric.closedBall (0 : D) b ×ˢ Metric.closedBall (0 : Z) b ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ V ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
                  (∀ z, (0, z) ∈ Φ.source → Φ (0, z) = g z) ∧
                    (∀ q ∈ Φ.source, (Φ q ∈ f '' U ↔ q.2 = 0) ∧ (Φ q ∈ g '' V ↔ q.1 = 0)) := by
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hleft, hright⟩ :=
    exists_simultaneous_sheetChart hU hV h0U h0V hf hg hzero hdim ht hO h0O
  have hballU : IsOpen {x : U | (x : D) ∈ Metric.ball 0 a} :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  have hballV : IsOpen {z : V | (z : Z) ∈ Metric.ball 0 a} :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  obtain ⟨A, hA, hpreA⟩ := hembf.isInducing.isOpen_iff.mp hballU
  obtain ⟨B, hB, hpreB⟩ := hembg.isInducing.isOpen_iff.mp hballV
  have h0A : f 0 ∈ A := by
    have hz : (⟨0, h0U⟩ : U) ∈ {x : U | (x : D) ∈ Metric.ball 0 a} := Metric.mem_ball_self ha
    rw [← hpreA] at hz
    exact hz
  have h0B : g 0 ∈ B := by
    have hz : (⟨0, h0V⟩ : V) ∈ {z : V | (z : Z) ∈ Metric.ball 0 a} := Metric.mem_ball_self ha
    rw [← hpreB] at hz
    exact hz
  have hsmallF {x : D} (hx : x ∈ U) (hxA : f x ∈ A) : x ∈ Metric.closedBall 0 a := by
    have hx' : (⟨x, hx⟩ : U) ∈ (fun x : U => f x) ⁻¹' A := hxA
    rw [hpreA] at hx'
    exact Metric.ball_subset_closedBall hx'
  have hsmallG {z : Z} (hz : z ∈ V) (hzB : g z ∈ B) : z ∈ Metric.closedBall 0 a := by
    have hz' : (⟨z, hz⟩ : V) ∈ (fun z : V => g z) ⁻¹' B := hzB
    rw [hpreB] at hz'
    exact Metric.ball_subset_closedBall hz'
  let Ψ := PartialChart.restrictTarget Φ (hA.inter hB)
  have h0Φ : (0, 0) ∈ Φ.source :=
    hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩
  have hcenter : Φ (0, 0) = f 0 := hleft 0 h0Φ
  have h0Ψ : (0, 0) ∈ Ψ.source := by
    refine ⟨h0Φ, ?_⟩
    change Φ (0, 0) ∈ A ∩ B
    rw [hcenter]
    exact ⟨h0A, hzero ▸ h0B⟩
  obtain ⟨b, hb, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ψ.open_source.mem_nhds h0Ψ)
  refine
    ⟨b, hb, Ψ, ?_, fun _ hq => hsource hq.1, fun _ hy => htarget hy.1, (fun x hx => hleft x hx.1),
      (fun z hz => hright z hz.1), ?_⟩
  · rw [closedBall_prod_same]
    exact hball
  · rintro ⟨x, z⟩ hq
    have hAq : Φ (x, z) ∈ A := hq.2.1
    have hBq : Φ (x, z) ∈ B := hq.2.2
    constructor
    · constructor
      · rintro ⟨u, hu, heq⟩
        have huA : f u ∈ A := heq ▸ hAq
        have haxis : (u, 0) ∈ Φ.source := hprod ⟨hsmallF hu huA, Metric.mem_closedBall_self ha.le⟩
        have hpair : (x, z) = (u, 0) :=
          Φ.toPartialEquiv.injOn hq.1 haxis (heq.symm.trans (hleft u haxis).symm)
        exact congrArg Prod.snd hpair
      · intro hz
        change z = 0 at hz
        subst z
        exact ⟨x, (hsource hq.1).1, (hleft x hq.1).symm⟩
    · constructor
      · rintro ⟨v, hv, heq⟩
        have hvB : g v ∈ B := heq ▸ hBq
        have haxis : (0, v) ∈ Φ.source := hprod ⟨Metric.mem_closedBall_self ha.le, hsmallG hv hvB⟩
        have hpair : (x, z) = (0, v) :=
          Φ.toPartialEquiv.injOn hq.1 haxis (heq.symm.trans (hright v haxis).symm)
        exact congrArg Prod.fst hpair
      · intro hx
        change x = 0 at hx
        subst x
        exact ⟨z, (hsource hq.1).2, (hright z hq.1).symm⟩

theorem exists_clean_crossingChart_of_parametrizations {E M D Z N P A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace N] [ChartedSpace D N]
    [TopologicalSpace P] [ChartedSpace Z P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞) (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source) (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ a : ℝ,
      0 < a ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, E) (A × B) M ∞,
          Metric.closedBall (0 : A) a ×ˢ Metric.closedBall (0 : B) a ⊆ Φ.source ∧
            Φ.source ⊆ c.source ×ˢ d.source ∧
              Φ.target ⊆ O ∧
                Φ (0, 0) = F (c 0) ∧
                  (∀ u, (u, 0) ∈ Φ.source → Φ (u, 0) = F (c u)) ∧
                    (∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (d v)) ∧
                      (∀ q ∈ Φ.source,
                        (Φ q ∈ Set.range F ↔ q.2 = 0) ∧ (Φ q ∈ Set.range G ↔ q.1 = 0)) := by
  let f := F ∘ c
  let g := G ∘ d
  have hf : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ f c.source := hF.comp_contMDiffOn c.contMDiffOn_toFun
  have hg : ContMDiffOn 𝓘(ℝ, B) 𝓘(ℝ, E) ∞ g d.source := hG.comp_contMDiffOn d.contMDiffOn_toFun
  have hembf : Topology.IsEmbedding (fun u : c.source => f u) :=
    hembF.comp c.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding
  have hembg : Topology.IsEmbedding (fun v : d.source => g v) :=
    hembG.comp d.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding
  have hdf :
    mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f 0 =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).comp (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, D) c 0) :=
    mfderiv_comp 0 (hF.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) hc0)
  have hdg :
    mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) g 0 =
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0)).comp (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, Z) d 0) :=
    mfderiv_comp 0 (hG.mdifferentiableAt (by simp)) (d.mdifferentiableAt (by simp) hd0)
  have ht' :
    Function.Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) g 0)) := by
    rw [hdf, hdg]
    intro w
    obtain ⟨⟨u, v⟩, huv⟩ := ht w
    obtain ⟨a, ha⟩ := (PartialChart.bijective_mfderiv c hc0).2 u
    obtain ⟨b, hb⟩ := (PartialChart.bijective_mfderiv d hd0).2 v
    refine ⟨(a, b), ?_⟩
    let DF : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)
    let DG : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0)
    let C : A →L[ℝ] D := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, D) c 0
    let Q : B →L[ℝ] Z := mfderiv 𝓘(ℝ, B) 𝓘(ℝ, Z) d 0
    change DF (C a) + DG (Q b) = w
    change C a = u at ha
    change Q b = v at hb
    rw [ha, hb]
    exact huv
  obtain ⟨U, hU, hpreU⟩ := hembF.isInducing.isOpen_iff.mp c.open_target
  obtain ⟨V, hV, hpreV⟩ := hembG.isInducing.isOpen_iff.mp d.open_target
  have hxU : F (c 0) ∈ U := by
    change c 0 ∈ F ⁻¹' U
    rw [hpreU]
    exact c.map_source' hc0
  have hyV : G (d 0) ∈ V := by
    change d 0 ∈ G ⁻¹' V
    rw [hpreV]
    exact d.map_source' hd0
  have hxV : F (c 0) ∈ V := hxy ▸ hyV
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hleft, hright, himages⟩ :=
    exists_clean_simultaneous_sheetChart c.open_source d.open_source hc0 hd0 hf hg hxy hembf hembg
      hdim ht' (hO.inter (hU.inter hV)) ⟨hxO, hxU, hxV⟩
  refine
    ⟨a, ha, Φ, hprod, hsource, fun _ hq => (htarget hq).1,
      hleft 0 (hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩), hleft,
      hright, ?_⟩
  intro q hq
  have hqUV := (htarget (Φ.map_source' hq)).2
  have hrangeF : Φ q ∈ Set.range F ↔ Φ q ∈ f '' c.source := by
    constructor
    · rintro ⟨n, hn⟩
      have hnU : F n ∈ U := hn ▸ hqUV.1
      have hnT : n ∈ c.target := by
        change n ∈ F ⁻¹' U at hnU
        rwa [hpreU] at hnU
      refine ⟨c.invFun n, c.map_target' hnT, ?_⟩
      exact (congrArg F (c.right_inv' hnT)).trans hn
    · rintro ⟨u, _, hu⟩
      exact ⟨c u, hu⟩
  have hrangeG : Φ q ∈ Set.range G ↔ Φ q ∈ g '' d.source := by
    constructor
    · rintro ⟨p, hp⟩
      have hpV : G p ∈ V := hp ▸ hqUV.2
      have hpT : p ∈ d.target := by
        change p ∈ G ⁻¹' V at hpV
        rwa [hpreV] at hpV
      refine ⟨d.invFun p, d.map_target' hpT, ?_⟩
      exact (congrArg G (d.right_inv' hpT)).trans hp
    · rintro ⟨v, _, hv⟩
      exact ⟨d v, hv⟩
  exact ⟨hrangeF.trans (himages q hq).1, hrangeG.trans (himages q hq).2⟩

theorem exists_clean_crossingChart {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G) (x : N) (y : P)
    (hxy : G y = F x) (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {O : Set M} (hO : IsOpen O) (hxO : F x ∈ O) :
    ∃ a : ℝ,
      0 < a ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
          Metric.closedBall (0 : D) a ×ˢ Metric.closedBall (0 : Z) a ⊆ Φ.source ∧
            Φ.source ⊆
                (NativeParametrization.centered (D := D) x).source ×ˢ
                  (NativeParametrization.centered (D := Z) y).source ∧
              Φ.target ⊆ O ∧
                Φ (0, 0) = F x ∧
                  (∀ u,
                      (u, 0) ∈ Φ.source →
                        Φ (u, 0) = F (NativeParametrization.centered (D := D) x u)) ∧
                    (∀ v,
                        (0, v) ∈ Φ.source →
                          Φ (0, v) = G (NativeParametrization.centered (D := Z) y v)) ∧
                      (∀ q ∈ Φ.source,
                        (Φ q ∈ Set.range F ↔ q.2 = 0) ∧ (Φ q ∈ Set.range G ↔ q.1 = 0)) := by
  let c := NativeParametrization.centered (D := D) x
  let d := NativeParametrization.centered (D := Z) y
  have hc0 : (0 : D) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hd0 : (0 : Z) ∈ d.source := NativeParametrization.zero_mem_centered_source y
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hdy : d 0 = y := NativeParametrization.centered_zero y
  have hxy' : G (d 0) = F (c 0) := by rw [hcx, hdy]; exact hxy
  have ht' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))) := by
    rw [hcx, hdy]
    exact ht
  have hxO' : F (c 0) ∈ O := by rw [hcx]; exact hxO
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hcenter, hleft, hright, himages⟩ :=
    exists_clean_crossingChart_of_parametrizations hF hG hembF hembG c d hc0 hd0 hxy' hdim ht' hO
      hxO'
  exact
    ⟨a, ha, Φ, hprod, hsource, htarget, hcenter.trans (congrArg F hcx), hleft, hright, himages⟩

theorem exists_isolating_crossing_neighborhood {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G) (x : N) (y : P)
    (hxy : G y = F x) (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) :
    ∃ O : Set M, IsOpen O ∧ F x ∈ O ∧ O ∩ (Set.range F ∩ Set.range G) = {F x} := by
  obtain ⟨a, ha, Φ, hprod, -, -, hcenter, -, -, himages⟩ :=
    exists_clean_crossingChart hF hG hembF hembG x y hxy hdim ht isOpen_univ (Set.mem_univ _)
  have h0Φ : (0, 0) ∈ Φ.source :=
    hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩
  have hFx : F x ∈ Φ.target := hcenter ▸ Φ.map_source' h0Φ
  refine ⟨Φ.target, Φ.open_target, hFx, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, hwF, hwG⟩
    let q := Φ.invFun w
    have hq : q ∈ Φ.source := Φ.map_target' hw
    have heq : Φ q = w := Φ.right_inv' hw
    have hqF : Φ q ∈ Set.range F := heq.symm ▸ hwF
    have hqG : Φ q ∈ Set.range G := heq.symm ▸ hwG
    have hq0 : q = (0, 0) := Prod.ext ((himages q hq).2.mp hqG) ((himages q hq).1.mp hqF)
    exact Set.mem_singleton_iff.mpr (heq.symm.trans ((congrArg Φ hq0).trans hcenter))
  · intro hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact ⟨hFx, ⟨x, rfl⟩, ⟨y, hxy⟩⟩

theorem isDiscrete_transverse_intersections {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      ∀ x y,
        G y = F x →
          Function.Surjective
            ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) :
    IsDiscrete (Set.range F ∩ Set.range G) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro z ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
  obtain ⟨O, hO, -, heq⟩ :=
    exists_isolating_crossing_neighborhood hF hG hembF hembG x y hxy hdim (ht x y hxy)
  exact ⟨O, hO, heq⟩

theorem finite_transverse_intersections {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] [CompactSpace N] [CompactSpace P] {F : N → M}
    {G : P → M} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hinjF : Function.Injective F) (hinjG : Function.Injective G)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      ∀ x y,
        G y = F x →
          Function.Surjective
            ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) :
    (Set.range F ∩ Set.range G).Finite := by
  have hembF := (hF.continuous.isClosedEmbedding hinjF).isEmbedding
  have hembG := (hG.continuous.isClosedEmbedding hinjG).isEmbedding
  exact
    ((isCompact_range hF.continuous).inter_right (isCompact_range hG.continuous).isClosed).finite
      (isDiscrete_transverse_intersections hF hG hembF hembG hdim ht)

def SphereBoundary.definingFunction {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ :=
  ‖x‖ ^ 2 - 1

theorem SphereBoundary.contDiff_definingFunction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : ContDiff ℝ ∞ (definingFunction (E := E)) :=
  (contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const

theorem SphereBoundary.definingFunction_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    (x : E) : definingFunction x = 0 ↔ x ∈ Metric.sphere (0 : E) 1 := by
  simp only [definingFunction, Metric.mem_sphere, dist_zero_right]
  constructor
  · intro h
    nlinarith [norm_nonneg x]
  · intro h
    rw [h]
    norm_num

theorem SphereBoundary.fderiv_definingFunction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) : fderiv ℝ (definingFunction (E := E)) x = 2 • innerSL ℝ x :=
  ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1).fderiv

theorem SphereBoundary.fderiv_definingFunction_eq_zero_iff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x v : E) :
    fderiv ℝ (definingFunction (E := E)) x v = 0 ↔ Inner.inner ℝ x v = 0 := by
  rw [fderiv_definingFunction]
  rw [two_smul, add_apply]
  change Inner.inner ℝ x v + Inner.inner ℝ x v = 0 ↔ Inner.inner ℝ x v = 0
  constructor
  · intro h
    linarith
  · intro h
    rw [h, add_zero]

theorem SphereBoundary.common_kernel_of_immersive_sphere_extension {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {γ : Metric.sphere (0 : E) 1 → N}
    (hext : ∀ x : Metric.sphere (0 : E) 1, f x.1 = γ x)
    (hγ : ∀ x, Function.Injective (mfderiv (𝓡 n) J γ x)) :
    ∀ y,
      definingFunction y = 0 →
        ∀ v : E,
          mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ (definingFunction (E := E)) y v = 0 → v = 0 := by
  intro y hy v hfv hρv
  let x : Metric.sphere (0 : E) 1 := ⟨y, (definingFunction_eq_zero_iff y).mp hy⟩
  have hinner : Inner.inner ℝ y v = 0 := (fderiv_definingFunction_eq_zero_iff y v).mp hρv
  have hrange : v ∈ (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : E) 1 → E) x).range := by
    rw [range_mvfderiv_subtypeVal]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hinner
  obtain ⟨w, hw⟩ := hrange
  change (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) w = v at hw
  have hextfun : (f ∘ (Subtype.val : Metric.sphere (0 : E) 1 → E)) = γ := funext hext
  have hchain :
    mfderiv (𝓡 n) J γ x =
      (mfderiv 𝓘(ℝ, E) J f y).comp
        (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) := by
    rw [← hextfun,
      mfderiv_comp x (hf.mdifferentiableAt (by simp))
        ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).mdifferentiableAt (by simp))]
  have hγzero : mfderiv (𝓡 n) J γ x w = 0 := by
    rw [hchain]
    change
      (mfderiv 𝓘(ℝ, E) J f y)
          ((mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) w) =
        0
    rw [hw]
    exact hfv
  have hwzero : w = 0 := (hγ x) (by simpa only [map_zero] using hγzero)
  rw [hwzero, map_zero] at hw
  exact hw.symm

def SphereNormalCoordinates.inclusionDerivative {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) : EuclideanSpace ℝ (Fin n) →L[ℝ] V :=
  mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) x

theorem SphereNormalCoordinates.inner_inclusionDerivative_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) (u : EuclideanSpace ℝ (Fin n)) :
    Inner.inner ℝ (x : V) (inclusionDerivative x u) = 0 := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← range_mvfderiv_subtypeVal (n := n) x]
  exact ⟨u, rfl⟩

theorem SphereNormalCoordinates.inner_self_eq_one {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (x : Metric.sphere (0 : V) 1) : Inner.inner ℝ (x : V) x = 1 := by
  have hx : ‖(x : V)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  rw [real_inner_self_eq_norm_sq, hx, one_pow]

def SphereNormalCoordinates.normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (x : V)).coprod ((inclusionDerivative x).comp A.inverse)

theorem SphereNormalCoordinates.normalFrame_apply {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (z : ℝ × N) :
    normalFrame x A z = z.1 • (x : V) + inclusionDerivative x (A.inverse z.2) :=
  rfl

theorem SphereNormalCoordinates.inner_normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (z : ℝ × N) :
    Inner.inner ℝ (x : V) (normalFrame x A z) = z.1 := by
  rw [normalFrame_apply, inner_add_right, inner_smul_right, inner_self_eq_one,
    inner_inclusionDerivative_zero, mul_one, add_zero]

theorem SphereNormalCoordinates.bijective_normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    Function.Bijective (normalFrame x A) := by
  constructor
  · intro z w hzw
    have hfst : z.1 = w.1 := by
      simpa only [inner_normalFrame] using congrArg (fun v : V => Inner.inner ℝ (x : V) v) hzw
    have ht : inclusionDerivative x (A.inverse z.2) = inclusionDerivative x (A.inverse w.2) := by
      rw [normalFrame_apply, normalFrame_apply, hfst] at hzw
      exact add_left_cancel hzw
    have hJ : Function.Injective (inclusionDerivative (n := n) x) :=
      injective_mvfderiv_subtypeVal_sphere x
    exact Prod.ext hfst (hA.inverse.injective (hJ ht))
  · intro v
    have ht : v - Inner.inner ℝ (x : V) v • (x : V) ∈ (inclusionDerivative (n := n) x).range := by
      change
        v - Inner.inner ℝ (x : V) v • (x : V) ∈
          (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) x).range
      rw [range_mvfderiv_subtypeVal]
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [inner_sub_right, inner_smul_right, inner_self_eq_one, mul_one, sub_self]
    obtain ⟨u, hu⟩ := ht
    change inclusionDerivative x u = v - Inner.inner ℝ (x : V) v • (x : V) at hu
    refine ⟨(Inner.inner ℝ (x : V) v, A u), ?_⟩
    rw [normalFrame_apply, hA.inverse_apply_self, hu]
    abel

def SphereNormalCoordinates.normalJacobian {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V) (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) : ℝ :=
  ((normalFrame x A).comp j.symm.toContinuousLinearMap).det

theorem SphereNormalCoordinates.normalJacobian_ne_zero {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] [FiniteDimensional ℝ V] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    normalJacobian j x A ≠ 0 := by
  apply (RegularValues.bijective_iff_det_ne_zero _).mp
  exact (bijective_normalFrame x A hA).comp j.symm.bijective

theorem SphereNormalCoordinates.normalJacobian_change_normal_model {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] {N' : Type*} [NormedAddCommGroup N']
    [NormedSpace ℝ N'] (r : (ℝ × N) ≃L[ℝ] V) (j : N' ≃L[ℝ] N) (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    normalJacobian ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) j).trans r)
        x (j.symm.toContinuousLinearMap.comp A) =
      normalJacobian r x A := by
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] N' := j.symm.toContinuousLinearMap.comp A
  have hj : j.symm.toContinuousLinearMap.IsInvertible := ⟨j.symm, rfl⟩
  have hB : B.IsInvertible := hj.comp hA
  have hinv (z : N) : B.inverse (j.symm z) = A.inverse z := by
    apply hB.injective
    rw [hB.self_apply_inverse]
    change j.symm z = j.symm (A (A.inverse z))
    rw [hA.self_apply_inverse]
  unfold normalJacobian
  apply congrArg ContinuousLinearMap.det
  apply ContinuousLinearMap.ext
  intro v
  change
    (r.symm v).1 • (x : V) + inclusionDerivative x (B.inverse (j.symm (r.symm v).2)) =
      (r.symm v).1 • (x : V) + inclusionDerivative x (A.inverse (r.symm v).2)
  rw [hinv]

def ManifoldMorse.MorseSurgeryData.beltNormalReference {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m) :
    (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hdim, Nat.add_comm])

def ManifoldMorse.MorseSurgeryData.beltIntersectionJacobian {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m) : ℝ :=
  letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  SphereNormalCoordinates.normalJacobian j x
    (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x)

def ManifoldMorse.MorseSurgeryData.beltIntersectionSign {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m) : SignType :=
  SignType.sign (d.beltIntersectionJacobian m j g x)

def ManifoldMorse.MorseSurgeryData.beltIntersectionPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) : Set (Hemisphere.Sphere m) :=
  g ⁻¹' Set.range d.surgery.beltSphere

theorem ManifoldMorse.MorseSurgeryData.beltIntersectionSigns_opposite_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x y : Hemisphere.Sphere m) :
    d.beltIntersectionSign m j g x * d.beltIntersectionSign m j g y = -1 ↔
      d.beltIntersectionJacobian m j g x * d.beltIntersectionJacobian m j g y < 0 := by
  unfold beltIntersectionSign
  rw [← sign_mul, sign_eq_neg_one_iff]

def ManifoldMorse.MorseSurgeryData.beltIntersectionCount {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel)
    (hfin : (d.beltIntersectionPoints m g).Finite) : ℤ :=
  ∑ x ∈ hfin.toFinset, (d.beltIntersectionSign m j g x : ℤ)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.beltIntersectionJacobian_ne_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g → d.beltIntersectionJacobian m j g x ≠ 0 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  exact SphereNormalCoordinates.normalJacobian_ne_zero j x A hAi

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.beltIntersectionSign_unit {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        d.beltIntersectionSign m j g x = 1 ∨ d.beltIntersectionSign m j g x = -1 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx
  have hn : d.beltIntersectionSign m j g x ≠ 0 :=
    sign_ne_zero.mpr (d.beltIntersectionJacobian_ne_zero hf n m hdim j g hg ht x hx)
  rcases SignType.trichotomy (d.beltIntersectionSign m j g x) with h | h | h
  · exact Or.inr h
  · exact (hn h).elim
  · exact Or.inl h

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.finite_beltIntersectionPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [T2Space M] [CompactSpace M] (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      (d.beltIntersectionPoints m g).Finite := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro hg hinj ht
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
    have hp : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1 := Fact.out
    have hs := d.chart.finrank_negative_add_positive
    omega
  have hfin :=
    finite_transverse_intersections hg (d.belt_smooth hf n) hinj
      d.belt_isClosedEmbedding.injective hdim' (fun x y hxy => ht x y hxy)
  have hpre : (g ⁻¹' (Set.range g ∩ Set.range d.surgery.beltSphere)).Finite :=
    hfin.preimage hinj.injOn
  exact hpre.subset (fun x hx => ⟨⟨x, rfl⟩, hx⟩)

def TransverseCoordinates.normalCoordinate {D B E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) : M → B :=
  Prod.snd ∘ Φ.symm

theorem TransverseCoordinates.contMDiffOn_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, B) ∞ (normalCoordinate Φ) Φ.target := by
  have hs : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
  exact hs.comp_contMDiffOn Φ.contMDiffOn_invFun

theorem TransverseCoordinates.mfderiv_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {p : M} (hp : p ∈ Φ.target) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) p =
      (ContinuousLinearMap.snd ℝ D B).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm p) := by
  have hs : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
  have hd :
    mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, B) (Prod.snd : D × B → B) (Φ.symm p) =
      ContinuousLinearMap.snd ℝ D B := by
    rw [mfderiv_eq_fderiv]
    exact (ContinuousLinearMap.snd ℝ D B).fderiv
  rw [normalCoordinate,
    mfderiv_comp p (hs.mdifferentiableAt (by simp)) (Φ.symm.mdifferentiableAt (by simp) hp), hd]
  rfl

theorem TransverseCoordinates.surjective_mfderiv_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {p : M} (hp : p ∈ Φ.target) :
    Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) p) := by
  rw [mfderiv_normalCoordinate Φ hp]
  exact
    (show Function.Surjective (ContinuousLinearMap.snd ℝ D B) from fun w => ⟨(0, w), rfl⟩).comp
      (PartialChart.bijective_mfderiv Φ.symm hp).2

theorem TransverseCoordinates.normalCoordinate_sheet_eventually_zero {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {N : Type*} [TopologicalSpace N]
    {F : N → M} (hF : Continuous F) (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) {x : N}
    (hx : F x ∈ Φ.target) : (normalCoordinate Φ ∘ F) =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hF.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)] with y hy
  have hq : Φ.invFun (F y) ∈ Φ.source := Φ.map_target' hy
  exact (hclean _ hq).mp ⟨y, (Φ.right_inv' hy).symm⟩

theorem TransverseCoordinates.normalDerivative_comp_sheet_eq_zero {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {G N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace N] [ChartedSpace G N] {F : N → M}
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0)
    {x : N} (hx : F x ∈ Φ.target) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (F x)).comp (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x) = 0 :=
  by
  have heq := normalCoordinate_sheet_eventually_zero Φ hF.continuous hclean hx
  have hzero : mfderiv 𝓘(ℝ, G) 𝓘(ℝ, B) (normalCoordinate Φ ∘ F) x = 0 := by
    rw [heq.mfderiv_eq]
    simp only [mfderiv_const]
    rfl
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hx)
  rw [mfderiv_comp x (hnormal.mdifferentiableAt (by simp))
      (hF.mdifferentiableAt (by simp))] at hzero
  exact hzero

theorem StripCoordinates.hasDerivAt_horizontalSlice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : (ℝ × ℝ) → E} {t s : ℝ} (hF : DifferentiableAt ℝ F (t, s)) :
    HasDerivAt (fun u : ℝ => F (u, s)) (fderiv ℝ F (t, s) (1, 0)) t := by
  have hi : HasDerivAt (fun u : ℝ => (u, s)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t s)
  exact hF.hasFDerivAt.comp_hasDerivAt t hi

abbrev StripCoordinates.Space (A B : Type*) :=
  (ℝ × A) × B

def StripCoordinates.center {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    (t : ℝ) : Space A B :=
  ((t, 0), 0)

def StripCoordinates.model {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] (v : ℝ → B) (p : ℝ × ℝ) : Space A B :=
  ((p.1, 0), p.2 • v p.1)

def StripCoordinates.normalDerivative {A B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (F : (ℝ × ℝ) → Space A B) (t : ℝ) : B :=
  fderiv ℝ (fun p => (F p).2) (t, 0) (0, 1)

def StripCoordinates.blend {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (v : ℝ → B) (F₀ F₁ : (ℝ × ℝ) → Space A B)
    (β₀ β₁ : ℝ → ℝ) (p : ℝ × ℝ) : Space A B :=
  model v p + β₀ p.1 • (F₀ p - model v p) + β₁ p.1 • (F₁ p - model v p)

theorem StripCoordinates.contDiff_model {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (model (A := A) v) :=
  (contDiff_fst.prodMk contDiff_const).prodMk (contDiff_snd.smul (hv.comp contDiff_fst))

theorem StripCoordinates.contDiff_blend {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁) :
    ContDiff ℝ ∞ (blend v F₀ F₁ β₀ β₁) :=
  ((contDiff_model hv).add ((hβ₀.comp contDiff_fst).smul (hF₀.sub (contDiff_model hv)))).add
    ((hβ₁.comp contDiff_fst).smul (hF₁.sub (contDiff_model hv)))

theorem StripCoordinates.model_zero {A B : Type*} [NormedAddCommGroup A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (v : ℝ → B) (t : ℝ) :
    model (A := A) v (t, 0) = StripCoordinates.center t := by
  simp only [model, StripCoordinates.center, zero_smul]

theorem StripCoordinates.blend_zero {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B} {F₀ F₁ : (ℝ × ℝ) → Space A B}
    {β₀ β₁ : ℝ → ℝ} (h₀ : ∀ t, β₀ t ≠ 0 → F₀ (t, 0) = StripCoordinates.center t)
    (h₁ : ∀ t, β₁ t ≠ 0 → F₁ (t, 0) = StripCoordinates.center t) (t : ℝ) :
    blend v F₀ F₁ β₀ β₁ (t, 0) = StripCoordinates.center t := by
  have hterm₀ : β₀ t • (F₀ (t, 0) - model v (t, 0)) = 0 := by
    by_cases h : β₀ t = 0
    · rw [h, zero_smul]
    · rw [h₀ t h, model_zero, sub_self, smul_zero]
  have hterm₁ : β₁ t • (F₁ (t, 0) - model v (t, 0)) = 0 := by
    by_cases h : β₁ t = 0
    · rw [h, zero_smul]
    · rw [h₁ t h, model_zero, sub_self, smul_zero]
  change
    model v (t, 0) + β₀ t • (F₀ (t, 0) - model v (t, 0)) + β₁ t • (F₁ (t, 0) - model v (t, 0)) =
      StripCoordinates.center t
  rw [hterm₀, hterm₁, add_zero, add_zero, model_zero]

theorem StripCoordinates.blend_eq_left {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} {p : ℝ × ℝ} (h₀ : β₀ p.1 = 1)
    (h₁ : β₁ p.1 = 0) : blend v F₀ F₁ β₀ β₁ p = F₀ p := by
  simp only [blend, h₀, h₁, one_smul, zero_smul, add_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem StripCoordinates.blend_eq_right {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} {p : ℝ × ℝ} (h₀ : β₀ p.1 = 0)
    (h₁ : β₁ p.1 = 1) : blend v F₀ F₁ β₀ β₁ p = F₁ p := by
  simp only [blend, h₀, h₁, one_smul, zero_smul, add_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem StripCoordinates.normalDerivative_blend {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (h₀ : ∀ t, β₀ t ≠ 0 → normalDerivative F₀ t = v t)
    (h₁ : ∀ t, β₁ t ≠ 0 → normalDerivative F₁ t = v t) (t : ℝ) :
    normalDerivative (blend v F₀ F₁ β₀ β₁) t = v t := by
  have hm : HasDerivAt (fun s : ℝ => s • v t) (v t) 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const (v t)
  have hd₀ :=
    hasDerivAt_verticalSlice (t := t) (s := 0) (hF₀.snd.contDiffAt.differentiableAt (by simp))
  have hd₁ :=
    hasDerivAt_verticalSlice (t := t) (s := 0) (hF₁.snd.contDiffAt.differentiableAt (by simp))
  have hterm₀ : β₀ t • (normalDerivative F₀ t - v t) = 0 := by
    by_cases h : β₀ t = 0
    · rw [h, zero_smul]
    · rw [h₀ t h, sub_self, smul_zero]
  have hterm₁ : β₁ t • (normalDerivative F₁ t - v t) = 0 := by
    by_cases h : β₁ t = 0
    · rw [h, zero_smul]
    · rw [h₁ t h, sub_self, smul_zero]
  have hblend :
    HasDerivAt (fun s : ℝ => (blend v F₀ F₁ β₀ β₁ (t, s)).2)
      (v t + β₀ t • (normalDerivative F₀ t - v t) + β₁ t • (normalDerivative F₁ t - v t)) 0 :=
    HasDerivAt.add (HasDerivAt.add hm (HasDerivAt.const_smul (β₀ t) (HasDerivAt.sub hd₀ hm)))
      (HasDerivAt.const_smul (β₁ t) (HasDerivAt.sub hd₁ hm))
  have hblend' : HasDerivAt (fun s : ℝ => (blend v F₀ F₁ β₀ β₁ (t, s)).2) (v t) 0 := by
    simpa only [hterm₀, hterm₁, add_zero] using hblend
  exact
    (hasDerivAt_verticalSlice
          ((contDiff_blend hv hF₀ hF₁ hβ₀ hβ₁).snd.contDiffAt.differentiableAt (by simp))).unique
      hblend'

structure StripNormalData (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (S : Set M) (k : (ℝ × ℝ) → M) where
  chart :
    PartialDiffeomorph 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) (StripCoordinates.Space A B) M ∞
  line : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) chart.source
  sheet : ∀ q ∈ chart.source, chart q ∈ S ↔ q.2 = 0
  center : ∀ t, k (t, 0) = chart (StripCoordinates.center t)
  normal_nonzero :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (TransverseCoordinates.normalCoordinate chart ∘ k) (t, 0) (0, 1) ≠ 0

theorem StripCoordinates.horizontal_derivative_of_center {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : (ℝ × ℝ) → Space A B} {t : ℝ} (hF : DifferentiableAt ℝ F (t, 0))
    (hc : ∀ s, F (s, 0) = StripCoordinates.center s) :
    fderiv ℝ F (t, 0) (1, 0) = StripCoordinates.center 1 := by
  have hd := hasDerivAt_horizontalSlice hF
  have heq : (fun s : ℝ => F (s, 0)) = StripCoordinates.center := funext hc
  rw [heq] at hd
  have hcenter :
    HasDerivAt (StripCoordinates.center : ℝ → Space A B) (StripCoordinates.center 1)
      t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))).prodMk (hasDerivAt_const t (0 : B))
  exact hd.unique hcenter

theorem StripCoordinates.horizontal_derivative_of_center_germ {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : (ℝ × ℝ) → Space A B} {t : ℝ} (hF : DifferentiableAt ℝ F (t, 0))
    (hc : (fun s : ℝ => F (s, 0)) =ᶠ[𝓝 t] StripCoordinates.center) :
    fderiv ℝ F (t, 0) (1, 0) = StripCoordinates.center 1 := by
  have hd := hasDerivAt_horizontalSlice hF
  have hcenter :
    HasDerivAt (StripCoordinates.center : ℝ → Space A B) (StripCoordinates.center 1)
      t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))).prodMk (hasDerivAt_const t (0 : B))
  exact hd.unique (hcenter.congr_of_eventuallyEq hc)

theorem StripCoordinates.normalDerivative_eq_snd_fderiv {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) : normalDerivative F t = (fderiv ℝ F (t, 0) (0, 1)).2 := by
  have hd := hF.hasFDerivAt.snd
  rw [normalDerivative, hd.fderiv]
  rfl

theorem StripCoordinates.injective_of_horizontal_and_normal {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : (ℝ × ℝ) →L[ℝ] Space A B) (hh : L (1, 0) = StripCoordinates.center 1)
    (hn : (L (0, 1)).2 ≠ 0) : Function.Injective L := by
  have hker : ∀ p : ℝ × ℝ, L p = 0 → p = 0 := by
    rintro ⟨a, b⟩ hp
    have hsplit : (a, b) = a • ((1 : ℝ), 0) + b • (0, 1) := by ext <;> simp
    rw [hsplit, map_add, map_smul, map_smul, hh] at hp
    have hb0 : b • (L (0, 1)).2 = 0 := by
      simpa [StripCoordinates.center] using congrArg Prod.snd hp
    have hb : b = 0 := (smul_eq_zero.mp hb0).resolve_right hn
    subst b
    have ha : a = 0 := by
      simpa [StripCoordinates.center] using congrArg (fun q : Space A B => q.1.1) hp
    subst a
    rfl
  intro p q hpq
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hpq, sub_self]

theorem StripCoordinates.injective_fderiv_at_center {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) (hc : ∀ s, F (s, 0) = StripCoordinates.center s)
    (hn : normalDerivative F t ≠ 0) : Function.Injective (fderiv ℝ F (t, 0)) := by
  apply
    injective_of_horizontal_and_normal (fderiv ℝ F (t, 0)) (horizontal_derivative_of_center hF hc)
  rwa [← normalDerivative_eq_snd_fderiv hF]

def StripCoordinates.sheetTransverseInclusion {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] : A →L[ℝ] Space A B :=
  (ContinuousLinearMap.inl ℝ (ℝ × A) B).comp (ContinuousLinearMap.inr ℝ ℝ A)

theorem StripCoordinates.sheetTransverseInclusion_apply {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (a : A) :
    (sheetTransverseInclusion : A →L[ℝ] Space A B) a = ((0, a), 0) :=
  rfl

theorem StripCoordinates.sheetTransverse_eq_strip_iff {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (L : (ℝ × ℝ) →L[ℝ] Space A B)
    (hh : L (1, 0) = StripCoordinates.center 1) (hn : (L (0, 1)).2 ≠ 0) (a : A)
    (p : ℝ × ℝ) : sheetTransverseInclusion a = L p ↔ a = 0 ∧ p = 0 := by
  constructor
  · intro heq
    have hsplit : p = p.1 • ((1 : ℝ), 0) + p.2 • (0, 1) := by ext <;> simp
    have hexp : L p = p.1 • StripCoordinates.center 1 + p.2 • L (0, 1) := by
      conv_lhs => rw [hsplit]
      rw [map_add, map_smul, map_smul, hh]
    rw [hexp] at heq
    have hp2zero : p.2 • (L (0, 1)).2 = 0 := by
      simpa [sheetTransverseInclusion_apply, StripCoordinates.center] using
        (congrArg Prod.snd heq).symm
    have hp2 : p.2 = 0 := (smul_eq_zero.mp hp2zero).resolve_right hn
    rw [hp2, zero_smul, add_zero] at heq
    have hp1 : p.1 = 0 := by
      simpa [sheetTransverseInclusion_apply, StripCoordinates.center] using
        (congrArg (fun q : Space A B => q.1.1) heq).symm
    have ha : a = 0 := by
      simpa [sheetTransverseInclusion_apply, StripCoordinates.center] using
        congrArg (fun q : Space A B => q.1.2) heq
    exact ⟨ha, Prod.ext hp1 hp2⟩
  · rintro ⟨rfl, rfl⟩
    rw [map_zero, map_zero]

theorem StripCoordinates.injective_sheetTransverse_normalQuotient {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : (ℝ × ℝ) →L[ℝ] Space A B) (Q : Space A B →L[ℝ] Z)
    (hh : L (1, 0) = StripCoordinates.center 1) (hn : (L (0, 1)).2 ≠ 0)
    (hker : Q.ker = L.range) : Function.Injective (Q.comp sheetTransverseInclusion) := by
  have hz : ∀ a : A, Q (sheetTransverseInclusion a) = 0 → a = 0 := by
    intro a ha
    have hmem : sheetTransverseInclusion a ∈ L.range := by
      rw [← hker]
      exact ha
    obtain ⟨p, hp⟩ := hmem
    exact ((sheetTransverse_eq_strip_iff L hh hn a p).mp hp.symm).1
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  change (Q.comp sheetTransverseInclusion) (a - b) = 0
  rw [map_sub, hab, sub_self]

theorem StripCoordinates.ker_comp_eq_range_of_injective {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : Space A B →L[ℝ] V) (L : (ℝ × ℝ) →L[ℝ] Space A B) (Q : V →L[ℝ] Z)
    (hT : Function.Injective T) (hker : Q.ker = (T.comp L).range) : (Q.comp T).ker = L.range := by
  ext v
  constructor
  · intro hv
    have hmem : T v ∈ (T.comp L).range := by
      rw [← hker]
      exact hv
    obtain ⟨p, hp⟩ := hmem
    exact ⟨p, hT hp⟩
  · rintro ⟨p, rfl⟩
    have hmem : T (L p) ∈ Q.ker := by
      rw [hker]
      exact ⟨p, rfl⟩
    exact hmem

def StripNormalData.coordinateMap {A B E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) : (ℝ × ℝ) → StripCoordinates.Space A B :=
  d.chart.symm ∘ k

theorem StripNormalData.center_mem_target {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    k (t, 0) ∈ d.chart.target := by
  rw [d.center t]
  exact d.chart.map_source' (d.line ht)

theorem StripNormalData.coordinate_center_germ {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.coordinateMap (s, 0)) =ᶠ[𝓝 t] StripCoordinates.center := by
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  filter_upwards [hc.continuousAt.preimage_mem_nhds
      (d.chart.open_source.mem_nhds (d.line ht))] with
    s hs
  change d.chart.invFun (k (s, 0)) = StripCoordinates.center s
  rw [d.center s, d.chart.left_inv' hs]

theorem StripNormalData.coordinate_center {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.coordinateMap (t, 0) = StripCoordinates.center t :=
  (d.coordinate_center_germ ht).eq_of_nhds

theorem StripNormalData.contDiffAt_coordinateMap {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) : ContDiffAt ℝ ∞ d.coordinateMap (t, 0) :=
  ((d.chart.contMDiffOn_invFun.contMDiffAt
          (d.chart.open_target.mem_nhds (d.center_mem_target ht))).comp
      (t, 0) hk).contDiffAt

theorem StripNormalData.horizontal_coordinateDerivative {A B E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    fderiv ℝ d.coordinateMap (t, 0) (1, 0) = StripCoordinates.center 1 :=
  StripCoordinates.horizontal_derivative_of_center_germ
    ((d.contDiffAt_coordinateMap ht hk).differentiableAt (by simp)) (d.coordinate_center_germ ht)

theorem StripNormalData.normal_coordinateDerivative_nonzero {A B E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    (fderiv ℝ d.coordinateMap (t, 0) (0, 1)).2 ≠ 0 := by
  rw [←
    StripCoordinates.normalDerivative_eq_snd_fderiv
      ((d.contDiffAt_coordinateMap ht hk).differentiableAt (by simp))]
  exact d.normal_nonzero t ht

theorem StripNormalData.native_derivative_factor {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0) =
      (mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
            (StripCoordinates.center t)).comp
        (fderiv ℝ d.coordinateMap (t, 0)) := by
  have hcoords := d.contDiffAt_coordinateMap ht hk
  have heq : (d.chart ∘ d.coordinateMap) =ᶠ[𝓝 (t, 0)] k := by
    filter_upwards [hk.continuousAt.preimage_mem_nhds
        (d.chart.open_target.mem_nhds (d.center_mem_target ht))] with
      p hp
    change d.chart (d.chart.invFun (k p)) = k p
    exact d.chart.right_inv' hp
  have hcsource : d.coordinateMap (t, 0) ∈ d.chart.source := by
    rw [d.coordinate_center ht]
    exact d.line ht
  rw [← heq.mfderiv_eq,
    mfderiv_comp (t, 0) (d.chart.mdifferentiableAt (by simp) hcsource)
      (hcoords.contMDiffAt.mdifferentiableAt (by simp)),
    d.coordinate_center ht, mfderiv_eq_fderiv]
  rfl

theorem TransverseCoordinates.mfderiv_zero_section {D B E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {f : D → M}
    (hzero : ∀ x, Φ (x, 0) = f x) {x : D} (hx : (x, 0) ∈ Φ.source) :
    mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x =
      (mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, E) Φ (x, 0)).comp (ContinuousLinearMap.inl ℝ D B) := by
  have heq : f = Φ ∘ (ContinuousLinearMap.inl ℝ D B) := funext (fun y => (hzero y).symm)
  have hinl : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, D × B) ∞ (ContinuousLinearMap.inl ℝ D B) :=
    (ContinuousLinearMap.inl ℝ D B).contDiff.contMDiff
  rw [heq, mfderiv_comp x (Φ.mdifferentiableAt (by simp) hx) (hinl.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, (ContinuousLinearMap.inl ℝ D B).fderiv]
  rfl

theorem TransverseCoordinates.ker_normalDerivative_eq_range_zero_section {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {f : D → M}
    (hzero : ∀ x, Φ (x, 0) = f x) {x : D} (hx : (x, 0) ∈ Φ.source) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (f x)).ker =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x).range := by
  let L : (D × B) →L[ℝ] E := mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, E) Φ (x, 0)
  let R : E →L[ℝ] (D × B) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm (Φ (x, 0))
  have hdiff : Φ.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, D × B) 𝓘(ℝ, E) :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  have hRL : R.comp L = ContinuousLinearMap.id ℝ (D × B) := hdiff.symm_comp_deriv hx
  have hRL_apply (q : D × B) : R (L q) = q := by
    change (R.comp L) q = q
    rw [hRL]
    rfl
  have hsurj : Function.Surjective L := (PartialChart.bijective_mfderiv Φ hx).2
  have hnormal :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (f x) = (ContinuousLinearMap.snd ℝ D B).comp R :=
    by
    rw [← hzero x, mfderiv_normalCoordinate Φ (Φ.map_source' hx)]
    rfl
  rw [hnormal, mfderiv_zero_section Φ hzero hx]
  ext v
  constructor
  · intro hv
    obtain ⟨⟨a, b⟩, hab⟩ := hsurj v
    have hb : b = 0 := by
      change (R v).2 = 0 at hv
      rw [← hab, hRL_apply] at hv
      exact hv
    subst b
    exact ⟨a, hab⟩
  · rintro ⟨a, rfl⟩
    change (R (L (a, 0))).2 = 0
    rw [hRL_apply]

def StripNormalData.normalFrame {A B Z E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) : A →L[ℝ] Z :=
  (fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
        (StripCoordinates.center t)).comp
    StripCoordinates.sheetTransverseInclusion

theorem StripNormalData.contDiffOn_normalFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.normalFrame Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have hnormal :=
    (TransverseCoordinates.contMDiffOn_normalCoordinate Ψ).contMDiffAt
      (Ψ.open_target.mem_nhds ht.2)
  have hchart := d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1)
  have htransition :
    ContDiffAt ℝ ∞ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
      (StripCoordinates.center t) :=
    (hnormal.comp (StripCoordinates.center t) hchart).contDiffAt
  have hcenter :
    ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  exact
    (((htransition.fderiv_right (by simp)).comp t hcenter.contDiffAt).clm_comp
        contDiffAt_const).contDiffWithinAt

theorem StripNormalData.exists_open_normalFrame_domain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame Ψ) U := by
  have hcenter :
    Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hW : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  refine
    ⟨StripCoordinates.center ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target),
      hW.preimage hcenter, fun t ht => ⟨d.line ht, htarget t ht⟩, ?_⟩
  exact d.contDiffOn_normalFrame Ψ

theorem StripNormalData.injective_normalFrame_of_strip_germ {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0))
    {f : (ℝ × ℝ) → M} (hzero : ∀ x, Ψ (x, 0) = f x) {p : ℝ × ℝ} (hp : (p, 0) ∈ Ψ.source)
    {c : (ℝ × ℝ) → (ℝ × ℝ)} (hc : ContDiffAt ℝ ∞ c p) (hcp : c p = (t, 0))
    (hcs : Function.Surjective (fderiv ℝ c p)) (hgerm : f =ᶠ[𝓝 p] k ∘ c) :
    Function.Injective (d.normalFrame Ψ t) := by
  let T : StripCoordinates.Space A B →L[ℝ] E :=
    mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
      (StripCoordinates.center t)
  let L : (ℝ × ℝ) →L[ℝ] StripCoordinates.Space A B := fderiv ℝ d.coordinateMap (t, 0)
  let Q : E →L[ℝ] Z :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ) (f p)
  let J : (ℝ × ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p
  let K : (ℝ × ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)
  have hfp : f p = d.chart (StripCoordinates.center t) := by
    have heq := hgerm.eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [hcp, d.center t] at heq
    exact heq
  have htarget : f p ∈ Ψ.target := by
    have h := Ψ.map_source' hp
    rwa [hzero p] at h
  have hk' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (c p) := by
    rw [hcp]
    exact hk
  have hdf :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p =
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)).comp (fderiv ℝ c p) := by
    rw [hgerm.mfderiv_eq,
      mfderiv_comp p (hk'.mdifferentiableAt (by simp))
        (hc.contMDiffAt.mdifferentiableAt (by simp)),
      hcp, mfderiv_eq_fderiv]
    rfl
  have hker : Q.ker = (T.comp L).range := by
    have h1 : Q.ker = J.range :=
      TransverseCoordinates.ker_normalDerivative_eq_range_zero_section Ψ hzero hp
    have h2 : J.range = K.range := by
      change (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p).range = K.range
      rw [hdf]
      exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hcs)
    have h3 : K.range = (T.comp L).range := by
      change (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)).range = (T.comp L).range
      rw [d.native_derivative_factor ht hk]
      rfl
    exact h1.trans (h2.trans h3)
  have hT : Function.Injective T := (PartialChart.bijective_mfderiv d.chart (d.line ht)).1
  have hinj :
    Function.Injective ((Q.comp T).comp StripCoordinates.sheetTransverseInclusion) :=
    StripCoordinates.injective_sheetTransverse_normalQuotient L (Q.comp T)
      (d.horizontal_coordinateDerivative ht hk) (d.normal_coordinateDerivative_nonzero ht hk)
      (StripCoordinates.ker_comp_eq_range_of_injective T L Q hT hker)
  have hnormal :=
    (TransverseCoordinates.contMDiffOn_normalCoordinate Ψ).contMDiffAt
      (Ψ.open_target.mem_nhds htarget)
  have hnormal' :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Z) ∞ (TransverseCoordinates.normalCoordinate Ψ)
      (d.chart (StripCoordinates.center t)) := by
    rw [← hfp]
    exact hnormal
  have htransition :
    fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
        (StripCoordinates.center t) =
      Q.comp T := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (StripCoordinates.center t) (hnormal'.mdifferentiableAt (by simp))
        (d.chart.mdifferentiableAt (by simp) (d.line ht))]
    rw [← hfp]
    rfl
  change
    Function.Injective
      ((fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
            (StripCoordinates.center t)).comp
        StripCoordinates.sheetTransverseInclusion)
  rw [htransition]
  exact hinj

def StripNormalData.sheetTransition {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    (ℝ × A) → ((ℝ × ℝ) × Z) :=
  (Ψ.symm ∘ d.chart) ∘ (ContinuousLinearMap.inl ℝ (ℝ × A) B)

def StripNormalData.sheetDifferential {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    (ℝ × A) →L[ℝ] ((ℝ × ℝ) × Z) :=
  fderiv ℝ (d.sheetTransition Ψ) (t, 0)

theorem StripNormalData.contDiffAt_tubularTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
  ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds htarget)).comp
      (StripCoordinates.center t)
      (d.chart.contMDiffOn_toFun.contMDiffAt
        (d.chart.open_source.mem_nhds (d.line ht)))).contDiffAt

theorem StripNormalData.contDiffAt_sheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ContDiffAt ℝ ∞ (d.sheetTransition Ψ) (t, 0) :=
  (d.contDiffAt_tubularTransition Ψ ht htarget).comp (t, 0)
    (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffAt

theorem StripNormalData.sheetDifferential_eq {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    d.sheetDifferential Ψ t =
      (fderiv ℝ (Ψ.symm ∘ d.chart) (StripCoordinates.center t)).comp
        (ContinuousLinearMap.inl ℝ (ℝ × A) B) := by
  rw [sheetDifferential, sheetTransition,
    fderiv_comp (t, 0) ((d.contDiffAt_tubularTransition Ψ ht htarget).differentiableAt (by simp))
      (ContinuousLinearMap.inl ℝ (ℝ × A) B).differentiableAt,
    (ContinuousLinearMap.inl ℝ (ℝ × A) B).fderiv]
  rfl

theorem StripNormalData.normal_sheetDifferential {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).comp
        ((d.sheetDifferential Ψ t).comp (ContinuousLinearMap.inr ℝ ℝ A)) =
      d.normalFrame Ψ t := by
  have hn :
    fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
        (StripCoordinates.center t) =
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).comp
        (fderiv ℝ (Ψ.symm ∘ d.chart) (StripCoordinates.center t)) := by
    change
      fderiv ℝ ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z) ∘ (Ψ.symm ∘ d.chart))
          (StripCoordinates.center t) =
        _
    rw [fderiv_comp _ (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).differentiableAt
        ((d.contDiffAt_tubularTransition Ψ ht htarget).differentiableAt (by simp)),
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).fderiv]
  rw [d.sheetDifferential_eq Ψ ht htarget, normalFrame, hn]
  rfl

theorem StripNormalData.sheetTransition_center_germ {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {f : (ℝ × ℝ) → M}
    (hzero : ∀ p, Ψ (p, 0) = f p) {q : ℝ → (ℝ × ℝ)} {t : ℝ} (hq : ContinuousAt q t)
    (hp : (q t, 0) ∈ Ψ.source) {c : (ℝ × ℝ) → (ℝ × ℝ)} (hcq : ∀ s, c (q s) = (s, 0))
    (hgerm : f =ᶠ[𝓝 (q t)] k ∘ c) :
    (fun s : ℝ => d.sheetTransition Ψ (s, 0)) =ᶠ[𝓝 t] fun s => (q s, 0) := by
  have hs := (hq.prodMk continuousAt_const).preimage_mem_nhds (Ψ.open_source.mem_nhds hp)
  filter_upwards [hs, hgerm.comp_tendsto hq.tendsto] with s hsource heq
  dsimp only [Function.comp_apply] at heq
  rw [hcq s] at heq
  change Ψ.invFun (d.chart (StripCoordinates.center s)) = (q s, 0)
  rw [← d.center s, ← heq, ← hzero (q s)]
  exact Ψ.left_inv' hsource

theorem StripNormalData.sheetDifferential_arc_of_germ {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    {q : ℝ → (ℝ × ℝ)} {v : ℝ × ℝ} (hq : HasDerivAt q v t)
    (hgerm : (fun s : ℝ => d.sheetTransition Ψ (s, 0)) =ᶠ[𝓝 t] fun s => (q s, 0)) :
    d.sheetDifferential Ψ t (1, 0) = (v, 0) := by
  have hF := (d.contDiffAt_sheetTransition Ψ ht htarget).differentiableAt (by simp)
  have hi : HasDerivAt (fun s : ℝ => (s, (0 : A))) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))
  have hd := hF.hasFDerivAt.comp_hasDerivAt t hi
  have hq' : HasDerivAt (fun s => (q s, (0 : Z))) (v, 0) t :=
    hq.prodMk (hasDerivAt_const t (0 : Z))
  exact hd.unique (hq'.congr_of_eventuallyEq hgerm)

def TransverseCoordinates.cornerLinear {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (u : D) (v : Z) :
    (ℝ × ℝ) →L[ℝ] (D × Z) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v)

theorem TransverseCoordinates.cornerLinear_apply {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (u : D) (v : Z) (p : ℝ × ℝ) :
    cornerLinear u v p = (p.1 • u, p.2 • v) :=
  rfl

theorem TransverseCoordinates.injective_cornerLinear {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) : Function.Injective (cornerLinear u v) := by
  intro p q hpq
  exact
    Prod.ext ((smul_left_injective ℝ hu) (congrArg Prod.fst hpq))
      ((smul_left_injective ℝ hv) (congrArg Prod.snd hpq))

def TransverseCoordinates.cornerMap {D Z : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) (u : D) (v : Z) : (ℝ × ℝ) → M :=
  Φ ∘ cornerLinear u v

theorem TransverseCoordinates.contMDiffOn_cornerMap {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) (u : D) (v : Z) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (cornerMap Φ u v) (cornerLinear u v ⁻¹' Φ.source) :=
  Φ.contMDiffOn_toFun.comp (cornerLinear u v).contDiff.contMDiff.contMDiffOn (fun _ hx => hx)

theorem TransverseCoordinates.injOn_cornerMap {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) : Set.InjOn (cornerMap Φ u v) (cornerLinear u v ⁻¹' Φ.source) := by
  intro p hp q hq heq
  exact injective_cornerLinear hu hv (Φ.toPartialEquiv.injOn hp hq heq)

theorem TransverseCoordinates.injective_mfderiv_cornerMap {D Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞) {u : D} {v : Z} (hu : u ≠ 0)
    (hv : v ≠ 0) {p : ℝ × ℝ} (hp : p ∈ cornerLinear u v ⁻¹' Φ.source) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (cornerMap Φ u v) p) := by
  have hL : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, D × Z) ∞ (cornerLinear u v) :=
    (cornerLinear u v).contDiff.contMDiff
  rw [cornerMap,
    mfderiv_comp p (Φ.mdifferentiableAt (by simp) hp) (hL.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, (cornerLinear u v).fderiv]
  exact (PartialChart.bijective_mfderiv Φ hp).1.comp (injective_cornerLinear hu hv)

theorem exists_native_clean_corner_of_parametrizations {E M D Z N P A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace N] [ChartedSpace D N]
    [TopologicalSpace P] [ChartedSpace Z P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞) (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source) (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {u : A} {v : B} (hu : u ≠ 0) (hv : v ≠ 0) {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        (0 : ℝ × ℝ) ∈ W ∧
          ∃ k : (ℝ × ℝ) → M,
            ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
              Set.InjOn k W ∧
                Set.MapsTo k W O ∧
                  k 0 = F (c 0) ∧
                    (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                      (∀ p ∈ W, (k p ∈ Set.range F ↔ p.2 = 0) ∧ (k p ∈ Set.range G ↔ p.1 = 0)) ∧
                        (∀ s, (s, 0) ∈ W → k (s, 0) = F (c (s • u))) ∧
                          (∀ t, (0, t) ∈ W → k (0, t) = G (d (t • v))) := by
  obtain ⟨a, ha, Φ, hprod, _, htarget, hcenter, hleft, hright, himages⟩ :=
    exists_clean_crossingChart_of_parametrizations hF hG hembF hembG c d hc0 hd0 hxy hdim ht hO
      hxO
  let L := TransverseCoordinates.cornerLinear u v
  let W := L ⁻¹' Φ.source
  let k := TransverseCoordinates.cornerMap Φ u v
  have h0W : (0 : ℝ × ℝ) ∈ W := by
    change L 0 ∈ Φ.source
    rw [map_zero]
    exact hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩
  refine
    ⟨W, Φ.open_source.preimage L.continuous, h0W, k,
      TransverseCoordinates.contMDiffOn_cornerMap Φ u v,
      TransverseCoordinates.injOn_cornerMap Φ hu hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact htarget (Φ.map_source' hp)
  · change Φ (L 0) = F (c 0)
    rw [map_zero]
    exact hcenter
  · intro p hp
    exact TransverseCoordinates.injective_mfderiv_cornerMap Φ hu hv hp
  · intro p hp
    have him := himages (L p) hp
    simpa only [L, k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, smul_eq_zero, hu, hv, or_false] using him
  · intro s hs
    have haxis : (s • u, 0) ∈ Φ.source := by
      change L (s, 0) ∈ Φ.source at hs
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using hs
    simpa only [k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hleft (s • u) haxis
  · intro t ht
    have haxis : (0, t • v) ∈ Φ.source := by
      change L (0, t) ∈ Φ.source at ht
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using ht
    simpa only [k, TransverseCoordinates.cornerMap, Function.comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hright (t • v) haxis

structure CleanCornerPatch {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) where
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains_zero : (0 : ℝ × ℝ) ∈ domain
  map : (ℝ × ℝ) → M
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : Set.InjOn map domain
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  sheets : ∀ p ∈ domain, (map p ∈ S ↔ p.2 = 0) ∧ (map p ∈ T ↔ p.1 = 0)
  axis_first : ∀ t, (t, 0) ∈ domain → map (t, 0) = a t
  axis_second : ∀ t, (0, t) ∈ domain → map (0, t) = b t

def CleanCornerPatch.swap {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    (c : CleanCornerPatch (E := E) S T a b) : CleanCornerPatch (E := E) T S b a := by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have he : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (e : (ℝ × ℝ) → ℝ × ℝ) := e.contDiff.contMDiff
  refine
    { domain := e ⁻¹' c.domain
      open_domain := c.open_domain.preimage e.continuous
      contains_zero := ?_
      map := c.map ∘ e
      smooth := c.smooth.comp he.contMDiffOn (fun _ hp => hp)
      injective := ?_
      derivative_injective := ?_
      sheets := fun p hp => ⟨(c.sheets (e p) hp).2, (c.sheets (e p) hp).1⟩
      axis_first := fun t ht => c.axis_second t ht
      axis_second := fun t ht => c.axis_first t ht }
  · change e 0 ∈ c.domain
    rw [map_zero]
    exact c.contains_zero
  · intro p hp q hq hpq
    exact e.injective (c.injective hp hq hpq)
  · intro p hp
    have hc := c.smooth.contMDiffAt (c.open_domain.mem_nhds hp)
    rw [mfderiv_comp p (hc.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))]
    exact
      (c.derivative_injective (e p) hp).comp
        (PartialChart.bijective_mfderiv e.toDiffeomorph.toPartialDiffeomorph
            (Set.mem_univ p)).1

structure CleanStripPatch {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a : ℝ → M) (k₀ k₁ : (ℝ × ℝ) → M) where
  width : ℝ
  width_pos : 0 < width
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains_strip : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-width) width ⊆ domain
  map : (ℝ × ℝ) → M
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : Set.InjOn map domain
  closed_embedding :
    Topology.IsClosedEmbedding (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-width) width => map p)
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  first_sheet : ∀ p ∈ domain, map p ∈ S ↔ p.2 = 0
  second_sheet : ∀ p ∈ domain, map p ∈ T ↔ p.1 = 0 ∨ p.1 = 1
  center : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (t, 0) = a t
  left_germ : map =ᶠ[𝓝 (0, 0)] k₀
  right_germ : map =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse

theorem bigon_strip_maps_left_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : h ≠ 0) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    k.map ∘ WhitneyPairModel.lowerStripCoordinates h =ᶠ[𝓝 (-1, 0)]
      l.map ∘ WhitneyPairModel.upperStripCoordinates h := by
  have hx : WhitneyPairModel.lowerStripCoordinates h (-1, 0) = (0, 0) := by
    convert WhitneyPairModel.lowerStripCoordinates_lower h 0 using 1
    norm_num
  have hy : WhitneyPairModel.upperStripCoordinates h (-1, 0) = (0, 0) := by
    convert WhitneyPairModel.upperStripCoordinates_upper h 0 using 1
    norm_num
  have hk :=
    k.left_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.lowerStripCoordinates h) (𝓝 (-1, 0)) (𝓝 (0, 0))
        by
        rw [← hx]
        exact (WhitneyPairModel.contDiff_lowerStripCoordinates hh).continuous.continuousAt)
  have hl :=
    l.left_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.upperStripCoordinates h) (𝓝 (-1, 0)) (𝓝 (0, 0))
        by
        rw [← hy]
        exact (WhitneyPairModel.contDiff_upperStripCoordinates hh).continuous.continuousAt)
  have hnear : ∀ᶠ p in 𝓝 ((-1 : ℝ), (0 : ℝ)), WhitneyPairModel.arcTime p ≤ 1 / 3 := by
    have ht : WhitneyPairModel.arcTime (-1, 0) < 1 / 3 := by norm_num [WhitneyPairModel.arcTime]
    exact
      ((WhitneyPairModel.contDiff_arcTime.continuous.continuousAt).eventually_lt_const ht).mono
        (fun _ hp => hp.le)
  filter_upwards [hk, hl, hnear] with p hkp hlp hp
  dsimp only [Function.comp_apply] at hkp hlp
  change
    k.map (WhitneyPairModel.lowerStripCoordinates h p) =
      l.map (WhitneyPairModel.upperStripCoordinates h p)
  rw [hkp, hlp, WhitneyPairModel.lowerStripCoordinates_left h hp,
    WhitneyPairModel.upperStripCoordinates_left hh hp]
  change
    c₀.map (WhitneyPairModel.leftCornerCoordinates h p) =
      c₀.map ((WhitneyPairModel.leftCornerCoordinates h p).swap.swap)
  rw [Prod.swap_swap]

theorem bigon_strip_maps_right_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : h ≠ 0) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    k.map ∘ WhitneyPairModel.lowerStripCoordinates h =ᶠ[𝓝 (1, 0)]
      l.map ∘ WhitneyPairModel.upperStripCoordinates h := by
  have hx : WhitneyPairModel.lowerStripCoordinates h (1, 0) = (1, 0) := by
    convert WhitneyPairModel.lowerStripCoordinates_lower h 1 using 1
    norm_num
  have hy : WhitneyPairModel.upperStripCoordinates h (1, 0) = (1, 0) := by
    convert WhitneyPairModel.upperStripCoordinates_upper h 1 using 1
    norm_num
  have hk :=
    k.right_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.lowerStripCoordinates h) (𝓝 (1, 0)) (𝓝 (1, 0))
        by
        have ht :=
          (WhitneyPairModel.contDiff_lowerStripCoordinates hh).continuous.continuousAt (x :=
            (1, 0))
        rw [ContinuousAt, hx] at ht
        exact ht)
  have hl :=
    l.right_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.upperStripCoordinates h) (𝓝 (1, 0)) (𝓝 (1, 0))
        by
        have ht :=
          (WhitneyPairModel.contDiff_upperStripCoordinates hh).continuous.continuousAt (x :=
            (1, 0))
        rw [ContinuousAt, hy] at ht
        exact ht)
  have hnear : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), 2 / 3 ≤ WhitneyPairModel.arcTime p := by
    have ht : 2 / 3 < WhitneyPairModel.arcTime (1, 0) := by norm_num [WhitneyPairModel.arcTime]
    exact
      ((WhitneyPairModel.contDiff_arcTime.continuous.continuousAt).eventually_const_lt ht).mono
        (fun _ hp => hp.le)
  filter_upwards [hk, hl, hnear] with p hkp hlp hp
  dsimp only [Function.comp_apply] at hkp hlp
  change
    k.map (WhitneyPairModel.lowerStripCoordinates h p) =
      l.map (WhitneyPairModel.upperStripCoordinates h p)
  rw [hkp, hlp]
  change
    c₁.map (StripCoordinates.reverse (WhitneyPairModel.lowerStripCoordinates h p)) =
      c₁.map ((StripCoordinates.reverse (WhitneyPairModel.upperStripCoordinates h p)).swap)
  rw [WhitneyPairModel.lowerStripCoordinates_right h hp,
    WhitneyPairModel.upperStripCoordinates_right hh hp, Prod.swap_swap]

theorem exists_smooth_open_gluing {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Y] [ChartedSpace F Y] {f g : X → Y} {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g V) (hfg : Set.EqOn f g (U ∩ V)) :
    ∃ k : X → Y, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k (U ∪ V) ∧ Set.EqOn k f U ∧ Set.EqOn k g V := by
  classical
  let k := U.piecewise f g
  have hkf : Set.EqOn k f U := fun x hx => Set.piecewise_eq_of_mem U f g hx
  have hkg : Set.EqOn k g V := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact (hkf hxU).trans (hfg ⟨hxU, hx⟩)
    · exact Set.piecewise_eq_of_notMem U f g hxU
  exact
    ⟨k, (hf.congr (fun _ hx => hkf hx)).union_of_isOpen (hg.congr (fun _ hx => hkg hx)) hU hV,
      hkf, hkg⟩

theorem exists_smooth_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    ∃ U : Set (ℝ × ℝ),
      ∃ V : Set (ℝ × ℝ),
        IsOpen U ∧
          IsOpen V ∧
            frontier (WhitneyPairModel.bigon h) ⊆ U ∪ V ∧
              Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U ∧
                Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V ∧
                  Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain ∧
                    Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain ∧
                      ∃ f : (ℝ × ℝ) → M,
                        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f (U ∪ V) ∧
                          Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U ∧
                            Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V ∧
                              (∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                  f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t) := by
  let Dlo := WhitneyPairModel.lowerStripCoordinates h ⁻¹' k.domain
  let Dhi := WhitneyPairModel.upperStripCoordinates h ⁻¹' l.domain
  have hDlo : IsOpen Dlo :=
    k.open_domain.preimage (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne').continuous
  have hDhi : IsOpen Dhi :=
    l.open_domain.preimage (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne').continuous
  have hkl :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) Dlo :=
    k.smooth.comp (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne').contMDiff.contMDiffOn
      (fun _ hp => hp)
  have hlu :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (l.map ∘ WhitneyPairModel.upperStripCoordinates h) Dhi :=
    l.smooth.comp (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne').contMDiff.contMDiffOn
      (fun _ hp => hp)
  obtain ⟨O₀, hO₀sub, hO₀, hleft⟩ := mem_nhds_iff.mp (bigon_strip_maps_left_germ hh.ne' c₀ c₁ k l)
  obtain ⟨O₁, hO₁sub, hO₁, hright⟩ :=
    mem_nhds_iff.mp (bigon_strip_maps_right_germ hh.ne' c₀ c₁ k l)
  have hlowD : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) Dlo := by
    intro t ht
    change WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0) ∈ k.domain
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have huppD :
    Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) Dhi := by
    intro t ht
    change
      WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ l.domain
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  obtain ⟨U, V, hU, hV, hUD, hVD, hover, hlowU, huppV, hfront⟩ :=
    WhitneyPairModel.exists_bigon_boundary_cover hh hDlo hDhi (hO₀.union hO₁) (Or.inl hleft)
      (Or.inr hright) hlowD huppD
  have hfg :
    Set.EqOn (k.map ∘ WhitneyPairModel.lowerStripCoordinates h)
      (l.map ∘ WhitneyPairModel.upperStripCoordinates h) (U ∩ V) := by
    intro p hp
    rcases hover hp with hp0 | hp1
    · exact hO₀sub hp0
    · exact hO₁sub hp1
  obtain ⟨f, hf, hflo, hfhi⟩ := exists_smooth_open_gluing hU hV (hkl.mono hUD) (hlu.mono hVD) hfg
  refine
    ⟨U, V, hU, hV, hfront, hlowU, huppV, fun _ hp => hUD hp, fun _ hp => hVD hp, f, hf, hflo,
      hfhi, ?_, ?_⟩
  · intro t ht
    rw [hflo (hlowU ht)]
    change k.map (WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0)) = a t
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.center t ht
  · intro t ht
    rw [hfhi (huppV ht)]
    change
      l.map (WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) =
        b t
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.center t ht

theorem StripCoordinates.injective_plane_of_horizontal_and_normal
    (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (hh : L (1, 0) = (1, 0)) (hn : (L (0, 1)).2 ≠ 0) :
    Function.Injective L := by
  let i : (ℝ × ℝ) →L[ℝ] Space ℝ ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hh' : (i.comp L) (1, 0) = StripCoordinates.center 1 := by
    change i (L (1, 0)) = StripCoordinates.center 1
    rw [hh]
    rfl
  have hi := injective_of_horizontal_and_normal (i.comp L) hh' hn
  intro p q hpq
  exact hi (congrArg i hpq)

def StripCoordinates.detector {A B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (v : ℝ → B) (F : (ℝ × ℝ) → Space A B) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, ⟪v p.1, (F p).2⟫_ℝ)

theorem StripCoordinates.contDiff_detector {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B}
    {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (detector v F) :=
  contDiff_fst.prodMk ((hv.comp contDiff_fst).inner ℝ hF.snd)

theorem StripCoordinates.detector_zero {A B : Type*} [NormedAddCommGroup A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hc : ∀ t, F (t, 0) = StripCoordinates.center t) (t : ℝ) :
    detector v F (t, 0) = (t, 0) := by
  simp only [detector, hc, StripCoordinates.center, inner_zero_right]

theorem StripCoordinates.detector_vertical_derivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] {v : ℝ → B}
    {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hn : ∀ t, normalDerivative F t = v t) (t : ℝ) :
    fderiv ℝ (detector v F) (t, 0) (0, 1) = (0, ⟪v t, v t⟫_ℝ) := by
  have hd : HasDerivAt (fun s : ℝ => (F (t, s)).2) (v t) 0 := by
    have h :=
      hasDerivAt_verticalSlice (t := t) (s := 0) (hF.snd.contDiffAt.differentiableAt (by simp))
    change HasDerivAt _ (normalDerivative F t) 0 at h
    rwa [hn t] at h
  have hinner : HasDerivAt (fun s : ℝ => ⟪v t, (F (t, s)).2⟫_ℝ) (⟪v t, v t⟫_ℝ) 0 := by
    simpa only [inner_zero_left, add_zero] using (hasDerivAt_const (0 : ℝ) (v t)).inner ℝ hd
  have hslice : HasDerivAt (fun s : ℝ => detector v F (t, s)) (0, ⟪v t, v t⟫_ℝ) 0 :=
    (hasDerivAt_const (0 : ℝ) t).prodMk hinner
  exact
    (hasDerivAt_verticalSlice
          ((contDiff_detector hv hF).contDiffAt.differentiableAt (by simp))).unique
      hslice

theorem StripCoordinates.injective_fderiv_detector_at_center {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    {v : ℝ → B} {F : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hc : ∀ t, F (t, 0) = StripCoordinates.center t) (hn : ∀ t, normalDerivative F t = v t)
    {t : ℝ} (ht : v t ≠ 0) : Function.Injective (fderiv ℝ (detector v F) (t, 0)) := by
  have hQ : DifferentiableAt ℝ (detector v F) (t, 0) :=
    (contDiff_detector hv hF).contDiffAt.differentiableAt (by simp)
  have hh : fderiv ℝ (detector v F) (t, 0) (1, 0) = (1, 0) := by
    have hd := hasDerivAt_horizontalSlice hQ
    have heq : (fun s : ℝ => detector v F (s, 0)) = fun s => (s, 0) := funext (detector_zero hc)
    rw [heq] at hd
    exact hd.unique ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ)))
  apply injective_plane_of_horizontal_and_normal _ hh
  rw [detector_vertical_derivative hv hF hn t]
  exact inner_self_ne_zero.mpr ht

theorem WhitneyPairModel.lowerStripCoordinates_horizontal_derivative {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : fderiv ℝ (lowerStripCoordinates h) (s, 0) (1, 0) = (1 / 2, 0) := by
  have hf : DifferentiableAt ℝ (lowerStripCoordinates h) (s, 0) :=
    (contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp)
  have hd := StripCoordinates.hasDerivAt_horizontalSlice hf
  have heq : (fun x : ℝ => lowerStripCoordinates h (x, 0)) = fun x => ((x + 1) / 2, 0) := by
    funext x
    simp [lowerStripCoordinates, arcTime]
  rw [heq] at hd
  exact
    hd.unique (((hasDerivAt_id s).add_const 1).div_const 2 |>.prodMk (hasDerivAt_const s (0 : ℝ)))

theorem WhitneyPairModel.lowerStripCoordinates_vertical_derivative {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) :
    fderiv ℝ (lowerStripCoordinates h) (s, 0) (0, 1) =
      (cornerSign ((s + 1) / 2) * (1 / (4 * h * cornerScale ((s + 1) / 2))),
        1 / (4 * h * cornerScale ((s + 1) / 2))) := by
  have hf : DifferentiableAt ℝ (lowerStripCoordinates h) (s, 0) :=
    (contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp)
  have hd := StripCoordinates.hasDerivAt_verticalSlice hf
  have hdiv :
    HasDerivAt (fun u : ℝ => u / (4 * h * cornerScale ((s + 1) / 2)))
      (1 / (4 * h * cornerScale ((s + 1) / 2))) 0 :=
    (hasDerivAt_id 0).div_const _
  have hfirst := (HasDerivAt.const_mul (cornerSign ((s + 1) / 2)) hdiv).const_add ((s + 1) / 2)
  exact hd.unique (hfirst.prodMk hdiv)

theorem WhitneyPairModel.injective_fderiv_lowerStripCoordinates {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : Function.Injective (fderiv ℝ (lowerStripCoordinates h) (s, 0)) := by
  let L := fderiv ℝ (lowerStripCoordinates h) (s, 0)
  have hhor : ((2 : ℝ) • L) (1, 0) = (1, 0) := by
    change (2 : ℝ) • (fderiv ℝ (lowerStripCoordinates h) (s, 0) (1, 0)) = (1, 0)
    rw [lowerStripCoordinates_horizontal_derivative hh]
    norm_num
  have hnorm : (((2 : ℝ) • L) (0, 1)).2 ≠ 0 := by
    change ((2 : ℝ) • (fderiv ℝ (lowerStripCoordinates h) (s, 0) (0, 1))).2 ≠ 0
    rw [lowerStripCoordinates_vertical_derivative hh]
    change (2 : ℝ) * (1 / (4 * h * cornerScale ((s + 1) / 2))) ≠ 0
    exact
      mul_ne_zero (by norm_num)
        (one_div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hh) (cornerScale_pos _).ne'))
  have hi :=
    StripCoordinates.injective_plane_of_horizontal_and_normal ((2 : ℝ) • L) hhor hnorm
  intro x y hxy
  exact hi (congrArg (fun z : ℝ × ℝ => (2 : ℝ) • z) hxy)

theorem WhitneyPairModel.injective_fderiv_exchangeEdges (h : ℝ) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (exchangeEdges h) p) := by
  have heq : exchangeEdges h ∘ exchangeEdges h = id := funext (exchangeEdges_involutive h)
  have hd :
    (fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [←
      fderiv_comp p ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp))
        ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp)),
      heq, fderiv_id]
  intro x y hxy
  have he := congrArg (fderiv ℝ (exchangeEdges h) (exchangeEdges h p)) hxy
  change
    ((fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p)) x =
      ((fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p))
        y at he
  rw [hd] at he
  exact he

theorem WhitneyPairModel.injective_fderiv_upperStripCoordinates {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : Function.Injective (fderiv ℝ (upperStripCoordinates h) (s, h * (1 - s ^ 2))) := by
  rw [upperStripCoordinates,
    fderiv_comp _ ((contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp))
      ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp))]
  have heq : exchangeEdges h (s, h * (1 - s ^ 2)) = (s, 0) := by
    simp only [exchangeEdges, sub_self]
  rw [heq]
  exact (injective_fderiv_lowerStripCoordinates hh s).comp (injective_fderiv_exchangeEdges h _)

theorem WhitneyPairModel.mem_frontier_bigon_iff_exists_time {h : ℝ} (hh : 0 < h)
    (p : ℝ × ℝ) :
    p ∈ frontier (bigon h) ↔
      ∃ t ∈ Set.Icc (0 : ℝ) 1, p = (2 * t - 1, 0) ∨ p = (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) := by
  constructor
  · intro hp
    obtain ⟨hpK, hpedge⟩ := (mem_frontier_bigon_iff h p).mp hp
    have hpr := bigon_subset_rectangle hh hpK
    let t := (p.1 + 1) / 2
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [t]
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * t - 1 := by dsimp [t]; ring
    refine ⟨t, ht, ?_⟩
    rcases hpedge with hpzero | hpupper
    · exact Or.inl (Prod.ext hbase hpzero)
    · right
      apply Prod.ext hbase
      rw [← hbase]
      exact hpupper
  · rintro ⟨t, ht, rfl | rfl⟩
    · apply (mem_frontier_bigon_iff h _).mpr
      refine ⟨lowerArc_mem_bigon hh.le ?_, Or.inl rfl⟩
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    · apply (mem_frontier_bigon_iff h _).mpr
      refine ⟨upperArc_mem_bigon hh.le ?_, Or.inr rfl⟩
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]

theorem WhitneyPairModel.injOn_frontier_bigon_of_arcs {M : Type*} {h : ℝ} (hh : 0 < h)
    {f : (ℝ × ℝ) → M} {a b : ℝ → M} (ha : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hb : Set.InjOn b (Set.Icc (0 : ℝ) 1))
    (hlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t)
    (hcoinc :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1)) :
    Set.InjOn f (frontier (bigon h)) := by
  have hcross {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (heq : a t = b s) : (2 * t - 1, (0 : ℝ)) = (2 * s - 1, h * (1 - (2 * s - 1) ^ 2)) := by
    rcases hcoinc t ht s hs heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  intro p hp q hq heq
  obtain ⟨t, ht, hp'⟩ := (mem_frontier_bigon_iff_exists_time hh p).mp hp
  obtain ⟨s, hs, hq'⟩ := (mem_frontier_bigon_iff_exists_time hh q).mp hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · rw [hlower t ht, hlower s hs] at heq
    rw [ha ht hs heq]
  · rw [hlower t ht, hupper s hs] at heq
    exact hcross ht hs heq
  · rw [hupper t ht, hlower s hs] at heq
    exact (hcross hs ht heq.symm).symm
  · rw [hupper t ht, hupper s hs] at heq
    rw [hb ht hs heq]

theorem CleanStripPatch.center_injOn {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁) : Set.InjOn a (Set.Icc (0 : ℝ) 1) := by
  intro t ht s hs heq
  have h0 : (0 : ℝ) ∈ Set.Icc (-k.width) k.width :=
    ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have htK : (t, 0) ∈ k.domain := k.contains_strip ⟨ht, h0⟩
  have hsK : (s, 0) ∈ k.domain := k.contains_strip ⟨hs, h0⟩
  have hmaps : k.map (t, 0) = k.map (s, 0) := by
    rw [k.center t ht, k.center s hs]
    exact heq
  exact congrArg Prod.fst (k.injective htK hsK hmaps)

theorem strip_center_coincidences_of_corner_overlap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
  intro t ht s hs heq
  have hk0 : (0 : ℝ) ∈ Set.Icc (-k.width) k.width :=
    ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have hl0 : (0 : ℝ) ∈ Set.Icc (-l.width) l.width :=
    ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  have hmaps : k.map (t, 0) = l.map (s, 0) := by rw [k.center t ht, l.center s hs]; exact heq
  rcases hover (t, 0) (k.contains_strip ⟨ht, hk0⟩) (s, 0) (l.contains_strip ⟨hs, hl0⟩) hmaps with
    hleft | hright
  · exact Or.inl ⟨congrArg Prod.fst hleft, (congrArg Prod.snd hleft).symm⟩
  · right
    have ht' : 1 - t = 0 := congrArg Prod.fst hright
    have hs' : 0 = 1 - s := congrArg Prod.snd hright
    constructor <;> linarith

theorem injective_nativeDerivative_of_strip_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁) {r : (ℝ × ℝ) → ℝ × ℝ}
    (hr : ContDiff ℝ ∞ r) {f : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (heq : Set.EqOn f (k.map ∘ r) U) (hmap : Set.MapsTo r U k.domain) {p : ℝ × ℝ} (hp : p ∈ U)
    (hi : Function.Injective (fderiv ℝ r p)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  have hgerm : f =ᶠ[𝓝 p] k.map ∘ r := Filter.mem_of_superset (hU.mem_nhds hp) (fun _ hx => heq hx)
  rw [hgerm.mfderiv_eq]
  have hk := k.smooth.contMDiffAt (k.open_domain.mem_nhds (hmap hp))
  rw [mfderiv_comp p (hk.mdifferentiableAt (by simp)) (hr.contMDiff.mdifferentiableAt (by simp))]
  have hri : Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) r p) := by
    rw [mfderiv_eq_fderiv]
    exact hi
  exact (k.derivative_injective (r p) (hmap hp)).comp hri

theorem injective_nativeDerivative_bigon_boundary {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁) {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hlowU : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U)
    (huppV : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V)
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) :
    ∀ p ∈ frontier (WhitneyPairModel.bigon h),
      Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  intro p hp
  obtain ⟨t, ht, rfl | rfl⟩ := (WhitneyPairModel.mem_frontier_bigon_iff_exists_time hh p).mp hp
  · exact
      injective_nativeDerivative_of_strip_germ k
        (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne') hU hflo hmapU (hlowU ht)
        (WhitneyPairModel.injective_fderiv_lowerStripCoordinates hh.ne' _)
  · exact
      injective_nativeDerivative_of_strip_germ l
        (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne') hV hfhi hmapV (huppV ht)
        (WhitneyPairModel.injective_fderiv_upperStripCoordinates hh.ne' _)

theorem exists_embedded_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap)
    {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)} (hU : IsOpen U) (hV : IsOpen V)
    (hfront : frontier (WhitneyPairModel.bigon h) ⊆ U ∪ V)
    (hlowU : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U)
    (huppV : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V)
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f (U ∪ V))
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        frontier (WhitneyPairModel.bigon h) ⊆ W ∧
          W ⊆ U ∪ V ∧
            Set.InjOn f W ∧ ∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  have hlow : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t := by
    intro t ht
    rw [hflo (hlowU ht)]
    change k.map (WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0)) = a t
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.center t ht
  have hupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t := by
    intro t ht
    rw [hfhi (huppV ht)]
    change
      l.map (WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) =
        b t
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.center t ht
  have hinj :=
    WhitneyPairModel.injOn_frontier_bigon_of_arcs hh k.center_injOn l.center_injOn hlow hupp
      (strip_center_coincidences_of_corner_overlap k l hover)
  have hi :=
    injective_nativeDerivative_bigon_boundary hh k l hU hV hlowU huppV hmapU hmapV hflo hfhi
  have hcompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  exact
    ManifoldImmersion.exists_open_embedded_immersive_neighborhood (hU.union hV) hf hcompact hfront
      hinj hi

theorem WhitneyPairModel.interpolated_strip_time_mem_Ioo {h t β z J : ℝ} (hh : 0 < h)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hJ : 0 < J)
    (hJdef : J = (1 - β) * (1 - t) + β * t) (hz : 0 < z) (hzupper : z < 4 * h * t * (1 - t)) :
    t + (2 * β - 1) * (z / (4 * h * J)) ∈ Set.Ioo (0 : ℝ) 1 := by
  let H := 4 * h * t * (1 - t)
  have hH : 0 < H := mul_pos (mul_pos (mul_pos (by norm_num) hh) ht.1) (sub_pos.mpr ht.2)
  let θ := z / H
  let e := t * β / J
  have hθ0 : 0 < θ := div_pos hz hH
  have hθ1 : θ < 1 := (div_lt_one hH).mpr hzupper
  have he0 : 0 ≤ e := div_nonneg (mul_nonneg ht.1.le hβ.1) hJ.le
  have he1 : e ≤ 1 := by
    apply (div_le_one hJ).mpr
    rw [hJdef]
    have hr := mul_nonneg (sub_nonneg.mpr hβ.2) (sub_nonneg.mpr ht.2.le)
    nlinarith
  have hid : t + (2 * β - 1) * (z / (4 * h * J)) = (1 - θ) * t + θ * e := by
    dsimp [θ, e, H]
    field_simp [hh.ne', ht.1.ne', (sub_pos.mpr ht.2).ne', hJ.ne']
    rw [hJdef]
    ring
  rw [hid]
  constructor
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ1) ht.1) (mul_nonneg hθ0.le he0)
  · have hpos : 0 < (1 - θ) * (1 - t) + θ * (1 - e) :=
      add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ1) (sub_pos.mpr ht.2))
        (mul_nonneg hθ0.le (sub_nonneg.mpr he1))
    nlinarith

theorem WhitneyPairModel.lowerStripCoordinates_interior {h : ℝ} (hh : 0 < h) {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) :
    (lowerStripCoordinates h p).1 ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < (lowerStripCoordinates h p).2 := by
  obtain ⟨hp0, hphi⟩ := (mem_interior_bigon_iff h p).mp hp
  have hheight : 0 < h * (1 - p.1 ^ 2) := hp0.trans hphi
  have hsq : p.1 ^ 2 < 1 := by
    have hpos : 0 < 1 - p.1 ^ 2 := (mul_pos_iff_of_pos_left hh).mp hheight
    linarith
  have ht : arcTime p ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [arcTime]
    constructor <;> nlinarith [sq_nonneg (p.1 - 1), sq_nonneg (p.1 + 1)]
  have hβ : cornerTransition (arcTime p) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hheight_eq : h * (1 - p.1 ^ 2) = 4 * h * arcTime p * (1 - arcTime p) := by
    dsimp [arcTime]
    ring
  have hzupper : p.2 < 4 * h * arcTime p * (1 - arcTime p) := hheight_eq ▸ hphi
  refine ⟨?_, ?_⟩
  · exact interpolated_strip_time_mem_Ioo hh ht hβ (cornerScale_pos _) rfl hp0 hzupper
  · exact div_pos hp0 (mul_pos (mul_pos (by norm_num) hh) (cornerScale_pos _))

theorem WhitneyPairModel.exchangeEdges_mem_interior {h : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) : exchangeEdges h p ∈ interior (bigon h) := by
  obtain ⟨hp0, hphi⟩ := (mem_interior_bigon_iff h p).mp hp
  apply (mem_interior_bigon_iff h _).mpr
  change 0 < h * (1 - p.1 ^ 2) - p.2 ∧ h * (1 - p.1 ^ 2) - p.2 < h * (1 - p.1 ^ 2)
  constructor <;> linarith

theorem WhitneyPairModel.upperStripCoordinates_interior {h : ℝ} (hh : 0 < h) {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) :
    (upperStripCoordinates h p).1 ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < (upperStripCoordinates h p).2 :=
  lowerStripCoordinates_interior hh (exchangeEdges_mem_interior hp)

theorem CleanStripPatch.avoids_sheets {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁) {p : ℝ × ℝ} (hp : p ∈ k.domain)
    (ht : p.1 ∈ Set.Ioo (0 : ℝ) 1) (hn : p.2 ≠ 0) : k.map p ∉ S ∪ T := by
  rintro (hS | hT)
  · exact hn ((k.first_sheet p hp).mp hS)
  · rcases (k.second_sheet p hp).mp hT with h0 | h1
    · exact ht.1.ne' h0
    · exact ht.2.ne h1

theorem bigon_boundary_map_avoids_sheets {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁) {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)}
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) {p : ℝ × ℝ}
    (hp : p ∈ U ∪ V) (hpi : p ∈ interior (WhitneyPairModel.bigon h)) : f p ∉ S ∪ T := by
  rcases hp with hpU | hpV
  · rw [hflo hpU]
    have hc := WhitneyPairModel.lowerStripCoordinates_interior hh hpi
    exact k.avoids_sheets (hmapU hpU) hc.1 hc.2.ne'
  · rw [hfhi hpV]
    have hc := WhitneyPairModel.upperStripCoordinates_interior hh hpi
    change l.map (WhitneyPairModel.upperStripCoordinates h p) ∉ S ∪ T
    rw [Set.union_comm]
    exact l.avoids_sheets (hmapV hpV) hc.1 hc.2.ne'

structure CleanBigonBoundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) (k l : (ℝ × ℝ) → M)
    (h : ℝ) where
  height_pos : 0 < h
  map : (ℝ × ℝ) → M
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : Set.InjOn map domain
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  interior_avoids : ∀ p ∈ domain ∩ interior (WhitneyPairModel.bigon h), map p ∉ S ∪ T
  closed_neighborhood : Set (ℝ × ℝ)
  compact_neighborhood : IsCompact closed_neighborhood
  closed_closed_neighborhood : IsClosed closed_neighborhood
  boundary_covered : frontier (WhitneyPairModel.bigon h) ⊆ interior closed_neighborhood
  neighborhood_subset : closed_neighborhood ⊆ domain
  closed_embedding : Topology.IsClosedEmbedding (fun p : closed_neighborhood => map p)
  clean :
    ∀ p ∈ WhitneyPairModel.bigon h ∩ closed_neighborhood,
      p ∉ frontier (WhitneyPairModel.bigon h) → map p ∉ S ∪ T
  lower : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, 0) = a t
  upper : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t
  lower_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, map =ᶠ[𝓝 (2 * t - 1, 0)] k ∘ WhitneyPairModel.lowerStripCoordinates h
  upper_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      map =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
        l ∘ WhitneyPairModel.upperStripCoordinates h

theorem exists_clean_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    ∃ f : (ℝ × ℝ) → M,
      ∃ W : Set (ℝ × ℝ),
        IsOpen W ∧
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f W ∧
            Set.InjOn f W ∧
              (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
                (∀ p ∈ W ∩ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T) ∧
                  ∃ C : Set (ℝ × ℝ),
                    IsCompact C ∧
                      IsClosed C ∧
                        frontier (WhitneyPairModel.bigon h) ⊆ interior C ∧
                          C ⊆ W ∧
                            Topology.IsClosedEmbedding (fun p : C => f p) ∧
                              (∀ p ∈ WhitneyPairModel.bigon h ∩ C,
                                  p ∉ frontier (WhitneyPairModel.bigon h) → f p ∉ S ∪ T) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t) ∧
                                  (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                      f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t) ∧
                                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                        f =ᶠ[𝓝 (2 * t - 1, 0)]
                                          k.map ∘ WhitneyPairModel.lowerStripCoordinates h) ∧
                                      (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                        f =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
                                          l.map ∘ WhitneyPairModel.upperStripCoordinates h) := by
  obtain ⟨U, V, hU, hV, hfront, hlowU, huppV, hmapU, hmapV, f, hf, hflo, hfhi, hlow, hupp⟩ :=
    exists_smooth_bigon_boundary_neighborhood hh c₀ c₁ k l
  obtain ⟨W, hW, hfrontW, hWUV, hinj, hi⟩ :=
    exists_embedded_bigon_boundary_neighborhood hh k l hover hU hV hfront hlowU huppV hmapU hmapV
      hf hflo hfhi
  have hclean : ∀ p ∈ W ∩ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T := fun p hp =>
    bigon_boundary_map_avoids_sheets hh k l hmapU hmapV hflo hfhi (hWUV hp.1) hp.2
  have hcompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, hC, hCclosed, hfrontC, hCW⟩ := exists_compact_closed_between hcompact hW hfrontW
  have hemb : Topology.IsClosedEmbedding (fun p : C => f p) := by
    let : CompactSpace C := isCompact_iff_compactSpace.mp hC
    have hc : Continuous (fun p : C => f p) :=
      continuousOn_iff_continuous_domRestrict.mp (hf.continuousOn.mono (hCW.trans hWUV))
    apply hc.isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinj (hCW p.property) (hCW q.property) hpq)
  refine
    ⟨f, W, hW, hf.mono hWUV, hinj, hi, hclean, C, hC, hCclosed, hfrontC, hCW, hemb, ?_, hlow,
      hupp, ?_, ?_⟩
  · intro p hp hnot
    apply hclean p ⟨hCW hp.2, ?_⟩
    by_contra hni
    apply hnot
    rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
    exact ⟨hp.1, hni⟩
  · intro t ht
    exact Filter.mem_of_superset (hU.mem_nhds (hlowU ht)) (fun _ hp => hflo hp)
  · intro t ht
    exact Filter.mem_of_superset (hV.mem_nhds (huppV ht)) (fun _ hp => hfhi hp)

theorem nonempty_cleanBigonBoundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M} {a b a₀ b₀ a₁ b₁ : ℝ → M}
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀) (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    Nonempty (CleanBigonBoundary (E := E) S T a b k.map l.map h) := by
  obtain
    ⟨f, W, hW, hf, hinj, hi, havoid, C, hC, hCc, hfront, hCW, hemb, hclean, hlow, hupp, hlowg,
      huppg⟩ :=
    exists_clean_bigon_boundary_neighborhood hh c₀ c₁ k l hover
  exact
    ⟨{  height_pos := hh
        map := f
        domain := W
        open_domain := hW
        smooth := hf
        injective := hinj
        derivative_injective := hi
        interior_avoids := havoid
        closed_neighborhood := C
        compact_neighborhood := hC
        closed_closed_neighborhood := hCc
        boundary_covered := hfront
        neighborhood_subset := hCW
        closed_embedding := hemb
        clean := hclean
        lower := hlow
        upper := hupp
        lower_germ := hlowg
        upper_germ := huppg }⟩

def SphereCone.point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : unitInterval × Metric.sphere (0 : E) 1) : Metric.closedBall (0 : E) 1 :=
  ⟨(1 - (p.1 : ℝ)) • (p.2 : E),
    by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr p.1.2.2), mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
    linarith [p.1.2.1]⟩

theorem SphereCone.norm_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : unitInterval × Metric.sphere (0 : E) 1) : ‖(point p : E)‖ = 1 - (p.1 : ℝ) := by
  change ‖(1 - (p.1 : ℝ)) • (p.2 : E)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.1.2.2),
    mem_sphere_zero_iff_norm.mp p.2.property, mul_one]

theorem SphereCone.continuous_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (point (E := E)) := by
  apply Continuous.subtype_mk
  exact
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)

theorem SphereCone.point_fibers {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : unitInterval × Metric.sphere (0 : E) 1} (hpq : point p = point q) :
    p = q ∨ (p.1 = 1 ∧ q.1 = 1) := by
  have hnorm := congrArg (fun x : Metric.closedBall (0 : E) 1 => ‖(x : E)‖) hpq
  rw [norm_point, norm_point] at hnorm
  have ht : p.1 = q.1 := Subtype.ext (by linarith)
  rcases p with ⟨t, x⟩
  rcases q with ⟨s, y⟩
  dsimp only at ht
  subst s
  by_cases htop : t = 1
  · exact Or.inr ⟨htop, htop⟩
  · have htval : (t : ℝ) ≠ 1 := fun heq => htop (Subtype.ext heq)
    have hnonzero : 1 - (t : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm htval)
    have hvec : (1 - (t : ℝ)) • (x : E) = (1 - (t : ℝ)) • (y : E) := congrArg Subtype.val hpq
    have hxy : x = y := Subtype.ext ((smul_right_injective E hnonzero) hvec)
    exact Or.inl (congrArg (fun z => (t, z)) hxy)

theorem SphereCone.surjective_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nonempty (Metric.sphere (0 : E) 1)] : Function.Surjective (point (E := E)) := by
  intro x
  by_cases hx : (x : E) = 0
  · refine ⟨(1, Classical.choice inferInstance), ?_⟩
    apply Subtype.ext
    change (1 - (1 : ℝ)) • _ = (x : E)
    rw [sub_self, zero_smul, hx]
  · have hxnorm : ‖(x : E)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
    let t : unitInterval :=
      ⟨1 - ‖(x : E)‖, sub_nonneg.mpr hxnorm, by linarith [norm_nonneg (x : E)]⟩
    refine ⟨(t, RadialExtension.direction (x : E) hx), ?_⟩
    apply Subtype.ext
    change (1 - (1 - ‖(x : E)‖)) • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
    rw [sub_sub_cancel, smul_inv_smul₀ (norm_ne_zero_iff.mpr hx)]

theorem SphereCone.isQuotientMap_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nonempty (Metric.sphere (0 : E) 1)] [FiniteDimensional ℝ E] :
    Topology.IsQuotientMap (point (E := E)) := by
  let : CompactSpace (Metric.sphere (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  exact .of_surjective_continuous surjective_point continuous_point

theorem SphereCone.homotopy_eq_of_point_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] (f : C(Metric.sphere (0 : E) 1, M)) (c : M)
    (H : f.Homotopy (ContinuousMap.const _ c)) {p q : unitInterval × Metric.sphere (0 : E) 1}
    (hpq : point p = point q) : H p = H q := by
  rcases point_fibers hpq with h | ⟨hp, hq⟩
  · exact congrArg H h
  · have hp' : p = (1, p.2) := Prod.ext hp rfl
    have hq' : q = (1, q.2) := Prod.ext hq rfl
    rw [hp', hq', H.apply_one, H.apply_one]
    rfl

def SphereCone.extensionFun {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) (x : Metric.closedBall (0 : E) 1) : M :=
  H (Function.surjInv surjective_point x)

theorem SphereCone.extensionFun_point {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c))
    (p : unitInterval × Metric.sphere (0 : E) 1) : extensionFun f c H (point p) = H p :=
  homotopy_eq_of_point_eq f c H (Function.surjInv_eq surjective_point (point p))

def SphereCone.extension {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) [FiniteDimensional ℝ E] :
    C(Metric.closedBall (0 : E) 1, M)
    where
  toFun := extensionFun f c H
  continuous_toFun := by
    apply isQuotientMap_point.continuous_iff.mpr
    have heq : extensionFun f c H ∘ point = H := funext (extensionFun_point f c H)
    rw [heq]
    exact H.continuous

theorem SphereCone.extension_boundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) [FiniteDimensional ℝ E]
    (x : Metric.sphere (0 : E) 1) :
    extension f c H ⟨x, Metric.sphere_subset_closedBall x.property⟩ = f x := by
  have heq :
    (⟨(x : E), Metric.sphere_subset_closedBall x.property⟩ : Metric.closedBall (0 : E) 1) =
      point (0, x) := by
    apply Subtype.ext
    change (x : E) = (1 - (0 : ℝ)) • (x : E)
    rw [sub_zero, one_smul]
  change extensionFun f c H _ = f x
  rw [heq, extensionFun_point, H.apply_zero]

theorem SphereCone.extension_zero {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) [FiniteDimensional ℝ E] :
    extension f c H ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = c := by
  let x : Metric.sphere (0 : E) 1 := Classical.choice inferInstance
  have heq :
    (⟨0, Metric.mem_closedBall_self zero_le_one⟩ : Metric.closedBall (0 : E) 1) = point (1, x) := by
    apply Subtype.ext
    change (0 : E) = (1 - (1 : ℝ)) • (x : E)
    rw [sub_self, zero_smul]
  change extensionFun f c H _ = c
  rw [heq, extensionFun_point, H.apply_one]
  rfl

def AnnularExtension.unitClamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (x : E) : E :=
  (Max.max a ‖x‖)⁻¹ • x

theorem AnnularExtension.max_radius_pos {E : Type*} [NormedAddCommGroup E] {a : ℝ}
    (ha : 0 < a) (x : E) : 0 < Max.max a ‖x‖ :=
  ha.trans_le (le_max_left _ _)

theorem AnnularExtension.continuous_unitClamp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) : Continuous (unitClamp (E := E) a) :=
  ((continuous_const.max continuous_norm).inv₀ (fun x => (max_radius_pos ha x).ne')).smul
    continuous_id

theorem AnnularExtension.norm_unitClamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (x : E) : ‖unitClamp a x‖ = ‖x‖ / Max.max a ‖x‖ := by
  rw [unitClamp, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (max_radius_pos ha x)),
    div_eq_mul_inv, mul_comm]

theorem AnnularExtension.norm_unitClamp_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) (x : E) : ‖unitClamp a x‖ ≤ 1 := by
  rw [norm_unitClamp ha]
  exact (div_le_one (max_radius_pos ha x)).mpr (le_max_right _ _)

def AnnularExtension.innerDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ}
    (ha : 0 < a) : C(E, Metric.closedBall (0 : E) 1)
    where
  toFun x := ⟨unitClamp a x, mem_closedBall_zero_iff.mpr (norm_unitClamp_le ha x)⟩
  continuous_toFun := (continuous_unitClamp ha).subtype_mk _

theorem AnnularExtension.unitClamp_of_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} {x : E} (hx : ‖x‖ ≤ a) : unitClamp a x = a⁻¹ • x := by
  rw [unitClamp, max_eq_left hx]

def AnnularExtension.clamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (x : E) : E :=
  a • unitClamp a x

theorem AnnularExtension.continuous_clamp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) : Continuous (clamp (E := E) a) :=
  continuous_const.smul (continuous_unitClamp ha)

theorem AnnularExtension.clamp_of_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) {x : E} (hx : ‖x‖ ≤ a) : clamp a x = x := by
  rw [clamp, unitClamp_of_norm_le hx, smul_inv_smul₀ ha.ne']

theorem AnnularExtension.norm_clamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (x : E) : ‖clamp a x‖ = Min.min a ‖x‖ := by
  by_cases hx : ‖x‖ ≤ a
  · rw [clamp_of_norm_le ha hx, min_eq_right hx]
  · have hx' : a ≤ ‖x‖ := le_of_not_ge hx
    have hnorm : ‖x‖ ≠ 0 := (ha.trans_le hx').ne'
    rw [clamp, norm_smul, Real.norm_eq_abs, abs_of_pos ha, norm_unitClamp ha, max_eq_right hx',
      div_self hnorm, mul_one, min_eq_left hx']

theorem AnnularExtension.clamp_mem_annulus {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} (hb : 0 < b) (hab : a ≤ b) {x : E} (hx : a ≤ ‖x‖) :
    a ≤ ‖clamp b x‖ ∧ ‖clamp b x‖ ≤ b := by
  rw [norm_clamp hb]
  exact ⟨le_min hab hx, min_le_left _ _⟩

def AnnularExtension.exteriorFactor {E : Type*} [NormedAddCommGroup E] (a : ℝ) (x : E) :
    ℝ :=
  Min.min 1 (Max.max 0 (2 - ‖x‖ / a))

theorem AnnularExtension.exteriorFactor_nonneg {E : Type*} [NormedAddCommGroup E] (a : ℝ)
    (x : E) : 0 ≤ exteriorFactor a x :=
  le_min zero_le_one (le_max_left _ _)

theorem AnnularExtension.exteriorFactor_le_one {E : Type*} [NormedAddCommGroup E] (a : ℝ)
    (x : E) : exteriorFactor a x ≤ 1 :=
  min_le_left _ _

def AnnularExtension.exteriorVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (x : E) : E :=
  exteriorFactor a x • unitClamp a x

theorem AnnularExtension.continuous_exteriorVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) : Continuous (exteriorVector (E := E) a) := by
  have hf : Continuous (exteriorFactor (E := E) a) := by unfold exteriorFactor; fun_prop
  exact hf.smul (continuous_unitClamp ha)

theorem AnnularExtension.norm_exteriorVector_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) (x : E) : ‖exteriorVector a x‖ ≤ 1 := by
  rw [exteriorVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (exteriorFactor_nonneg a x)]
  calc
    _ ≤ 1 * 1 :=
      mul_le_mul (exteriorFactor_le_one a x) (norm_unitClamp_le ha x) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

def AnnularExtension.exteriorDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) : C(E, Metric.closedBall (0 : E) 1)
    where
  toFun x := ⟨exteriorVector a x, mem_closedBall_zero_iff.mpr (norm_exteriorVector_le ha x)⟩
  continuous_toFun := (continuous_exteriorVector ha).subtype_mk _

theorem AnnularExtension.exteriorVector_on_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) {x : E} (hx : ‖x‖ = a) :
    exteriorVector a x = unitClamp a x := by
  have hf : exteriorFactor a x = 1 := by
    unfold exteriorFactor
    rw [hx, div_self ha.ne']
    norm_num
  rw [exteriorVector, hf, one_smul]

theorem AnnularExtension.exteriorVector_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) {x : E} (hx : 2 * a ≤ ‖x‖) : exteriorVector a x = 0 := by
  have hdiv : 2 ≤ ‖x‖ / a := (le_div_iff₀ ha).mpr hx
  have hf : exteriorFactor a x = 0 := by
    unfold exteriorFactor
    rw [max_eq_left (by linarith : 2 - ‖x‖ / a ≤ 0), min_eq_right zero_le_one]
  rw [exteriorVector, hf, zero_smul]

theorem AnnularExtension.disk_extension_on_radius {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] {a : ℝ} (ha : 0 < a) {g : E → M}
    (F : C(Metric.closedBall (0 : E) 1, M))
    (hF :
      ∀ v : Metric.sphere (0 : E) 1,
        F ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    {x : E} (hx : ‖x‖ = a) : F (innerDisk ha x) = g x := by
  let v : Metric.sphere (0 : E) 1 :=
    ⟨unitClamp a x, by
      rw [mem_sphere_zero_iff_norm, norm_unitClamp ha, hx, max_self, div_self ha.ne']⟩
  have heq : innerDisk ha x = ⟨(v : E), Metric.sphere_subset_closedBall v.property⟩ := rfl
  rw [heq, hF]
  change g (clamp a x) = g x
  rw [clamp_of_norm_le ha hx.le]

theorem AnnularExtension.exterior_extension_on_radius {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] {a : ℝ} (ha : 0 < a) {g : E → M}
    (F : C(Metric.closedBall (0 : E) 1, M))
    (hF :
      ∀ v : Metric.sphere (0 : E) 1,
        F ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    {x : E} (hx : ‖x‖ = a) : F (exteriorDisk ha x) = g x := by
  have heq : exteriorDisk ha x = innerDisk ha x := Subtype.ext (exteriorVector_on_sphere ha hx)
  rw [heq]
  exact disk_extension_on_radius ha F hF hx

theorem AnnularExtension.exists_continuous_annular_extension {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {g : E → M} (hg : ContinuousOn g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b})
    (F₀ F₁ : C(Metric.closedBall (0 : E) 1, M))
    (hF₀ :
      ∀ v : Metric.sphere (0 : E) 1,
        F₀ ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    (hF₁ :
      ∀ v : Metric.sphere (0 : E) 1,
        F₁ ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (b • (v : E))) :
    ∃ G : C(E, M),
      Set.EqOn G g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ∧
        ∀ x, 2 * b ≤ ‖x‖ → G x = F₁ ⟨0, Metric.mem_closedBall_self zero_le_one⟩ := by
  classical
  have hb : 0 < b := ha.trans hab
  let inner : C(E, M) := F₀.comp (innerDisk ha)
  let outer : C(E, M) := F₁.comp (exteriorDisk hb)
  let middle : E → M := g ∘ clamp b
  have houtside : closure (Metric.closedBall (0 : E) a)ᶜ ⊆ {x : E | a ≤ ‖x‖} := by
    apply closure_minimal
    · intro x hx
      have hn : ¬‖x‖ ≤ a := by simpa only [Set.mem_compl_iff, mem_closedBall_zero_iff] using hx
      exact le_of_lt (lt_of_not_ge hn)
    · exact isClosed_le continuous_const continuous_norm
  have hmiddle : ContinuousOn middle (closure (Metric.closedBall (0 : E) a)ᶜ) :=
    hg.comp (continuous_clamp hb).continuousOn
      (fun _ hx => clamp_mem_annulus hb hab.le (houtside hx))
  have hjoin₀ : ∀ x ∈ frontier (Metric.closedBall (0 : E) a), inner x = middle x := by
    intro x hx
    rw [frontier_closedBall _ ha.ne'] at hx
    have hnorm : ‖x‖ = a := mem_sphere_zero_iff_norm.mp hx
    change F₀ (innerDisk ha x) = g (clamp b x)
    rw [disk_extension_on_radius ha F₀ hF₀ hnorm, clamp_of_norm_le hb (hnorm.le.trans hab.le)]
  let G₀ : E → M := (Metric.closedBall (0 : E) a).piecewise inner middle
  have hG₀ : Continuous G₀ := continuous_piecewise hjoin₀ inner.continuous.continuousOn hmiddle
  have hG₀eq : Set.EqOn G₀ g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
    intro x hx
    by_cases hxa : x ∈ Metric.closedBall (0 : E) a
    · have hnorm : ‖x‖ = a := le_antisymm (mem_closedBall_zero_iff.mp hxa) hx.1
      change ((Metric.closedBall (0 : E) a).piecewise inner middle) x = g x
      rw [Set.piecewise_eq_of_mem _ _ _ hxa]
      exact disk_extension_on_radius ha F₀ hF₀ hnorm
    · change ((Metric.closedBall (0 : E) a).piecewise inner middle) x = g x
      rw [Set.piecewise_eq_of_notMem _ _ _ hxa]
      change g (clamp b x) = g x
      rw [clamp_of_norm_le hb hx.2]
  have hjoin₁ : ∀ x ∈ frontier (Metric.closedBall (0 : E) b), G₀ x = outer x := by
    intro x hx
    rw [frontier_closedBall _ hb.ne'] at hx
    have hnorm : ‖x‖ = b := mem_sphere_zero_iff_norm.mp hx
    rw [hG₀eq (show a ≤ ‖x‖ ∧ ‖x‖ ≤ b by rw [hnorm]; exact ⟨hab.le, le_rfl⟩)]
    exact (exterior_extension_on_radius hb F₁ hF₁ hnorm).symm
  let G : C(E, M) :=
    ⟨(Metric.closedBall (0 : E) b).piecewise G₀ outer, hG₀.piecewise hjoin₁ outer.continuous⟩
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    change ((Metric.closedBall (0 : E) b).piecewise G₀ outer) x = g x
    rw [Set.piecewise_eq_of_mem _ _ _ (mem_closedBall_zero_iff.mpr hx.2)]
    exact hG₀eq hx
  · intro x hx
    have hxb : x ∉ Metric.closedBall (0 : E) b := by
      rw [mem_closedBall_zero_iff]
      linarith
    change ((Metric.closedBall (0 : E) b).piecewise G₀ outer) x = _
    rw [Set.piecewise_eq_of_notMem _ _ _ hxb]
    change F₁ (exteriorDisk hb x) = F₁ ⟨0, Metric.mem_closedBall_self zero_le_one⟩
    apply congrArg F₁
    exact Subtype.ext (exteriorVector_eq_zero hb hx)

theorem AnnularExtension.dist_direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) : Dist.dist x (RadialExtension.direction x hx : E) = |‖x‖ - 1| := by
  let v := RadialExtension.direction x hx
  have hvec : ‖x‖ • (v : E) = x := smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) x
  have hn : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  change Dist.dist x (v : E) = _
  calc
    _ = ‖(‖x‖ - 1) • (v : E)‖ := by rw [dist_eq_norm, sub_smul, one_smul, hvec]
    _ = |‖x‖ - 1| := by rw [norm_smul, Real.norm_eq_abs, hn, mul_one]

theorem AnnularExtension.exists_closed_annulus_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {W : Set E} (hW : IsOpen W)
    (hSW : Metric.sphere (0 : E) 1 ⊆ W) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧ {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ⊆ W := by
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_sphere (0 : E) 1).exists_cthickening_subset_open hW hSW
  let ε := Min.min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεsmall : ε ≤ 1 / 2 := min_le_right _ _
  have hεδ : ε ≤ δ := (min_le_left _ _).trans (by linarith)
  refine ⟨1 - ε, 1 + ε, by linarith, by linarith, by linarith, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro heq
    have hxlo := hx.1
    rw [heq, norm_zero] at hxlo
    linarith
  have hdist : Dist.dist x (RadialExtension.direction x hx0 : E) ≤ δ := by
    rw [dist_direction]
    apply le_trans (abs_le.mpr ?_) hεδ
    constructor <;> linarith [hx.1, hx.2]
  exact
    hδW
      (Metric.mem_cthickening_of_dist_le x (RadialExtension.direction x hx0) δ
        (Metric.sphere (0 : E) 1) (RadialExtension.direction x hx0).property hdist)

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

theorem ClosedHemisphere.unit_norm {E : Type*} [NormedAddCommGroup E]
    (x : UnitSphere E) : ‖(x : E)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

abbrev Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

noncomputable def normalizedSphereMap {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (g : C(X, E)) (hg : ∀ x, g x ≠ 0) :
    C(X, UnitSphere E) := by
  let gN : X → E := fun x ↦ NormedSpace.normalize (g x)
  have hm : ∀ x, gN x ∈ UnitSphere E := by
    intro x
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize (hg x)
  have hc : Continuous gN :=
    (g.continuous.norm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr (hg x))).smul g.continuous
  exact ⟨fun x ↦ ⟨gN x, hm x⟩, hc.subtype_mk hm⟩

theorem nearby_unit_ne_zero {E : Type*} [NormedAddCommGroup E] (a : UnitSphere E) (b : E)
    (h : Dist.dist b (a : E) < 1) : b ≠ 0 := by
  intro hb
  rw [hb, dist_zero_left, ClosedHemisphere.unit_norm] at h
  exact (lt_irrefl 1) h

theorem nearby_segment_dist_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : UnitSphere E) (b : E) (h : Dist.dist b (a : E) < 1) (t : (unitInterval)) :
    Dist.dist ((a : E) + (t : ℝ) • (b - (a : E))) (a : E) < 1 := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  calc
    (t : ℝ) * ‖b - (a : E)‖ ≤ ‖b - (a : E)‖ := mul_le_of_le_one_left (norm_nonneg _) t.2.2
    _ < 1 := by simpa only [dist_eq_norm] using h

theorem nearby_segment_ne_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : UnitSphere E) (b : E) (h : Dist.dist b (a : E) < 1) (t : (unitInterval)) :
    (a : E) + (t : ℝ) • (b - (a : E)) ≠ 0 :=
  nearby_unit_ne_zero a _ (nearby_segment_dist_lt a b h t)

noncomputable def nearbyNormalizationHomotopy {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : C(X, UnitSphere E)) (g : C(X, E))
    (h : ∀ x, Dist.dist (g x) (f x : E) < 1) :
    f.Homotopy (normalizedSphereMap g (fun x ↦ nearby_unit_ne_zero (f x) (g x) (h x)))
    where
  toFun
    p :=
    ⟨NormedSpace.normalize ((f p.2 : E) + (p.1 : ℝ) • (g p.2 - (f p.2 : E))), by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        NormedSpace.norm_normalize (nearby_segment_ne_zero (f p.2) (g p.2) (h p.2) p.1)⟩
  continuous_toFun := by
    have hf : Continuous (fun p : (unitInterval) × X ↦ (f p.2 : E)) :=
      continuous_subtype_val.comp (f.continuous.comp continuous_snd)
    have hg := g.continuous.comp (continuous_snd : Continuous (Prod.snd : (unitInterval) × X → X))
    have ht : Continuous (fun p : (unitInterval) × X ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hb := hf.add (ht.smul (hg.sub hf))
    exact
      ((hb.norm.inv₀
                (fun p ↦
                  norm_ne_zero_iff.mpr (nearby_segment_ne_zero (f p.2) (g p.2) (h p.2) p.1))).smul
            hb).subtype_mk
        _
  map_zero_left
    x := by
    apply Subtype.ext
    change NormedSpace.normalize ((f x : E) + (0 : ℝ) • (g x - (f x : E))) = (f x : E)
    simpa only [zero_smul, add_zero] using
      NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (f x))
  map_one_left
    x := by
    apply Subtype.ext
    change
      NormedSpace.normalize ((f x : E) + (1 : ℝ) • (g x - (f x : E))) =
        NormedSpace.normalize (g x)
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]

theorem contMDiff_normalize {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M] {g : M → E}
    (hg : ContMDiff I 𝓘(ℝ, E) ∞ g) (hn : ∀ x, g x ≠ 0) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun x ↦ NormedSpace.normalize (g x)) := by
  intro x
  have hN : ContDiffAt ℝ ∞ (NormedSpace.normalize : E → E) (g x) :=
    ((contDiffAt_norm ℝ (hn x)).inv (norm_ne_zero_iff.mpr (hn x))).smul contDiffAt_id
  exact hN.comp_contMDiffAt (f := g) (x := x) (hg x)

theorem exists_smoothSphereRepresentative {B H M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M]
    [ChartedSpace H M] [FiniteDimensional ℝ B] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] (n : ℕ) (f : C(M, Sphere n)) :
    ∃ g : C(M, Sphere n), ContMDiff I (𝓡 n) ∞ g ∧ f.Homotopic g := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hf : Continuous (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) :=
    continuous_subtype_val.comp f.continuous
  obtain ⟨g, hg, _⟩ :=
    hf.exists_contMDiff_approx I (⊤ : ℕ∞) (ε := fun _ ↦ 1) continuous_const (fun _ ↦ zero_lt_one)
  let gC : C(M, EuclideanSpace ℝ (Fin (n + 1))) := ⟨g, g.contMDiff.continuous⟩
  have hn : ∀ x, gC x ≠ 0 := fun x ↦ nearby_unit_ne_zero (f x) (gC x) (hg x)
  refine ⟨normalizedSphereMap gC hn, ?_, ⟨nearbyNormalizationHomotopy f gC hg⟩⟩
  exact
    (contMDiff_normalize g.contMDiff hn).codRestrict_sphere (n := n)
      (fun x ↦ (normalizedSphereMap gC hn x).2)

noncomputable def chartContractionHomotopy {X Y E : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (f : C(X, Y))
    (c : OpenPartialHomeomorph Y E) (ht : c.target = Set.univ) (hf : ∀ x, f x ∈ c.source) :
    f.Homotopy (ContinuousMap.const _ (c.symm 0))
    where
  toFun p := c.symm ((1 - (p.1 : ℝ)) • c (f p.2))
  continuous_toFun := by
    have hc : Continuous (fun x ↦ c (f x)) := c.continuousOn.comp_continuous f.continuous hf
    have hci : Continuous c.symm := by
      apply continuousOn_univ.mp
      rw [← ht]
      exact c.symm.continuousOn
    exact
      hci.comp
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (hc.comp continuous_snd))
  map_zero_left
    x := by
    change c.symm ((1 - (0 : ℝ)) • c (f x)) = f x
    rw [sub_zero, one_smul]
    exact c.left_inv (hf x)
  map_one_left
    x := by
    change c.symm ((1 - (1 : ℝ)) • c (f x)) = c.symm 0
    rw [sub_self, zero_smul]

theorem sphereMap_nullhomotopic_of_omitted_point {X : Type*} [TopologicalSpace X] (n : ℕ)
    (f : C(X, Sphere n)) (p : Sphere n) (hp : ∀ x, f x ≠ p) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let c := stereographic' n p
  have hf : ∀ x, f x ∈ c.source := by
    intro x
    simpa only [c, stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using hp x
  exact ⟨c.symm 0, ⟨chartContractionHomotopy f c (stereographic'_target (n := n) p) hf⟩⟩

theorem sphereMap_nullhomotopic_of_dim_lt {B H M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    [T2Space M] (n : ℕ) (f : C(M, Sphere n)) (hd : Module.finrank ℝ B < n) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  classical
  obtain ⟨g, hg, hfg⟩ := exists_smoothSphereRepresentative (I := I) n f
  let : Nonempty (Sphere n) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  have hn : ¬Function.Surjective g :=
    not_surjective_contMDiff_of_dim_lt hg (by simpa only [finrank_euclideanSpace_fin] using hd)
  obtain ⟨p, hp⟩ : ∃ p, ∀ x, g x ≠ p := by
    simpa only [Function.Surjective, Classical.not_forall, not_exists] using hn
  obtain ⟨c, hgc⟩ := sphereMap_nullhomotopic_of_omitted_point n g p hp
  exact ⟨c, hfg.trans hgc⟩

theorem sphere_sphere_nullhomotopic {m n : ℕ} (hmn : m < n) (f : C(Sphere m, Sphere n)) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) :=
  sphereMap_nullhomotopic_of_dim_lt (I := 𝓡 m) n f
    (by simpa only [finrank_euclideanSpace_fin] using hmn)

theorem nullhomotopic_of_homotopySixSphere_comp {X M : Type*} [TopologicalSpace X]
    [TopologicalSpace M] (e : M ≃ₕ SixSphere) (g : C(X, M))
    (h : ∃ c, (e.toFun.comp g).Homotopic (ContinuousMap.const X c)) :
    ∃ c, g.Homotopic (ContinuousMap.const X c) := by
  obtain ⟨c, hnull⟩ := h
  have h₀ : (e.invFun.comp (e.toFun.comp g)).Homotopic g :=
    e.left_inv.comp (ContinuousMap.Homotopic.refl g)
  have h₁ : (e.invFun.comp (e.toFun.comp g)).Homotopic (ContinuousMap.const X (e.invFun c)) :=
    (ContinuousMap.Homotopic.refl e.invFun).comp hnull
  exact ⟨e.invFun c, h₀.symm.trans h₁⟩

theorem manifoldMap_nullhomotopic_of_homotopySixSphere {X M : Type*} [TopologicalSpace X]
    [TopologicalSpace M] {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [TopologicalSpace H] (I : ModelWithCorners ℝ B H) [I.Boundaryless]
    [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X] (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ B < 6) (g : C(X, M)) : ∃ c, g.Homotopic (ContinuousMap.const _ c) :=
  nullhomotopic_of_homotopySixSphere_comp e g
    (sphereMap_nullhomotopic_of_dim_lt (I := I) 6 (e.toFun.comp g) hdim)

theorem exists_circle_neighborhood_extension_of_circle_nullhomotopies {M : Type*}
    [TopologicalSpace M]
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (ContinuousMap.const _ c))
    {g : Hemisphere.Ambient 2 → M} {W : Set (Hemisphere.Ambient 2)} (hW : IsOpen W)
    (hg : ContinuousOn g W) (hSW : Metric.sphere (0 : Hemisphere.Ambient 2) 1 ⊆ W) :
    ∃ G : C(Hemisphere.Ambient 2, M),
      ∃ c : M,
        ∃ K : Set (Hemisphere.Ambient 2),
          IsCompact K ∧
            (∀ x ∉ K, G x = c) ∧
              ∃ U : Set (Hemisphere.Ambient 2),
                IsOpen U ∧
                  Metric.sphere (0 : Hemisphere.Ambient 2) 1 ⊆ U ∧ U ⊆ W ∧ Set.EqOn G g U := by
  obtain ⟨a, b, ha, ha1, h1b, hAW⟩ := AnnularExtension.exists_closed_annulus_subset hW hSW
  have hab : a < b := ha1.trans h1b
  have hb : 0 < b := ha.trans hab
  let A : Set (Hemisphere.Ambient 2) := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  have hgA : ContinuousOn g A := hg.mono hAW
  have hscale (r : ℝ) (hr : r ∈ Set.Icc a b) (v : Hemisphere.Sphere 1) :
    r • (v : Hemisphere.Ambient 2) ∈ A := by
    have hr0 : 0 < r := ha.trans_le hr.1
    have hnorm : ‖r • (v : Hemisphere.Ambient 2)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, mem_sphere_zero_iff_norm.mp v.property,
        mul_one]
    change a ≤ ‖r • (v : Hemisphere.Ambient 2)‖ ∧ ‖r • (v : Hemisphere.Ambient 2)‖ ≤ b
    rw [hnorm]
    exact hr
  have hcontinuous (r : ℝ) :
    Continuous (fun v : Hemisphere.Sphere 1 => r • (v : Hemisphere.Ambient 2)) := by fun_prop
  let f₀ : C(Hemisphere.Sphere 1, M) :=
    ⟨fun v => g (a • (v : Hemisphere.Ambient 2)),
      hgA.comp_continuous (hcontinuous a) (hscale a ⟨le_rfl, hab.le⟩)⟩
  let f₁ : C(Hemisphere.Sphere 1, M) :=
    ⟨fun v => g (b • (v : Hemisphere.Ambient 2)),
      hgA.comp_continuous (hcontinuous b) (hscale b ⟨hab.le, le_rfl⟩)⟩
  obtain ⟨c₀, ⟨H₀⟩⟩ := hnull f₀
  obtain ⟨c₁, ⟨H₁⟩⟩ := hnull f₁
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let : Nonempty (Metric.sphere (0 : Hemisphere.Ambient 2) 1) := ⟨⟨v, hv⟩⟩
  let F₀ := SphereCone.extension f₀ c₀ H₀
  let F₁ := SphereCone.extension f₁ c₁ H₁
  obtain ⟨G, hGeq, hGconst⟩ :=
    AnnularExtension.exists_continuous_annular_extension ha hab hgA F₀ F₁
      (SphereCone.extension_boundary f₀ c₀ H₀) (SphereCone.extension_boundary f₁ c₁ H₁)
  let U : Set (Hemisphere.Ambient 2) := {x | a < ‖x‖ ∧ ‖x‖ < b}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hUA : U ⊆ A := fun _ hx => ⟨hx.1.le, hx.2.le⟩
  refine
    ⟨G, c₁, Metric.closedBall 0 (2 * b), ProperSpace.isCompact_closedBall _ _, ?_, U, hU, ?_,
      hUA.trans hAW, hGeq.mono hUA⟩
  · intro x hx
    have hn : 2 * b < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hx
    rw [hGconst x hn.le]
    exact SphereCone.extension_zero f₁ c₁ H₁
  · intro x hx
    have hn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    change a < ‖x‖ ∧ ‖x‖ < b
    rw [hn]
    exact ⟨ha1, h1b⟩

theorem WhitneyPairModel.convex_bigon {h : ℝ} (hh : 0 ≤ h) : Convex ℝ (bigon h) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x.2 + b * y.2 ∧ h * (a * x.1 + b * y.1) ^ 2 + (a * x.2 + b * y.2) ≤ h
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_⟩
  have hsq : (a * x.1 + b * y.1) ^ 2 = a * x.1 ^ 2 + b * y.1 ^ 2 - a * b * (x.1 - y.1) ^ 2 := by
    calc
      _ = (a + b) * (a * x.1 ^ 2 + b * y.1 ^ 2) - a * b * (x.1 - y.1) ^ 2 := by ring
      _ = _ := by rw [hab, one_mul]
  calc
    _ = a * (h * x.1 ^ 2 + x.2) + b * (h * y.1 ^ 2 + y.2) - h * a * b * (x.1 - y.1) ^ 2 := by
      rw [hsq]; ring
    _ ≤ a * (h * x.1 ^ 2 + x.2) + b * (h * y.1 ^ 2 + y.2) :=
      (sub_le_self _ (mul_nonneg (mul_nonneg (mul_nonneg hh ha) hb) (sq_nonneg _)))
    _ ≤ a * h + b * h :=
      (add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb))
    _ = h := by rw [← add_mul, hab, one_mul]

theorem WhitneyPairModel.bigon_center_mem_interior {h : ℝ} (hh : 0 < h) :
    (0, h / 2) ∈ interior (bigon h) := by
  apply (mem_interior_bigon_iff h _).mpr
  change 0 < h / 2 ∧ h / 2 < h * (1 - 0 ^ 2)
  norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one]
  constructor <;> linarith

theorem WhitneyPairModel.interior_bigon_nonempty {h : ℝ} (hh : 0 < h) :
    (interior (bigon h)).Nonempty :=
  ⟨(0, h / 2), bigon_center_mem_interior hh⟩

theorem WhitneyPairModel.exists_bigon_disk_homeomorph {h : ℝ} (hh : 0 < h) :
    ∃ e : (ℝ × ℝ) ≃ₜ Hemisphere.Ambient 2,
      e '' bigon h = Metric.closedBall 0 1 ∧
        e '' interior (bigon h) = Metric.ball 0 1 ∧ e '' frontier (bigon h) = Metric.sphere 0 1 :=
  by
  let L : (ℝ × ℝ) ≃L[ℝ] Hemisphere.Ambient 2 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Hemisphere.Ambient, Module.finrank_prod])
  let K : Set (Hemisphere.Ambient 2) := L '' bigon h
  have hK : IsCompact K := (isCompact_bigon hh).image L.continuous
  have hc : Convex ℝ K := (convex_bigon hh.le).linear_image L.toLinearEquiv.toLinearMap
  have hLint : L '' interior (bigon h) = interior K := L.toHomeomorph.image_interior (bigon h)
  have hLfront : L '' frontier (bigon h) = frontier K := L.toHomeomorph.image_frontier (bigon h)
  have hne : (interior K).Nonempty := by
    rw [← hLint]
    exact (interior_bigon_nonempty hh).image L
  obtain ⟨e, heint, heclosed, hefront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hK.isBounded
  refine ⟨L.toHomeomorph.trans e, ?_, ?_, ?_⟩
  · calc
      _ = e '' (L '' bigon h) := (Set.image_image e L (bigon h)).symm
      _ = Metric.closedBall 0 1 := by
        change e '' K = _
        rwa [hK.isClosed.closure_eq] at heclosed
  · calc
      _ = e '' (L '' interior (bigon h)) := (Set.image_image e L (interior (bigon h))).symm
      _ = Metric.ball 0 1 := by rw [hLint]; exact heint
  · calc
      _ = e '' (L '' frontier (bigon h)) := (Set.image_image e L (frontier (bigon h))).symm
      _ = Metric.sphere 0 1 := by rw [hLfront]; exact hefront

theorem exists_bigon_neighborhood_extension_of_circle_nullhomotopies {M : Type*}
    [TopologicalSpace M]
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (ContinuousMap.const _ c)) {h : ℝ}
    (hh : 0 < h) {f : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hf : ContinuousOn f W)
    (hfrontW : frontier (WhitneyPairModel.bigon h) ⊆ W) :
    ∃ F : C(ℝ × ℝ, M),
      ∃ c : M,
        ∃ K : Set (ℝ × ℝ),
          IsCompact K ∧
            (∀ x ∉ K, F x = c) ∧
              ∃ U : Set (ℝ × ℝ),
                IsOpen U ∧ frontier (WhitneyPairModel.bigon h) ⊆ U ∧ U ⊆ W ∧ Set.EqOn F f U := by
  obtain ⟨φ, _, _, hφfront⟩ := WhitneyPairModel.exists_bigon_disk_homeomorph hh
  let W' : Set (Hemisphere.Ambient 2) := φ.symm ⁻¹' W
  let g : Hemisphere.Ambient 2 → M := f ∘ φ.symm
  have hW' : IsOpen W' := hW.preimage φ.symm.continuous
  have hg : ContinuousOn g W' := hf.comp φ.symm.continuous.continuousOn (fun _ hx => hx)
  have hSW : Metric.sphere (0 : Hemisphere.Ambient 2) 1 ⊆ W' := by
    intro y hy
    have hy' : y ∈ φ '' frontier (WhitneyPairModel.bigon h) := by rw [hφfront]; exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    change φ.symm (φ x) ∈ W
    rw [φ.symm_apply_apply]
    exact hfrontW hx
  obtain ⟨G, c, K', hK', hconst, U', hU', hSU', hU'W', heq⟩ :=
    exists_circle_neighborhood_extension_of_circle_nullhomotopies hnull hW' hg hSW
  let F : C(ℝ × ℝ, M) := G.comp ⟨φ, φ.continuous⟩
  let K := φ.symm '' K'
  let U := φ ⁻¹' U'
  refine ⟨F, c, K, hK'.image φ.symm.continuous, ?_, U, hU'.preimage φ.continuous, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : φ x ∉ K' := fun hmem => hx ⟨φ x, hmem, φ.symm_apply_apply x⟩
    exact hconst (φ x) hx'
  · intro x hx
    apply hSU'
    rw [← hφfront]
    exact Set.mem_image_of_mem φ hx
  · intro x hx
    have hx' : φ.symm (φ x) ∈ W := hU'W' hx
    rwa [φ.symm_apply_apply] at hx'
  · intro x hx
    change G (φ x) = f x
    rw [heq hx]
    change f (φ.symm (φ x)) = f x
    rw [φ.symm_apply_apply]

theorem exists_smooth_bigon_neighborhood_extension_of_circle_nullhomotopies {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (ContinuousMap.const _ c)) {h : ℝ}
    (hh : 0 < h) {f : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f W)
    (hfrontW : frontier (WhitneyPairModel.bigon h) ⊆ W) :
    ∃ F : C(ℝ × ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ frontier (WhitneyPairModel.bigon h) ⊆ U ∧ U ⊆ W ∧ Set.EqOn F f U := by
  obtain ⟨G, c, K, hK, hconst, V, hV, hfrontV, hVW, hGeq⟩ :=
    exists_bigon_neighborhood_extension_of_circle_nullhomotopies hnull hh hW hf.continuousOn
      hfrontW
  have hfrontCompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, _, hC, hfrontC, hCV⟩ := exists_compact_closed_between hfrontCompact hV hfrontV
  have hGV : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G V := (hf.mono hVW).congr (fun _ hx => hGeq hx)
  have hGK : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G Kᶜ :=
    (contMDiff_const (c := c)).contMDiffOn.congr (fun x hx => hconst x hx)
  obtain ⟨F, hF, hrel⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact G hK hC hV hCV hGV hGK
  refine ⟨F, hF, interior C, isOpen_interior, hfrontC, interior_subset.trans (hCV.trans hVW), ?_⟩
  intro x hx
  exact (hrel.fst_eq_snd (interior_subset hx)).symm.trans (hGeq (hCV (interior_subset hx)))

structure TubularBigon {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) (k l : (ℝ × ℝ) → M)
    (h : ℝ) (n : ℕ := 4) where
  height_pos : 0 < h
  map : C(ℝ × ℝ, M)
  smooth : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map
  closed_embedding : Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => map p)
  derivative_injective :
    ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  interior_avoids : ∀ p ∈ interior (WhitneyPairModel.bigon h), map p ∉ S ∪ T
  lower : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, 0) = a t
  upper : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t
  lower_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, map =ᶠ[𝓝 (2 * t - 1, 0)] k ∘ WhitneyPairModel.lowerStripCoordinates h
  upper_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      map =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
        l ∘ WhitneyPairModel.upperStripCoordinates h
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
      ((ℝ × ℝ) × EuclideanSpace ℝ (Fin n)) M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = map p

def WhitneyPairModel.lowerBoundaryArc (t : ℝ) : ℝ × ℝ :=
  (2 * t - 1, 0)

def WhitneyPairModel.upperBoundaryArc (h t : ℝ) : ℝ × ℝ :=
  (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))

theorem WhitneyPairModel.hasDerivAt_lowerBoundaryArc (t : ℝ) :
    HasDerivAt lowerBoundaryArc (2, 0) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  exact hs.prodMk (hasDerivAt_const t (0 : ℝ))

theorem WhitneyPairModel.hasDerivAt_upperBoundaryArc (h t : ℝ) :
    HasDerivAt (upperBoundaryArc h) (2, -4 * h * (2 * t - 1)) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  have hy : HasDerivAt (fun s : ℝ => h * (1 - (2 * s - 1) ^ 2)) (-4 * h * (2 * t - 1)) t := by
    convert HasDerivAt.const_mul h ((hasDerivAt_const t (1 : ℝ)).sub (hs.pow 2)) using 1 <;>
      first
      | rfl
      | ring
  exact hs.prodMk hy

theorem TubularBigon.lowerBoundaryArc_mem_bigon {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    WhitneyPairModel.lowerBoundaryArc t ∈ WhitneyPairModel.bigon h := by
  have hf :
    WhitneyPairModel.lowerBoundaryArc t ∈ frontier (WhitneyPairModel.bigon h) :=
    (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
      ⟨t, ht, Or.inl rfl⟩
  exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1

theorem TubularBigon.upperBoundaryArc_mem_bigon {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    WhitneyPairModel.upperBoundaryArc h t ∈ WhitneyPairModel.bigon h := by
  have hf :
    WhitneyPairModel.upperBoundaryArc h t ∈ frontier (WhitneyPairModel.bigon h) :=
    (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
      ⟨t, ht, Or.inr rfl⟩
  exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1

theorem TubularBigon.lowerBoundaryArc_zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (WhitneyPairModel.lowerBoundaryArc t, 0) ∈ tube.chart.source :=
  tube.source_contains
    ⟨tube.lowerBoundaryArc_mem_bigon ht, Metric.mem_closedBall_self tube.radius_pos.le⟩

theorem TubularBigon.upperBoundaryArc_zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (WhitneyPairModel.upperBoundaryArc h t, 0) ∈ tube.chart.source :=
  tube.source_contains
    ⟨tube.upperBoundaryArc_mem_bigon ht, Metric.mem_closedBall_self tube.radius_pos.le⟩

theorem TubularBigon.lower_chart_center_mem_target {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.chart (StripCoordinates.center t) ∈ tube.chart.target := by
  have hg := (tube.lower_germ t ht).eq_of_nhds
  dsimp only [Function.comp_apply] at hg
  rw [WhitneyPairModel.lowerStripCoordinates_lower, d.center t] at hg
  have hp := tube.chart.map_source' (tube.lowerBoundaryArc_zero_mem_source ht)
  rw [tube.zero_section, WhitneyPairModel.lowerBoundaryArc, hg] at hp
  exact hp

theorem TubularBigon.upper_chart_center_mem_target {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.chart (StripCoordinates.center t) ∈ tube.chart.target := by
  have hg := (tube.upper_germ t ht).eq_of_nhds
  dsimp only [Function.comp_apply] at hg
  rw [WhitneyPairModel.upperStripCoordinates_upper, d.center t] at hg
  have hp := tube.chart.map_source' (tube.upperBoundaryArc_zero_mem_source ht)
  rw [tube.zero_section, WhitneyPairModel.upperBoundaryArc, hg] at hp
  exact hp

theorem TubularBigon.lower_sheetTransition_center_germ {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.sheetTransition tube.chart (s, 0)) =ᶠ[𝓝 t] fun s =>
      (WhitneyPairModel.lowerBoundaryArc s, 0) :=
  d.sheetTransition_center_germ tube.chart tube.zero_section
    (WhitneyPairModel.hasDerivAt_lowerBoundaryArc t).continuousAt
    (tube.lowerBoundaryArc_zero_mem_source ht)
    (WhitneyPairModel.lowerStripCoordinates_lower h) (tube.lower_germ t ht)

theorem TubularBigon.upper_sheetTransition_center_germ {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.sheetTransition tube.chart (s, 0)) =ᶠ[𝓝 t] fun s =>
      (WhitneyPairModel.upperBoundaryArc h s, 0) :=
  d.sheetTransition_center_germ tube.chart tube.zero_section
    (WhitneyPairModel.hasDerivAt_upperBoundaryArc h t).continuousAt
    (tube.upperBoundaryArc_zero_mem_source ht)
    (WhitneyPairModel.upperStripCoordinates_upper h) (tube.upper_germ t ht)

theorem TubularBigon.lower_sheetDifferential_arc {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.sheetDifferential tube.chart t (1, 0) = ((2, 0), 0) :=
  d.sheetDifferential_arc_of_germ tube.chart ht (tube.lower_chart_center_mem_target d ht)
    (WhitneyPairModel.hasDerivAt_lowerBoundaryArc t)
    (tube.lower_sheetTransition_center_germ d ht)

theorem TubularBigon.upper_sheetDifferential_arc {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.sheetDifferential tube.chart t (1, 0) = ((2, -4 * h * (2 * t - 1)), 0) :=
  d.sheetDifferential_arc_of_germ tube.chart ht (tube.upper_chart_center_mem_target d ht)
    (WhitneyPairModel.hasDerivAt_upperBoundaryArc h t)
    (tube.upper_sheetTransition_center_germ d ht)

theorem FrameField.det_of_zero_lower_left {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (T : (D × Z) →L[ℝ] (D × Z)) (hT : ∀ u : D, (T (u, 0)).2 = 0) :
    T.toLinearMap.det =
      ((ContinuousLinearMap.fst ℝ D Z).comp
            (T.comp (ContinuousLinearMap.inl ℝ D Z))).toLinearMap.det *
        ((ContinuousLinearMap.snd ℝ D Z).comp
            (T.comp (ContinuousLinearMap.inr ℝ D Z))).toLinearMap.det := by
  classical
  let bD := Module.finBasis ℝ D
  let bZ := Module.finBasis ℝ Z
  let A := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inl ℝ D Z))
  let B := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  let K := (ContinuousLinearMap.snd ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  have hmat :
    LinearMap.toMatrix (bD.prod bZ) (bD.prod bZ) T.toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix bD bD A.toLinearMap)
        (LinearMap.toMatrix bZ bD B.toLinearMap) 0 (LinearMap.toMatrix bZ bZ K.toLinearMap) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply, hT, A, B, K]
  rw [← LinearMap.det_toMatrix (bD.prod bZ), hmat, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

theorem FrameField.det_of_fixed_first_factor {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (T : (D × Z) →L[ℝ] (D × Z)) (hT : ∀ u : D, T (u, 0) = (u, 0)) :
    T.toLinearMap.det =
      ((ContinuousLinearMap.snd ℝ D Z).comp
          (T.comp (ContinuousLinearMap.inr ℝ D Z))).toLinearMap.det := by
  classical
  let bD := Module.finBasis ℝ D
  let bZ := Module.finBasis ℝ Z
  let B := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  let K := (ContinuousLinearMap.snd ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  have hmat :
    LinearMap.toMatrix (bD.prod bZ) (bD.prod bZ) T.toLinearMap =
      Matrix.fromBlocks 1 (LinearMap.toMatrix bZ bD B.toLinearMap) 0
        (LinearMap.toMatrix bZ bZ K.toLinearMap) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, hT, B, K, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.det_toMatrix (bD.prod bZ), hmat, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    one_mul, LinearMap.det_toMatrix]

theorem FrameField.det_frame_eq_det_split_mul_det_coefficient {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : (D × Z) ≃L[ℝ] F) (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).toLinearMap.det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).toLinearMap.det *
        ((complementQuotient G C).comp L).toLinearMap.det := by
  let T := G.coprod C
  let R := G.coprod L
  let A := T.inverse.comp R
  have hA : ∀ u : D, A (u, 0) = (u, 0) := by
    intro u
    change T.inverse (G u + L 0) = (u, 0)
    rw [map_zero, add_zero]
    have hi := h.inverse_apply_self (u, 0)
    change T.inverse (G u + C 0) = (u, 0) at hi
    simpa only [map_zero, add_zero] using hi
  have hblock :
    (ContinuousLinearMap.snd ℝ D Z).comp (A.comp (ContinuousLinearMap.inr ℝ D Z)) =
      (complementQuotient G C).comp L := by
    apply ContinuousLinearMap.ext
    intro v
    change (T.inverse (G 0 + L v)).2 = (T.inverse (L v)).2
    rw [map_zero, zero_add]
  have hdetA : A.toLinearMap.det = ((complementQuotient G C).comp L).toLinearMap.det := by
    rw [det_of_fixed_first_factor A hA, hblock]
  have hfactor :
    j.symm.toContinuousLinearMap.comp R = (j.symm.toContinuousLinearMap.comp T).comp A := by
    apply ContinuousLinearMap.ext
    intro v
    change j.symm (R v) = j.symm (T (T.inverse (R v)))
    rw [h.self_apply_inverse]
  change (j.symm.toContinuousLinearMap.comp R).toLinearMap.det = _
  rw [hfactor]
  have hmul :
    ((j.symm.toContinuousLinearMap.comp T).comp A).toLinearMap.det =
      (j.symm.toContinuousLinearMap.comp T).toLinearMap.det * A.toLinearMap.det :=
    map_mul LinearMap.det _ _
  rw [hmul, hdetA]

def PlanarFrame.area (u v : PlaneImmersion.Plane) : ℝ :=
  u.1 * v.2 - u.2 * v.1

def PlanarFrame.squareLength (u : PlaneImmersion.Plane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

def PlanarFrame.quarterTurn (u : PlaneImmersion.Plane) : PlaneImmersion.Plane :=
  (-u.2, u.1)

def PlanarFrame.parallelCoeff (u v : PlaneImmersion.Plane) : ℝ :=
  (u.1 * v.1 + u.2 * v.2) / squareLength u

def PlanarFrame.transverseCoeff (u v : PlaneImmersion.Plane) : ℝ :=
  area u v / squareLength u

def PlanarFrame.determinant
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) : ℝ :=
  area (L (1, 0)) (L (0, 1))

theorem PlanarFrame.squareLength_pos {u : PlaneImmersion.Plane} (hu : u ≠ 0) :
    0 < squareLength u := by
  have hsq₁ := sq_nonneg u.1
  have hsq₂ := sq_nonneg u.2
  by_contra h
  have hz : u.1 ^ 2 + u.2 ^ 2 ≤ 0 := le_of_not_gt h
  have hu₁ : u.1 = 0 := by nlinarith
  have hu₂ : u.2 = 0 := by nlinarith
  exact hu (Prod.ext hu₁ hu₂)

theorem PlanarFrame.decompose_second_column {u : PlaneImmersion.Plane} (hu : u ≠ 0)
    (v : PlaneImmersion.Plane) :
    parallelCoeff u v • u + transverseCoeff u v • quarterTurn u = v := by
  have hnorm := (squareLength_pos hu).ne'
  ext <;> dsimp [parallelCoeff, transverseCoeff, area, quarterTurn]
  · field_simp
    simp only [squareLength]
    ring
  · field_simp
    simp only [squareLength]
    ring

theorem PlanarFrame.area_transverse (u : PlaneImmersion.Plane) (a b : ℝ) :
    area u (a • u + b • quarterTurn u) = b * squareLength u := by
  dsimp [area, quarterTurn, squareLength]
  ring

theorem PlanarFrame.linearMap_first (u v : PlaneImmersion.Plane) :
    PlaneImmersion.linearMap (u, v) (1, 0) = u := by
  simp [PlaneImmersion.linearMap_apply]

theorem PlanarFrame.linearMap_second (u v : PlaneImmersion.Plane) :
    PlaneImmersion.linearMap (u, v) (0, 1) = v := by
  simp [PlaneImmersion.linearMap_apply]

theorem PlanarFrame.linearMap_columns
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) :
    PlaneImmersion.linearMap (L (1, 0), L (0, 1)) = L := by
  apply ContinuousLinearMap.ext
  intro p
  have hp : p = p.1 • ((1 : ℝ), 0) + p.2 • (0, 1) := by ext <;> simp
  rw [PlaneImmersion.linearMap_apply, ← map_smul, ← map_smul, ← map_add, ← hp]

theorem PlanarFrame.determinant_linearMap (u v : PlaneImmersion.Plane) :
    determinant (PlaneImmersion.linearMap (u, v)) = area u v := by
  rw [determinant, linearMap_first, linearMap_second]

theorem PlanarFrame.determinant_eq_det
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) :
    determinant L = L.toLinearMap.det := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr, determinant, area, mul_comm]

theorem PlanarFrame.bijective_of_determinant_ne_zero
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (hL : determinant L ≠ 0) :
    Function.Bijective L := by
  have hdet : L.toLinearMap.det ≠ 0 := by rwa [determinant_eq_det] at hL
  have hker : L.toLinearMap.ker = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hi : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

theorem PlanarFrame.continuous_determinant : Continuous determinant := by
  have h₁ :
    Continuous
      (fun L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane => L (1, 0)) :=
    continuous_id.clm_apply continuous_const
  have h₂ :
    Continuous
      (fun L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane => L (0, 1)) :=
    continuous_id.clm_apply continuous_const
  exact (h₁.fst.mul h₂.snd).sub (h₁.snd.mul h₂.fst)

theorem PlanarFrame.continuous_quarterTurn : Continuous quarterTurn :=
  continuous_snd.neg.prodMk continuous_fst

theorem PlanarFrame.continuous_linearMap :
    Continuous
      (PlaneImmersion.linearMap :
        (PlaneImmersion.Plane × PlaneImmersion.Plane) →
          (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane)) := by
  exact
    ((ContinuousLinearMap.smulRightL ℝ PlaneImmersion.Plane PlaneImmersion.Plane
              (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.comp
          continuous_fst).add
      ((ContinuousLinearMap.smulRightL ℝ PlaneImmersion.Plane PlaneImmersion.Plane
            (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.comp
        continuous_snd)

def IntersectionCoordinates.jointBlock {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F) (P : (ℝ × A) →L[ℝ] (PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (PlaneImmersion.Plane × F)) :
    (PlaneImmersion.Plane × (A × B)) →L[ℝ] (PlaneImmersion.Plane × (A × B)) :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ PlaneImmersion.Plane)
        j.symm).toContinuousLinearMap.comp
    ((P.coprod Q).comp
      (ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B).symm.toContinuousLinearMap)

theorem IntersectionCoordinates.jointBlock_apply {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F) (P : (ℝ × A) →L[ℝ] (PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (PlaneImmersion.Plane × F))
    (p : PlaneImmersion.Plane × (A × B)) :
    jointBlock j P Q p =
      ((P (p.1.1, p.2.1) + Q (p.1.2, p.2.2)).1,
        j.symm ((P (p.1.1, p.2.1) + Q (p.1.2, p.2.2)).2)) :=
  rfl

theorem IntersectionCoordinates.map_first_axis {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : (ℝ × A) →L[ℝ] (PlaneImmersion.Plane × F)) (s : ℝ) : P (s, 0) = s • P (1, 0) := by
  have hs : (s, (0 : A)) = s • ((1 : ℝ), 0) := by ext <;> simp
  rw [hs, map_smul]

theorem IntersectionCoordinates.det_jointBlock {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] (j : (A × B) ≃L[ℝ] F)
    (P : (ℝ × A) →L[ℝ] (PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (PlaneImmersion.Plane × F)) {u v : PlaneImmersion.Plane}
    (hP : P (1, 0) = (u, 0)) (hQ : Q (1, 0) = (v, 0)) :
    (jointBlock j P Q).toLinearMap.det =
      (PlaneImmersion.linearMap (u, v)).toLinearMap.det *
        (j.symm.toContinuousLinearMap.comp
            (((ContinuousLinearMap.snd ℝ PlaneImmersion.Plane F).comp
                  (P.comp (ContinuousLinearMap.inr ℝ ℝ A))).coprod
              ((ContinuousLinearMap.snd ℝ PlaneImmersion.Plane F).comp
                (Q.comp (ContinuousLinearMap.inr ℝ ℝ B))))).toLinearMap.det := by
  have hzero : ∀ w : PlaneImmersion.Plane, (jointBlock j P Q (w, 0)).2 = 0 := by
    intro w
    rw [jointBlock_apply]
    change j.symm ((P (w.1, 0) + Q (w.2, 0)).2) = 0
    rw [map_first_axis P w.1, map_first_axis Q w.2, hP, hQ]
    simp
  have hfirst :
    (ContinuousLinearMap.fst ℝ PlaneImmersion.Plane (A × B)).comp
        ((jointBlock j P Q).comp (ContinuousLinearMap.inl ℝ PlaneImmersion.Plane (A × B))) =
      PlaneImmersion.linearMap (u, v) := by
    apply ContinuousLinearMap.ext
    intro w
    change (jointBlock j P Q (w, 0)).1 = w.1 • u + w.2 • v
    rw [jointBlock_apply]
    change (P (w.1, 0) + Q (w.2, 0)).1 = w.1 • u + w.2 • v
    rw [map_first_axis P w.1, map_first_axis Q w.2, hP, hQ]
    rfl
  have hsecond :
    (ContinuousLinearMap.snd ℝ PlaneImmersion.Plane (A × B)).comp
        ((jointBlock j P Q).comp (ContinuousLinearMap.inr ℝ PlaneImmersion.Plane (A × B))) =
      j.symm.toContinuousLinearMap.comp
        (((ContinuousLinearMap.snd ℝ PlaneImmersion.Plane F).comp
              (P.comp (ContinuousLinearMap.inr ℝ ℝ A))).coprod
          ((ContinuousLinearMap.snd ℝ PlaneImmersion.Plane F).comp
            (Q.comp (ContinuousLinearMap.inr ℝ ℝ B)))) := by
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [FrameField.det_of_zero_lower_left _ hzero, hfirst, hsecond]

theorem FrameField.bijective_coprod_of_orthogonal_range {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : D →L[ℝ] F)
    (B : Z →L[ℝ] F) (hL : Function.Injective L) (hB : Function.Injective B)
    (hr : B.range = L.rangeᗮ) : Function.Bijective (L.coprod B) := by
  have hd : Disjoint L.range B.range := by
    rw [hr]
    exact L.range.orthogonal_disjoint
  constructor
  · change Function.Injective (L.toLinearMap.coprod B.toLinearMap)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
      LinearMap.ker_eq_bot.mpr hL, LinearMap.ker_eq_bot.mpr hB, Submodule.prod_bot]
  · change Function.Surjective (L.toLinearMap.coprod B.toLinearMap)
    rw [← LinearMap.range_eq_top, LinearMap.range_coprod, hr]
    exact L.range.isCompl_orthogonal.sup_eq_top

theorem FrameField.exists_smooth_complement_near_starConvex_on {E D F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {L : E → (D →L[ℝ] F)} {O : Set E} (hO : IsOpen O) (hL : ContDiffOn ℝ ∞ L O) {K : Set E}
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K) (h0 : (0 : E) ∈ K) (hKO : K ⊆ O)
    (hi : ∀ x ∈ K, Function.Injective (L x)) (n : ℕ)
    (hdim : Module.finrank ℝ D + n = Module.finrank ℝ F) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ B : E → (EuclideanSpace ℝ (Fin n) →L[ℝ] F),
            ContDiffOn ℝ ∞ B V ∧
              (∀ x ∈ K, (B x).range = (L x).rangeᗮ) ∧
                ∀ x ∈ V, Function.Bijective ((L x).coprod (B x)) := by
  let φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ D)) ≃L[ℝ] D :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let A (x : E) := (L x).comp φ.toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A O := hL.clm_comp contDiffOn_const
  have hAr (x : E) : (A x).range = (L x).range :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
  let U : Set E := O ∩ {x | Function.Injective (L x)}
  have hU : IsOpen U :=
    hL.continuousOn.isOpen_inter_preimage hO ContinuousLinearMap.isOpen_injective
  have hKU : K ⊆ U := fun x hx => ⟨hKO hx, hi x hx⟩
  let P (x : E) : F →L[ℝ] F := 1 - gramProjection (A x)
  have hP (x : E) (hx : x ∈ U) : P x = ((L x).rangeᗮ).starProjection := by
    dsimp only [P]
    rw [gramProjection_eq_starProjection _ (hx.2.comp φ.injective)]
    simp only [hAr]
    exact (Submodule.starProjection_orthogonal' (L x).range).symm
  have hsP : ContDiffOn ℝ ∞ P U := by
    intro x hx
    have hg : ContDiffAt ℝ ∞ (fun y => gramProjection (A y)) x :=
      (contMDiffAt_gramProjection (hA.contDiffAt (hO.mem_nhds hx.1)).contMDiffAt
          (hx.2.comp φ.injective)).contDiffAt
    exact (contDiffAt_const.sub hg).contDiffWithinAt
  have hidem : ∀ x ∈ K, IsIdempotentElem (P x) := by
    intro x hx
    rw [hP x (hKU hx)]
    exact ((L x).rangeᗮ).isIdempotentElem_starProjection
  obtain ⟨W, hW, hKW, B₀, hB₀, hB₀i⟩ :=
    DiskFraming.exists_smooth_frame_near_starConvex hK hstar hU hKU P hidem hsP
  have hr (x : E) (hx : x ∈ K) : (P x).range = (L x).rangeᗮ := by
    rw [hP x (hKU hx), Submodule.range_starProjection]
  have hcenter : Module.finrank ℝ (P 0).range = n := by
    have hrank : Module.finrank ℝ (L 0).range = Module.finrank ℝ D :=
      LinearMap.finrank_range_of_inj (hi 0 h0)
    have hs := (L 0).range.finrank_add_finrank_orthogonal
    rw [hrank] at hs
    rw [hr 0 h0]
    omega
  let ψ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (P 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  let B (x : E) := (B₀ x).comp ψ.toContinuousLinearMap
  have hB : ContDiffOn ℝ ∞ B (W ∩ O) := (hB₀.clm_comp contDiffOn_const).mono Set.inter_subset_left
  have hBr : ∀ x ∈ K, (B x).range = (L x).rangeᗮ := by
    intro x hx
    calc
      (B x).range = (B₀ x).range :=
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr ψ.surjective)
      _ = (P x).range := (hB₀i x hx).2
      _ = (L x).rangeᗮ := hr x hx
  have hBi : ∀ x ∈ K, Function.Injective (B x) := fun x hx => (hB₀i x hx).1.comp ψ.injective
  let T (x : E) := (L x).coprod (B x)
  have hT : ContDiffOn ℝ ∞ T (W ∩ O) := by
    have hs :=
      ((hL.mono Set.inter_subset_right).clm_comp
            (contDiffOn_const (c := ContinuousLinearMap.fst ℝ D (EuclideanSpace ℝ (Fin n))))).add
        (hB.clm_comp
          (contDiffOn_const (c := ContinuousLinearMap.snd ℝ D (EuclideanSpace ℝ (Fin n)))))
    exact hs
  have hTi : ∀ x ∈ K, Function.Bijective (T x) := fun x hx =>
    bijective_coprod_of_orthogonal_range (L x) (B x) (hi x hx) (hBi x hx) (hBr x hx)
  let V : Set E := (W ∩ O) ∩ {x | Function.Injective (T x)}
  have hV : IsOpen V :=
    hT.continuousOn.isOpen_inter_preimage (hW.inter hO) ContinuousLinearMap.isOpen_injective
  refine
    ⟨V, hV, fun x hx => ⟨⟨hKW hx, hKO hx⟩, (hTi x hx).1⟩, B, hB.mono Set.inter_subset_left, hBr,
      ?_⟩
  intro x hx
  have hdim' : Module.finrank ℝ (D × EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ F := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact hdim
  exact ⟨hx.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hx.2⟩

theorem FrameField.exists_smooth_complement_near_starConvex {E D F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {L : E → (D →L[ℝ] F)} (hL : ContDiff ℝ ∞ L) {K : Set E} (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : E) K) (h0 : (0 : E) ∈ K) (hi : ∀ x ∈ K, Function.Injective (L x))
    (n : ℕ) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ F) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ B : E → (EuclideanSpace ℝ (Fin n) →L[ℝ] F),
            ContDiffOn ℝ ∞ B V ∧
              (∀ x ∈ K, (B x).range = (L x).rangeᗮ) ∧
                ∀ x ∈ V, Function.Bijective ((L x).coprod (B x)) :=
  exists_smooth_complement_near_starConvex_on isOpen_univ hL.contDiffOn hK hstar h0
    (Set.subset_univ K) hi n hdim

theorem TubularBigon.lower_sheetFrame {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : (ℝ × ℝ) → M} {n : ℕ} (tube : TubularBigon (E := E) S T a b k.map l h n)
    (d : StripNormalData A B (E := E) S k.map) :
    (∃ U : Set ℝ,
        IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (d.normalFrame tube.chart t) := by
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ WhitneyPairModel.bigon h := by
    intro t ht
    have hf : (2 * t - 1, 0) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inl rfl⟩
    exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1
  have hsource : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((2 * t - 1, 0), 0) ∈ tube.chart.source := fun t ht =>
    tube.source_contains ⟨hpoint t ht, Metric.mem_closedBall_self tube.radius_pos.le⟩
  constructor
  · apply d.exists_open_normalFrame_domain tube.chart
    intro t ht
    have hp := tube.chart.map_source' (hsource t ht)
    rw [tube.zero_section, tube.lower t ht] at hp
    rw [← d.center t, k.center t ht]
    exact hp
  · intro t ht
    have hkt : (t, (0 : ℝ)) ∈ k.domain :=
      k.contains_strip ⟨ht, ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩⟩
    have hcs :
      Function.Surjective
        (fderiv ℝ (WhitneyPairModel.lowerStripCoordinates h) (2 * t - 1, 0)) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (WhitneyPairModel.injective_fderiv_lowerStripCoordinates tube.height_pos.ne'
          (2 * t - 1))
    exact
      d.injective_normalFrame_of_strip_germ tube.chart ht
        (k.smooth.contMDiffAt (k.open_domain.mem_nhds hkt)) tube.zero_section (hsource t ht)
        (WhitneyPairModel.contDiff_lowerStripCoordinates tube.height_pos.ne').contDiffAt
        (WhitneyPairModel.lowerStripCoordinates_lower h t) hcs (tube.lower_germ t ht)

theorem TubularBigon.upper_sheetFrame {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} {l : CleanStripPatch (E := E) T S b k₀ k₁}
    {k : (ℝ × ℝ) → M} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l.map h n)
    (d : StripNormalData A B (E := E) T l.map) :
    (∃ U : Set ℝ,
        IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (d.normalFrame tube.chart t) := by
  have hpoint :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ WhitneyPairModel.bigon h := by
    intro t ht
    have hf :
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inr rfl⟩
    exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1
  have hsource :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ((2 * t - 1, h * (1 - (2 * t - 1) ^ 2)), 0) ∈ tube.chart.source :=
    fun t ht => tube.source_contains ⟨hpoint t ht, Metric.mem_closedBall_self tube.radius_pos.le⟩
  constructor
  · apply d.exists_open_normalFrame_domain tube.chart
    intro t ht
    have hp := tube.chart.map_source' (hsource t ht)
    rw [tube.zero_section, tube.upper t ht] at hp
    rw [← d.center t, l.center t ht]
    exact hp
  · intro t ht
    have hlt : (t, (0 : ℝ)) ∈ l.domain :=
      l.contains_strip ⟨ht, ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩⟩
    have hcs :
      Function.Surjective
        (fderiv ℝ (WhitneyPairModel.upperStripCoordinates h)
          (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (WhitneyPairModel.injective_fderiv_upperStripCoordinates tube.height_pos.ne'
          (2 * t - 1))
    exact
      d.injective_normalFrame_of_strip_germ tube.chart ht
        (l.smooth.contMDiffAt (l.open_domain.mem_nhds hlt)) tube.zero_section (hsource t ht)
        (WhitneyPairModel.contDiff_upperStripCoordinates tube.height_pos.ne').contDiffAt
        (WhitneyPairModel.upperStripCoordinates_upper h t) hcs (tube.upper_germ t ht)

theorem TubularBigon.upper_sheetFrame_complement_of_finrank {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} [FiniteDimensional ℝ A]
    {l : CleanStripPatch (E := E) T S b k₀ k₁} {k : (ℝ × ℝ) → M} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k l.map h n)
    (d : StripNormalData A B (E := E) T l.map) (m : ℕ) (hdim : Module.finrank ℝ A + m = n) :
    ∃ V : Set ℝ,
      IsOpen V ∧
        Set.Icc (0 : ℝ) 1 ⊆ V ∧
          ContDiffOn ℝ ∞ (d.normalFrame tube.chart) V ∧
            ∃ C : ℝ → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)),
              ContDiffOn ℝ ∞ C V ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1, (C t).range = (d.normalFrame tube.chart t).rangeᗮ) ∧
                  ∀ t ∈ V, Function.Bijective ((d.normalFrame tube.chart t).coprod (C t)) := by
  obtain ⟨⟨U, hU, hIU, hs⟩, hi⟩ := tube.upper_sheetFrame d
  have hstar : StarConvex ℝ (0 : ℝ) (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  have hdim' : Module.finrank ℝ A + m = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨W, hW, hIW, C, hC, hr, hc⟩ :=
    FrameField.exists_smooth_complement_near_starConvex_on hU hs
      CompactIccSpace.isCompact_Icc hstar (by simp) hIU hi m hdim'
  exact
    ⟨W ∩ U, hW.inter hU, fun t ht => ⟨hIW ht, hIU ht⟩, hs.mono Set.inter_subset_right, C,
      hC.mono Set.inter_subset_left, hr, fun t ht => hc t ht.1⟩

def DiskFraming.puncturedModel (B : Type*) [NormedAddCommGroup B] :
    TopologicalSpace.Opens B :=
  ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩

theorem DiskFraming.exists_smooth_punctured_curve_with_germ {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {a : ℝ → B} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ≠ 0) :
    ∃ f : C(ℝ, puncturedModel B),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ f ∧ (fun t => (f t : B)) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → puncturedModel B := fun t => if h : a t = 0 then ⟨a t₀, ha0⟩ else ⟨a t, h⟩
  let V := U ∩ a ⁻¹' ({0}ᶜ : Set B)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hs0 : a s ≠ 0 := hs.2
    simp only [Function.comp_apply, A, dif_neg hs0]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ A V := by
    intro t ht
    have haAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ a t :=
      (ha.contDiffAt (hU.mem_nhds ht.1)).contMDiffAt
    have hvalAt := haAt.congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff (puncturedModel B) A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨f, hf, hfgerm⟩ := exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨f, hf, ?_⟩
  filter_upwards [hfgerm, hval htV] with t ht htval
  exact (congrArg Subtype.val ht).trans htval

theorem DiskFraming.exists_nonzero_smooth_curve_with_endpoint_germs {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] {a b : ℝ → B} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V) (ha0 : a 0 ≠ 0) (hb1 : b 1 ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) :
    ∃ v : ℝ → B, ContDiff ℝ ∞ v ∧ (∀ t, v t ≠ 0) ∧ (v =ᶠ[𝓝 (0 : ℝ)] a) ∧ (v =ᶠ[𝓝 (1 : ℝ)] b) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_punctured_curve_with_germ ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_smooth_punctured_curve_with_germ hb hV h1V hb1
  have hrank : 1 < Module.rank ℝ B := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ B by omega)
  let : PathConnectedSpace (puncturedModel B) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : B))
  let γ := PathConnectedSpace.somePath (a' 0) (b' 1)
  obtain ⟨f, hf, hfa, hfb⟩ := exists_smooth_curve_with_endpoint_germs a' b' ha' hb' γ
  let v : ℝ → B := fun t => (f t : B)
  have hv : ContDiff ℝ ∞ v :=
    ((contMDiff_subtype_val (I := 𝓘(ℝ, B)) (U := puncturedModel B)).comp hf).contDiff
  refine ⟨v, hv, fun t => (f t).property, ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num), heqa] with t ht hta
    change t < 1 / 8 at ht
    exact (congrArg Subtype.val (hfa ht.le)).trans hta
  · filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num), heqb] with t ht htb
    change 7 / 8 < t at ht
    exact (congrArg Subtype.val (hfb ht.le)).trans htb

def PlanarFrame.determinantComponent (σ : ℝ) :
    TopologicalSpace.Opens (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) :=
  ⟨{L | 0 < σ * determinant L},
    isOpen_lt continuous_const (continuous_const.mul continuous_determinant)⟩

theorem PlanarFrame.first_column_ne_zero {σ : ℝ} (L : determinantComponent σ) :
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0) ≠ 0 := by
  intro hz
  have h := L.property
  change
    0 <
      σ *
        area ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
          ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1)) at h
  rw [hz] at h
  simp [area] at h

theorem PlanarFrame.signed_transverseCoeff_pos {σ : ℝ} (L : determinantComponent σ) :
    0 <
      σ *
        transverseCoeff ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
          ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1)) := by
  rw [transverseCoeff, ← mul_div_assoc]
  exact div_pos L.property (squareLength_pos (first_column_ne_zero L))

theorem PlanarFrame.nonempty_path_determinantComponent {σ : ℝ}
    (a b : determinantComponent σ) : Nonempty (Path a b) := by
  have hrank : 1 < Module.rank ℝ PlaneImmersion.Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
  let : PathConnectedSpace (DiskFraming.puncturedModel PlaneImmersion.Plane) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : PlaneImmersion.Plane))
  let a₁ : DiskFraming.puncturedModel PlaneImmersion.Plane :=
    ⟨(a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0),
      first_column_ne_zero a⟩
  let b₁ : DiskFraming.puncturedModel PlaneImmersion.Plane :=
    ⟨(b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0),
      first_column_ne_zero b⟩
  let γ := PathConnectedSpace.somePath a₁ b₁
  let v : unitInterval → PlaneImmersion.Plane := fun t => (γ t : PlaneImmersion.Plane)
  have hv : Continuous v := continuous_subtype_val.comp γ.continuous
  have hvne (t : unitInterval) : v t ≠ 0 := (γ t).property
  let α₀ :=
    parallelCoeff ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let α₁ :=
    parallelCoeff ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let β₀ :=
    transverseCoeff ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let β₁ :=
    transverseCoeff ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let α (t : unitInterval) : ℝ := (1 - (t : ℝ)) * α₀ + (t : ℝ) * α₁
  let β (t : unitInterval) : ℝ := (1 - (t : ℝ)) * β₀ + (t : ℝ) * β₁
  have hα : Continuous α :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hβ : Continuous β :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hβpos (t : unitInterval) : 0 < σ * β t := by
    have hpos : 0 < (1 - (t : ℝ)) * (σ * β₀) + (t : ℝ) * (σ * β₁) :=
      (convex_Ioi (0 : ℝ)) (signed_transverseCoeff_pos a) (signed_transverseCoeff_pos b)
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    have heq : σ * β t = (1 - (t : ℝ)) * (σ * β₀) + (t : ℝ) * (σ * β₁) := by
      dsimp only [β]
      ring
    rwa [heq]
  let F (t : unitInterval) : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane :=
    PlaneImmersion.linearMap (v t, α t • v t + β t • quarterTurn (v t))
  have hF : Continuous F :=
    continuous_linearMap.comp
      (hv.prodMk ((hα.smul hv).add (hβ.smul (continuous_quarterTurn.comp hv))))
  have hcomponent (t : unitInterval) : F t ∈ determinantComponent σ := by
    change
      0 <
        σ *
          determinant (PlaneImmersion.linearMap (v t, α t • v t + β t • quarterTurn (v t)))
    rw [determinant_linearMap, area_transverse, ← mul_assoc]
    exact mul_pos (hβpos t) (squareLength_pos (hvne t))
  have hv0 : v 0 = (a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0) :=
    congrArg Subtype.val γ.source
  have hv1 : v 1 = (b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0) :=
    congrArg Subtype.val γ.target
  have hF0 : F 0 = (a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) := by
    change PlaneImmersion.linearMap (v 0, α 0 • v 0 + β 0 • quarterTurn (v 0)) = _
    have hα0 : α 0 = α₀ := by simp [α]
    have hβ0 : β 0 = β₀ := by simp [β]
    rw [hv0, hα0, hβ0, decompose_second_column (first_column_ne_zero a)]
    exact linearMap_columns a
  have hF1 : F 1 = (b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) := by
    change PlaneImmersion.linearMap (v 1, α 1 • v 1 + β 1 • quarterTurn (v 1)) = _
    have hα1 : α 1 = α₁ := by simp [α]
    have hβ1 : β 1 = β₁ := by simp [β]
    rw [hv1, hα1, hβ1, decompose_second_column (first_column_ne_zero b)]
    exact linearMap_columns b
  exact
    ⟨{  toFun := fun t => ⟨F t, hcomponent t⟩
        continuous_toFun := hF.subtype_mk hcomponent
        source' := Subtype.ext hF0
        target' := Subtype.ext hF1 }⟩

theorem PlanarFrame.exists_smooth_join_of_same_determinant_sign
    {a b : ℝ → (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hsign
    exact lt_irrefl _ hsign
  have ha0 : a 0 ∈ determinantComponent σ := by
    change 0 < (a 0).toLinearMap.det * determinant (a 0)
    rw [determinant_eq_det]
    exact mul_self_pos.mpr ha0ne
  have hb1 : b 1 ∈ determinantComponent σ := by
    change 0 < (a 0).toLinearMap.det * determinant (b 1)
    rw [determinant_eq_det]
    exact hsign
  obtain ⟨γ⟩ :=
    nonempty_path_determinantComponent (⟨a 0, ha0⟩ : determinantComponent σ)
      (⟨b 1, hb1⟩ : determinantComponent σ)
  obtain ⟨L, hL, hmem, hleft, hright⟩ :=
    exists_smooth_open_curve_with_endpoint_germs (determinantComponent σ) ha hb hU hV h0U
      h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := by
    have h := hmem t
    change 0 < (a 0).toLinearMap.det * determinant (L t) at h
    rwa [determinant_eq_det] at h
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  apply bijective_of_determinant_ne_zero (L t)
  intro hz
  rw [determinant_eq_det] at hz
  have h := hpositive t
  rw [hz, MulZeroClass.mul_zero] at h
  exact lt_irrefl _ h

theorem FrameField.exists_smooth_invertible_join_of_finrank_two {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (hdim : Module.finrank ℝ D = 2) {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  have hdim' : Module.finrank ℝ PlaneImmersion.Plane = Module.finrank ℝ D := by
    simp [PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self, hdim]
  let e : PlaneImmersion.Plane ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq hdim'
  let a' (t : ℝ) := e.symm.toContinuousLinearMap.comp ((a t).comp e.toContinuousLinearMap)
  let b' (t : ℝ) := e.symm.toContinuousLinearMap.comp ((b t).comp e.toContinuousLinearMap)
  have ha' : ContDiffOn ℝ ∞ a' U := contDiffOn_const.clm_comp (ha.clm_comp contDiffOn_const)
  have hb' : ContDiffOn ℝ ∞ b' V := contDiffOn_const.clm_comp (hb.clm_comp contDiffOn_const)
  have hadet (t : ℝ) : (a' t).toLinearMap.det = (a t).toLinearMap.det :=
    LinearMap.det_conj (a t).toLinearMap e.symm.toLinearEquiv
  have hbdet (t : ℝ) : (b' t).toLinearMap.det = (b t).toLinearMap.det :=
    LinearMap.det_conj (b t).toLinearMap e.symm.toLinearEquiv
  have hsign' : 0 < (a' 0).toLinearMap.det * (b' 1).toLinearMap.det := by
    rw [hadet, hbdet]
    exact hsign
  obtain ⟨L', hL', hi', hdet', hleft, hright⟩ :=
    PlanarFrame.exists_smooth_join_of_same_determinant_sign ha' hb' hU hV h0U h1V hsign'
  let L (t : ℝ) := e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap)
  have hL : ContDiff ℝ ∞ L := contDiff_const.clm_comp (hL'.clm_comp contDiff_const)
  have hi (t : ℝ) : Function.Bijective (L t) := e.bijective.comp ((hi' t).comp e.symm.bijective)
  have hdet (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := by
    have heq : (L t).toLinearMap.det = (L' t).toLinearMap.det :=
      LinearMap.det_conj (L' t).toLinearMap e.toLinearEquiv
    rw [heq, ← hadet 0]
    exact hdet' t
  refine ⟨L, hL, hi, hdet, ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    change e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap) = a t
    rw [ht]
    apply ContinuousLinearMap.ext
    intro v
    change e (e.symm (a t (e (e.symm v)))) = a t v
    simp only [e.apply_symm_apply]
  · filter_upwards [hright] with t ht
    change e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap) = b t
    rw [ht]
    apply ContinuousLinearMap.ext
    intro v
    change e (e.symm (b t (e (e.symm v)))) = b t v
    simp only [e.apply_symm_apply]

theorem FrameField.exists_global_field_with_closed_germ {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {L : PlaneImmersion.Plane → F} {U C : Set PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) :
    ∃ L₀ : PlaneImmersion.Plane → F, ContDiff ℝ ∞ L₀ ∧ L₀ =ᶠ[𝓝ˢ C] L := by
  have hdisj : Disjoint Uᶜ C := Set.disjoint_left.mpr (fun _ hxU hxC => hxU (hCU hxC))
  obtain ⟨β, hβ0, hβ1, _⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, PlaneImmersion.Plane)
      hU.isClosed_compl hC hdisj (n := ⊤)
  let L₀ : PlaneImmersion.Plane → F := fun x => β x • L x
  have hβ : ContDiff ℝ ∞ (β : PlaneImmersion.Plane → ℝ) := β.contMDiff.contDiff
  have hL₀ : ContDiff ℝ ∞ L₀ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hβ.contDiffAt.smul (hL.contDiffAt (hU.mem_nhds hx))
    · apply
        (contDiffAt_const :
            ContDiffAt ℝ ∞ (fun _ : PlaneImmersion.Plane => (0 : F))
              x).congr_of_eventuallyEq
      have hβx : ∀ᶠ y in 𝓝 x, β y = 0 := hβ0.filter_mono (nhds_le_nhdsSet hx)
      filter_upwards [hβx] with y hy
      change β y • L y = 0
      rw [hy, zero_smul]
  refine ⟨L₀, hL₀, ?_⟩
  filter_upwards [hβ1] with x hx
  change β x • L x = L x
  rw [hx, one_smul]

theorem FrameField.exists_nonzero_field_rel_closed {P F : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {v : P → F} (hv : ContDiff ℝ ∞ v)
    (hdim : Module.finrank ℝ P < Module.finrank ℝ F) {K C : Set P} (hK : IsCompact K)
    (hC : IsClosed C) (hne : ∀ x ∈ K ∩ C, v x ≠ 0) :
    ∃ v' : P → F, ContDiff ℝ ∞ v' ∧ v' =ᶠ[𝓝ˢ C] v ∧ ∀ x ∈ K, v' x ≠ 0 := by
  let B : Set P := K ∩ v ⁻¹' {0}
  have hB : IsCompact B := hK.inter_right (isClosed_singleton.preimage hv.continuous)
  have hdisj : Disjoint C B := Set.disjoint_left.mpr (fun x hxC hxB => hne x ⟨hxB.1, hxC⟩ hxB.2)
  obtain ⟨β, hβ0, hβ1, -⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, P) hC hB.isClosed hdisj (n := ⊤)
  have hfixed : ∀ x ∈ K, β x = 0 → v x ≠ 0 := by
    intro x hx hβx hvx
    have heq : β x = 1 := hβ1.self_of_nhdsSet x ⟨hx, hvx⟩
    exact zero_ne_one (hβx.symm.trans heq)
  let Z := EuclideanSpace ℝ (Fin 0)
  let g : Z → F := fun _ => 0
  have hg : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, F) ∞ g := contMDiff_const
  have hdim' : Module.finrank ℝ P + Module.finrank ℝ Z < Module.finrank ℝ F := by
    simpa only [Z, finrank_euclideanSpace_fin, add_zero] using hdim
  obtain ⟨a, -, ha⟩ :=
    exists_small_localized_image_avoidance hv.contMDiff hg β.contMDiff hdim'
      (show (0 : ℝ) < 1 by norm_num)
  refine ⟨fun x => v x + β x • a, hv.add (β.contMDiff.contDiff.smul contDiff_const), ?_, ?_⟩
  · filter_upwards [hβ0] with x hx
    rw [hx, zero_smul, add_zero]
  · intro x hx
    by_cases hβx : β x = 0
    · simpa only [hβx, zero_smul, add_zero] using hfixed x hx hβx
    · exact ha x hβx (0 : Z)

theorem FrameField.exists_nonzero_extension_of_local_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {v : PlaneImmersion.Plane → F} {U C K : Set PlaneImmersion.Plane} (hU : IsOpen U)
    (hv : ContDiffOn ℝ ∞ v U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hne : ∀ x ∈ K ∩ C, v x ≠ 0) (hdim : 3 ≤ Module.finrank ℝ F) :
    ∃ v' : PlaneImmersion.Plane → F, ContDiff ℝ ∞ v' ∧ v' =ᶠ[𝓝ˢ C] v ∧ ∀ x ∈ K, v' x ≠ 0 := by
  obtain ⟨v₀, hv₀, heq⟩ := exists_global_field_with_closed_germ hU hv hC hCU
  have hne₀ : ∀ x ∈ K ∩ C, v₀ x ≠ 0 := by
    intro x hx
    rw [heq.self_of_nhdsSet hx.2]
    exact hne x hx
  have hdim' : Module.finrank ℝ PlaneImmersion.Plane < Module.finrank ℝ F := by
    change Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ F
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨v', hv', hgerm, hne'⟩ := exists_nonzero_field_rel_closed hv₀ hdim' hK hC hne₀
  exact ⟨v', hv', hgerm.trans heq, hne'⟩

theorem FrameField.injective_iff_ne_zero_of_finrank_one {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hA : Module.finrank ℝ A = 1) (L : A →L[ℝ] F) : Function.Injective L ↔ L ≠ 0 := by
  constructor
  · intro hi hzero
    let : Nontrivial A := Module.nontrivial_of_finrank_pos (by rw [hA]; norm_num)
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    apply hi
    rw [hzero]
    rfl
  · intro hne
    have hr : L.range ≠ ⊥ := by
      intro hbot
      have hz : L.toLinearMap = 0 := LinearMap.range_eq_bot.mp hbot
      apply hne
      ext x
      exact congrArg (fun f : A →ₗ[ℝ] F => f x) hz
    have hrank := L.toLinearMap.finrank_range_add_finrank_ker
    have hpos : 1 ≤ Module.finrank ℝ L.range := Submodule.one_le_finrank_iff.mpr hr
    have hk : Module.finrank ℝ L.ker = 0 := by
      rw [hA] at hrank
      omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

theorem FrameField.finrank_one_column {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hA : Module.finrank ℝ A = 1) : Module.finrank ℝ (A →L[ℝ] F) = Module.finrank ℝ F := by
  rw [← (LinearMap.toContinuousLinearMap : (A →ₗ[ℝ] F) ≃ₗ[ℝ] (A →L[ℝ] F)).finrank_eq,
    Module.finrank_linearMap, hA, one_mul]

theorem FrameField.exists_one_column_extension_of_local_field {A F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (hA : Module.finrank ℝ A = 1)
    {L : PlaneImmersion.Plane → (A →L[ℝ] F)} {U C K : Set PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hi : ∀ x ∈ K ∩ C, Function.Injective (L x)) (hdim : 3 ≤ Module.finrank ℝ F) :
    ∃ L' : PlaneImmersion.Plane → (A →L[ℝ] F),
      ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧ ∀ x ∈ K, Function.Injective (L' x) := by
  have hne : ∀ x ∈ K ∩ C, L x ≠ 0 := fun x hx =>
    (injective_iff_ne_zero_of_finrank_one hA (L x)).mp (hi x hx)
  have hdim' : 3 ≤ Module.finrank ℝ (A →L[ℝ] F) := by rwa [finrank_one_column hA]
  obtain ⟨L', hL', heq, hne'⟩ := exists_nonzero_extension_of_local_field hU hL hC hCU hK hne hdim'
  exact
    ⟨L', hL', heq, fun x hx => (injective_iff_ne_zero_of_finrank_one hA (L' x)).mpr (hne' x hx)⟩

theorem FrameField.exists_completed_one_column_frame {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hA : Module.finrank ℝ A = 1)
    {L : PlaneImmersion.Plane → (A →L[ℝ] F)} {U C K : Set PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : PlaneImmersion.Plane) K)
    (h0 : (0 : PlaneImmersion.Plane) ∈ K) (hi : ∀ x ∈ K ∩ C, Function.Injective (L x))
    (hdim : Module.finrank ℝ F = 3) :
    ∃ L' : PlaneImmersion.Plane → (A →L[ℝ] F),
      ContDiff ℝ ∞ L' ∧
        L' =ᶠ[𝓝ˢ C] L ∧
          ∃ V : Set PlaneImmersion.Plane,
            IsOpen V ∧
              K ⊆ V ∧
                ∃ B : PlaneImmersion.Plane → (EuclideanSpace ℝ (Fin 2) →L[ℝ] F),
                  ContDiffOn ℝ ∞ B V ∧
                    (∀ x ∈ K, (B x).range = (L' x).rangeᗮ) ∧
                      ∀ x ∈ V, Function.Bijective ((L' x).coprod (B x)) := by
  obtain ⟨L', hL', heq, hi'⟩ :=
    exists_one_column_extension_of_local_field hA hU hL hC hCU hK hi hdim.ge
  have hcodim : Module.finrank ℝ A + 2 = Module.finrank ℝ F := by rw [hA, hdim]
  obtain ⟨V, hV, hKV, B, hB, hr, hb⟩ :=
    exists_smooth_complement_near_starConvex hL' hK hstar h0 hi' 2 hcodim
  exact ⟨L', hL', heq, V, hV, hKV, B, hB, hr, hb⟩

theorem FrameField.eq_det_smul_id_of_finrank_one {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (hdim : Module.finrank ℝ D = 1) (A : D →L[ℝ] D) :
    A.toLinearMap = A.toLinearMap.det • LinearMap.id := by
  obtain ⟨a, ha, -⟩ := A.toLinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
  have hdet : A.toLinearMap.det = a := by
    rw [ha, LinearMap.det_smul, hdim, pow_one, LinearMap.det_id, mul_one]
  rw [hdet]
  exact ha

theorem FrameField.det_smul_add_of_finrank_one {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (hdim : Module.finrank ℝ D = 1) (A B : D →L[ℝ] D) (a b : ℝ) :
    (a • A + b • B).toLinearMap.det = a * A.toLinearMap.det + b * B.toLinearMap.det := by
  have hlin :
    (a • A + b • B).toLinearMap =
      (a * A.toLinearMap.det + b * B.toLinearMap.det) • LinearMap.id := by
    calc
      _ = a • (A.toLinearMap.det • LinearMap.id) + b • (B.toLinearMap.det • LinearMap.id) :=
        congrArg₂ (fun L K : D →ₗ[ℝ] D => a • L + b • K) (eq_det_smul_id_of_finrank_one hdim A)
          (eq_det_smul_id_of_finrank_one hdim B)
      _ = _ := by rw [smul_smul, smul_smul, ← add_smul]
  rw [hlin, LinearMap.det_smul, hdim, pow_one, LinearMap.det_id, mul_one]

theorem FrameField.exists_smooth_invertible_join_of_finrank_one {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (hdim : Module.finrank ℝ D = 1) {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  let S : TopologicalSpace.Opens (D →L[ℝ] D) :=
    ⟨{L | 0 < σ * L.toLinearMap.det},
      isOpen_lt continuous_const (continuous_const.mul ContinuousLinearMap.continuous_det)⟩
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hsign
    exact lt_irrefl _ hsign
  have hpos : 0 < σ * (a 0).toLinearMap.det := mul_self_pos.mpr ha0ne
  have ha0 : a 0 ∈ S := hpos
  have hb1 : b 1 ∈ S := hsign
  let γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S) :=
    { toFun := fun t =>
        ⟨(1 - (t : ℝ)) • a 0 + (t : ℝ) • b 1,
          by
          change 0 < σ * ((1 - (t : ℝ)) • a 0 + (t : ℝ) • b 1).toLinearMap.det
          rw [det_smul_add_of_finrank_one hdim]
          have heq :
            σ * ((1 - (t : ℝ)) * (a 0).toLinearMap.det + (t : ℝ) * (b 1).toLinearMap.det) =
              (1 - (t : ℝ)) * (σ * (a 0).toLinearMap.det) +
                (t : ℝ) * (σ * (b 1).toLinearMap.det) := by ring
          rw [heq]
          by_cases ht : (t : ℝ) = 0
          · simpa only [ht, sub_zero, one_mul, MulZeroClass.zero_mul, add_zero] using hpos
          · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
            exact
              add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr t.property.2) hpos.le)
                (mul_pos htpos hsign)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        fun_prop
      source' := by
        apply Subtype.ext
        simp
      target' := by
        apply Subtype.ext
        simp }
  obtain ⟨L, hL, hmem, hleft, hright⟩ :=
    exists_smooth_open_curve_with_endpoint_germs S ha hb hU hV h0U h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := hmem t
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  have hdet : (L t).toLinearMap.det ≠ 0 := by
    intro hz
    have hp := hpositive t
    rw [hz, MulZeroClass.mul_zero] at hp
    exact lt_irrefl _ hp
  have hker : (L t).toLinearMap.ker = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hi : Function.Injective (L t) := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

theorem FrameField.mul_endpoints_pos_of_continuous_nonzero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) :
    0 < f 0 * f 1 := by
  by_contra h
  rcases mul_nonpos_iff.mp (le_of_not_gt h) with h | h
  · obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hf ⟨h.2, h.1⟩
    exact hne t ht hft
  · obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf h
    exact hne t ht hft

theorem FrameField.det_mul_endpoints_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {T : ℝ → (E →L[ℝ] E)}
    (hT : ContinuousOn T (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective (T t)) :
    0 < (T 0).toLinearMap.det * (T 1).toLinearMap.det := by
  apply
    mul_endpoints_pos_of_continuous_nonzero
      (ContinuousLinearMap.continuous_det.comp_continuousOn hT)
  intro t ht hz
  have hker : (T t).toLinearMap.ker ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz
  exact hker (LinearMap.ker_eq_bot.mpr (hi t ht).1)

theorem FrameField.same_sign_frames_iff_coefficients {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (D × Z) ≃L[ℝ] F)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} (hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1))
    (hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible) :
    (0 <
        (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) ↔
      (0 <
        ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) := by
  let T (t : ℝ) := j.symm.toContinuousLinearMap.comp ((G t).coprod (C t))
  have hs : ContDiffOn ℝ ∞ T (Set.Icc (0 : ℝ) 1) :=
    contDiffOn_const.clm_comp (contDiffOn_coprod hG hC)
  have hT : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective (T t) := fun t ht =>
    j.symm.bijective.comp (hi t ht).bijective
  have hpositive := det_mul_endpoints_pos hs.continuousOn hT
  have h0 := det_frame_eq_det_split_mul_det_coefficient j (G 0) (C 0) (L 0) (hi 0 (by simp))
  have h1 := det_frame_eq_det_split_mul_det_coefficient j (G 1) (C 1) (L 1) (hi 1 (by simp))
  rw [h0, h1]
  have heq :
    ((T 0).toLinearMap.det * ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det) *
        ((T 1).toLinearMap.det * ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) =
      ((T 0).toLinearMap.det * (T 1).toLinearMap.det) *
        (((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) := by ring
  change (0 < ((T 0).toLinearMap.det * _) * ((T 1).toLinearMap.det * _)) ↔ _
  rw [heq]
  exact mul_pos_iff_of_pos_left hpositive

theorem FrameField.exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two
    {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hdim : Module.finrank ℝ Z = 1 ∨ Module.finrank ℝ Z = 2)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ} (hU : IsOpen U) (h0U : (0 : ℝ) ∈ U)
    (h1U : (1 : ℝ) ∈ U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hL : ContDiffOn ℝ ∞ L U) (hi : ∀ t ∈ U, Function.Bijective ((G t).coprod (C t)))
    (hsign :
      0 <
        ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F),
      ContDiffOn ℝ ∞ H U ∧
        (∀ t ∈ U, Function.Bijective ((G t).coprod (H t))) ∧
          (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) := by
  have hinv : ∀ t ∈ U, ((G t).coprod (C t)).IsInvertible := fun t ht =>
    isInvertible_coprod_of_bijective (G t) (C t) (hi t ht)
  let K (t : ℝ) := (complementQuotient (G t) (C t)).comp (L t)
  have hK : ContDiffOn ℝ ∞ K U := (contDiffOn_complementQuotient hU hG hC hinv).clm_comp hL
  have hjoin :=
    hdim.elim
      (fun hd => exists_smooth_invertible_join_of_finrank_one hd hK hK hU hU h0U h1U hsign)
      (fun hd => exists_smooth_invertible_join_of_finrank_two hd hK hK hU hU h0U h1U hsign)
  obtain ⟨K', hK', hiK', _, hleft, hright⟩ := hjoin
  let H (t : ℝ) := correctedComplement (G t) (C t) (L t) (K' t)
  have hH : ContDiffOn ℝ ∞ H U := contDiffOn_correctedComplement hU hG hC hL hK'.contDiffOn hinv
  refine
    ⟨H, hH, fun t ht =>
      bijective_coprod_correctedComplement (G t) (C t) (L t) (K' t) (hinv t ht) (hiK' t), ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    change correctedComplement (G t) (C t) (L t) (K' t) = L t
    rw [ht]
    exact correctedComplement_self (G t) (C t) (L t)
  · filter_upwards [hright] with t ht
    change correctedComplement (G t) (C t) (L t) (K' t) = L t
    rw [ht]
    exact correctedComplement_self (G t) (C t) (L t)

theorem FrameField.exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
    {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hdim : Module.finrank ℝ Z = 1 ∨ Module.finrank ℝ Z = 2)
    (j : (D × Z) ≃L[ℝ] F) {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ}
    (hU : IsOpen U) (hIU : Set.Icc (0 : ℝ) 1 ⊆ U) (hG : ContDiffOn ℝ ∞ G U)
    (hC : ContDiffOn ℝ ∞ C U) (hL : ContDiffOn ℝ ∞ L U)
    (hi : ∀ t ∈ U, Function.Bijective ((G t).coprod (C t)))
    (hsign :
      0 <
        (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F),
      ContDiffOn ℝ ∞ H U ∧
        (∀ t ∈ U, Function.Bijective ((G t).coprod (H t))) ∧
          (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) := by
  have hinv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible := fun t ht =>
    isInvertible_coprod_of_bijective _ _ (hi t (hIU ht))
  have hcoeff := (same_sign_frames_iff_coefficients j (hG.mono hIU) (hC.mono hIU) hinv).mp hsign
  exact
    exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two hdim hU (hIU (by simp))
      (hIU (by simp)) hG hC hL hi hcoeff

theorem WhitneyPairModel.exists_smooth_bigon_boundary_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ} (hh : 0 < h) {L H : ℝ → F} {D : Set ℝ}
    (hD : IsOpen D) (hID : Set.Icc (0 : ℝ) 1 ⊆ D) (hL : ContDiffOn ℝ ∞ L D)
    (hH : ContDiffOn ℝ ∞ H D) (h0 : H =ᶠ[𝓝 (0 : ℝ)] L) (h1 : H =ᶠ[𝓝 (1 : ℝ)] L) :
    ∃ U V : Set (ℝ × ℝ),
      IsOpen U ∧
        IsOpen V ∧
          frontier (bigon h) ⊆ U ∪ V ∧
            Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U ∧
              Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V ∧
                ∃ W : (ℝ × ℝ) → F,
                  ContDiffOn ℝ ∞ W (U ∪ V) ∧
                    Set.EqOn W (L ∘ arcTime) U ∧ Set.EqOn W (H ∘ arcTime) V := by
  let P := arcTime ⁻¹' D
  have hP : IsOpen P := hD.preimage contDiff_arcTime.continuous
  have hLP : ContDiffOn ℝ ∞ (L ∘ arcTime) P :=
    hL.comp contDiff_arcTime.contDiffOn (fun _ hp => hp)
  have hHP : ContDiffOn ℝ ∞ (H ∘ arcTime) P :=
    hH.comp contDiff_arcTime.contDiffOn (fun _ hp => hp)
  have htime0 : Filter.Tendsto arcTime (𝓝 ((-1 : ℝ), (0 : ℝ))) (𝓝 (0 : ℝ)) := by
    simpa [ContinuousAt, arcTime] using
      (contDiff_arcTime.continuous.continuousAt (x := ((-1 : ℝ), (0 : ℝ))))
  have htime1 : Filter.Tendsto arcTime (𝓝 ((1 : ℝ), (0 : ℝ))) (𝓝 (1 : ℝ)) := by
    simpa [ContinuousAt, arcTime] using
      (contDiff_arcTime.continuous.continuousAt (x := ((1 : ℝ), (0 : ℝ))))
  have hg0 : (L ∘ arcTime) =ᶠ[𝓝 ((-1 : ℝ), (0 : ℝ))] (H ∘ arcTime) := h0.symm.comp_tendsto htime0
  have hg1 : (L ∘ arcTime) =ᶠ[𝓝 ((1 : ℝ), (0 : ℝ))] (H ∘ arcTime) := h1.symm.comp_tendsto htime1
  obtain ⟨O₀, hO₀sub, hO₀, hleft⟩ := mem_nhds_iff.mp hg0
  obtain ⟨O₁, hO₁sub, hO₁, hright⟩ := mem_nhds_iff.mp hg1
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  have hlowP : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) P := by
    intro t ht
    change arcTime (2 * t - 1, 0) ∈ D
    rw [htime]
    exact hID ht
  have huppP : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) P :=
    by
    intro t ht
    change arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ D
    rw [htime]
    exact hID ht
  obtain ⟨U, V, hU, hV, hUP, hVP, hover, hlowU, huppV, hfront⟩ :=
    exists_bigon_boundary_cover hh hP hP (hO₀.union hO₁) (Or.inl hleft) (Or.inr hright) hlowP
      huppP
  have hLH : Set.EqOn (L ∘ arcTime) (H ∘ arcTime) (U ∩ V) := by
    intro p hp
    rcases hover hp with hp0 | hp1
    · exact hO₀sub hp0
    · exact hO₁sub hp1
  obtain ⟨W, hW, hWL, hWH⟩ :=
    exists_smooth_open_gluing hU hV (hLP.mono hUP).contMDiffOn (hHP.mono hVP).contMDiffOn
      hLH
  exact ⟨U, V, hU, hV, hfront, hlowU, huppV, W, hW.contDiffOn, hWL, hWH⟩

theorem WhitneyPairModel.exists_injective_bigon_boundary_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {h : ℝ} (hh : 0 < h) {L H : ℝ → (A →L[ℝ] F)} {D : Set ℝ} (hD : IsOpen D)
    (hID : Set.Icc (0 : ℝ) 1 ⊆ D) (hL : ContDiffOn ℝ ∞ L D) (hH : ContDiffOn ℝ ∞ H D)
    (h0 : H =ᶠ[𝓝 (0 : ℝ)] L) (h1 : H =ᶠ[𝓝 (1 : ℝ)] L)
    (hiL : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (L t))
    (hiH : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (H t)) :
    ∃ O : Set (ℝ × ℝ),
      IsOpen O ∧
        frontier (bigon h) ⊆ O ∧
          ∃ W : (ℝ × ℝ) → (A →L[ℝ] F),
            ContDiffOn ℝ ∞ W O ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, W =ᶠ[𝓝 (2 * t - 1, 0)] (L ∘ arcTime)) ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                    W =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))] (H ∘ arcTime)) ∧
                  ∀ p ∈ frontier (bigon h), Function.Injective (W p) := by
  obtain ⟨U, V, hU, hV, hfront, hlow, hupp, W, hW, hWL, hWH⟩ :=
    exists_smooth_bigon_boundary_field hh hD hID hL hH h0 h1
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  refine ⟨U ∪ V, hU.union hV, hfront, W, hW, ?_, ?_, ?_⟩
  · intro t ht
    exact Filter.mem_of_superset (hU.mem_nhds (hlow ht)) (fun _ hp => hWL hp)
  · intro t ht
    exact Filter.mem_of_superset (hV.mem_nhds (hupp ht)) (fun _ hp => hWH hp)
  · intro p hp
    obtain ⟨t, ht, rfl | rfl⟩ := (mem_frontier_bigon_iff_exists_time hh p).mp hp
    · rw [hWL (hlow ht)]
      dsimp only [Function.comp_apply]
      rw [htime]
      exact hiL t ht
    · rw [hWH (hupp ht)]
      dsimp only [Function.comp_apply]
      rw [htime]
      exact hiH t ht

def FrameField.rankThreePairCoordinates :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearEquiv.ofFinrankEq
    (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin])

def FrameField.rankThreePairDet
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (B : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (rankThreePairCoordinates.symm.toContinuousLinearMap.comp (A.coprod B)).toLinearMap.det

theorem TubularBigon.exists_rankThree_boundary_complement_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ U : Set ℝ,
      IsOpen U ∧
        Set.Icc (0 : ℝ) 1 ⊆ U ∧
          ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U ∧
            ∃ H : ℝ → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
              ContDiffOn ℝ ∞ H U ∧
                (∀ t ∈ U, Function.Bijective ((e.normalFrame tube.chart t).coprod (H t))) ∧
                  (H =ᶠ[𝓝 (0 : ℝ)] d.normalFrame tube.chart) ∧
                    (H =ᶠ[𝓝 (1 : ℝ)] d.normalFrame tube.chart) := by
  obtain ⟨⟨V, hV, hIV, hL⟩, -⟩ := tube.lower_sheetFrame d
  obtain ⟨W, hW, hIW, hR, C, hC, -, hRC⟩ :=
    tube.upper_sheetFrame_complement_of_finrank e 1 (by simp only [finrank_euclideanSpace_fin])
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  have hIU : Set.Icc (0 : ℝ) 1 ⊆ U := fun _ ht => ⟨hIV ht, hIW ht⟩
  have hLU := hL.mono (show U ⊆ V from Set.inter_subset_left)
  have hRU := hR.mono (show U ⊆ W from Set.inter_subset_right)
  have hCU := hC.mono (show U ⊆ W from Set.inter_subset_right)
  have hsplit : ∀ t ∈ U, Function.Bijective ((e.normalFrame tube.chart t).coprod (C t)) :=
    fun t ht => hRC t ht.2
  obtain ⟨H, hH, hiH, hleft, hright⟩ :=
    FrameField.exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
      (Or.inl finrank_euclideanSpace_fin) FrameField.rankThreePairCoordinates hU hIU hRU hCU
      hLU hsplit hsign
  exact ⟨U, hU, hIU, hLU, H, hH, hiH, hleft, hright⟩

theorem TubularBigon.exists_rankThree_planar_boundary_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ O : Set (ℝ × ℝ),
      IsOpen O ∧
        frontier (WhitneyPairModel.bigon h) ⊆ O ∧
          ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
            ContDiffOn ℝ ∞ W O ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                  W =ᶠ[𝓝 (2 * t - 1, 0)]
                    (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                    Function.Bijective
                      ((e.normalFrame tube.chart t).coprod
                        (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
                  ∀ p ∈ frontier (WhitneyPairModel.bigon h), Function.Injective (W p) := by
  obtain ⟨D, hD, hID, hL, H, hH, hcomp, h0, h1⟩ :=
    tube.exists_rankThree_boundary_complement_of_normal_sign d e hsign
  have hHi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (H t) := by
    intro t ht u v huv
    have heq :
      ((e.normalFrame tube.chart t).coprod (H t)) (0, u) =
        ((e.normalFrame tube.chart t).coprod (H t)) (0, v) := by
      simpa only [ContinuousLinearMap.coprod_apply, map_zero, zero_add] using huv
    exact congrArg Prod.snd ((hcomp t (hID ht)).1 heq)
  obtain ⟨O, hO, hfront, W, hW, hlo, hhi, hinj⟩ :=
    WhitneyPairModel.exists_injective_bigon_boundary_field tube.height_pos hD hID hL hH h0
      h1 (tube.lower_sheetFrame d).2 hHi
  refine ⟨O, hO, hfront, W, hW, hlo, ?_, hinj⟩
  intro t ht
  rw [(hhi t ht).eq_of_nhds]
  have htime : WhitneyPairModel.arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = t := by
    dsimp [WhitneyPairModel.arcTime]
    ring
  change
    Function.Bijective
      ((e.normalFrame tube.chart t).coprod
        (H (WhitneyPairModel.arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)))))
  rw [htime]
  exact hcomp t (hID ht)

theorem TubularBigon.exists_rankThree_planar_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
              Function.Bijective
                ((e.normalFrame tube.chart t).coprod
                  (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
            ∃ V : Set (ℝ × ℝ),
              IsOpen V ∧
                WhitneyPairModel.bigon h ⊆ V ∧
                  ∃ B : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                    ContDiffOn ℝ ∞ B V ∧
                      (∀ p ∈ WhitneyPairModel.bigon h, (B p).range = (W p).rangeᗮ) ∧
                        ∀ p ∈ V, Function.Bijective ((W p).coprod (B p)) := by
  obtain ⟨O, hO, hfront, W₀, hW₀, hlo, hhi, hinj⟩ :=
    tube.exists_rankThree_planar_boundary_frame_of_normal_sign d e hsign
  obtain ⟨W, hW, heq, V, hV, hKV, B, hB, hr, hb⟩ :=
    FrameField.exists_completed_one_column_frame finrank_euclideanSpace_fin hO hW₀
      isClosed_frontier hfront (WhitneyPairModel.isCompact_bigon tube.height_pos)
      (WhitneyPairModel.starConvex_bigon tube.height_pos.le)
      (WhitneyPairModel.zero_mem_bigon tube.height_pos.le) (fun p hp => hinj p hp.2)
      finrank_euclideanSpace_fin
  refine ⟨W, hW, ?_, ?_, V, hV, hKV, B, hB, hr, hb⟩
  · intro t ht
    have hp : (2 * t - 1, 0) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inl rfl⟩
    exact (heq.filter_mono (nhds_le_nhdsSet hp)).trans (hlo t ht)
  · intro t ht
    have hp :
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inr rfl⟩
    rw [heq.self_of_nhdsSet hp]
    exact hhi t ht

theorem FrameField.bijective_coprod_comm {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (H : Z →L[ℝ] F) (hi : Function.Bijective (H.coprod W)) :
    Function.Bijective (W.coprod H) := by
  have heq :
    W.coprod H = (H.coprod W).comp (ContinuousLinearEquiv.prodComm ℝ D Z).toContinuousLinearMap :=
    by
    apply ContinuousLinearMap.ext
    intro p
    change W p.1 + H p.2 = H p.2 + W p.1
    exact add_comm _ _
  rw [heq]
  exact hi.comp (ContinuousLinearEquiv.prodComm ℝ D Z).bijective

def FrameField.transportComplement {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : D →L[ℝ] F) (B : Z →L[ℝ] F) (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F) : Z →L[ℝ] F :=
  (W.coprod B).comp ((W₀.coprod B₀).inverse.comp H)

theorem FrameField.transportComplement_self {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (B H : Z →L[ℝ] F) (h : (W.coprod B).IsInvertible) :
    transportComplement W B W B H = H := by
  apply ContinuousLinearMap.ext
  intro z
  exact h.self_apply_inverse (H z)

theorem FrameField.coprod_transportComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (B : Z →L[ℝ] F) (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F)
    (h₀ : (W₀.coprod B₀).IsInvertible) :
    W.coprod (transportComplement W B W₀ B₀ H) =
      ((W.coprod B).comp (W₀.coprod B₀).inverse).comp (W₀.coprod H) := by
  have hfirst (u : D) : (W₀.coprod B₀).inverse (W₀ u) = (u, 0) := by
    simpa only [ContinuousLinearMap.coprod_apply, map_zero, add_zero] using
      h₀.inverse_apply_self (u, 0)
  apply ContinuousLinearMap.ext
  intro p
  simp only [transportComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coprod_apply, map_add, hfirst, map_zero, add_zero]

theorem FrameField.bijective_transportComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (B : Z →L[ℝ] F) (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F)
    (h : (W.coprod B).IsInvertible) (h₀ : (W₀.coprod B₀).IsInvertible)
    (hH : Function.Bijective (W₀.coprod H)) :
    Function.Bijective (W.coprod (transportComplement W B W₀ B₀ H)) := by
  rw [coprod_transportComplement W B W₀ B₀ H h₀]
  exact (h.bijective.comp h₀.inverse.bijective).comp hH

theorem FrameField.contDiffOn_transportComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {W W₀ : X → (D →L[ℝ] F)} {B B₀ H : X → (Z →L[ℝ] F)} {U : Set X}
    (hU : IsOpen U) (hW : ContDiffOn ℝ ∞ W U) (hB : ContDiffOn ℝ ∞ B U)
    (hW₀ : ContDiffOn ℝ ∞ W₀ U) (hB₀ : ContDiffOn ℝ ∞ B₀ U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : ∀ x ∈ U, ((W₀ x).coprod (B₀ x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => transportComplement (W x) (B x) (W₀ x) (B₀ x) (H x)) U := by
  have hT₀ := contDiffOn_coprod hW₀ hB₀
  have hInv : ContDiffOn ℝ ∞ (fun x => ((W₀ x).coprod (B₀ x)).inverse) U := by
    intro x hx
    exact
      ((hi x hx).contDiffAt_map_inverse.comp x (hT₀.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  exact (contDiffOn_coprod hW hB).clm_comp (hInv.clm_comp hH)

theorem TubularBigon.exists_rankThree_adapted_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
          ∃ O : Set (ℝ × ℝ),
            IsOpen O ∧
              WhitneyPairModel.bigon h ⊆ O ∧
                ∃ C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                  ContDiffOn ℝ ∞ C O ∧
                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                        C (WhitneyPairModel.upperBoundaryArc h t) =
                          e.normalFrame tube.chart t) ∧
                      ∀ p ∈ O, Function.Bijective ((W p).coprod (C p)) := by
  obtain ⟨W, hW, hlo, hhi, V, hV, hKV, B, hB, -, hb⟩ :=
    tube.exists_rankThree_planar_frame_of_normal_sign d e hsign
  obtain ⟨⟨D, hD, hID, hG⟩, -⟩ := tube.upper_sheetFrame e
  let r : (ℝ × ℝ) → (ℝ × ℝ) :=
    WhitneyPairModel.upperBoundaryArc h ∘ WhitneyPairModel.arcTime
  have hq : ContDiff ℝ ∞ (WhitneyPairModel.upperBoundaryArc h) := by
    unfold WhitneyPairModel.upperBoundaryArc; fun_prop
  have hr : ContDiff ℝ ∞ r := hq.comp WhitneyPairModel.contDiff_arcTime
  have htime (t y : ℝ) : WhitneyPairModel.arcTime (2 * t - 1, y) = t := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have htq (t : ℝ) :
    WhitneyPairModel.arcTime (WhitneyPairModel.upperBoundaryArc h t) = t := htime t _
  have hrq (t : ℝ) :
    r (WhitneyPairModel.upperBoundaryArc h t) =
      WhitneyPairModel.upperBoundaryArc h t := by
    dsimp only [r, Function.comp_apply]
    rw [htq]
  have htimeK :
    Set.MapsTo WhitneyPairModel.arcTime (WhitneyPairModel.bigon h)
      (Set.Icc (0 : ℝ) 1) := by
    intro p hp
    have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have hrK : Set.MapsTo r (WhitneyPairModel.bigon h) (WhitneyPairModel.bigon h) :=
    fun _ hp => tube.upperBoundaryArc_mem_bigon (htimeK hp)
  let O₀ := V ∩ (r ⁻¹' V ∩ WhitneyPairModel.arcTime ⁻¹' D)
  have hO₀ : IsOpen O₀ :=
    hV.inter
      ((hV.preimage hr.continuous).inter
        (hD.preimage WhitneyPairModel.contDiff_arcTime.continuous))
  have hKO₀ : WhitneyPairModel.bigon h ⊆ O₀ := fun p hp =>
    ⟨hKV hp, hKV (hrK hp), hID (htimeK hp)⟩
  let C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) := fun p =>
    FrameField.transportComplement (W p) (B p) (W (r p)) (B (r p))
      (e.normalFrame tube.chart (WhitneyPairModel.arcTime p))
  have hC : ContDiffOn ℝ ∞ C O₀ := by
    apply
      FrameField.contDiffOn_transportComplement hO₀ hW.contDiffOn
        (hB.mono Set.inter_subset_left) (hW.comp hr).contDiffOn
        (hB.comp hr.contDiffOn (fun _ hp => hp.2.1))
        (hG.comp WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.2))
    intro p hp
    exact FrameField.isInvertible_coprod_of_bijective (W (r p)) (B (r p)) (hb _ hp.2.1)
  have hcompK : ∀ p ∈ WhitneyPairModel.bigon h, Function.Bijective ((W p).coprod (C p)) := by
    intro p hp
    have ht := htimeK hp
    have hupper :
      Function.Bijective
        ((W (r p)).coprod (e.normalFrame tube.chart (WhitneyPairModel.arcTime p))) :=
      FrameField.bijective_coprod_comm _ _ (hhi (WhitneyPairModel.arcTime p) ht)
    exact
      FrameField.bijective_transportComplement (W p) (B p) (W (r p)) (B (r p)) _
        (FrameField.isInvertible_coprod_of_bijective _ _ (hb p (hKV hp)))
        (FrameField.isInvertible_coprod_of_bijective _ _ (hb _ (hKV (hrK hp)))) hupper
  have hTC : ContDiffOn ℝ ∞ (fun p => (W p).coprod (C p)) O₀ :=
    FrameField.contDiffOn_coprod hW.contDiffOn hC
  let O := O₀ ∩ {p | Function.Injective ((W p).coprod (C p))}
  have hO : IsOpen O :=
    hTC.continuousOn.isOpen_inter_preimage hO₀ ContinuousLinearMap.isOpen_injective
  have hKO : WhitneyPairModel.bigon h ⊆ O := fun p hp => ⟨hKO₀ hp, (hcompK p hp).1⟩
  refine ⟨W, hW, hlo, O, hO, hKO, C, hC.mono Set.inter_subset_left, ?_, ?_⟩
  · intro t ht
    dsimp only [C]
    rw [hrq, htq]
    exact
      FrameField.transportComplement_self _ _ _
        (FrameField.isInvertible_coprod_of_bijective _ _
          (hb _ (hKV (tube.upperBoundaryArc_mem_bigon ht))))
  · intro p hp
    have hdim :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact ⟨hp.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hp.2⟩

def TubularBigon.rankThreeSheetPairJacobian {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (t : ℝ) :
    ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) →L[ℝ]
      ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) :=
  IntersectionCoordinates.jointBlock FrameField.rankThreePairCoordinates
    (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)

def TubularBigon.rankThreeSheetPairDet {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (t : ℝ) : ℝ :=
  (tube.rankThreeSheetPairJacobian d e t).toLinearMap.det

theorem TubularBigon.rankThree_corner_sheet_charts_coincide {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    {t : ℝ} (ht : t = 0 ∨ t = 1) :
    d.chart (StripCoordinates.center t) = e.chart (StripCoordinates.center t) := by
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
  have hheight : h * (1 - (2 * t - 1) ^ 2) = 0 := by rcases ht with rfl | rfl <;> ring
  have hd := (tube.lower_germ t htI).eq_of_nhds
  have he := (tube.upper_germ t htI).eq_of_nhds
  dsimp only [Function.comp_apply] at hd he
  rw [WhitneyPairModel.lowerStripCoordinates_lower, d.center t] at hd
  rw [WhitneyPairModel.upperStripCoordinates_upper, e.center t, hheight] at he
  exact hd.symm.trans he

theorem TubularBigon.rankThreeSheetPairDet_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    tube.rankThreeSheetPairDet d e t =
      (8 * h * (2 * t - 1)) *
        FrameField.rankThreePairDet (e.normalFrame tube.chart t)
          (d.normalFrame tube.chart t) := by
  rw [rankThreeSheetPairDet, rankThreeSheetPairJacobian,
    IntersectionCoordinates.det_jointBlock FrameField.rankThreePairCoordinates
      (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)
      (tube.upper_sheetDifferential_arc e ht) (tube.lower_sheetDifferential_arc d ht),
    e.normal_sheetDifferential tube.chart ht (tube.upper_chart_center_mem_target e ht),
    d.normal_sheetDifferential tube.chart ht (tube.lower_chart_center_mem_target d ht)]
  have hplane :
    (PlaneImmersion.linearMap ((2, -4 * h * (2 * t - 1)), (2, 0))).toLinearMap.det =
      8 * h * (2 * t - 1) := by
    rw [← PlanarFrame.determinant_eq_det, PlanarFrame.determinant_linearMap]
    dsimp [PlanarFrame.area]
    ring
  rw [hplane]
  rfl

theorem TubularBigon.opposite_rankThree_corner_determinants_iff_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l) :
    (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
      (0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) := by
  let n :=
    FrameField.rankThreePairDet (e.normalFrame tube.chart 0) (d.normalFrame tube.chart 0) *
      FrameField.rankThreePairDet (e.normalFrame tube.chart 1) (d.normalFrame tube.chart 1)
  have hprod :
    tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 = -((8 * h) ^ 2 * n) := by
    rw [tube.rankThreeSheetPairDet_eq d e (t := 0) (by simp),
      tube.rankThreeSheetPairDet_eq d e (t := 1) (by simp)]
    dsimp only [n]
    ring
  have hscale : 0 < (8 * h) ^ 2 := sq_pos_of_pos (mul_pos (by norm_num) tube.height_pos)
  change (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔ 0 < n
  rw [hprod]
  constructor
  · intro hn
    have hp : 0 < (8 * h) ^ 2 * n := by linarith
    exact (mul_pos_iff_of_pos_left hscale).mp hp
  · intro hn
    have hp : 0 < (8 * h) ^ 2 * n := mul_pos hscale hn
    linarith

theorem TubularBigon.exists_rankThree_adapted_frame_of_opposite_corner_signs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
          ∃ O : Set (ℝ × ℝ),
            IsOpen O ∧
              WhitneyPairModel.bigon h ⊆ O ∧
                ∃ C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                  ContDiffOn ℝ ∞ C O ∧
                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                        C (WhitneyPairModel.upperBoundaryArc h t) =
                          e.normalFrame tube.chart t) ∧
                      ∀ p ∈ O, Function.Bijective ((W p).coprod (C p)) :=
  tube.exists_rankThree_adapted_frame_of_normal_sign d e
    ((tube.opposite_rankThree_corner_determinants_iff_normal_sign d e).mp hsign)

def IntersectionCoordinates.pairCoordinates {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F) :
    ((ℝ × A) × (ℝ × B)) ≃L[ℝ] (PlaneImmersion.Plane × F) :=
  (ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B).trans
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ PlaneImmersion.Plane) j)

theorem IntersectionCoordinates.det_jointBlock_eq_tangentSum {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F)
    (P : (ℝ × A) →L[ℝ] (PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (PlaneImmersion.Plane × F)) :
    (jointBlock j P Q).det =
      ((pairCoordinates j).symm.toContinuousLinearMap.comp (P.coprod Q)).det := by
  let k := ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B
  let T := (pairCoordinates j).symm.toContinuousLinearMap.comp (P.coprod Q)
  have heq :
    (jointBlock j P Q).toLinearMap =
      k.toLinearEquiv.toLinearMap.comp (T.toLinearMap.comp k.symm.toLinearEquiv.toLinearMap) := by
    apply LinearMap.ext
    intro z
    rfl
  change (jointBlock j P Q).toLinearMap.det = T.toLinearMap.det
  rw [heq]
  exact LinearMap.det_conj T.toLinearMap k.toLinearEquiv

theorem FrameField.normalDetector_eq_comp_quotient {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (Q : F →L[ℝ] Z)
    (hi : (G.coprod C).IsInvertible) (hQG : Q.comp G = 0) :
    Q = (Q.comp C).comp (complementQuotient G C) := by
  apply ContinuousLinearMap.ext
  intro v
  let w := (G.coprod C).inverse v
  have hv : G w.1 + C w.2 = v := hi.self_apply_inverse v
  have hzero : Q (G w.1) = 0 := congrArg (fun L : D →L[ℝ] Z => L w.1) hQG
  change Q v = Q (C w.2)
  rw [← hv, map_add, hzero, zero_add]

theorem FrameField.det_intersection_mul_normalComplement {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    (j : (D × Z) ≃L[ℝ] F) (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (Q : F →L[ℝ] Z)
    (hi : (G.coprod C).IsInvertible) (hQG : Q.comp G = 0) :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).det * (Q.comp C).det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).det * (Q.comp L).det := by
  have hnormal : Q.comp L = (Q.comp C).comp ((complementQuotient G C).comp L) := by
    have h := normalDetector_eq_comp_quotient G C Q hi hQG
    exact congrArg (fun R : F →L[ℝ] Z => R.comp L) h
  have hdet : (Q.comp L).det = (Q.comp C).det * ((complementQuotient G C).comp L).det := by
    rw [hnormal]
    exact LinearMap.det_comp _ _
  have hframe :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).det *
        ((complementQuotient G C).comp L).det :=
    det_frame_eq_det_split_mul_det_coefficient j G C L hi
  rw [hframe, hdet]
  ring

theorem FrameField.opposite_intersectionDet_iff_normalDet {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    (j : (D × Z) ≃L[ℝ] F) (G : ℝ → (D →L[ℝ] F)) (C L : ℝ → (Z →L[ℝ] F)) (Q : ℝ → (F →L[ℝ] Z))
    (hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1)) (hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1))
    (hQ : ContDiffOn ℝ ∞ Q (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible)
    (hQs : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Surjective (Q t))
    (hQG : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Q t).comp (G t) = 0) :
    ((j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det <
        0) ↔
      ((Q 0).comp (L 0)).det * ((Q 1).comp (L 1)).det < 0 := by
  let T (t : ℝ) := j.symm.toContinuousLinearMap.comp ((G t).coprod (C t))
  let K (t : ℝ) := (Q t).comp (C t)
  have hT : ContDiffOn ℝ ∞ T (Set.Icc (0 : ℝ) 1) :=
    contDiffOn_const.clm_comp (contDiffOn_coprod hG hC)
  have hK : ContDiffOn ℝ ∞ K (Set.Icc (0 : ℝ) 1) := hQ.clm_comp hC
  have hTpos :=
    det_mul_endpoints_pos hT.continuousOn (fun t ht => j.symm.bijective.comp (hi t ht).bijective)
  have hKpos :=
    det_mul_endpoints_pos hK.continuousOn
      (fun t ht =>
        TransverseCoordinates.bijective_normal_comp (Q t) (G t) (C t) (hQs t ht)
          (hi t ht).surjective (hQG t ht) rfl)
  have h₀ :=
    det_intersection_mul_normalComplement j (G 0) (C 0) (L 0) (Q 0) (hi 0 (by simp))
      (hQG 0 (by simp))
  have h₁ :=
    det_intersection_mul_normalComplement j (G 1) (C 1) (L 1) (Q 1) (hi 1 (by simp))
      (hQG 1 (by simp))
  let a :=
    (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
      (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det
  let b := ((Q 0).comp (L 0)).det * ((Q 1).comp (L 1)).det
  have heq : a * ((K 0).det * (K 1).det) = ((T 0).det * (T 1).det) * b := by
    dsimp [a, b, T, K]
    calc
      _ =
          ((j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
              ((Q 0).comp (C 0)).det) *
            ((j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det *
              ((Q 1).comp (C 1)).det) := by ring
      _ = _ := by rw [h₀, h₁]; ring
  change a < 0 ↔ b < 0
  constructor
  · intro ha
    have hn : ((T 0).det * (T 1).det) * b < 0 := heq ▸ mul_neg_of_neg_of_pos ha hKpos
    rcases mul_neg_iff.mp hn with ⟨_, hb⟩ | ⟨ht, _⟩
    · exact hb
    · exact (not_lt_of_gt hTpos ht).elim
  · intro hb
    have hn : a * ((K 0).det * (K 1).det) < 0 := heq.symm ▸ mul_neg_of_pos_of_neg hTpos hb
    rcases mul_neg_iff.mp hn with ⟨_, hk⟩ | ⟨ha, _⟩
    · exact (not_lt_of_gt hKpos hk).elim
    · exact ha

def StripNormalData.sheetBaseFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    A →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ (ℝ × ℝ) Z).comp
    ((d.sheetDifferential Ψ t).comp (ContinuousLinearMap.inr ℝ ℝ A))

theorem StripNormalData.contDiffOn_sheetDifferential {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetDifferential Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have htransition : ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
    ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds ht.2)).comp
        (StripCoordinates.center t)
        (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1))).contDiffAt
  have hs : ContDiffAt ℝ ∞ (d.sheetTransition Ψ) (t, 0) :=
    htransition.comp (t, 0) (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffAt
  have hc : ContDiff ℝ ∞ (fun s : ℝ => (s, (0 : A))) := contDiff_id.prodMk contDiff_const
  exact ((hs.fderiv_right (by simp)).comp t hc.contDiffAt).contDiffWithinAt

theorem StripNormalData.contDiffOn_sheetBaseFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetBaseFrame Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} :=
  contDiffOn_const.clm_comp ((d.contDiffOn_sheetDifferential Ψ).clm_comp contDiffOn_const)

theorem StripNormalData.exists_open_sheetBaseFrame_domain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.sheetBaseFrame Ψ) U := by
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hO : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  exact
    ⟨StripCoordinates.center ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target), hO.preimage hc,
      fun t ht => ⟨d.line ht, htarget t ht⟩, d.contDiffOn_sheetBaseFrame Ψ⟩

theorem StripNormalData.sheetDifferential_transverse_eq {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (u : A) : d.sheetDifferential Ψ t (0, u) = (d.sheetBaseFrame Ψ t u, d.normalFrame Ψ t u) := by
  apply Prod.ext
  · rfl
  · exact congrArg (fun L : A →L[ℝ] Z => L u) (d.normal_sheetDifferential Ψ ht htarget)

def StripNormalData.tubularTransitionDerivative {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    StripCoordinates.Space A B →L[ℝ] ((ℝ × ℝ) × Z) :=
  fderiv ℝ (Ψ.symm ∘ d.chart) (StripCoordinates.center t)

def StripNormalData.sheetComplement {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    B →L[ℝ] ((ℝ × ℝ) × Z) :=
  (d.tubularTransitionDerivative Ψ t).comp (ContinuousLinearMap.inr ℝ (ℝ × A) B)

theorem StripNormalData.contDiffOn_tubularTransitionDerivative {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.tubularTransitionDerivative Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have htransition : ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
    ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds ht.2)).comp
        (StripCoordinates.center t)
        (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1))).contDiffAt
  have hc : ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  exact ((htransition.fderiv_right (by simp)).comp t hc.contDiffAt).contDiffWithinAt

theorem StripNormalData.contDiffOn_sheetComplement {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetComplement Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} :=
  (d.contDiffOn_tubularTransitionDerivative Ψ).clm_comp contDiffOn_const

theorem StripNormalData.bijective_tubularTransitionDerivative {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    Function.Bijective (d.tubularTransitionDerivative Ψ t) := by
  unfold tubularTransitionDerivative
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp (StripCoordinates.center t) (Ψ.symm.mdifferentiableAt (by simp) htarget)
      (d.chart.mdifferentiableAt (by simp) (d.line ht))]
  exact
    (PartialChart.bijective_mfderiv Ψ.symm htarget).comp
      (PartialChart.bijective_mfderiv d.chart (d.line ht))

theorem StripNormalData.sheet_coprod_complement_eq {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (d.sheetDifferential Ψ t).coprod (d.sheetComplement Ψ t) =
      d.tubularTransitionDerivative Ψ t := by
  rw [d.sheetDifferential_eq Ψ ht htarget]
  apply ContinuousLinearMap.ext
  intro z
  change
    d.tubularTransitionDerivative Ψ t (z.1, 0) + d.tubularTransitionDerivative Ψ t (0, z.2) =
      d.tubularTransitionDerivative Ψ t z
  rw [← map_add]
  simp

theorem StripNormalData.isInvertible_sheet_coprod_complement {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) [FiniteDimensional ℝ A]
    [FiniteDimensional ℝ B] {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ((d.sheetDifferential Ψ t).coprod (d.sheetComplement Ψ t)).IsInvertible := by
  apply FrameField.isInvertible_coprod_of_bijective
  rw [d.sheet_coprod_complement_eq Ψ ht htarget]
  exact d.bijective_tubularTransitionDerivative Ψ ht htarget

def StripNormalData.normalDetector {A B Z E M N : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) (t : ℝ) :
    ((ℝ × ℝ) × Z) →L[ℝ] N :=
  fderiv ℝ (q ∘ Ψ) (Ψ.symm (d.chart (StripCoordinates.center t)))

theorem StripNormalData.contDiffAt_normalMap_in_tube {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    ContDiffAt ℝ ∞ (q ∘ Ψ) (Ψ.symm (d.chart (StripCoordinates.center t))) := by
  have hinv :
    Ψ (Ψ.symm (d.chart (StripCoordinates.center t))) =
      d.chart (StripCoordinates.center t) :=
    Ψ.right_inv' htarget
  have hq' :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (Ψ (Ψ.symm (d.chart (StripCoordinates.center t)))) :=
    hinv.symm ▸ hq
  exact
    (hq'.comp _
        (Ψ.contMDiffOn_toFun.contMDiffAt
          (Ψ.open_source.mem_nhds (Ψ.map_target' htarget)))).contDiffAt

theorem StripNormalData.contDiffOn_normalDetector {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {O : Set M}
    (hO : IsOpen O) (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q O)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hcenter : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ O) :
    ContDiffOn ℝ ∞ (d.normalDetector Ψ q) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  have hqΨ :=
    d.contDiffAt_normalMap_in_tube Ψ q (htarget t ht)
      (hq.contMDiffAt (hO.mem_nhds (hcenter t ht)))
  have hc : ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  have hx : ContDiffAt ℝ ∞ (fun s => Ψ.symm (d.chart (StripCoordinates.center s))) t :=
    (d.contDiffAt_tubularTransition Ψ ht (htarget t ht)).comp t hc.contDiffAt
  exact ((hqΨ.fderiv_right (by simp)).comp t hx).contDiffWithinAt

theorem StripNormalData.normalDetector_eq_native {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    d.normalDetector Ψ q t =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) q (d.chart (StripCoordinates.center t)) : E →L[ℝ] N).comp
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) Ψ
            (Ψ.symm (d.chart (StripCoordinates.center t))) :
          ((ℝ × ℝ) × Z) →L[ℝ] E) := by
  have hinv :
    Ψ (Ψ.symm (d.chart (StripCoordinates.center t))) =
      d.chart (StripCoordinates.center t) :=
    Ψ.right_inv' htarget
  have hq' :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) q
      (Ψ (Ψ.symm (d.chart (StripCoordinates.center t)))) :=
    hinv.symm ▸ hq.mdifferentiableAt (by simp)
  unfold normalDetector
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp _ hq' (Ψ.mdifferentiableAt (by simp) (Ψ.map_target' htarget)), hinv]

theorem StripNormalData.surjective_normalDetector {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t)))
    (hqs :
      Function.Surjective
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) q (d.chart (StripCoordinates.center t)))) :
    Function.Surjective (d.normalDetector Ψ q t) := by
  rw [d.normalDetector_eq_native Ψ q htarget hq]
  exact hqs.comp (PartialChart.bijective_mfderiv Ψ (Ψ.map_target' htarget)).surjective

theorem StripNormalData.normalDetector_comp_sheet_eq_zero {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {O : Set M}
    (hO : IsOpen O) (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q O) (hzero : ∀ y ∈ S ∩ O, q y = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hcenter : d.chart (StripCoordinates.center t) ∈ O) :
    (d.normalDetector Ψ q t).comp (d.sheetDifferential Ψ t) = 0 := by
  let i := ContinuousLinearMap.inl ℝ (ℝ × A) B
  have hi : ContinuousAt i (t, 0) := i.continuous.continuousAt
  have hdc : ContinuousAt d.chart (i (t, 0)) :=
    d.chart.contMDiffOn_toFun.continuousOn.continuousAt (d.chart.open_source.mem_nhds (d.line ht))
  have hd : ContinuousAt (d.chart ∘ i) (t, 0) := ContinuousAt.comp (g := d.chart) (f := i) hdc hi
  have hnearS : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), i w ∈ d.chart.source :=
    hi.preimage_mem_nhds (d.chart.open_source.mem_nhds (d.line ht))
  have hnear : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), d.chart (i w) ∈ Ψ.target ∩ O :=
    hd.preimage_mem_nhds ((Ψ.open_target.inter hO).mem_nhds ⟨htarget, hcenter⟩)
  have hvanish : ((q ∘ Ψ) ∘ d.sheetTransition Ψ) =ᶠ[𝓝 (t, (0 : A))] (fun _ => 0) := by
    filter_upwards [hnearS, hnear] with w hw hwo
    change q (Ψ (Ψ.symm (d.chart (i w)))) = 0
    have hinv : Ψ (Ψ.symm (d.chart (i w))) = d.chart (i w) := Ψ.right_inv' hwo.1
    rw [hinv]
    exact hzero _ ⟨(d.sheet _ hw).mpr rfl, hwo.2⟩
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q htarget (hq.contMDiffAt (hO.mem_nhds hcenter))
  have hsheet := d.contDiffAt_sheetTransition Ψ ht htarget
  have hchain :=
    fderiv_comp (t, (0 : A)) (hqΨ.differentiableAt (by simp)) (hsheet.differentiableAt (by simp))
  have hder : fderiv ℝ ((q ∘ Ψ) ∘ d.sheetTransition Ψ) (t, (0 : A)) = 0 := by
    rw [hvanish.fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : N) (t, (0 : A))).fderiv
  exact hchain.symm.trans hder

theorem StripNormalData.normalDetector_comp_sheet {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    (d.normalDetector Ψ q t).comp (d.sheetDifferential Ψ t) =
      fderiv ℝ (fun w : ℝ × A => q (d.chart (w, 0))) (t, 0) := by
  let i := ContinuousLinearMap.inl ℝ (ℝ × A) B
  have hi : ContinuousAt i (t, 0) := i.continuous.continuousAt
  have hdc : ContinuousAt d.chart (i (t, 0)) :=
    d.chart.contMDiffOn_toFun.continuousOn.continuousAt (d.chart.open_source.mem_nhds (d.line ht))
  have hd : ContinuousAt (d.chart ∘ i) (t, 0) := ContinuousAt.comp (g := d.chart) (f := i) hdc hi
  have hnear : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), d.chart (i w) ∈ Ψ.target :=
    hd.preimage_mem_nhds (Ψ.open_target.mem_nhds htarget)
  have heq :
    ((q ∘ Ψ) ∘ d.sheetTransition Ψ) =ᶠ[𝓝 (t, (0 : A))] (fun w : ℝ × A => q (d.chart (w, 0))) := by
    filter_upwards [hnear] with w hw
    exact congrArg q (Ψ.right_inv' hw)
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q htarget hq
  have hsheet := d.contDiffAt_sheetTransition Ψ ht htarget
  have hchain :=
    fderiv_comp (t, (0 : A)) (hqΨ.differentiableAt (by simp)) (hsheet.differentiableAt (by simp))
  exact hchain.symm.trans heq.fderiv_eq

theorem TubularBigon.opposite_rankThree_corners_iff_normal_sheet_determinants {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (q : M → (ℝ × EuclideanSpace ℝ (Fin 1))) {O : Set M} (hO : IsOpen O)
    (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q O)
    (hzero : ∀ y ∈ T ∩ O, q y = 0)
    (hcenter : ∀ t ∈ Set.Icc (0 : ℝ) 1, e.chart (StripCoordinates.center t) ∈ O)
    (hqs :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Function.Surjective
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) q
            (e.chart (StripCoordinates.center t)))) :
    (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
      (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (0, 0)).det *
          (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (1, 0)).det <
        0 := by
  let i : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let j := IntersectionCoordinates.pairCoordinates FrameField.rankThreePairCoordinates
  let G := e.sheetDifferential tube.chart
  let L := d.sheetDifferential tube.chart
  let C (t : ℝ) := (e.sheetComplement tube.chart t).comp i.toContinuousLinearMap
  let Q := e.normalDetector tube.chart q
  have htarget :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, e.chart (StripCoordinates.center t) ∈ tube.chart.target :=
    fun _ ht => tube.upper_chart_center_mem_target e ht
  have hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1) :=
    (e.contDiffOn_sheetDifferential tube.chart).mono (fun t ht => ⟨e.line ht, htarget t ht⟩)
  have hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1) :=
    ((e.contDiffOn_sheetComplement tube.chart).mono
          (fun t ht => ⟨e.line ht, htarget t ht⟩)).clm_comp
      contDiffOn_const
  have hQ : ContDiffOn ℝ ∞ Q (Set.Icc (0 : ℝ) 1) :=
    e.contDiffOn_normalDetector tube.chart q hO hq htarget hcenter
  have hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible := by
    intro t ht
    let p :=
      ContinuousLinearEquiv.prodCongr
        (ContinuousLinearEquiv.refl ℝ (ℝ × EuclideanSpace ℝ (Fin 2))) i
    have heq :
      (G t).coprod (C t) =
        ((e.sheetDifferential tube.chart t).coprod (e.sheetComplement tube.chart t)).comp
          p.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro z
      rfl
    apply FrameField.isInvertible_coprod_of_bijective
    rw [heq]
    exact
      (e.isInvertible_sheet_coprod_complement tube.chart ht (htarget t ht)).bijective.comp
        p.bijective
  have hQs : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Surjective (Q t) := fun t ht =>
    e.surjective_normalDetector tube.chart q (htarget t ht)
      (hq.contMDiffAt (hO.mem_nhds (hcenter t ht))) (hqs t ht)
  have hQG : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Q t).comp (G t) = 0 := fun t ht =>
    e.normalDetector_comp_sheet_eq_zero tube.chart q hO hq hzero ht (htarget t ht) (hcenter t ht)
  have hsign :=
    FrameField.opposite_intersectionDet_iff_normalDet j G C L Q hG hC hQ hi hQs hQG
  have hdet (t : ℝ) :
    tube.rankThreeSheetPairDet d e t =
      (j.symm.toContinuousLinearMap.comp ((G t).coprod (L t))).det :=
    IntersectionCoordinates.det_jointBlock_eq_tangentSum
      FrameField.rankThreePairCoordinates (G t) (L t)
  have hcoeff (t : ℝ) (ht : t = 0 ∨ t = 1) :
    (Q t).comp (L t) =
      fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (t, 0) := by
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
    have hpoint := tube.rankThree_corner_sheet_charts_coincide d e ht
    have hqD :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q
        (d.chart (StripCoordinates.center t)) :=
      hpoint.symm ▸ hq.contMDiffAt (hO.mem_nhds (hcenter t htI))
    have hQeq : Q t = d.normalDetector tube.chart q t := by
      change e.normalDetector tube.chart q t = d.normalDetector tube.chart q t
      unfold StripNormalData.normalDetector
      rw [hpoint]
    rw [hQeq]
    exact
      d.normalDetector_comp_sheet tube.chart q htI (tube.lower_chart_center_mem_target d htI) hqD
  rw [hdet 0, hdet 1]
  exact hsign.trans (by rw [hcoeff 0 (Or.inl rfl), hcoeff 1 (Or.inr rfl)])

def ManifoldMorse.MorseSurgeryData.beltSheetNormal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p)
    (j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates) :
    D.UpperLevel → (ℝ × EuclideanSpace ℝ (Fin 1)) :=
  j.symm ∘ D.beltNormal

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.opposite_belt_corners_iff_normal_sheet_determinants
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates) {S : Set D.UpperLevel}
    {a b : ℝ → D.UpperLevel} {k l : (ℝ × ℝ) → D.UpperLevel} {h : ℝ} :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∀
      (tube :
        TubularBigon (E := RegularLevel.Model E) S (Set.range D.surgery.beltSphere) a
          b k l h 3)
      (d :
        StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E :=
          RegularLevel.Model E) S k)
      (e :
        StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E :=
          RegularLevel.Model E) (Set.range D.surgery.beltSphere) l),
      (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
        (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => D.beltSheetNormal j (d.chart (w, 0)))
                (0, 0)).det *
            (fderiv ℝ
                (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => D.beltSheetNormal j (d.chart (w, 0)))
                (1, 0)).det <
          0 := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  intro tube d e
  have hq :
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞
      (D.beltSheetNormal j) D.beltNormalDomain :=
    j.symm.contDiff.contMDiff.comp_contMDiffOn (D.contMDiffOn_beltNormal hf)
  have hcenter (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    e.chart (StripCoordinates.center t) ∈ Set.range D.surgery.beltSphere :=
    (e.sheet _ (e.line ht)).mpr rfl
  have hcenterO (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    e.chart (StripCoordinates.center t) ∈ D.beltNormalDomain := by
    obtain ⟨v, hv⟩ := hcenter t ht
    exact hv ▸ D.belt_mem_normalDomain v
  apply
    tube.opposite_rankThree_corners_iff_normal_sheet_determinants d e (D.beltSheetNormal j)
      D.isOpen_beltNormalDomain hq
  · rintro y ⟨⟨v, rfl⟩, _⟩
    change j.symm (D.beltNormal (D.surgery.beltSphere v)) = 0
    rw [D.beltNormal_belt, map_zero]
  · exact hcenterO
  · intro t ht
    obtain ⟨v, hv⟩ := hcenter t ht
    rw [← hv]
    have hnormal :=
      (D.contMDiffOn_beltNormal hf).contMDiffAt
        (D.isOpen_beltNormalDomain.mem_nhds (D.belt_mem_normalDomain v))
    have hJ :
      mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) j.symm
          (D.beltNormal (D.surgery.beltSphere v)) =
        j.symm.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact j.symm.toContinuousLinearMap.fderiv
    have hjSmooth :
      ContMDiff 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ j.symm :=
      j.symm.contDiff.contMDiff
    rw [beltSheetNormal,
      mfderiv_comp _ (hjSmooth.mdifferentiableAt (by simp)) (hnormal.mdifferentiableAt (by simp)),
      hJ]
    exact j.symm.surjective.comp (D.surjective_beltNormal_derivative hf v)

def NativeSheetCoordinates.projection {D B E M N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M) (x : N) : D :=
  (Φ.symm (F x)).1

theorem NativeSheetCoordinates.contMDiffOn_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) : ContMDiffOn I 𝓘(ℝ, D) ∞ (projection Φ F) (F ⁻¹' Φ.target) := by
  have hcoord : ContMDiffOn I 𝓘(ℝ, D × B) ∞ (Φ.symm ∘ F) (F ⁻¹' Φ.target) :=
    Φ.contMDiffOn_invFun.comp hF.contMDiffOn (fun _ hx => hx)
  exact contDiff_fst.contMDiff.comp_contMDiffOn hcoord

theorem NativeSheetCoordinates.injective_mfderiv_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0) {x : N}
    (hx : F x ∈ Φ.target) (hiF : Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    Function.Injective (mfderiv I 𝓘(ℝ, D) (projection Φ F) x) := by
  let C : N → (D × B) := Φ.symm ∘ F
  let T : G →L[ℝ] (D × B) := mfderiv I 𝓘(ℝ, D × B) C x
  have hC : ContMDiffAt I 𝓘(ℝ, D × B) ∞ C x :=
    (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hx)).comp x hF.contMDiffAt
  have hTi : Function.Injective T := by
    change Function.Injective (mfderiv I 𝓘(ℝ, D × B) (Φ.symm ∘ F) x)
    rw [mfderiv_comp x (Φ.symm.mdifferentiableAt (by simp) hx) (hF.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv Φ.symm hx).injective.comp hiF
  have hfst :
    (mfderiv I 𝓘(ℝ, D) (projection Φ F) x : G →L[ℝ] D) = (ContinuousLinearMap.fst ℝ D B).comp T :=
    by
    have hp : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, D) ∞ (Prod.fst : D × B → D) := contDiff_fst.contMDiff
    have hd :
      mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, D) (Prod.fst : D × B → D) (C x) = ContinuousLinearMap.fst ℝ D B := by
      rw [mfderiv_eq_fderiv]
      exact (ContinuousLinearMap.fst ℝ D B).fderiv
    change mfderiv I 𝓘(ℝ, D) (Prod.fst ∘ C) x = _
    rw [mfderiv_comp x (hp.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp)), hd]
    rfl
  have hzero : (Prod.snd ∘ C) =ᶠ[𝓝 x] (fun _ => (0 : B)) := by
    filter_upwards [hF.continuous.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)] with
      y hy
    exact (hclean _ (Φ.map_target' hy)).mp ⟨y, (Φ.right_inv' hy).symm⟩
  have hsnd : (ContinuousLinearMap.snd ℝ D B).comp T = 0 := by
    have hp : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
    have hd :
      mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, B) (Prod.snd : D × B → B) (C x) = ContinuousLinearMap.snd ℝ D B := by
      rw [mfderiv_eq_fderiv]
      exact (ContinuousLinearMap.snd ℝ D B).fderiv
    have hz : (mfderiv I 𝓘(ℝ, B) (Prod.snd ∘ C) x : G →L[ℝ] B) = 0 := by
      rw [hzero.mfderiv_eq, mfderiv_const]
      rfl
    rw [mfderiv_comp x (hp.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp)),
      hd] at hz
    exact hz
  intro u v huv
  apply hTi
  apply Prod.ext
  · exact
      (congrArg (fun L : G →L[ℝ] D => L u) hfst).symm.trans
        (huv.trans (congrArg (fun L : G →L[ℝ] D => L v) hfst))
  · have hz (w : G) : (T w).2 = 0 := congrArg (fun L : G →L[ℝ] B => L w) hsnd
    rw [hz u, hz v]

theorem NativeSheetCoordinates.isLocalDiffeomorphOn_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M) [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ G] [I.Boundaryless] [IsManifold I ∞ N] (hF : ContMDiff I 𝓘(ℝ, E) ∞ F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D)
    (hiF : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    IsLocalDiffeomorphOn I 𝓘(ℝ, D) ∞ (projection Φ F) (F ⁻¹' Φ.target) := by
  have hU : IsOpen (F ⁻¹' Φ.target) := Φ.open_target.preimage hF.continuous
  intro x
  let A : G →L[ℝ] D := mfderiv I 𝓘(ℝ, D) (projection Φ F) x.1
  have hi : Function.Injective A := injective_mfderiv_projection Φ F hF hclean x.2 (hiF x.1)
  have hb : Function.Bijective A :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩
  have hA : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  exact isLocalDiffeomorphAt_boundaryless hU x.2 (contMDiffOn_projection Φ F hF) hA

theorem NativeSheetCoordinates.exists_induced_sheet_chart {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {I : ModelWithCorners ℝ G H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I ∞ N] [Nonempty N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) (hinjF : Function.Injective F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D)
    (hiF : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, D) I D N ∞,
      c.source = {u | (u, (0 : B)) ∈ Φ.source} ∧
        c.target = F ⁻¹' Φ.target ∧
          (∀ u ∈ c.source, F (c u) = Φ (u, 0)) ∧ ∀ x, c.symm x = projection Φ F x := by
  let U := F ⁻¹' Φ.target
  have hU : IsOpen U := Φ.open_target.preimage hF.continuous
  have hzero (x : N) (hx : x ∈ U) : (Φ.symm (F x)).2 = 0 :=
    (hclean _ (Φ.map_target' hx)).mp ⟨x, (Φ.right_inv' hx).symm⟩
  have hinj : Set.InjOn (projection Φ F) U := by
    intro x hx y hy heq
    have hc : Φ.symm (F x) = Φ.symm (F y) := Prod.ext heq ((hzero x hx).trans (hzero y hy).symm)
    apply hinjF
    exact (Φ.right_inv' hx).symm.trans ((congrArg Φ hc).trans (Φ.right_inv' hy))
  let p :=
    partialDiffeomorphOfInjectiveLocal hU hinj
      (isLocalDiffeomorphOn_projection Φ F hF hclean hdim hiF)
  have htarget : p.target = {u | (u, (0 : B)) ∈ Φ.source} := by
    change projection Φ F '' U = _
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      have heq : (projection Φ F x, (0 : B)) = Φ.symm (F x) := Prod.ext rfl (hzero x hx).symm
      change (projection Φ F x, (0 : B)) ∈ Φ.source
      rw [heq]
      exact Φ.map_target' hx
    · intro hu
      obtain ⟨x, hx⟩ := (hclean (u, 0) hu).mpr rfl
      have hxU : x ∈ U := by
        change F x ∈ Φ.target
        rw [hx]
        exact Φ.map_source' hu
      refine ⟨x, hxU, ?_⟩
      change (Φ.symm (F x)).1 = u
      rw [hx]
      exact congrArg Prod.fst (Φ.left_inv' hu)
  refine ⟨p.symm, htarget, rfl, ?_, fun _ => rfl⟩
  intro u hu
  have hx : p.symm u ∈ U := p.map_target' hu
  have hp : projection Φ F (p.symm u) = u := p.right_inv' hu
  have heq : Φ.symm (F (p.symm u)) = (u, (0 : B)) := Prod.ext hp (hzero (p.symm u) hx)
  exact (Φ.right_inv' hx).symm.trans (congrArg Φ heq)

def SphereNormalCoordinates.radialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (x : V)).coprod ((inclusionDerivative x).comp C)

theorem SphereNormalCoordinates.normalFrame_comp_normalDerivative {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (normalFrame x A).comp ((ContinuousLinearMap.id ℝ ℝ).prodMap (A.comp C)) = radialFrame x C := by
  apply ContinuousLinearMap.ext
  intro z
  change
    z.1 • (x : V) + inclusionDerivative x (A.inverse (A (C z.2))) =
      z.1 • (x : V) + inclusionDerivative x (C z.2)
  rw [hA.inverse_apply_self]

theorem SphereNormalCoordinates.bijective_radialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) (hC : C.IsInvertible) :
    Function.Bijective (radialFrame x C) := by
  have heq : radialFrame x C = normalFrame x C.inverse := by
    apply ContinuousLinearMap.ext
    intro z
    change
      z.1 • (x : V) + inclusionDerivative x (C z.2) =
        z.1 • (x : V) + inclusionDerivative x (C.inverse.inverse z.2)
    rw [hC.inverse_inverse]
  rw [heq]
  exact bijective_normalFrame x C.inverse hC.inverse

theorem SphereNormalCoordinates.normalJacobian_mul_chartDet {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] [FiniteDimensional ℝ N] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    normalJacobian j x A * (A.comp C).det =
      ((radialFrame x C).comp j.symm.toContinuousLinearMap).det := by
  let R : (ℝ × N) →L[ℝ] (ℝ × N) := (ContinuousLinearMap.id ℝ ℝ).prodMap (A.comp C)
  let T : V →L[ℝ] V := j.toContinuousLinearMap.comp (R.comp j.symm.toContinuousLinearMap)
  have hdetT : T.det = (A.comp C).det := by
    have hconj : T.det = R.det := LinearMap.det_conj R.toLinearMap j.toLinearEquiv
    rw [hconj]
    change (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (A.comp C).toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hfactor :
    ((normalFrame x A).comp j.symm.toContinuousLinearMap).comp T =
      (radialFrame x C).comp j.symm.toContinuousLinearMap := by
    have h := normalFrame_comp_normalDerivative x A hA C
    ext v
    change normalFrame x A (j.symm (j (R (j.symm v)))) = radialFrame x C (j.symm v)
    rw [j.symm_apply_apply]
    exact congrArg (fun L : (ℝ × N) →L[ℝ] V => L (j.symm v)) h
  calc
    normalJacobian j x A * (A.comp C).det =
        (((normalFrame x A).comp j.symm.toContinuousLinearMap).comp T).det := by
      rw [← hdetT]
      exact (LinearMap.det_comp _ _).symm
    _ = _ := congrArg ContinuousLinearMap.det hfactor

def SphereNormalCoordinates.chartRadialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) (z : N) :
    (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (c z : V)).coprod (fderiv ℝ (fun w => (c w : V)) z)

theorem SphereNormalCoordinates.chartRadialFrame_eq {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) {z : N}
    (hz : z ∈ c.source) :
    chartRadialFrame c z =
      radialFrame (N := N) (c z) (mfderiv 𝓘(ℝ, N) (𝓡 n) c z : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  by
  have hchain :
    fderiv ℝ (fun w => (c w : V)) z =
      (inclusionDerivative (c z)).comp
        (mfderiv 𝓘(ℝ, N) (𝓡 n) c z : N →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    have h :=
      mfderiv_comp z ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).mdifferentiableAt (by simp))
        (c.mdifferentiableAt (by simp) hz)
    rw [mfderiv_eq_fderiv] at h
    exact h
  unfold chartRadialFrame radialFrame
  rw [hchain]
  rfl

theorem SphereNormalCoordinates.contDiffOn_chartRadialFrame {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) :
    ContDiffOn ℝ ∞ (chartRadialFrame c) c.source := by
  have hc : ContDiffOn ℝ ∞ (fun w => (c w : V)) c.source :=
    ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).comp_contMDiffOn c.contMDiffOn_toFun).contDiffOn
  exact
    FrameField.contDiffOn_coprod (contDiffOn_const.smulRight hc)
      (hc.fderiv_of_isOpen c.open_source (m := ∞) (by simp))

theorem SphereNormalCoordinates.bijective_chartRadialFrame {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) [FiniteDimensional ℝ N]
    {z : N} (hz : z ∈ c.source) : Function.Bijective (chartRadialFrame c z) := by
  rw [chartRadialFrame_eq c hz]
  let C : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c z
  have hC : C.IsInvertible :=
    ⟨(LinearEquiv.ofBijective C.toLinearMap
          (PartialChart.bijective_mfderiv c hz)).toContinuousLinearEquiv,
      rfl⟩
  exact bijective_radialFrame (c z) C hC

theorem SphereNormalCoordinates.chartRadialFrame_det_mul_endpoints_pos {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ V] (j : (ℝ × N) ≃L[ℝ] V) (a : ℝ → N)
    (ha : ContinuousOn a (Set.Icc (0 : ℝ) 1)) (haS : Set.MapsTo a (Set.Icc (0 : ℝ) 1) c.source) :
    0 <
      ((chartRadialFrame c (a 0)).comp j.symm.toContinuousLinearMap).det *
        ((chartRadialFrame c (a 1)).comp j.symm.toContinuousLinearMap).det := by
  have hF := (contDiffOn_chartRadialFrame c).continuousOn.comp ha haS
  exact
    FrameField.det_mul_endpoints_pos (hF.clm_comp continuousOn_const)
      (fun t ht => (bijective_chartRadialFrame c (haS ht)).comp j.symm.bijective)

theorem SphereNormalCoordinates.opposite_normalJacobians_iff_chartDet {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ V] (j : (ℝ × N) ≃L[ℝ] V) (a : ℝ → N)
    (ha : ContinuousOn a (Set.Icc (0 : ℝ) 1)) (haS : Set.MapsTo a (Set.Icc (0 : ℝ) 1) c.source)
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) (hB : B.IsInvertible) :
    normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B < 0 ↔
      (A.comp (mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 0) : N →L[ℝ] EuclideanSpace ℝ (Fin n))).det *
          (B.comp (mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 1) : N →L[ℝ] EuclideanSpace ℝ (Fin n))).det <
        0 := by
  let C₀ : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 0)
  let C₁ : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 1)
  have h₀ :
    normalJacobian j (c (a 0)) A * (A.comp C₀).det =
      ((chartRadialFrame c (a 0)).comp j.symm.toContinuousLinearMap).det := by
    rw [chartRadialFrame_eq c (haS (by simp))]
    exact normalJacobian_mul_chartDet j (c (a 0)) A hA C₀
  have h₁ :
    normalJacobian j (c (a 1)) B * (B.comp C₁).det =
      ((chartRadialFrame c (a 1)).comp j.symm.toContinuousLinearMap).det := by
    rw [chartRadialFrame_eq c (haS (by simp))]
    exact normalJacobian_mul_chartDet j (c (a 1)) B hB C₁
  have hp :
    0 <
      (normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B) *
        ((A.comp C₀).det * (B.comp C₁).det) := by
    have heq :
      (normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B) *
          ((A.comp C₀).det * (B.comp C₁).det) =
        (normalJacobian j (c (a 0)) A * (A.comp C₀).det) *
          (normalJacobian j (c (a 1)) B * (B.comp C₁).det) := by ring
    rw [heq, h₀, h₁]
    exact chartRadialFrame_det_mul_endpoints_pos c j a ha haS
  change _ ↔ (A.comp C₀).det * (B.comp C₁).det < 0
  rcases mul_pos_iff.mp hp with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact iff_of_false (not_lt_of_gt hp) (not_lt_of_gt hq)
  · exact iff_of_true hp hq

theorem SphereNormalCoordinates.opposite_normalJacobians_iff_retained_sheet
    {V A B E M : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (Φ : PartialDiffeomorph 𝓘(ℝ, (ℝ × A) × B) 𝓘(ℝ, E) ((ℝ × A) × B) M ∞)
    (F : Metric.sphere (0 : V) 1 → M) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ F)
    (hinjF : Function.Injective F) (hiF : ∀ x, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) F x))
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hline : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((t, (0 : A)), (0 : B)) ∈ Φ.source)
    (hdim : Module.finrank ℝ (ℝ × A) = n) (q : M → (ℝ × A)) (r : (ℝ × (ℝ × A)) ≃L[ℝ] V)
    (x₀ x₁ : Metric.sphere (0 : V) 1) (hx₀ : F x₀ = Φ ((0, 0), 0)) (hx₁ : F x₁ = Φ ((1, 0), 0))
    (hq₀ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x₀))
    (hq₁ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x₁))
    (hi₀ : (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀).IsInvertible)
    (hi₁ : (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁).IsInvertible) :
    normalJacobian r x₀ (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀) *
          normalJacobian r x₁ (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁) <
        0 ↔
      (fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (0, 0)).det *
          (fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (1, 0)).det <
        0 := by
  let _ : Nonempty (Metric.sphere (0 : V) 1) := ⟨x₀⟩
  obtain ⟨c, hcS, _, hFc, _⟩ :=
    NativeSheetCoordinates.exists_induced_sheet_chart Φ F hF hinjF hclean
      (by simpa only [finrank_euclideanSpace_fin] using hdim.symm) hiF
  let a : ℝ → (ℝ × A) := fun t => (t, 0)
  have ha : ContinuousOn a (Set.Icc (0 : ℝ) 1) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have haS : Set.MapsTo a (Set.Icc (0 : ℝ) 1) c.source := by
    intro t ht
    rw [hcS]
    exact hline t ht
  have h₀ : c (a 0) = x₀ := hinjF ((hFc _ (haS (by simp))).trans hx₀.symm)
  have h₁ : c (a 1) = x₁ := hinjF ((hFc _ (haS (by simp))).trans hx₁.symm)
  let A₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) := mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀
  let A₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) := mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁
  have hsign := opposite_normalJacobians_iff_chartDet c r a ha haS A₀ A₁ hi₀ hi₁
  have hcoeff (t : ℝ) (x : Metric.sphere (0 : V) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : c (a t) = x) (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x)) :
    (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A)).comp
        (mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a t) : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (t, 0) := by
    have hqF : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ × A) ∞ (q ∘ F) (c (a t)) := by
      rw [hx]
      exact hq.comp x hF.contMDiffAt
    have hchain :=
      mfderiv_comp (a t) (hqF.mdifferentiableAt (by simp))
        (c.mdifferentiableAt (by simp) (haS ht))
    have heq : ((q ∘ F) ∘ c) =ᶠ[𝓝 (a t)] (fun w => q (Φ (w, 0))) := by
      filter_upwards [c.open_source.mem_nhds (haS ht)] with w hw
      exact congrArg q (hFc w hw)
    have hpoint :
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) (c (a t)) : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A)) =
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x := by rw [hx]
    rw [mfderiv_eq_fderiv] at hchain
    have h := hchain.symm.trans heq.fderiv_eq
    exact
      (congrArg
            (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) =>
              L.comp (mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a t) : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n)))
            hpoint).symm.trans
        h
  rw [h₀, h₁] at hsign
  let C₀ : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a 0)
  let C₁ : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a 1)
  have hc₀ : A₀.comp C₀ = fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (0, 0) :=
    hcoeff 0 x₀ (by simp) h₀ hq₀
  have hc₁ : A₁.comp C₁ = fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (1, 0) :=
    hcoeff 1 x₁ (by simp) h₁ hq₁
  change
    normalJacobian r x₀ A₀ * normalJacobian r x₁ A₁ < 0 ↔
      (A₀.comp C₀).det * (A₁.comp C₁).det < 0 at hsign
  rw [hc₀, hc₁] at hsign
  exact hsign

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.opposite_beltIntersectionSigns_iff_Whitney_corners
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : Hemisphere.Sphere 2 → D.UpperLevel) {a b : ℝ → D.UpperLevel}
    {k l : (ℝ × ℝ) → D.UpperLevel} {h : ℝ} :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g
            D.surgery.beltSphere x y)
      (tube :
        TubularBigon (E := RegularLevel.Model E) (Set.range g)
          (Set.range D.surgery.beltSphere) a b k l h 3)
      (d :
        StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E :=
          RegularLevel.Model E) (Set.range g) k)
      (e :
        StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E :=
          RegularLevel.Model E) (Set.range D.surgery.beltSphere) l)
      (x₀ x₁ : Hemisphere.Sphere 2),
      g x₀ = d.chart (StripCoordinates.center 0) →
        g x₁ = d.chart (StripCoordinates.center 1) →
          ((D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1) ↔
            tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg hinj hi ht tube d e x₀ x₁ hx₀ hx₁
  let j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hindex])
  let q := D.beltSheetNormal j
  let r' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) j).trans r
  have hjSmooth :
    ContMDiff 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ j.symm :=
    j.symm.contDiff.contMDiff
  have hdata (x : Hemisphere.Sphere 2) (hx : g x ∈ Set.range D.surgery.beltSphere) :
    ContMDiffAt 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q (g x) ∧
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (q ∘ g) x).IsInvertible ∧
        SphereNormalCoordinates.normalJacobian r' x
            (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (q ∘ g) x) =
          D.beltIntersectionJacobian 2 r g x := by
    obtain ⟨v, hv⟩ := hx
    have hxO : g x ∈ D.beltNormalDomain := hv ▸ D.belt_mem_normalDomain v
    have hnormal :=
      (D.contMDiffOn_beltNormal hf).contMDiffAt (D.isOpen_beltNormalDomain.mem_nhds hxO)
    have hq :
      ContMDiffAt 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q (g x) :=
      hjSmooth.contMDiffAt.comp _ hnormal
    let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates :=
      mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g) x
    let B : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) :=
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (q ∘ g) x
    have hAb : Function.Bijective A :=
      D.bijective_beltNormal_comp_of_transverse hf 3 2 hindex g hg x v hv (ht x v hv)
    have hA : A.IsInvertible :=
      ⟨(LinearEquiv.ofBijective A.toLinearMap hAb).toContinuousLinearEquiv, rfl⟩
    have hJ :
      mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) j.symm
          (D.beltNormal (g x)) =
        j.symm.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact j.symm.toContinuousLinearMap.fderiv
    have hBA : B = j.symm.toContinuousLinearMap.comp A := by
      change mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (j.symm ∘ (D.beltNormal ∘ g)) x = _
      rw [mfderiv_comp x (hjSmooth.mdifferentiableAt (by simp))
          ((hnormal.comp x hg.contMDiffAt).mdifferentiableAt (by simp))]
      change
        (mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) j.symm
                  (D.beltNormal (g x)) :
                D.chart.NegativeCoordinates →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1))).comp
            A =
          _
      exact
        congrArg
          (fun L : D.chart.NegativeCoordinates →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) => L.comp A)
          hJ
    refine ⟨hq, ?_, ?_⟩
    · change B.IsInvertible
      rw [hBA]
      exact (show j.symm.toContinuousLinearMap.IsInvertible from ⟨j.symm, rfl⟩).comp hA
    · change
        SphereNormalCoordinates.normalJacobian r' x B =
          SphereNormalCoordinates.normalJacobian r x A
      rw [hBA]
      exact SphereNormalCoordinates.normalJacobian_change_normal_model r j x A hA
  have hcross (t : ℝ) (ht' : t = 0 ∨ t = 1) (x : Hemisphere.Sphere 2)
    (hx : g x = d.chart (StripCoordinates.center t)) :
    g x ∈ Set.range D.surgery.beltSphere := by
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht' with rfl | rfl <;> simp
    rw [hx, tube.rankThree_corner_sheet_charts_coincide d e ht']
    exact (e.sheet _ (e.line htI)).mpr rfl
  obtain ⟨hq₀, hi₀, hJ₀⟩ := hdata x₀ (hcross 0 (Or.inl rfl) x₀ hx₀)
  obtain ⟨hq₁, hi₁, hJ₁⟩ := hdata x₁ (hcross 1 (Or.inr rfl) x₁ hx₁)
  have hsign :=
    SphereNormalCoordinates.opposite_normalJacobians_iff_retained_sheet d.chart g hg hinj hi
      d.sheet d.line (by simp [Module.finrank_prod]) q r' x₀ x₁ hx₀ hx₁ hq₀ hq₁ hi₀ hi₁
  rw [hJ₀, hJ₁] at hsign
  exact
    (D.beltIntersectionSigns_opposite_iff 2 r g x₀ x₁).trans
      (hsign.trans (D.opposite_belt_corners_iff_normal_sheet_determinants hf j tube d e).symm)

def WhitneyPairModel.innerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - r) • (0, h / 2) + r • p

theorem WhitneyPairModel.innerBigonMap_one (h : ℝ) (p : ℝ × ℝ) : innerBigonMap h 1 p = p := by
  simp only [innerBigonMap, sub_self, zero_smul, one_smul, zero_add]

theorem WhitneyPairModel.contDiff_innerBigonMap (h : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => innerBigonMap h z.1 z.2) := by
  unfold innerBigonMap
  fun_prop

def WhitneyPairModel.innerBigonDiffeomorph (h r : ℝ) (hr : r ≠ 0) :
    Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞
    where
  toEquiv :=
    { toFun := innerBigonMap h r
      invFun := fun p => r⁻¹ • (p - (1 - r) • (0, h / 2))
      left_inv := by
        intro p
        simp only [innerBigonMap, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]
      right_inv := by
        intro p
        simp only [innerBigonMap, smul_smul, mul_inv_cancel₀ hr, one_smul]
        abel }
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (innerBigonMap h r)
    apply ContDiff.contMDiff
    unfold innerBigonMap
    fun_prop
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun p : ℝ × ℝ => r⁻¹ • (p - (1 - r) • (0, h / 2)))
    apply ContDiff.contMDiff
    fun_prop

theorem WhitneyPairModel.bijective_mfderiv_innerBigonMap (h r : ℝ) (hr : r ≠ 0)
    (p : ℝ × ℝ) : Function.Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (innerBigonMap h r) p) :=
  PartialChart.bijective_mfderiv (innerBigonDiffeomorph h r hr).toPartialDiffeomorph
    (Set.mem_univ p)

theorem WhitneyPairModel.innerBigonMap_mem_interior {h r : ℝ} (hh : 0 < h)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    innerBigonMap h r p ∈ interior (bigon h) :=
  (convex_bigon hh.le).combo_interior_self_mem_interior (bigon_center_mem_interior hh) hp
    (sub_pos.mpr hr.2) hr.1.le (by ring)

def WhitneyPairModel.innerBigonCollar (h r : ℝ) : Set (ℝ × ℝ) :=
  bigon h \ innerBigonMap h r '' interior (bigon h)

def WhitneyPairModel.inverseInnerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  r⁻¹ • (p - (1 - r) • (0, h / 2))

theorem WhitneyPairModel.inverseInnerBigonMap_one (h : ℝ) (p : ℝ × ℝ) :
    inverseInnerBigonMap h 1 p = p := by
  simp only [inverseInnerBigonMap, inv_one, sub_self, zero_smul, sub_zero, one_smul]

theorem WhitneyPairModel.inner_inverseInnerBigonMap (h r : ℝ) (hr : r ≠ 0) (p : ℝ × ℝ) :
    innerBigonMap h r (inverseInnerBigonMap h r p) = p :=
  (innerBigonDiffeomorph h r hr).apply_symm_apply p

theorem WhitneyPairModel.continuousAt_inverseInnerBigonMap (h : ℝ) (p : ℝ × ℝ) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ) => inverseInnerBigonMap h z.1 z.2) (1, p) := by
  unfold inverseInnerBigonMap
  fun_prop (disch := norm_num)

theorem WhitneyPairModel.isCompact_innerBigonCollar {h r : ℝ} (hh : 0 < h) (hr : r ≠ 0) :
    IsCompact (innerBigonCollar h r) := by
  have ho : IsOpen (innerBigonMap h r '' interior (bigon h)) :=
    (innerBigonDiffeomorph h r hr).toHomeomorph.isOpenMap _ isOpen_interior
  exact (isCompact_bigon hh).inter_right ho.isClosed_compl

theorem WhitneyPairModel.innerBigonMap_mem_collar_iff {h r : ℝ} (hh : 0 < h)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    innerBigonMap h r p ∈ innerBigonCollar h r ↔ p ∈ frontier (bigon h) := by
  rw [frontier, (isClosed_bigon h).closure_eq]
  constructor
  · intro hx
    exact ⟨hp, fun hi => hx.2 (Set.mem_image_of_mem _ hi)⟩
  · intro hx
    refine ⟨interior_subset (innerBigonMap_mem_interior hh hr hp), ?_⟩
    rintro ⟨q, hq, heq⟩
    have hqp : q = p := (innerBigonDiffeomorph h r hr.1.ne').injective heq
    exact hx.2 (hqp ▸ hq)

theorem WhitneyPairModel.exists_inner_bigon_collar_in_open {h : ℝ} (hh : 0 < h)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hfrontU : frontier (bigon h) ⊆ U) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        innerBigonCollar h r ⊆ U ∧
          Set.MapsTo (innerBigonMap h r) (frontier (bigon h)) (U ∩ interior (bigon h)) := by
  let bad : Set (ℝ × ℝ) := bigon h \ U
  have hbad : IsCompact bad := (isCompact_bigon hh).inter_right hU.isClosed_compl
  have hbadInterior : bad ⊆ interior (bigon h) := by
    intro p hp
    by_contra hi
    apply hp.2
    apply hfrontU
    rw [frontier, (isClosed_bigon h).closure_eq]
    exact ⟨hp.1, hi⟩
  have hnearInv : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ bad, inverseInnerBigonMap h r p ∈ interior (bigon h) :=
    by
    apply hbad.eventually_forall_of_forall_eventually
    intro p hp
    apply (continuousAt_inverseInnerBigonMap h p).preimage_mem_nhds
    apply isOpen_interior.mem_nhds
    simpa only [inverseInnerBigonMap_one] using hbadInterior hp
  have hcompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  have hnearFront : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ frontier (bigon h), innerBigonMap h r p ∈ U := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((contDiff_innerBigonMap h).continuous.continuousAt (x := (1, p))).preimage_mem_nhds
    apply hU.mem_nhds
    simpa only [innerBigonMap_one] using hfrontU hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hnearInv.and hnearFront)
  let δ : ℝ := Min.min ε 1 / 2
  have hδpos : 0 < δ := half_pos (lt_min hε zero_lt_one)
  have hδε : δ < ε := by
    dsimp [δ]
    have hm := min_le_left ε 1
    linarith
  have hδ1 : δ < 1 := by
    dsimp [δ]
    have hm := min_le_right ε 1
    linarith
  have hr : 1 - δ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hrball : 1 - δ ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : 1 - δ - 1 = -δ := by ring
    rw [heq, abs_neg, abs_of_pos hδpos]
    exact hδε
  have hretained := hball hrball
  refine ⟨1 - δ, hr, ?_, fun p hp => ⟨hretained.2 p hp, ?_⟩⟩
  · intro p hp
    by_contra hpU
    exact
      hp.2
        ⟨inverseInnerBigonMap h (1 - δ) p, hretained.1 p ⟨hp.1, hpU⟩,
          inner_inverseInnerBigonMap h (1 - δ) hr.1.ne' p⟩
  · exact innerBigonMap_mem_interior hh hr ((mem_frontier_bigon_iff h p).mp hp).1

theorem CleanBigonBoundary.exists_inner_clean_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ V : Set (ℝ × ℝ),
            IsOpen V ∧
              frontier (WhitneyPairModel.bigon h) ⊆ V ∧
                ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
                    (d.map ∘ WhitneyPairModel.innerBigonMap h r) V ∧
                  Set.InjOn (d.map ∘ WhitneyPairModel.innerBigonMap h r) V ∧
                    (∀ p ∈ V,
                        Function.Injective
                          (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E)
                            (d.map ∘ WhitneyPairModel.innerBigonMap h r) p)) ∧
                      Set.MapsTo (WhitneyPairModel.innerBigonMap h r) V
                          (d.domain ∩ interior (WhitneyPairModel.bigon h)) ∧
                        ∀ p ∈ V, d.map (WhitneyPairModel.innerBigonMap h r p) ∉ S ∪ T := by
  have hfrontD : frontier (WhitneyPairModel.bigon h) ⊆ d.domain :=
    d.boundary_covered.trans (interior_subset.trans d.neighborhood_subset)
  obtain ⟨r, hr, hcollar, hfront⟩ :=
    WhitneyPairModel.exists_inner_bigon_collar_in_open d.height_pos d.open_domain hfrontD
  let c := WhitneyPairModel.innerBigonDiffeomorph h r hr.1.ne'
  let V : Set (ℝ × ℝ) :=
    WhitneyPairModel.innerBigonMap h r ⁻¹'
      (d.domain ∩ interior (WhitneyPairModel.bigon h))
  have hc : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (WhitneyPairModel.innerBigonMap h r) :=
    c.contMDiff
  have hV : IsOpen V := (d.open_domain.inter isOpen_interior).preimage hc.continuous
  have hsmooth :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (d.map ∘ WhitneyPairModel.innerBigonMap h r) V :=
    d.smooth.comp hc.contMDiffOn (fun _ hp => hp.1)
  have hinj : Set.InjOn (d.map ∘ WhitneyPairModel.innerBigonMap h r) V := by
    intro p hp q hq hpq
    exact c.injective (d.injective hp.1 hq.1 hpq)
  refine ⟨r, hr, hcollar, V, hV, hfront, hsmooth, hinj, ?_, fun _ hp => hp, ?_⟩
  · intro p hp
    have hdf := (d.smooth.contMDiffAt (d.open_domain.mem_nhds hp.1)).mdifferentiableAt (by simp)
    rw [mfderiv_comp p hdf (hc.mdifferentiableAt (by simp))]
    exact
      (d.derivative_injective _ hp.1).comp
        (WhitneyPairModel.bijective_mfderiv_innerBigonMap h r hr.1.ne' p).injective
  · intro p hp
    exact d.interior_avoids _ hp

theorem CleanBigonBoundary.exists_smooth_inner_extension_in_open {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h) (U : TopologicalSpace.Opens M)
    (hU : (S ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, U), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ F : C(ℝ × ℝ, U),
            ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
              ∃ W : Set (ℝ × ℝ),
                IsOpen W ∧
                  frontier (WhitneyPairModel.bigon h) ⊆ W ∧
                    Set.EqOn (Subtype.val ∘ F) (d.map ∘ WhitneyPairModel.innerBigonMap h r)
                        W ∧
                      Set.InjOn F W ∧
                        (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
                          ∀ p ∈ W, (F p : M) ∉ S ∪ T := by
  classical
  obtain ⟨r, hr, hcollar, V, hV, hfrontV, hsmooth, hinj, hderiv, -, havoid⟩ :=
    d.exists_inner_clean_neighborhood
  have hzero : (0 : ℝ × ℝ) ∈ frontier (WhitneyPairModel.bigon h) := by
    rw [WhitneyPairModel.mem_frontier_bigon_iff]
    refine ⟨?_, Or.inl rfl⟩
    change 0 ≤ (0 : ℝ) ∧ h * 0 ^ 2 + 0 ≤ h
    simpa only [zero_pow (by decide : 2 ≠ 0), MulZeroClass.mul_zero, add_zero] using
      And.intro le_rfl d.height_pos.le
  let c : U := ⟨d.map (WhitneyPairModel.innerBigonMap h r 0), hU (havoid 0 (hfrontV hzero))⟩
  let f : (ℝ × ℝ) → U := fun p =>
    if hp : p ∈ V then ⟨d.map (WhitneyPairModel.innerBigonMap h r p), hU (havoid p hp)⟩
    else c
  have hval (p : ℝ × ℝ) (hp : p ∈ V) :
    (f p : M) = d.map (WhitneyPairModel.innerBigonMap h r p) := by
    dsimp [f]
    rw [dif_pos hp]
  have hfval : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (Subtype.val ∘ f) V :=
    hsmooth.congr (fun p hp => hval p hp)
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f V := by
    intro p hp
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U f V p).mp (hfval p hp)
  obtain ⟨F, hF, W, hW, hfrontW, hWV, hEq⟩ :=
    exists_smooth_bigon_neighborhood_extension_of_circle_nullhomotopies hnull d.height_pos
      hV hf hfrontV
  have hEqval : Set.EqOn (Subtype.val ∘ F) (d.map ∘ WhitneyPairModel.innerBigonMap h r) W :=
    by
    intro p hp
    exact (congrArg Subtype.val (hEq hp)).trans (hval p (hWV hp))
  have hinjF : Set.InjOn F W := by
    intro p hp q hq hpq
    apply hinj (hWV hp) (hWV hq)
    exact (hEqval hp).symm.trans ((congrArg Subtype.val hpq).trans (hEqval hq))
  refine ⟨r, hr, hcollar, F, hF, W, hW, hfrontW, hEqval, hinjF, ?_, ?_⟩
  · intro p hp
    have heq : (Subtype.val ∘ F) =ᶠ[𝓝 p] (d.map ∘ WhitneyPairModel.innerBigonMap h r) :=
      Filter.mem_of_superset (hW.mem_nhds hp) (fun _ hq => hEqval hq)
    have hi : Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Subtype.val ∘ F) p) := by
      rw [heq.mfderiv_eq]
      exact hderiv p (hWV hp)
    have hc : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : U → M) := contMDiff_subtype_val
    rw [mfderiv_comp p (hc.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))] at hi
    intro v w hvw
    apply hi
    exact congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) (F p)) hvw
  · intro p hp
    change (Subtype.val ∘ F) p ∉ S ∪ T
    rw [hEqval hp]
    exact havoid p (hWV hp)

theorem CleanBigonBoundary.exists_embedded_inner_extension_in_open {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] [T2Space M] {D Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y]
    [ChartedSpace D Y] [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M))
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g) {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (Set.range g) T a b k l h)
    (U : TopologicalSpace.Opens M) (hU : (Set.range g ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, U), ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ F : C(ℝ × ℝ, U),
            ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
              Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => F p) ∧
                (∀ p ∈ WhitneyPairModel.bigon h,
                    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
                  (∀ p ∈ WhitneyPairModel.bigon h, (F p : M) ∉ Set.range g) ∧
                    ∃ W : Set (ℝ × ℝ),
                      IsOpen W ∧
                        frontier (WhitneyPairModel.bigon h) ⊆ W ∧
                          Set.EqOn (Subtype.val ∘ F)
                            (d.map ∘ WhitneyPairModel.innerBigonMap h r) W := by
  obtain ⟨r, hr, hcollar, F, hF, V, hV, hfrontV, hEq, hinj, hderiv, havoid⟩ :=
    d.exists_smooth_inner_extension_in_open U hU hnull
  have hcompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon d.height_pos).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, -, hC, hfrontC, hCV⟩ := exists_compact_closed_between hcompact hV hfrontV
  have hinjC : Set.InjOn F (WhitneyPairModel.bigon h ∩ C) :=
    hinj.mono (Set.inter_subset_right.trans hCV)
  have hiC :
    ∀ p ∈ WhitneyPairModel.bigon h ∩ C,
      Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p) :=
    fun p hp => hderiv p (hCV hp.2)
  have hclean :
    ∀ p ∈ WhitneyPairModel.bigon h ∩ C, p ∉ (∅ : Set (ℝ × ℝ)) → (F p : M) ∉ Set.range g := by
    intro p hp _ hmem
    exact havoid p (hCV hp.2) (Or.inl hmem)
  obtain ⟨G, hG, hhom, hemb, hiG, havoidG⟩ :=
    ManifoldImmersion.exists_relative_embedded_avoidance_in_open U F g hF hg
      (by simp [Module.finrank_prod]) hdim (by simpa [Module.finrank_prod] using hobstacle)
      (WhitneyPairModel.isCompact_bigon d.height_pos) hC (Set.empty_subset _) hinjC hiC
      hclean
  refine ⟨r, hr, hcollar, G, hG, hemb, hiG, ?_, interior C, isOpen_interior, hfrontC, ?_⟩
  · intro p hp
    exact havoidG p ⟨hp, Set.notMem_empty p⟩
  · intro p hp
    have hpC : p ∈ C := interior_subset hp
    exact (congrArg Subtype.val (hhom.fst_eq_snd hpC)).symm.trans (hEq (hCV hpC))

theorem CleanBigonBoundary.exists_collar_disjoint_inner_extension_in_open {E M D Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y] [ChartedSpace D Y]
    [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M)) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (Set.range g) T a b k l h)
    (U : TopologicalSpace.Opens M) (hU : (Set.range g ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, U), ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ r : ℝ,
      r ∈ Set.Ioo (0 : ℝ) 1 ∧
        WhitneyPairModel.innerBigonCollar h r ⊆ d.domain ∧
          ∃ F : C(ℝ × ℝ, U),
            ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
              Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => F p) ∧
                (∀ p ∈ WhitneyPairModel.bigon h,
                    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
                  (∀ p ∈ WhitneyPairModel.bigon h, (F p : M) ∉ Set.range g) ∧
                    (∀ p ∈ interior (WhitneyPairModel.bigon h),
                        (F p : M) ∉ d.map '' WhitneyPairModel.innerBigonCollar h r) ∧
                      ∃ W : Set (ℝ × ℝ),
                        IsOpen W ∧
                          frontier (WhitneyPairModel.bigon h) ⊆ W ∧
                            Set.EqOn (Subtype.val ∘ F)
                              (d.map ∘ WhitneyPairModel.innerBigonMap h r) W := by
  obtain ⟨r, hr, hcollar, F, hF, hemb, hi, havoid, V, hV, hfrontV, hEq⟩ :=
    d.exists_embedded_inner_extension_in_open g hg U hU hnull hdim hobstacle
  let Q : TopologicalSpace.Opens (ℝ × ℝ) := ⟨d.domain, d.open_domain⟩
  let q : C(Q, M) :=
    ⟨fun p => d.map p, continuousOn_iff_continuous_domRestrict.mp d.smooth.continuousOn⟩
  have hq : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ q := by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact d.smooth.contMDiffAt (d.open_domain.mem_nhds p.property)
  let A : Set Q := Subtype.val ⁻¹' WhitneyPairModel.innerBigonCollar h r
  have himage : q '' A = d.map '' WhitneyPairModel.innerBigonCollar h r := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hcollar hp⟩, hp, rfl⟩
  have hclosed : IsClosed (q '' A) := by
    rw [himage]
    exact
      ((WhitneyPairModel.isCompact_innerBigonCollar d.height_pos
              hr.1.ne').image_of_continuousOn
          (d.smooth.continuousOn.mono hcollar)).isClosed
  have hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (WhitneyPairModel.innerBigonMap h r) :=
    (WhitneyPairModel.innerBigonDiffeomorph h r hr.1.ne').contMDiff
  let V' : Set (ℝ × ℝ) := V ∩ WhitneyPairModel.innerBigonMap h r ⁻¹' d.domain
  have hV' : IsOpen V' := hV.inter (d.open_domain.preimage hs.continuous)
  have hfrontV' : frontier (WhitneyPairModel.bigon h) ⊆ V' := by
    intro p hp
    refine ⟨hfrontV hp, hcollar ?_⟩
    exact
      (WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr
            ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1).mpr
        hp
  have hfrontCompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon d.height_pos).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, -, hC, hfrontC, hCV⟩ := exists_compact_closed_between hfrontCompact hV' hfrontV'
  have hinj : Set.InjOn F (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) heq)
  have hclean :
    ∀ p ∈ WhitneyPairModel.bigon h ∩ C,
      p ∉ frontier (WhitneyPairModel.bigon h) → (F p : M) ∉ q '' A := by
    intro p hp hpB hmem
    rw [himage] at hmem
    obtain ⟨z, hz, heq⟩ := hmem
    have hzp : z = WhitneyPairModel.innerBigonMap h r p :=
      d.injective (hcollar hz) (hCV hp.2).2 (heq.trans (hEq (hCV hp.2).1))
    exact
      hpB
        ((WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr hp.1).mp (hzp ▸ hz))
  let O : Set U := (Subtype.val : U → M) ⁻¹' (Set.range g)ᶜ
  have hO : IsOpen O :=
    (isCompact_range g.continuous).isClosed.isOpen_compl.preimage continuous_subtype_val
  have hmaps : Set.MapsTo F (WhitneyPairModel.bigon h) O := fun p hp => havoid p hp
  have hdim' : 2 * Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  have hobstacle' : Module.finrank ℝ (ℝ × ℝ) + Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨G, hG, hhom, hembG, hiG, hmapsG, havoidG⟩ :=
    ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood_in_open U F q A
      hF hq hclosed hdim' hobstacle' (WhitneyPairModel.isCompact_bigon d.height_pos) hC
      hfrontC hinj hi hclean hO hmaps
  refine ⟨r, hr, hcollar, G, hG, hembG, hiG, hmapsG, ?_, interior C, isOpen_interior, hfrontC, ?_⟩
  · intro p hp hmem
    have hpB : p ∉ frontier (WhitneyPairModel.bigon h) := by
      intro hfront
      rw [frontier] at hfront
      exact hfront.2 hp
    exact havoidG p ⟨interior_subset hp, hpB⟩ (by rwa [himage])
  · intro p hp
    have hpC : p ∈ C := interior_subset hp
    exact (congrArg Subtype.val (hhom.fst_eq_snd hpC)).symm.trans (hEq (hCV hpC).1)

theorem exists_filled_clean_bigon_of_collar_disjoint_inner {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hcollar : WhitneyPairModel.innerBigonCollar h r ⊆ d.domain) (F : C(ℝ × ℝ, M))
    (hF : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F) (hinjF : Set.InjOn F (WhitneyPairModel.bigon h))
    (hiF : ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p))
    (havoidF : ∀ p ∈ WhitneyPairModel.bigon h, F p ∉ S ∪ T)
    (hcollarF :
      ∀ p ∈ interior (WhitneyPairModel.bigon h),
        F p ∉ d.map '' WhitneyPairModel.innerBigonCollar h r)
    {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hfrontW : frontier (WhitneyPairModel.bigon h) ⊆ W)
    (hEq : Set.EqOn F (d.map ∘ WhitneyPairModel.innerBigonMap h r) W) :
    ∃ f : C(ℝ × ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f ∧
        Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => f p) ∧
          (∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
            (∀ p ∈ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T) ∧
              ∃ V : Set (ℝ × ℝ),
                IsOpen V ∧ frontier (WhitneyPairModel.bigon h) ⊆ V ∧ Set.EqOn f d.map V := by
  let c := WhitneyPairModel.innerBigonDiffeomorph h r hr.1.ne'
  let core : Set (ℝ × ℝ) := c '' WhitneyPairModel.bigon h
  let P : Set (ℝ × ℝ) := c '' (interior (WhitneyPairModel.bigon h) ∪ W)
  let Q : Set (ℝ × ℝ) := d.domain \ c '' (WhitneyPairModel.bigon h \ W)
  let G : (ℝ × ℝ) → M := F ∘ c.symm
  have hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G := hF.comp c.symm.contMDiff
  have hP : IsOpen P := c.toHomeomorph.isOpenMap _ (isOpen_interior.union hW)
  have hQ : IsOpen Q :=
    d.open_domain.inter
      (((WhitneyPairModel.isCompact_bigon d.height_pos).inter_right hW.isClosed_compl).image
          c.continuous).isClosed.isOpen_compl
  have hfront (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h)
    (hi : p ∉ interior (WhitneyPairModel.bigon h)) : p ∈ frontier (WhitneyPairModel.bigon h) := by
    rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
    exact ⟨hp, hi⟩
  have hcoreP : core ⊆ P := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    by_cases hi : p ∈ interior (WhitneyPairModel.bigon h)
    · exact Or.inl hi
    · exact Or.inr (hfrontW (hfront p hp hi))
  have hcollarQ : WhitneyPairModel.innerBigonCollar h r ⊆ Q := by
    intro p hp
    refine ⟨hcollar hp, ?_⟩
    rintro ⟨z, hz, rfl⟩
    exact
      hz.2 (hfrontW ((WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr hz.1).mp hp))
  have hnotCore (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h) (hn : p ∉ core) :
    p ∈ WhitneyPairModel.innerBigonCollar h r :=
    ⟨hp, fun hi => hn (Set.image_mono interior_subset hi)⟩
  have hcover : WhitneyPairModel.bigon h ⊆ P ∪ Q := by
    intro p hp
    by_cases hc : p ∈ core
    · exact Or.inl (hcoreP hc)
    · exact Or.inr (hcollarQ (hnotCore p hp hc))
  have hfrontQ : frontier (WhitneyPairModel.bigon h) ⊆ Q := by
    intro p hp
    apply hcollarQ
    refine ⟨((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1, ?_⟩
    rintro ⟨z, hz, heq⟩
    have hi : p ∈ interior (WhitneyPairModel.bigon h) :=
      heq ▸ WhitneyPairModel.innerBigonMap_mem_interior d.height_pos hr (interior_subset hz)
    rw [frontier] at hp
    exact hp.2 hi
  have hmatch : Set.EqOn G d.map (P ∩ Q) := by
    rintro p ⟨hp, hq⟩
    obtain ⟨z, hz, rfl⟩ := hp
    have hzW : z ∈ W := by
      rcases hz with hz | hz
      · by_contra hn
        exact hq.2 ⟨z, ⟨interior_subset hz, hn⟩, rfl⟩
      · exact hz
    change F (c.symm (c z)) = d.map (c z)
    rw [c.symm_apply_apply]
    exact hEq hzW
  obtain ⟨j, hj, hjG, hjd⟩ :=
    exists_smooth_open_gluing hP hQ hG.contMDiffOn (d.smooth.mono Set.inter_subset_left) hmatch
  have hjInner (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h) : j (c p) = F p :=
    (hjG (hcoreP ⟨p, hp, rfl⟩)).trans (congrArg F (c.symm_apply_apply p))
  have hjCollar (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.innerBigonCollar h r) : j p = d.map p :=
    hjd (hcollarQ hp)
  have hcross (p : ℝ × ℝ) (hp : p ∈ WhitneyPairModel.bigon h) (z : ℝ × ℝ)
    (hz : z ∈ WhitneyPairModel.innerBigonCollar h r) (heq : F p = d.map z) : c p = z := by
    by_cases hi : p ∈ interior (WhitneyPairModel.bigon h)
    · exact False.elim (hcollarF p hi ⟨z, hz, heq.symm⟩)
    · have hpf := hfront p hp hi
      apply
        d.injective
          (hcollar ((WhitneyPairModel.innerBigonMap_mem_collar_iff d.height_pos hr hp).mpr hpf))
          (hcollar hz)
      exact (hEq (hfrontW hpf)).symm.trans heq
  have hinj : Set.InjOn j (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    by_cases hpCore : p ∈ core
    · obtain ⟨p', hp', rfl⟩ := hpCore
      rw [hjInner p' hp'] at heq
      by_cases hzCore : z ∈ core
      · obtain ⟨z', hz', rfl⟩ := hzCore
        rw [hjInner z' hz'] at heq
        exact congrArg c (hinjF hp' hz' heq)
      · have hzC := hnotCore z hz hzCore
        rw [hjCollar z hzC] at heq
        exact hcross p' hp' z hzC heq
    · have hpC := hnotCore p hp hpCore
      rw [hjCollar p hpC] at heq
      by_cases hzCore : z ∈ core
      · obtain ⟨z', hz', rfl⟩ := hzCore
        rw [hjInner z' hz'] at heq
        exact (hcross z' hz' p hpC heq.symm).symm
      · have hzC := hnotCore z hz hzCore
        rw [hjCollar z hzC] at heq
        exact d.injective (hcollar hpC) (hcollar hzC) heq
  have hi :
    ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) j p) := by
    intro p hp
    by_cases hpCore : p ∈ core
    · have heq : j =ᶠ[𝓝 p] G :=
        Filter.mem_of_superset (hP.mem_nhds (hcoreP hpCore)) (fun _ hx => hjG hx)
      rw [heq.mfderiv_eq]
      change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (F ∘ c.symm) p)
      rw [mfderiv_comp p (hF.mdifferentiableAt (by simp))
          (c.symm.contMDiff.mdifferentiableAt (by simp))]
      have hpin : c.symm p ∈ WhitneyPairModel.bigon h := by
        obtain ⟨z, hz, rfl⟩ := hpCore
        rwa [c.symm_apply_apply]
      exact
        (hiF _ hpin).comp
          (PartialChart.bijective_mfderiv c.symm.toPartialDiffeomorph (Set.mem_univ p)).injective
    · have hpC := hnotCore p hp hpCore
      have heq : j =ᶠ[𝓝 p] d.map :=
        Filter.mem_of_superset (hQ.mem_nhds (hcollarQ hpC)) (fun _ hx => hjd hx)
      rw [heq.mfderiv_eq]
      exact d.derivative_injective p (hcollar hpC)
  have havoid : ∀ p ∈ interior (WhitneyPairModel.bigon h), j p ∉ S ∪ T := by
    intro p hp
    by_cases hpCore : p ∈ core
    · obtain ⟨z, hz, rfl⟩ := hpCore
      rw [hjInner z hz]
      exact havoidF z hz
    · have hpC := hnotCore p (interior_subset hp) hpCore
      rw [hjCollar p hpC]
      exact d.interior_avoids p ⟨hcollar hpC, hp⟩
  obtain ⟨f, hf, V, hV, hKV, -, hfj⟩ :=
    exists_smooth_extension_near_starConvex (WhitneyPairModel.isCompact_bigon d.height_pos)
      (WhitneyPairModel.zero_mem_bigon d.height_pos.le)
      (WhitneyPairModel.starConvex_bigon d.height_pos.le) (hP.union hQ) hcover hj
  have hinjf : Set.InjOn f (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    apply hinj hp hz
    exact (hfj (hKV hp)).symm.trans (heq.trans (hfj (hKV hz)))
  have hembf : Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => f p) := by
    let : CompactSpace (WhitneyPairModel.bigon h) :=
      isCompact_iff_compactSpace.mp (WhitneyPairModel.isCompact_bigon d.height_pos)
    apply (hf.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro p z heq
    exact Subtype.ext (hinjf p.property z.property heq)
  refine ⟨⟨f, hf.continuous⟩, hf, hembf, ?_, ?_, V ∩ Q, hV.inter hQ, ?_, ?_⟩
  · intro p hp
    have heq : f =ᶠ[𝓝 p] j := Filter.mem_of_superset (hV.mem_nhds (hKV hp)) (fun _ hx => hfj hx)
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)
    rw [heq.mfderiv_eq]
    exact hi p hp
  · intro p hp
    change f p ∉ S ∪ T
    rw [hfj (hKV (interior_subset hp))]
    exact havoid p hp
  · intro p hp
    exact ⟨hKV ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1, hfrontQ hp⟩
  · intro p hp
    exact (hfj hp.1).trans (hjd hp.2)

theorem CleanBigonBoundary.exists_filled_bigon_of_complement_contractions {E M D Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y] [ChartedSpace D Y]
    [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M)) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (Set.range g) T a b k l h) (hT : IsClosed T)
    (hnull :
      ∀ f : C(Hemisphere.Sphere 1, (⟨Tᶜ, hT.isOpen_compl⟩ : TopologicalSpace.Opens M)),
        ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ f : C(ℝ × ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f ∧
        Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => f p) ∧
          (∀ p ∈ WhitneyPairModel.bigon h,
              Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
            (∀ p ∈ interior (WhitneyPairModel.bigon h), f p ∉ Set.range g ∪ T) ∧
              ∃ V : Set (ℝ × ℝ),
                IsOpen V ∧ frontier (WhitneyPairModel.bigon h) ⊆ V ∧ Set.EqOn f d.map V := by
  let U : TopologicalSpace.Opens M := ⟨Tᶜ, hT.isOpen_compl⟩
  have hU : (Set.range g ∪ T)ᶜ ⊆ U := fun _ hp ht => hp (Or.inr ht)
  obtain ⟨r, hr, hcollar, F, hF, hemb, hi, havoid, havoidCollar, W, hW, hfrontW, hEq⟩ :=
    d.exists_collar_disjoint_inner_extension_in_open g hg U hU hnull hdim hobstacle
  let F' : C(ℝ × ℝ, M) := ⟨Subtype.val ∘ F, continuous_subtype_val.comp F.continuous⟩
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : U → M) := contMDiff_subtype_val
  have hF' : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F' := hv.comp hF
  have hinjF' : Set.InjOn F' (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    have hFval : F p = F z := Subtype.ext heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) hFval)
  have hiF' :
    ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F' p) :=
    by
    intro p hp
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Subtype.val ∘ F) p)
    rw [mfderiv_comp p (hv.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))]
    exact (NativeOpenSubmanifold.injective_mfderiv_subtype_val U (F p)).comp (hi p hp)
  have havoidF' : ∀ p ∈ WhitneyPairModel.bigon h, F' p ∉ Set.range g ∪ T := by
    intro p hp hmem
    rcases hmem with hmem | hmem
    · exact havoid p hp hmem
    · exact (F p).property hmem
  exact
    exists_filled_clean_bigon_of_collar_disjoint_inner d hr hcollar F' hF' hinjF' hiF'
      havoidF' havoidCollar hW hfrontW hEq

theorem CleanBigonBoundary.nonempty_tubularBigon_of_complement_contractions
    {E M D Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace Y]
    [ChartedSpace D Y] [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y] (g : C(Y, M))
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g) {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (Set.range g) T a b k l h) (hT : IsClosed T)
    (hnull :
      ∀ f : C(Hemisphere.Sphere 1, (⟨Tᶜ, hT.isOpen_compl⟩ : TopologicalSpace.Opens M)),
        ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E)
    (n : ℕ) (hcodim : 2 + n = Module.finrank ℝ E) :
    Nonempty (TubularBigon (E := E) (Set.range g) T a b k l h n) := by
  obtain ⟨f, hf, hemb, hi, havoid, V, hV, hfrontV, hEq⟩ :=
    d.exists_filled_bigon_of_complement_contractions g hg hT hnull hdim hobstacle
  have hinj : Set.InjOn f (WhitneyPairModel.bigon h) := by
    intro p hp z hz heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) heq)
  obtain ⟨ε, hε, Φ, hsource, hzero, -⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      (WhitneyPairModel.isCompact_bigon d.height_pos)
      (WhitneyPairModel.zero_mem_bigon d.height_pos.le)
      (WhitneyPairModel.starConvex_bigon d.height_pos.le) hinj hi n
      (by simpa only [Module.finrank_prod, Module.finrank_self] using hcodim) isOpen_univ
      (Set.mapsTo_univ _ _)
  have hgerm : ∀ p ∈ frontier (WhitneyPairModel.bigon h), (f : (ℝ × ℝ) → M) =ᶠ[𝓝 p] d.map :=
    fun _ hp => Filter.mem_of_superset (hV.mem_nhds (hfrontV hp)) (fun _ hx => hEq hx)
  have hlow :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ frontier (WhitneyPairModel.bigon h) :=
    fun t ht =>
    (WhitneyPairModel.mem_frontier_bigon_iff_exists_time d.height_pos _).mpr
      ⟨t, ht, Or.inl rfl⟩
  have hupp :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (WhitneyPairModel.bigon h) :=
    fun t ht =>
    (WhitneyPairModel.mem_frontier_bigon_iff_exists_time d.height_pos _).mpr
      ⟨t, ht, Or.inr rfl⟩
  exact
    ⟨{  height_pos := d.height_pos
        map := f
        smooth := hf
        closed_embedding := hemb
        derivative_injective := hi
        interior_avoids := havoid
        lower := fun t ht => (hEq (hfrontV (hlow t ht))).trans (d.lower t ht)
        upper := fun t ht => (hEq (hfrontV (hupp t ht))).trans (d.upper t ht)
        lower_germ := fun t ht => (hgerm _ (hlow t ht)).trans (d.lower_germ t ht)
        upper_germ := fun t ht => (hgerm _ (hupp t ht)).trans (d.upper_germ t ht)
        radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := hzero }⟩

theorem ManifoldImmersion.exists_weighted_immersive_patch_with_property
    {B E G F H H' X N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ B H}
    {J : ModelWithCorners ℝ G H'} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [LindelofSpace (X × E)] [TopologicalSpace N] [ChartedSpace H' N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) {β χ : E → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) {S : Set X}
    (hplateau : ∀ x ∈ S, b x ∈ interior {y | χ y = 1})
    (hcommon : ∀ x ∈ S, ∀ v, mfderiv 𝓘(ℝ, E) J f (b x) v = 0 → fderiv ℝ β (b x) v = 0 → v = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ F) (Q : (E → N) → Prop)
    (hQ : ∀ᶠ a : F in 𝓝 0, Q (ChartMapPerturbation.perturb c f β a)) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        Q g ∧
          f.HomotopicRel g {y | β y = 0} ∧
            ∀ x ∈ S, Function.Injective (mfderiv 𝓘(ℝ, E) J g (b x)) := by
  let k := ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k := fun _ =>
      ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ :=
    ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff hcompact hsupport
  have hQmem : {a : F | Q (ChartMapPerturbation.perturb c f β a)} ∈ 𝓝 0 := hQ
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hQmem
  obtain ⟨a, ha, -, hkernel⟩ :=
    WeightedPerturbation.exists_small_parameter_with_common_kernel hb hk hβ hdim
      (lt_min hε hδ)
  have haε : ‖a‖ < ε := (lt_min_iff.mp ha).1
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).2
  have hv := hvalid a haε
  have hsmooth := ChartMapPerturbation.contMDiff_perturb c hf hβ.contMDiff hsupport hv
  let g : C(E, N) := ⟨ChartMapPerturbation.perturb c f β a, hsmooth.continuous⟩
  have hQg : Q g :=
    hδkeep (show a ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  refine
    ⟨g, hsmooth, hQg,
      ⟨ChartMapPerturbation.homotopyRel c hf hβ.contMDiff hsupport hvalid haε⟩, ?_⟩
  intro x hx
  have hxplateau := hplateau x hx
  have hsource (y : E) (hy : χ y = 1) : f y ∈ c.source :=
    hχsupport (subset_tsupport χ (by change χ y ≠ 0; rw [hy]; exact one_ne_zero))
  have hxone : χ (b x) = 1 := interior_subset (s := {y | χ y = 1}) hxplateau
  have hfx := hsource (b x) hxone
  have hgx : g (b x) ∈ c.source := ChartMapPerturbation.perturb_mem_source c f β hv hfx
  have heqold : k =ᶠ[𝓝 (b x)] (c ∘ f) := by
    filter_upwards [isOpen_interior.mem_nhds hxplateau] with y hy
    exact
      ChartMapPerturbation.cutoffCoordinates_eq_of_one c f χ
        (interior_subset (s := {y | χ y = 1}) hy)
  have heqnew : (c ∘ g) =ᶠ[𝓝 (b x)] WeightedPerturbation.perturb k β a := by
    filter_upwards [isOpen_interior.mem_nhds hxplateau] with y hy
    have hyone : χ y = 1 := interior_subset (s := {y | χ y = 1}) hy
    change c (ChartMapPerturbation.perturb c f β a y) = _
    rw [ChartMapPerturbation.chart_perturb c f β hv (hsource y hyone)]
    simp only [ChartMapPerturbation.coordinateFamily, WeightedPerturbation.perturb, k,
      ChartMapPerturbation.cutoffCoordinates, hyone, one_smul]
  apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgx).mp
  change Function.Injective (fderiv ℝ (c ∘ g) (b x))
  rw [heqnew.fderiv_eq]
  intro v w hvw
  have hzero : fderiv ℝ (WeightedPerturbation.perturb k β a) (b x) (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  obtain ⟨hkzero, hβzero⟩ := (hkernel x (v - w)).mp hzero
  have hnative : mfderiv 𝓘(ℝ, E) J f (b x) (v - w) = 0 := by
    apply (fderiv_chart_eq_zero_iff c (hf.mdifferentiableAt (by simp)) hfx (v - w)).mp
    rw [← heqold.fderiv_eq]
    exact hkzero
  exact sub_eq_zero.mp (hcommon x hx (v - w) hnative hβzero)

theorem ChartMapPerturbation.derivative_eq_zero_iff_of_weight_derivative_eq_zero
    {E G F H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N} {β : E → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hβ : ContDiff ℝ ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {a : F} (ha : Valid c f β a) {x v : E} (hweight : fderiv ℝ β x v = 0) :
    mfderiv 𝓘(ℝ, E) J (perturb c f β a) x v = 0 ↔ mfderiv 𝓘(ℝ, E) J f x v = 0 := by
  by_cases hx : f x ∈ c.source
  · have hsmooth := contMDiff_perturb c hf hβ.contMDiff hsupport ha
    have hgx := perturb_mem_source c f β ha hx
    have hcf : ContDiffAt ℝ ∞ (c ∘ f) x :=
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).comp x
          hf.contMDiffAt) |>.contDiffAt
    have hcd :
      HasFDerivAt (fun y => c (f y) + β y • a) (fderiv ℝ (c ∘ f) x + (fderiv ℝ β x).smulRight a)
        x :=
      (hcf.differentiableAt (by simp)).hasFDerivAt.add
        ((hβ.differentiable (by simp) x).hasFDerivAt.smul_const a)
    have heq : (c ∘ perturb c f β a) =ᶠ[𝓝 x] (fun y => c (f y) + β y • a) := by
      filter_upwards [(c.open_source.preimage hf.continuous).mem_nhds hx] with y hy
      exact chart_perturb c f β ha hy
    have hderiv :
      fderiv ℝ (c ∘ perturb c f β a) x = fderiv ℝ (c ∘ f) x + (fderiv ℝ β x).smulRight a :=
      heq.fderiv_eq.trans hcd.fderiv
    rw [←
      ManifoldImmersion.fderiv_chart_eq_zero_iff c (hsmooth.mdifferentiableAt (by simp)) hgx
        v,
      ← ManifoldImmersion.fderiv_chart_eq_zero_iff c (hf.mdifferentiableAt (by simp)) hx v,
      hderiv]
    change fderiv ℝ (c ∘ f) x v + fderiv ℝ β x v • a = 0 ↔ fderiv ℝ (c ∘ f) x v = 0
    rw [hweight, zero_smul, add_zero]
  · have hn : x ∉ tsupport β := fun ht => hx (hsupport ht)
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hn
    have heq : perturb c f β a =ᶠ[𝓝 x] f := by
      filter_upwards [hzero] with y hy
      exact perturb_eq_of_zero c f β a hy
    rw [heq.mfderiv_eq]
    rfl

theorem ChartMapPerturbation.fderiv_cutoff_mul_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ψ ρ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hρ : ContDiff ℝ ∞ ρ) {x v : E}
    (hx : ρ x = 0) (hv : fderiv ℝ ρ x v = 0) : fderiv ℝ (fun y => ψ y * ρ y) x v = 0 := by
  rw [fderiv_fun_mul (hψ.differentiable (by simp) x) (hρ.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul, hx, hv, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, add_zero]

theorem ChartMapPerturbation.common_kernel_preserved_on_zero_set {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N}
    {ψ ρ : E → ℝ} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hψ : ContDiff ℝ ∞ ψ) (hρ : ContDiff ℝ ∞ ρ)
    (hsupport : tsupport (fun y => ψ y * ρ y) ⊆ f ⁻¹' c.source) {a : F}
    (ha : Valid c f (fun y => ψ y * ρ y) a)
    (hcommon : ∀ x, ρ x = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f x v = 0 → fderiv ℝ ρ x v = 0 → v = 0) :
    ∀ x,
      ρ x = 0 →
        ∀ v,
          mfderiv 𝓘(ℝ, E) J (perturb c f (fun y => ψ y * ρ y) a) x v = 0 →
            fderiv ℝ ρ x v = 0 → v = 0 := by
  intro x hx v hzero hv
  have hweight := fderiv_cutoff_mul_eq_zero hψ hρ hx hv
  have hold :=
    (derivative_eq_zero_iff_of_weight_derivative_eq_zero c hf (hψ.mul hρ) hsupport ha hweight).mp
      hzero
  exact hcommon x hx v hold hv

theorem ManifoldImmersion.exists_boundary_derivative_repair_step {B E G H H' X N : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [LindelofSpace (X × E)]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N)) (i : ι)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G) {K L : Set E}
    (hK : IsCompact K) (hinj : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f y))
    (hLsub : L ⊆ (p i).plateau) (hLrange : L ⊆ Set.range b)
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          f.HomotopicRel g {y | ρ y = 0} ∧
            (∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) ∧
              ∀ y ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  let β : E → ℝ := fun y => (p i).cutoff y * ρ y
  have hβ : ContDiff ℝ ∞ β := (p i).smooth.contDiff.mul hρ
  have hcompact : HasCompactSupport β := (p i).compact.mul_right
  have hsupport : tsupport β ⊆ f ⁻¹' (p i).chart.source :=
    tsupport_mul_subset_left.trans ((p i).inner_compatible (hcompatible i))
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f β a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf hβ.contMDiff
        hsupport (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf hβ.contMDiff
      hcompact hsupport hK hinj
  let Common (g : E → N) : Prop :=
    ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 → fderiv ℝ ρ y v = 0 → v = 0
  have hretain :
    ∀ᶠ a in 𝓝 (0 : G), Common (ChartMapPerturbation.perturb (p i).chart f β a) := by
    filter_upwards [ChartMapPerturbation.eventually_valid (p i).chart hf hβ.contMDiff
        hcompact hsupport] with
      a ha
    exact
      ChartMapPerturbation.common_kernel_preserved_on_zero_set (p i).chart hf
        (p i).smooth.contDiff hρ hsupport ha hcommon
  let Q : (E → N) → Prop := fun g =>
    (∀ j, (p j).Compatible g) ∧ (∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g y)) ∧ Common g
  have hQ : ∀ᶠ a in 𝓝 (0 : G), Q (ChartMapPerturbation.perturb (p i).chart f β a) :=
    hkeep.and (hold.and hretain)
  have houter : (p i).plateau ⊆ interior {y | (p i).outer y = 1} := by
    apply isOpen_interior.subset_interior_iff.mpr
    intro y hy
    apply (p i).nested y
    apply subset_tsupport (p i).cutoff
    change (p i).cutoff y ≠ 0
    rw [interior_subset (s := {y | (p i).cutoff y = 1}) hy]
    exact one_ne_zero
  have hplateau : ∀ x ∈ b ⁻¹' L, b x ∈ interior {y | (p i).outer y = 1} := fun _ hx =>
    houter (hLsub hx)
  have hcommonβ :
    ∀ x ∈ b ⁻¹' L, ∀ v, mfderiv 𝓘(ℝ, E) J f (b x) v = 0 → fderiv ℝ β (b x) v = 0 → v = 0 := by
    intro x hx v hfv hβv
    have heq : β =ᶠ[𝓝 (b x)] ρ := by
      filter_upwards [(p i).plateau_eventually_one (hLsub hx)] with y hy
      simp only [β, hy, one_mul]
    apply hcommon (b x) (hzero x) v hfv
    rw [← heq.fderiv_eq]
    exact hβv
  obtain ⟨g, hg, ⟨hc, hinjg, hcommong⟩, ⟨Hrel⟩, hnew⟩ :=
    exists_weighted_immersive_patch_with_property (p i).chart f hf hb hβ
      (p i).outer_smooth.contDiff hcompact hsupport (hcompatible i) hplateau hcommonβ hdim Q hQ
  refine ⟨g, hg, hc, ?_, hcommong, ?_⟩
  · refine ⟨{ Hrel.toHomotopy with prop' := ?_ }⟩
    intro t y hy
    apply Hrel.eq_fst t
    change (p i).cutoff y * ρ y = 0
    rw [hy, MulZeroClass.mul_zero]
  · intro y hy
    rcases hy with hy | hy
    · exact hinjg y hy
    · obtain ⟨x, rfl⟩ := hLrange hy
      exact hnew x hy

theorem ManifoldImmersion.exists_finite_boundary_derivative_repair {B E G H H' X N : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [LindelofSpace (X × E)]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N))
    (L : ι → Set E) (hL : ∀ i, IsCompact (L i)) (hLsub : ∀ i, L i ⊆ (p i).plateau) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ i, (p i).Compatible f) {b : X → E}
    (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hLrange : ∀ i, L i ⊆ Set.range b) {ρ : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G) {K : Set E}
    (hK : IsCompact K) (hinj : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f y))
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ ρ y v = 0 → v = 0)
    (s : Finset ι) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ i, (p i).Compatible g) ∧
          f.HomotopicRel g {y | ρ y = 0} ∧
            (∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) ∧
              ∀ y ∈ K ∪ ⋃ i ∈ s, L i, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, ContinuousMap.HomotopicRel.refl f, hcommon, ?_⟩
    simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] using
      hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hcommon₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) := hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hcommon₂, hinj₂⟩ :=
      exists_boundary_derivative_repair_step p i g₁ hg₁ hc₁ hb hρ hzero hdim hKold hinj₁ (hLsub i)
        (hLrange i) hcommon₁
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, hcommon₂, ?_⟩
    intro y hy
    apply hinj₂ y
    rcases hy with hy | hy
    · exact Or.inl (Or.inl hy)
    · obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hyj
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjs, hyj⟩))

theorem ManifoldImmersion.exists_compact_boundary_derivative_repair {B E G H H' X N : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X]
    [LindelofSpace (X × E)] [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b)
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G)
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        f.HomotopicRel g {y | ρ y = 0} ∧
          ∀ y ∈ Set.range b, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  classical
  have hboundary : IsCompact (Set.range b) := isCompact_range hb.continuous
  have hp (x : Set.range b) :
    ∃ p : ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ D : Set E, p.Compatible f ∧ IsCompact D ∧ D ∈ 𝓝 x.1 ∧ D ⊆ p.plateau := by
    obtain ⟨p, hcompatible, hplateau⟩ :=
      ManifoldSmoothing.exists_smoothing_patch_at (I := 𝓘(ℝ, E)) (J := J) f x.1
    obtain ⟨D, hDx, hDsub, hD⟩ := local_compact_nhds (isOpen_interior.mem_nhds hplateau)
    exact ⟨p, D, hcompatible, hD, hDx, hDsub⟩
  choose p D hcompatible hD hn hsub using hp
  have hcover : Set.range b ⊆ ⋃ x : Set.range b, interior (D x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ :=
    hboundary.elim_finite_subcover (fun x : Set.range b => interior (D x))
      (fun _ => isOpen_interior) hcover
  let L (i : s) := Set.range b ∩ D i.1
  have hL (i : s) : IsCompact (L i) := hboundary.inter_right (hD i.1).isClosed
  have hLsub (i : s) : L i ⊆ (p i.1).plateau := fun _ hx => hsub i.1 hx.2
  have hLrange (i : s) : L i ⊆ Set.range b := Set.inter_subset_left
  obtain ⟨g, hg, -, hhom, -, hinj⟩ :=
    exists_finite_boundary_derivative_repair (fun i : s => p i.1) L hL hLsub f hf
      (fun i => hcompatible i.1) hb hLrange hρ hzero hdim isCompact_empty
      (fun _ hx => False.elim hx) hcommon Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro y hy
  obtain ⟨i, hi, hyD⟩ := Set.mem_iUnion₂.mp (hs hy)
  apply hinj y
  exact Or.inr (Set.mem_iUnion₂.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hy, interior_subset hyD⟩)

def CurveImmersion.endpointFunction (t : ℝ) : ℝ :=
  t * (1 - t)

theorem CurveImmersion.contDiff_endpointFunction : ContDiff ℝ ∞ endpointFunction := by
  unfold endpointFunction
  fun_prop

theorem CurveImmersion.endpointFunction_eq_zero_iff (t : ℝ) :
    endpointFunction t = 0 ↔ t = 0 ∨ t = 1 := by
  rw [endpointFunction, mul_eq_zero, sub_eq_zero]
  exact or_congr Iff.rfl eq_comm

theorem CurveImmersion.fderiv_endpointFunction (t v : ℝ) :
    fderiv ℝ endpointFunction t v = v * (1 - 2 * t) := by
  have hd : HasDerivAt endpointFunction (1 * (1 - t) + t * (0 - 1)) t :=
    (hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  have heq : 1 * (1 - t) + t * (0 - 1) = 1 - 2 * t := by ring
  rw [heq] at hd
  rw [hd.hasFDerivAt.fderiv]
  rfl

theorem CurveImmersion.injective_endpointFunction_derivative {t : ℝ}
    (ht : endpointFunction t = 0) {v : ℝ} (hv : fderiv ℝ endpointFunction t v = 0) : v = 0 := by
  rw [fderiv_endpointFunction] at hv
  rcases (endpointFunction_eq_zero_iff t).mp ht with rfl | rfl
  · simpa using hv
  · norm_num at hv
    exact hv

theorem ManifoldImmersion.exists_curve_endpoint_derivative_repair {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 2 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        f.HomotopicRel g ({0, 1} : Set ℝ) ∧
          ∀ t ∈ ({0, 1} : Set ℝ), Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let X := ({0, 1} : Set ℝ)
  let : Fintype X := ((Set.finite_singleton (1 : ℝ)).insert 0).fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z X := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ X := IsManifold.of_discreteTopology _
  let b : X → ℝ := Subtype.val
  have hb : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ b := contMDiff_of_discreteTopology
  have hrange : Set.range b = ({0, 1} : Set ℝ) := by ext t; simp [b, X]
  have hzero : ∀ x, CurveImmersion.endpointFunction (b x) = 0 := by
    intro x
    apply (CurveImmersion.endpointFunction_eq_zero_iff _).mpr
    exact x.property
  have hzset : {t | CurveImmersion.endpointFunction t = 0} = ({0, 1} : Set ℝ) := by
    ext t
    simp only [Set.mem_ofPred_eq, CurveImmersion.endpointFunction_eq_zero_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  have hd : Module.finrank ℝ Z + Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin, Module.finrank_self]
    omega
  obtain ⟨g, hg, hrel, hi⟩ :=
    exists_compact_boundary_derivative_repair f hf hb
      CurveImmersion.contDiff_endpointFunction hzero hd
      (fun _ ht _ _ hv => CurveImmersion.injective_endpointFunction_derivative ht hv)
  refine ⟨g, hg, ?_, ?_⟩
  · simpa only [hzset] using hrel
  · simpa only [hrange] using hi

theorem exists_short_embedded_arc {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] {U : Set N}
    (hU : IsOpen U) {x : N} (hx : x ∈ U) (hdim : 2 ≤ Module.finrank ℝ G) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        f 0 = x ∧
          f 1 ≠ x ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ∈ U := by
  let c : C(ℝ, N) := ContinuousMap.const ℝ x
  obtain ⟨g, hg, hrel, hi⟩ :=
    ManifoldImmersion.exists_curve_endpoint_derivative_repair (J := J) c contMDiff_const hdim
  have hg0 : g 0 = x := (hrel.fst_eq_snd (by simp)).symm
  have hi0 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g 0) := hi 0 (by simp)
  obtain ⟨V, hV, h0V, hinj⟩ :=
    ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative hg hi0
  let W := V ∩ ({t : ℝ | Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t)} ∩ g ⁻¹' U)
  have hW : IsOpen W :=
    hV.inter ((ManifoldImmersion.isOpen_injective_derivative hg).inter (hU.preimage g.continuous))
  have h0W : (0 : ℝ) ∈ W := ⟨h0V, hi0, (show g 0 ∈ U from hg0.symm ▸ hx)⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0W)
  let L : ℝ →L[ℝ] ℝ := (r / 2) • ContinuousLinearMap.id ℝ ℝ
  have hLs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ L := L.contDiff.contMDiff
  have hL (t : ℝ) : L t = (r / 2) * t := rfl
  have hscale : 0 < r / 2 := by positivity
  have hLinj : Function.Injective L := by
    intro s t hst
    exact mul_left_cancel₀ hscale.ne' hst
  have hLW : ∀ t ∈ Set.Icc (0 : ℝ) 1, L t ∈ W := by
    intro t ht
    apply hball
    change Dist.dist (L t) 0 < r
    rw [dist_zero_right, Real.norm_eq_abs, hL, abs_of_nonneg (mul_nonneg hscale.le ht.1)]
    have hbound := mul_le_mul_of_nonneg_left ht.2 hscale.le
    linarith
  let f : C(ℝ, N) := ⟨g ∘ L, g.continuous.comp L.continuous⟩
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f := hg.comp hLs
  have hfinj : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact hLinj (hinj (hLW s hs).1 (hLW t ht).1 hst)
  have hf0 : f 0 = x := by
    change g (L 0) = x
    rw [map_zero, hg0]
  have hemb : Topology.IsClosedEmbedding (fun t : unitInterval => f t) := by
    apply (f.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro s t hst
    exact Subtype.ext (hfinj s.property t.property hst)
  refine ⟨f, hf, hf0, ?_, hemb, ?_, ?_⟩
  · intro hfx
    have h10 : (1 : ℝ) = 0 := hfinj (by simp) (by simp) (hfx.trans hf0.symm)
    exact one_ne_zero h10
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (g ∘ L) t)
    rw [mfderiv_comp t (hg.mdifferentiableAt (by simp)) (hLs.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv, L.fderiv]
    exact (hLW t ht).2.1.comp hLinj
  · intro t ht
    exact (hLW t ht).2.2

theorem exists_embedded_connecting_arc_avoiding_finite_dim_two {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {x y : N} (γ : Path x y) (hxy : x ≠ y)
    (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        f 0 = x ∧
          f 1 = y ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S := by
  have hSx : (S \ { x }).Finite := hS.subset Set.sdiff_subset
  obtain ⟨g, hg, hg0, hg1, hemb, hi, havoid⟩ :=
    exists_short_embedded_arc (J := J) hSx.isClosed.isOpen_compl
      (show x ∈ (S \ { x })ᶜ from by simp) hdim
  have hginj : Set.InjOn g (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) hst)
  have hg1S : g 1 ∉ S := by
    intro hs
    exact havoid 1 (by simp) ⟨hs, hg1⟩
  let C : Set N := (Insert.insert x S) \ { y }
  have hC : C.Finite := (hS.insert x).subset Set.sdiff_subset
  have hxC : x ∈ C := ⟨Set.mem_insert x S, hxy⟩
  have hg1C : g 1 ∉ C := by
    rintro ⟨hr, _⟩
    rcases hr with hr | hr
    · exact hg1 hr
    · exact hg1S hr
  have hyC : y ∉ C := fun hy => hy.2 rfl
  let α : Path x (g 1) :=
    { toFun := fun t => g t
      continuous_toFun := g.continuous.comp continuous_subtype_val
      source' := hg0
      target' := rfl }
  obtain ⟨d, hd, hfix⟩ :=
    exists_pointMoving_fixing_finite (J := J) (α.symm.trans γ) hdim hC hg1C hyC
  let f : C(ℝ, N) := ⟨d ∘ g, d.continuous.comp g.continuous⟩
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f := d.contMDiff.comp hg
  refine ⟨f, hf, ?_, hd, ?_, ?_, ?_⟩
  · change d (g 0) = x
    rw [hg0]
    exact hfix x hxC
  · apply (f.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro s t hst
    exact hemb.injective (d.injective hst)
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (d ∘ g) t)
    rw [mfderiv_comp t (d.contMDiff.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))]
    exact
      (PartialChart.bijective_mfderiv d.toPartialDiffeomorph (Set.mem_univ (g t))).1.comp
        (hi t ht)
  · intro t ht hftS
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    by_cases hfty : f t = y
    · have hgt : g t = g 1 := d.injective (hfty.trans hd.symm)
      exact ht.2.ne (hginj htI (by simp) hgt)
    · have hftC : f t ∈ C := ⟨Or.inr hftS, hfty⟩
      have hgt : g t = f t := d.injective (hfix (f t) hftC).symm
      have hgtS : g t ∈ S := hgt.symm ▸ hftS
      have hgtx : g t ≠ x := by
        intro he
        exact ht.1.ne' (hginj htI (by simp) (he.trans hg0.symm))
      exact havoid t htI ⟨hgtS, hgtx⟩

theorem exists_tubular_connecting_arc_avoiding_finite_with_global_zero {G N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] [CompactSpace N] {x y : N}
    (γ : Path x y) (hxy : x ≠ y) (hdim : 2 ≤ Module.finrank ℝ G) (n : ℕ)
    (hcodim : 1 + n = Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, G) ∞ f ∧
        f 0 = x ∧
          f 1 = y ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, G) f t)) ∧
                (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S) ∧
                  ∃ ε : ℝ,
                    0 < ε ∧
                      ∃ Φ :
                        PartialDiffeomorph 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, G)
                          (ℝ × EuclideanSpace ℝ (Fin n)) N ∞,
                        Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
                          (∀ t, Φ (t, 0) = f t) ∧ Φ.target ⊆ (S \ { x, y })ᶜ := by
  obtain ⟨f, hf, hf0, hf1, hemb, hi, havoid⟩ :=
    exists_embedded_connecting_arc_avoiding_finite_dim_two (J := 𝓘(ℝ, G)) γ hxy hdim hS
  have hinj : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro t ht s hs hts
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) hts)
  have hO : IsOpen (S \ { x, y })ᶜ := (hS.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hfO : Set.MapsTo f (Set.Icc (0 : ℝ) 1) (S \ { x, y })ᶜ := by
    intro t ht
    change f t ∉ S \ { x, y }
    by_cases ht0 : t = 0
    · rw [ht0, hf0]
      exact fun hx => hx.2 (by simp)
    by_cases ht1 : t = 1
    · rw [ht1, hf1]
      exact fun hy => hy.2 (by simp)
    have hti : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact fun hs => havoid t hti hs.1
  have hstar : StarConvex ℝ (0 : ℝ) (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      CompactIccSpace.isCompact_Icc (by simp) hstar hinj hi n
      (by simpa only [Module.finrank_self] using hcodim) hO hfO
  exact ⟨f, hf, hf0, hf1, hemb, hi, havoid, ε, hε, Φ, hsource, hzero, htarget⟩

theorem exists_clean_corner_of_tubular_arcs {E M D Z N P A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [TopologicalSpace N] [ChartedSpace D N] [TopologicalSpace P] [ChartedSpace Z P] {F : N → M}
    {G : P → M} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ × A) 𝓘(ℝ, D) (ℝ × A) N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞) {f : ℝ → N} {g : ℝ → P}
    (hc : ∀ t, c (t, 0) = f t) (hd : ∀ t, d (t, 0) = g t) {t₀ : ℝ}
    (htc : (t₀, (0 : A)) ∈ c.source) (htd : (t₀, (0 : B)) ∈ d.source) (hxy : G (g t₀) = F (f t₀))
    (hdim : Module.finrank ℝ (ℝ × A) + Module.finrank ℝ (ℝ × B) = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f t₀)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g t₀))))
    {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) {O : Set M} (hO : IsOpen O) (hxO : F (f t₀) ∈ O) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        (0 : ℝ × ℝ) ∈ W ∧
          ∃ k : (ℝ × ℝ) → M,
            ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
              Set.InjOn k W ∧
                Set.MapsTo k W O ∧
                  k 0 = F (f t₀) ∧
                    (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                      (∀ p ∈ W, (k p ∈ Set.range F ↔ p.2 = 0) ∧ (k p ∈ Set.range G ↔ p.1 = 0)) ∧
                        (∀ s, (s, 0) ∈ W → k (s, 0) = F (f (t₀ + s * σ))) ∧
                          (∀ t, (0, t) ∈ W → k (0, t) = G (g (t₀ + t * τ))) := by
  let c' := (NativeParametrization.translation (t₀, (0 : A))).toPartialDiffeomorph.trans c
  let d' := (NativeParametrization.translation (t₀, (0 : B))).toPartialDiffeomorph.trans d
  have hc0 : (0 : ℝ × A) ∈ c'.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change 0 + (t₀, (0 : A)) ∈ c.source
    rw [zero_add]
    exact htc
  have hd0 : (0 : ℝ × B) ∈ d'.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change 0 + (t₀, (0 : B)) ∈ d.source
    rw [zero_add]
    exact htd
  have hcx : c' 0 = f t₀ := by
    change c (0 + (t₀, (0 : A))) = f t₀
    rw [zero_add, hc]
  have hdy : d' 0 = g t₀ := by
    change d (0 + (t₀, (0 : B))) = g t₀
    rw [zero_add, hd]
  have hxy' : G (d' 0) = F (c' 0) := by rw [hcx, hdy]; exact hxy
  have ht' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c' 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d' 0))) := by
    rw [hcx, hdy]
    exact ht
  have hxO' : F (c' 0) ∈ O := by rw [hcx]; exact hxO
  have hu : (σ, (0 : A)) ≠ 0 := fun he => hσ (congrArg Prod.fst he)
  have hv : (τ, (0 : B)) ≠ 0 := fun he => hτ (congrArg Prod.fst he)
  obtain ⟨W, hW, h0W, k, hk, hinj, hWO, hcenter, hi, hclean, hlo, hhi⟩ :=
    exists_native_clean_corner_of_parametrizations hF hG hembF hembG c' d' hc0 hd0 hxy' hdim ht'
      hu hv hO hxO'
  refine ⟨W, hW, h0W, k, hk, hinj, hWO, hcenter.trans (congrArg F hcx), hi, hclean, ?_, ?_⟩
  · intro s hs
    rw [hlo s hs]
    apply congrArg F
    change c (s • (σ, (0 : A)) + (t₀, 0)) = f (t₀ + s * σ)
    have he : s • (σ, (0 : A)) + (t₀, 0) = (t₀ + s * σ, 0) := by simp [smul_eq_mul, add_comm]
    rw [he, hc]
  · intro t ht
    rw [hhi t ht]
    apply congrArg G
    change d (t • (τ, (0 : B)) + (t₀, 0)) = g (t₀ + t * τ)
    have he : t • (τ, (0 : B)) + (t₀, 0) = (t₀ + t * τ, 0) := by simp [smul_eq_mul, add_comm]
    rw [he, hd]

theorem nonempty_cleanCornerPatch_of_tubular_arcs {E M D Z N P A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace N] [ChartedSpace D N]
    [TopologicalSpace P] [ChartedSpace Z P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ × A) 𝓘(ℝ, D) (ℝ × A) N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞) {f : ℝ → N} {g : ℝ → P}
    (hc : ∀ t, c (t, 0) = f t) (hd : ∀ t, d (t, 0) = g t) {t₀ : ℝ}
    (htc : (t₀, (0 : A)) ∈ c.source) (htd : (t₀, (0 : B)) ∈ d.source) (hxy : G (g t₀) = F (f t₀))
    (hdim : Module.finrank ℝ (ℝ × A) + Module.finrank ℝ (ℝ × B) = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f t₀)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g t₀))))
    {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) :
    Nonempty
      (CleanCornerPatch (E := E) (Set.range F) (Set.range G) (fun s => F (f (t₀ + s * σ)))
        (fun t => G (g (t₀ + t * τ)))) := by
  obtain ⟨W, hW, h0W, k, hk, hinj, _, _, hi, hsheets, hlo, hhi⟩ :=
    exists_clean_corner_of_tubular_arcs hF hG hembF hembG c d hc hd htc htd hxy hdim ht hσ hτ
      isOpen_univ (Set.mem_univ _)
  exact
    ⟨{ domain := W, open_domain := hW, contains_zero := h0W, map := k, smooth := hk,
        injective := hinj, derivative_injective := hi, sheets := hsheets, axis_first := hlo,
        axis_second := hhi }⟩

theorem exists_clean_ambient_chart_along_embedded_arc {E M G N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] [CompactSpace N] {F : N → M}
    {f : ℝ → N} (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) (hembF : Topology.IsEmbedding F)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, G) ∞ f) (hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, G) f t)) (n m : ℕ)
    (hsheet : 1 + n = Module.finrank ℝ G) (hcodim : Module.finrank ℝ G + m = Module.finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : Set.MapsTo (F ∘ f) (Set.Icc (0 : ℝ) 1) O) :
    ∃ Φ :
      PartialDiffeomorph
        𝓘(ℝ, StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) 𝓘(ℝ, E)
        (StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) M ∞,
      Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) Φ.source ∧
        Φ.target ⊆ O ∧
          (∀ t, StripCoordinates.center t ∈ Φ.source → Φ (StripCoordinates.center t) = F (f t)) ∧
            (∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) := by
  have hstar : StarConvex ℝ (0 : ℝ) (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  obtain ⟨a, ha, c, hprod, hzero, _⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      CompactIccSpace.isCompact_Icc (by simp) hstar hinjf hif n
      (by simpa only [Module.finrank_self] using hsheet) isOpen_univ (fun _ _ => Set.mem_univ _)
  let K := Set.Icc (0 : ℝ) 1 ×ˢ {(0 : EuclideanSpace ℝ (Fin n))}
  have hK : IsCompact K := CompactIccSpace.isCompact_Icc.prod isCompact_singleton
  have h0K : (0 : ℝ × EuclideanSpace ℝ (Fin n)) ∈ K := by simp [K]
  have hstarK : StarConvex ℝ (0 : ℝ × EuclideanSpace ℝ (Fin n)) K :=
    hstar.prod (starConvex_singleton _)
  have hKc : K ⊆ c.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hprod ⟨ht, Metric.mem_closedBall_self ha.le⟩
  have hFO : Set.MapsTo (F ∘ c) K O := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change F (c (t, 0)) ∈ O
    rw [hzero]
    exact hfO ht
  have hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin n)) + m = Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin,
      hsheet] using hcodim
  obtain ⟨b, hb, Φ, hΦprod, _, htarget, hΦzero, hclean⟩ :=
    exists_clean_embedded_sheet_neighborhood hF hembF c hK h0K hstarK hKc (fun x _ => hiF (c x)) m
      hdim hO hFO
  refine ⟨Φ, ?_, htarget, ?_, hclean⟩
  · intro t ht
    exact hΦprod ⟨⟨ht, rfl⟩, Metric.mem_closedBall_self hb.le⟩
  · intro t ht
    exact (hΦzero (t, 0) ht).trans (congrArg F (hzero t))

theorem TransverseCoordinates.bijective_normalDerivative_transverse_sheet
    {D B E M A Z N P : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace A N] [TopologicalSpace P] [ChartedSpace Z P]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) {x : N} {y : P} (hx : F x ∈ Φ.target)
    (hxy : G y = F x)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) :
    Function.Bijective (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, B) (normalCoordinate Φ ∘ G) y) := by
  let Q : E →L[ℝ] B := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (F x)
  let DF : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x
  let DG : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y
  have hQ : Function.Surjective Q := surjective_mfderiv_normalCoordinate Φ hx
  have hQA : Q.comp DF = 0 := normalDerivative_comp_sheet_eq_zero Φ hF hclean hx
  have hb : Function.Bijective (Q.comp DG) := bijective_normal_comp Q DF DG hQ ht hQA hdim
  have hy : G y ∈ Φ.target := hxy.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have hderiv : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, B) (normalCoordinate Φ ∘ G) y = Q.comp DG := by
    rw [mfderiv_comp y (hnormal.mdifferentiableAt (by simp)) (hG.mdifferentiableAt (by simp)),
      hxy]
    rfl
  rw [hderiv]
  exact hb

theorem TransverseCoordinates.bijective_normalDerivative_transverse_parametrization
    {D B E M A Z N P : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace A N] [TopologicalSpace P] [ChartedSpace Z P]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {Z' : Type*} [NormedAddCommGroup Z']
    [NormedSpace ℝ Z'] {F : N → M} {G : P → M} (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G) (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0)
    (c : PartialDiffeomorph 𝓘(ℝ, Z') 𝓘(ℝ, Z) Z' P ∞) {z : Z'} (hz : z ∈ c.source) {x : N}
    (hx : F x ∈ Φ.target) (hxy : G (c z) = F x)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c z))))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) :
    Function.Bijective (fderiv ℝ ((normalCoordinate Φ ∘ G) ∘ c) z) := by
  have hb := bijective_normalDerivative_transverse_sheet Φ hF hG hclean hx hxy ht hdim
  have hy : G (c z) ∈ Φ.target := hxy.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have hg : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, B) ∞ (normalCoordinate Φ ∘ G) (c z) :=
    hnormal.comp (c z) hG.contMDiffAt
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp z (hg.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) hz)]
  exact hb.comp (PartialChart.bijective_mfderiv c hz)

def NativeParametrization.line {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (u : D) : ℝ →L[ℝ] D :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight u

theorem NativeParametrization.line_apply {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (u : D) (t : ℝ) : line u t = t • u :=
  rfl

theorem TransverseCoordinates.vertical_derivative_of_axis_germ {Z B : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {H : (ℝ × ℝ) → B} {a : Z → B} (v : Z) (hH : DifferentiableAt ℝ H 0)
    (ha : DifferentiableAt ℝ a 0) (heq : (fun t : ℝ => H (0, t)) =ᶠ[𝓝 0] (fun t => a (t • v))) :
    fderiv ℝ H (0, 0) (0, 1) = fderiv ℝ a 0 v := by
  let S : ℝ →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.inr ℝ ℝ ℝ
  let L : ℝ →L[ℝ] Z := NativeParametrization.line v
  have hHS : fderiv ℝ (H ∘ S) 0 = (fderiv ℝ H 0).comp S := by
    rw [fderiv_comp 0 (by simpa only [map_zero] using hH) S.differentiableAt, map_zero, S.fderiv]
  have haL : fderiv ℝ (a ∘ L) 0 = (fderiv ℝ a 0).comp L := by
    rw [fderiv_comp 0 (by simpa only [map_zero] using ha) L.differentiableAt, map_zero, L.fderiv]
  have heq' : (H ∘ S) =ᶠ[𝓝 (0 : ℝ)] (a ∘ L) := heq
  have hd : fderiv ℝ (H ∘ S) 0 = fderiv ℝ (a ∘ L) 0 := heq'.fderiv_eq
  rw [hHS, haL] at hd
  have hval := congrArg (fun T : ℝ →L[ℝ] B => T 1) hd
  change fderiv ℝ H (0 : ℝ × ℝ) (0, 1) = fderiv ℝ a 0 v
  simpa only [ContinuousLinearMap.comp_apply, S, L, NativeParametrization.line_apply,
    one_smul, ContinuousLinearMap.inr_apply] using hval

theorem TransverseCoordinates.eventually_vertical_derivative_ne_zero {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {H : (ℝ × ℝ) → B} {p : ℝ × ℝ}
    (hH : ContDiffAt ℝ ∞ H p) (hn : fderiv ℝ H p (0, 1) ≠ 0) :
    ∀ᶠ q in 𝓝 p, fderiv ℝ H q (0, 1) ≠ 0 := by
  have hd : ContinuousAt (fderiv ℝ H) p := hH.continuousAt_fderiv (by simp)
  have hv : ContinuousAt (fun q => fderiv ℝ H q (0, 1)) p := hd.clm_apply continuousAt_const
  exact hv.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hn)

theorem TransverseCoordinates.corner_normalDerivative_ne_zero {D B E M A Z Z' N P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup Z'] [NormedSpace ℝ Z']
    [TopologicalSpace N] [ChartedSpace A N] [TopologicalSpace P] [ChartedSpace Z P]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0)
    (c : PartialDiffeomorph 𝓘(ℝ, Z') 𝓘(ℝ, Z) Z' P ∞) (hc : (0 : Z') ∈ c.source) {x : N}
    (hx : F x ∈ Φ.target) (hxy : G (c 0) = F x)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c 0))))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) {k : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W) (hW : IsOpen W) (h0W : (0 : ℝ × ℝ) ∈ W) {v : Z'}
    (hv : v ≠ 0) (haxis : ∀ t, (0, t) ∈ W → k (0, t) = G (c (t • v))) :
    fderiv ℝ (normalCoordinate Φ ∘ k) (0, 0) (0, 1) ≠ 0 ∧
      ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), fderiv ℝ (normalCoordinate Φ ∘ k) q (0, 1) ≠ 0 := by
  let H := normalCoordinate Φ ∘ k
  let a := (normalCoordinate Φ ∘ G) ∘ c
  have hk0 : k (0 : ℝ × ℝ) = F x := by
    have h := haxis 0 h0W
    rw [zero_smul] at h
    exact h.trans hxy
  have hkΦ : k (0 : ℝ × ℝ) ∈ Φ.target := hk0.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hkΦ)
  have hH : ContDiffAt ℝ ∞ H 0 := (hnormal.comp 0 (hk.contMDiffAt (hW.mem_nhds h0W))).contDiffAt
  have hy : G (c 0) ∈ Φ.target := hxy.symm ▸ hx
  have hnormalG := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have ha : ContDiffAt ℝ ∞ a 0 :=
    ((hnormalG.comp (c 0) hG.contMDiffAt).comp 0
        (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc))).contDiffAt
  have haxisW : ∀ᶠ t : ℝ in 𝓝 0, (0, t) ∈ W :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hW.mem_nhds h0W)
  have heq : (fun t : ℝ => H (0, t)) =ᶠ[𝓝 0] (fun t => a (t • v)) := by
    filter_upwards [haxisW] with t htW
    exact congrArg (normalCoordinate Φ) (haxis t htW)
  have hderiv :=
    vertical_derivative_of_axis_germ v (hH.differentiableAt (by simp))
      (ha.differentiableAt (by simp)) heq
  have hbij : Function.Bijective (fderiv ℝ a 0) :=
    bijective_normalDerivative_transverse_parametrization Φ hF hG hclean c hc hx hxy ht hdim
  have hn : fderiv ℝ H (0, 0) (0, 1) ≠ 0 := by
    rw [hderiv]
    intro hz
    exact hv (hbij.1 (hz.trans (map_zero (fderiv ℝ a 0)).symm))
  exact ⟨hn, eventually_vertical_derivative_ne_zero hH hn⟩

theorem StripCoordinates.exists_smooth_strip_matching_germs {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hc₀ : (fun t : ℝ => F₀ (t, 0)) =ᶠ[𝓝 0] StripCoordinates.center)
    (hc₁ : (fun t : ℝ => F₁ (t, 0)) =ᶠ[𝓝 1] StripCoordinates.center)
    (hn₀ : normalDerivative F₀ =ᶠ[𝓝 (0 : ℝ)] v) (hn₁ : normalDerivative F₁ =ᶠ[𝓝 (1 : ℝ)] v) :
    ∃ F : (ℝ × ℝ) → Space A B,
      ContDiff ℝ ∞ F ∧
        (∀ t, F (t, 0) = StripCoordinates.center t) ∧
          (∀ t, normalDerivative F t = v t) ∧ (F =ᶠ[𝓝 (0, 0)] F₀) ∧ (F =ᶠ[𝓝 (1, 0)] F₁) := by
  have hgood₀ :
    {t : ℝ |
        F₀ (t, 0) = StripCoordinates.center t ∧ normalDerivative F₀ t = v t ∧ t < 1 / 3} ∈
      𝓝 (0 : ℝ) := by
    filter_upwards [hc₀, hn₀, Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t hc hn ht
    exact ⟨hc, hn, ht⟩
  have hgood₁ :
    {t : ℝ |
        F₁ (t, 0) = StripCoordinates.center t ∧ normalDerivative F₁ t = v t ∧ 2 / 3 < t} ∈
      𝓝 (1 : ℝ) := by
    filter_upwards [hc₁, hn₁, Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t hc hn ht
    exact ⟨hc, hn, ht⟩
  obtain ⟨β₀, _, hβ₀⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℝ)) (0 : ℝ)).mem_iff.mp hgood₀
  obtain ⟨β₁, _, hβ₁⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℝ)) (1 : ℝ)).mem_iff.mp hgood₁
  have hcβ₀ (t : ℝ) (ht : β₀ t ≠ 0) : F₀ (t, 0) = StripCoordinates.center t :=
    (hβ₀ (subset_tsupport β₀ ht)).1
  have hcβ₁ (t : ℝ) (ht : β₁ t ≠ 0) : F₁ (t, 0) = StripCoordinates.center t :=
    (hβ₁ (subset_tsupport β₁ ht)).1
  have hnβ₀ (t : ℝ) (ht : β₀ t ≠ 0) : normalDerivative F₀ t = v t :=
    (hβ₀ (subset_tsupport β₀ ht)).2.1
  have hnβ₁ (t : ℝ) (ht : β₁ t ≠ 0) : normalDerivative F₁ t = v t :=
    (hβ₁ (subset_tsupport β₁ ht)).2.1
  have hβ₀zero : (β₀ : ℝ → ℝ) =ᶠ[𝓝 (1 : ℝ)] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro ht
    have hbad : (1 : ℝ) < 1 / 3 := (hβ₀ ht).2.2
    norm_num at hbad
  have hβ₁zero : (β₁ : ℝ → ℝ) =ᶠ[𝓝 (0 : ℝ)] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro ht
    have hbad : (2 / 3 : ℝ) < 0 := (hβ₁ ht).2.2
    norm_num at hbad
  let F := blend v F₀ F₁ β₀ β₁
  have hF : ContDiff ℝ ∞ F :=
    contDiff_blend hv hF₀ hF₁ β₀.contMDiff.contDiff β₁.contMDiff.contDiff
  refine
    ⟨F, hF, blend_zero hcβ₀ hcβ₁,
      normalDerivative_blend hv hF₀ hF₁ β₀.contMDiff.contDiff β₁.contMDiff.contDiff hnβ₀ hnβ₁, ?_,
      ?_⟩
  · have hp : Filter.Tendsto (Prod.fst : ℝ × ℝ → ℝ) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_fst.continuousAt.tendsto
    filter_upwards [hp β₀.eventuallyEq_one, hp hβ₁zero] with p hp₀ hp₁
    exact blend_eq_left hp₀ hp₁
  · have hp : Filter.Tendsto (Prod.fst : ℝ × ℝ → ℝ) (𝓝 (1, 0)) (𝓝 1) :=
      continuous_fst.continuousAt.tendsto
    filter_upwards [hp hβ₀zero, hp β₁.eventuallyEq_one] with p hp₀ hp₁
    exact blend_eq_right hp₀ hp₁

theorem StripCoordinates.exists_clean_strip_neighborhood {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hc : ∀ t, F (t, 0) = StripCoordinates.center t) (hD : ∀ t, normalDerivative F t = v t)
    (hn : ∀ t ∈ Set.Icc (0 : ℝ) 1, v t ≠ 0) {O : Set (Space A B)} (hO : IsOpen O)
    (hcenterO : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ W : Set (ℝ × ℝ),
          IsOpen W ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
              Set.InjOn F W ∧
                Set.MapsTo F W O ∧
                  (∀ p ∈ W, Function.Injective (fderiv ℝ F p)) ∧
                    (∀ p ∈ W, (F p).2 = 0 ↔ p.2 = 0) ∧
                      Topology.IsClosedEmbedding
                        (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => F p) := by
  let K := Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := CompactIccSpace.isCompact_Icc.prod isCompact_singleton
  have hFK : Set.InjOn F K := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨u, r⟩ ⟨hu, hr⟩ heq
    have hs0 : s = 0 := hs
    have hr0 : r = 0 := hr
    subst s
    subst r
    have htu : t = u := by
      simpa only [hc, StripCoordinates.center] using
        congrArg (fun q : Space A B => q.1.1) heq
    exact Prod.ext htu rfl
  have hiF : ∀ p ∈ K, Function.Injective (fderiv ℝ F p) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    apply injective_fderiv_at_center (hF.contDiffAt.differentiableAt (by simp)) hc
    rw [hD t]
    exact hn t ht
  have hiFM : ∀ p ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Space A B) F p) := by
    intro p hp
    rw [mfderiv_eq_fderiv]
    exact hiF p hp
  obtain ⟨V, hV, hKV, hinjV⟩ :=
    ManifoldImmersion.exists_open_injOn_near_compact hF.contMDiff hK hFK hiFM
  let Q := detector v F
  have hQ : ContDiff ℝ ∞ Q := contDiff_detector hv hF
  have hQK : Set.InjOn Q K := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨u, r⟩ ⟨hu, hr⟩ heq
    have hs0 : s = 0 := hs
    have hr0 : r = 0 := hr
    subst s
    subst r
    have htu : t = u := congrArg Prod.fst heq
    exact Prod.ext htu rfl
  have hiQ : ∀ p ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) Q p) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    rw [mfderiv_eq_fderiv]
    exact injective_fderiv_detector_at_center hv hF hc hD (hn t ht)
  obtain ⟨T, hT, hKT, hinjT⟩ :=
    ManifoldImmersion.exists_open_injOn_near_compact hQ.contMDiff hK hQK hiQ
  let I := {p : ℝ × ℝ | Function.Injective (fderiv ℝ F p)}
  have hI : IsOpen I :=
    ContinuousLinearMap.isOpen_injective.preimage (hF.continuous_fderiv (by simp))
  let W := ((V ∩ T) ∩ I) ∩ (F ⁻¹' O ∩ (fun p : ℝ × ℝ => (p.1, 0)) ⁻¹' T)
  have hW : IsOpen W :=
    ((hV.inter hT).inter hI).inter
      ((hO.preimage hF.continuous).inter (hT.preimage (continuous_fst.prodMk continuous_const)))
  have hKW : K ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    have hpK : (t, (0 : ℝ)) ∈ K := ⟨ht, rfl⟩
    refine ⟨⟨⟨hKV hpK, hKT hpK⟩, hiF _ hpK⟩, ⟨?_, hKT hpK⟩⟩
    change F (t, 0) ∈ O
    rw [hc]
    exact hcenterO ht
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hW hKW
  have hrect : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hprod
    refine ⟨ht, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  have hinjW : Set.InjOn F W := hinjV.mono (fun _ hp => hp.1.1.1)
  refine ⟨ε, hε, W, hW, hrect, hinjW, fun _ hp => hp.2.1, fun _ hp => hp.1.2, ?_, ?_⟩
  · rintro ⟨t, s⟩ hp
    constructor
    · intro hz
      have heq : Q (t, s) = Q (t, 0) := by
        change detector v F (t, s) = detector v F (t, 0)
        rw [detector_zero hc]
        change (t, ⟪v t, (F (t, s)).2⟫_ℝ) = (t, 0)
        rw [hz, inner_zero_right]
      exact congrArg Prod.snd (hinjT hp.1.1.2 hp.2.2 heq)
    · intro hs
      change s = 0 at hs
      subst s
      rw [hc]
      rfl
  · let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
    let : CompactSpace R :=
      isCompact_iff_compactSpace.mp
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
    apply (hF.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjW (hrect p.property) (hrect q.property) hpq)

theorem StripCoordinates.contDiff_normalDerivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (normalDerivative F) :=
  ((hF.snd.fderiv_right (by simp)).clm_apply contDiff_const).comp
    (contDiff_id.prodMk contDiff_const)

theorem StripCoordinates.normalDerivative_congr_germ {A B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {F G : (ℝ × ℝ) → Space A B} {t : ℝ} (heq : F =ᶠ[𝓝 (t, 0)] G) :
    normalDerivative F t = normalDerivative G t := by
  have heq' : (fun p => (F p).2) =ᶠ[𝓝 (t, (0 : ℝ))] (fun p => (G p).2) := by
    filter_upwards [heq] with p hp
    exact congrArg Prod.snd hp
  have hd : fderiv ℝ (fun p => (F p).2) (t, 0) = fderiv ℝ (fun p => (G p).2) (t, 0) :=
    heq'.fderiv_eq
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] B => L (0, 1)) hd

theorem StripCoordinates.exists_clean_strip_matching_local_germs {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] {F₀ F₁ : (ℝ × ℝ) → Space A B}
    {U₀ U₁ : Set (ℝ × ℝ)} (hF₀ : ContDiffOn ℝ ∞ F₀ U₀) (hF₁ : ContDiffOn ℝ ∞ F₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (h0U₀ : (0, 0) ∈ U₀) (h1U₁ : (1, 0) ∈ U₁)
    (hc₀ : (fun t : ℝ => F₀ (t, 0)) =ᶠ[𝓝 0] StripCoordinates.center)
    (hc₁ : (fun t : ℝ => F₁ (t, 0)) =ᶠ[𝓝 1] StripCoordinates.center)
    (hn₀ : normalDerivative F₀ 0 ≠ 0) (hn₁ : normalDerivative F₁ 1 ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) {O : Set (Space A B)} (hO : IsOpen O)
    (hcenterO : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) O) :
    ∃ F : (ℝ × ℝ) → Space A B,
      ContDiff ℝ ∞ F ∧
        (∀ t, F (t, 0) = StripCoordinates.center t) ∧
          (F =ᶠ[𝓝 (0, 0)] F₀) ∧
            (F =ᶠ[𝓝 (1, 0)] F₁) ∧
              ∃ ε : ℝ,
                0 < ε ∧
                  ∃ W : Set (ℝ × ℝ),
                    IsOpen W ∧
                      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
                        Set.InjOn F W ∧
                          Set.MapsTo F W O ∧
                            (∀ p ∈ W, Function.Injective (fderiv ℝ F p)) ∧
                              (∀ p ∈ W, (F p).2 = 0 ↔ p.2 = 0) ∧
                                Topology.IsClosedEmbedding
                                    (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => F p) ∧
                                  (∀ t, normalDerivative F t ≠ 0) := by
  obtain ⟨G₀, hG₀, heq₀⟩ := exists_smooth_extension_near_point hF₀.contMDiffOn hU₀ h0U₀
  obtain ⟨G₁, hG₁, heq₁⟩ := exists_smooth_extension_near_point hF₁.contMDiffOn hU₁ h1U₁
  have hnG₀ : normalDerivative G₀ 0 ≠ 0 := by rwa [normalDerivative_congr_germ heq₀]
  have hnG₁ : normalDerivative G₁ 1 ≠ 0 := by rwa [normalDerivative_congr_germ heq₁]
  obtain ⟨v, hv, hvne, hv₀, hv₁⟩ :=
    DiskFraming.exists_nonzero_smooth_curve_with_endpoint_germs
      (contDiff_normalDerivative hG₀.contDiff).contDiffOn
      (contDiff_normalDerivative hG₁.contDiff).contDiffOn isOpen_univ isOpen_univ (Set.mem_univ _)
      (Set.mem_univ _) hnG₀ hnG₁ hdim
  have hcG₀ : (fun t : ℝ => G₀ (t, 0)) =ᶠ[𝓝 0] StripCoordinates.center := by
    have hi : Filter.Tendsto (fun t : ℝ => (t, (0 : ℝ))) (𝓝 0) (𝓝 (0, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    exact (heq₀.comp_tendsto hi).trans hc₀
  have hcG₁ : (fun t : ℝ => G₁ (t, 0)) =ᶠ[𝓝 1] StripCoordinates.center := by
    have hi : Filter.Tendsto (fun t : ℝ => (t, (0 : ℝ))) (𝓝 1) (𝓝 (1, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    exact (heq₁.comp_tendsto hi).trans hc₁
  obtain ⟨F, hF, hc, hD, hFG₀, hFG₁⟩ :=
    exists_smooth_strip_matching_germs hv hG₀.contDiff hG₁.contDiff hcG₀ hcG₁ hv₀.symm hv₁.symm
  obtain ⟨ε, hε, W, hW, hrect, hinj, hmap, hi, hclean, hemb⟩ :=
    exists_clean_strip_neighborhood hv hF hc hD (fun t _ => hvne t) hO hcenterO
  exact
    ⟨F, hF, hc, hFG₀.trans heq₀, hFG₁.trans heq₁, ε, hε, W, hW, hrect, hinj, hmap, hi, hclean,
      hemb, fun t => by rw [hD t]; exact hvne t⟩

theorem exists_native_clean_strip_matching_germs {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M]
    (Φ :
      PartialDiffeomorph 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) (StripCoordinates.Space A B) M
        ∞)
    (hline : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) Φ.source) {S : Set M}
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ S ↔ q.2 = 0) {k₀ k₁ : (ℝ × ℝ) → M} {U₀ U₁ : Set (ℝ × ℝ)}
    (hk₀ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₀ U₀)
    (hk₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0U₀ : (0, 0) ∈ U₀) (h1U₁ : (1, 0) ∈ U₁)
    (hc₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] fun t => Φ (StripCoordinates.center t))
    (hc₁ : (fun t : ℝ => k₁ (t, 0)) =ᶠ[𝓝 1] fun t => Φ (StripCoordinates.center t))
    (hn₀ : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₀) (0, 0) (0, 1) ≠ 0)
    (hn₁ : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁) (1, 0) (0, 1) ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ W : Set (ℝ × ℝ),
          IsOpen W ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
              ∃ k : (ℝ × ℝ) → M,
                ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
                  Set.InjOn k W ∧
                    Set.MapsTo k W Φ.target ∧
                      Topology.IsClosedEmbedding
                          (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) ∧
                        (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                          (∀ p ∈ W, k p ∈ S ↔ p.2 = 0) ∧
                            (∀ t, k (t, 0) = Φ (StripCoordinates.center t)) ∧
                              (k =ᶠ[𝓝 (0, 0)] k₀) ∧
                                (k =ᶠ[𝓝 (1, 0)] k₁) ∧
                                  (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                    fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k) (t, 0)
                                        (0, 1) ≠
                                      0) := by
  let C₀ := U₀ ∩ k₀ ⁻¹' Φ.target
  let C₁ := U₁ ∩ k₁ ⁻¹' Φ.target
  have hC₀ : IsOpen C₀ := hk₀.continuousOn.isOpen_inter_preimage hU₀ Φ.open_target
  have hC₁ : IsOpen C₁ := hk₁.continuousOn.isOpen_inter_preimage hU₁ Φ.open_target
  have hline₀ : StripCoordinates.center (0 : ℝ) ∈ Φ.source := hline (by simp)
  have hline₁ : StripCoordinates.center (1 : ℝ) ∈ Φ.source := hline (by simp)
  have h0C₀ : (0, 0) ∈ C₀ := by
    refine ⟨h0U₀, ?_⟩
    change k₀ (0, 0) ∈ Φ.target
    rw [hc₀.eq_of_nhds]
    exact Φ.map_source' hline₀
  have h1C₁ : (1, 0) ∈ C₁ := by
    refine ⟨h1U₁, ?_⟩
    change k₁ (1, 0) ∈ Φ.target
    rw [hc₁.eq_of_nhds]
    exact Φ.map_source' hline₁
  let G₀ : (ℝ × ℝ) → StripCoordinates.Space A B := Φ.invFun ∘ k₀
  let G₁ : (ℝ × ℝ) → StripCoordinates.Space A B := Φ.invFun ∘ k₁
  have hG₀ : ContDiffOn ℝ ∞ G₀ C₀ :=
    (Φ.contMDiffOn_invFun.comp (hk₀.mono Set.inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hG₁ : ContDiffOn ℝ ∞ G₁ C₁ :=
    (Φ.contMDiffOn_invFun.comp (hk₁.mono Set.inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hcG₀ : (fun t : ℝ => G₀ (t, 0)) =ᶠ[𝓝 0] StripCoordinates.center := by
    have hsource := hc.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₀)
    filter_upwards [hc₀, hsource] with t hkt ht
    change Φ.invFun (k₀ (t, 0)) = StripCoordinates.center t
    rw [hkt]
    exact Φ.left_inv' ht
  have hcG₁ : (fun t : ℝ => G₁ (t, 0)) =ᶠ[𝓝 1] StripCoordinates.center := by
    have hsource := hc.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₁)
    filter_upwards [hc₁, hsource] with t hkt ht
    change Φ.invFun (k₁ (t, 0)) = StripCoordinates.center t
    rw [hkt]
    exact Φ.left_inv' ht
  obtain
    ⟨F, hF, hFc, hFG₀, hFG₁, ε, hε, W, hW, hrect, hinjF, hsource, hiF, hcleanF, _, hnormalF⟩ :=
    StripCoordinates.exists_clean_strip_matching_local_germs hG₀ hG₁ hC₀ hC₁ h0C₀ h1C₁ hcG₀ hcG₁
      hn₀ hn₁ hdim Φ.open_source hline
  let k := Φ ∘ F
  have hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W :=
    Φ.contMDiffOn_toFun.comp hF.contMDiff.contMDiffOn hsource
  have hinjk : Set.InjOn k W := by
    intro p hp q hq heq
    exact hinjF hp hq (Φ.toPartialEquiv.injOn (hsource hp) (hsource hq) heq)
  have hemb : Topology.IsClosedEmbedding (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) := by
    let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
    let : CompactSpace R :=
      isCompact_iff_compactSpace.mp
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
    apply
      (continuousOn_iff_continuous_domRestrict.mp (hk.continuousOn.mono hrect)).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjk (hrect p.property) (hrect q.property) hpq)
  refine
    ⟨ε, hε, W, hW, hrect, k, hk, hinjk, fun _ hp => Φ.map_source' (hsource hp), hemb, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · intro p hp
    have hiFM : Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, StripCoordinates.Space A B) F p) := by
      rw [mfderiv_eq_fderiv]
      exact hiF p hp
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Φ ∘ F) p)
    rw [mfderiv_comp p (Φ.mdifferentiableAt (by simp) (hsource hp))
        (hF.contMDiff.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv Φ (hsource hp)).1.comp hiFM
  · intro p hp
    exact (hclean (F p) (hsource hp)).trans (hcleanF p hp)
  · intro t
    exact congrArg Φ (hFc t)
  · filter_upwards [hFG₀, hC₀.mem_nhds h0C₀] with p hFp hp
    change Φ (F p) = k₀ p
    rw [hFp]
    exact Φ.right_inv' hp.2
  · filter_upwards [hFG₁, hC₁.mem_nhds h1C₁] with p hFp hp
    change Φ (F p) = k₁ p
    rw [hFp]
    exact Φ.right_inv' hp.2
  · intro t ht
    have hp : (t, (0 : ℝ)) ∈ W := hrect ⟨ht, ⟨neg_nonpos.mpr hε.le, hε.le⟩⟩
    have heq : (TransverseCoordinates.normalCoordinate Φ ∘ k) =ᶠ[𝓝 (t, 0)] (fun p => (F p).2) := by
      filter_upwards [hW.mem_nhds hp] with p hpW
      change (Φ.invFun (Φ (F p))).2 = (F p).2
      rw [Φ.left_inv' (hsource hpW)]
    rw [heq.fderiv_eq]
    exact hnormalF t

theorem exists_strip_neighborhood_with_exact_endpoint_contacts {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {k : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ k W) (hW : IsOpen W)
    (hKW : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ W) {B : Set M} (hB : IsClosed B)
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, k (t, 0) ∉ B)
    (hc₀ : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), k p ∈ B ↔ p.1 = 0)
    (hc₁ : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), k p ∈ B ↔ p.1 = 1) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ U ∧
              U ⊆ W ∧ ∀ p ∈ U, k p ∈ B ↔ p.1 = 0 ∨ p.1 = 1 := by
  obtain ⟨V₀, hV₀sub, hV₀, h0V₀⟩ := _root_.mem_nhds_iff.mp hc₀
  obtain ⟨V₁, hV₁sub, hV₁, h1V₁⟩ := _root_.mem_nhds_iff.mp hc₁
  let L := V₀ ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Iio (1 / 3)
  let R := V₁ ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ioi (2 / 3)
  let C := (W ∩ k ⁻¹' Bᶜ) ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ioo 0 1
  have hL : IsOpen L := hV₀.inter (isOpen_Iio.preimage continuous_fst)
  have hR : IsOpen R := hV₁.inter (isOpen_Ioi.preimage continuous_fst)
  have hC : IsOpen C :=
    (hk.continuousOn.isOpen_inter_preimage hW hB.isOpen_compl).inter
      (isOpen_Ioo.preimage continuous_fst)
  let U := W ∩ ((L ∪ R) ∪ C)
  have hU : IsOpen U := hW.inter ((hL.union hR).union hC)
  have hKU : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ U := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    have htW := hKW ⟨ht, rfl⟩
    refine ⟨htW, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (Or.inl ⟨h0V₀, by change (0 : ℝ) < 1 / 3; norm_num⟩)
    by_cases ht1 : t = 1
    · subst t
      exact Or.inl (Or.inr ⟨h1V₁, by change (2 / 3 : ℝ) < 1; norm_num⟩)
    have hti : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact Or.inr ⟨⟨htW, havoid t hti⟩, hti⟩
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hU hKU
  refine ⟨ε, hε, U, hU, ?_, Set.inter_subset_left, ?_⟩
  · rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hprod
    refine ⟨ht, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  · intro p hp
    rcases hp.2 with (hpL | hpR) | hpC
    · have hcontact : k p ∈ B ↔ p.1 = 0 := hV₀sub hpL.1
      have hlt : p.1 < 1 / 3 := hpL.2
      constructor
      · exact fun h => Or.inl (hcontact.mp h)
      · intro h
        rcases h with h0 | h1
        · exact hcontact.mpr h0
        · rw [h1] at hlt
          norm_num at hlt
    · have hcontact : k p ∈ B ↔ p.1 = 1 := hV₁sub hpR.1
      have hgt : 2 / 3 < p.1 := hpR.2
      constructor
      · exact fun h => Or.inr (hcontact.mp h)
      · intro h
        rcases h with h0 | h1
        · rw [h0] at hgt
          norm_num at hgt
        · exact hcontact.mpr h1
    · have hnot : k p ∉ B := hpC.1.2
      have hti : p.1 ∈ Set.Ioo (0 : ℝ) 1 := hpC.2
      constructor
      · exact fun h => (hnot h).elim
      · intro h
        rcases h with h0 | h1
        · exact (hti.1.ne' h0).elim
        · exact (hti.2.ne h1).elim

theorem exists_strip_along_arc_matching_parametrized_corners {E M D Z Z₀ Z₁ N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup Z₀] [NormedSpace ℝ Z₀]
    [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁] [TopologicalSpace N] [ChartedSpace D N]
    [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P] [ChartedSpace Z P] [T2Space N] [CompactSpace N]
    [CompactSpace P] {F : N → M} {G : P → M} {f : ℝ → N} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G) (hembF : Topology.IsEmbedding F)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f) (hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t))
    (c₀ : PartialDiffeomorph 𝓘(ℝ, Z₀) 𝓘(ℝ, Z) Z₀ P ∞)
    (c₁ : PartialDiffeomorph 𝓘(ℝ, Z₁) 𝓘(ℝ, Z) Z₁ P ∞) (hc₀ : (0 : Z₀) ∈ c₀.source)
    (hc₁ : (0 : Z₁) ∈ c₁.source) (hcross₀ : G (c₀ 0) = F (f 0)) (hcross₁ : G (c₁ 0) = F (f 1))
    (ht₀ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c₀ 0))))
    (ht₁ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c₁ 0))))
    (n : ℕ) (hsheet : 1 + n = Module.finrank ℝ D)
    (hcodim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (hdimZ : 2 ≤ Module.finrank ℝ Z) {v₀ : Z₀} {v₁ : Z₁} (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F (f t) ∉ Set.range G) {k₀ k₁ : (ℝ × ℝ) → M}
    {U₀ U₁ : Set (ℝ × ℝ)} (hk₀ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₀ U₀)
    (hk₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0U₀ : (0 : ℝ × ℝ) ∈ U₀) (h0U₁ : (0 : ℝ × ℝ) ∈ U₁)
    (hl₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] (F ∘ f))
    (hl₁ : (fun t : ℝ => k₁ (t, 0)) =ᶠ[𝓝 0] fun t => F (f (1 - t)))
    (hr₀ : ∀ s, (0, s) ∈ U₀ → k₀ (0, s) = G (c₀ (s • v₀)))
    (hr₁ : ∀ s, (0, s) ∈ U₁ → k₁ (0, s) = G (c₁ (s • v₁)))
    (hcG₀ : ∀ p ∈ U₀, k₀ p ∈ Set.range G ↔ p.1 = 0)
    (hcG₁ : ∀ p ∈ U₁, k₁ p ∈ Set.range G ↔ p.1 = 0) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo (F ∘ f) (Set.Icc (0 : ℝ) 1) O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ W : Set (ℝ × ℝ),
          IsOpen W ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
              ∃ k : (ℝ × ℝ) → M,
                ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
                  Set.InjOn k W ∧
                    Set.MapsTo k W O ∧
                      Topology.IsClosedEmbedding
                          (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) ∧
                        (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                          (∀ p ∈ W, k p ∈ Set.range F ↔ p.2 = 0) ∧
                            (∀ p ∈ W, k p ∈ Set.range G ↔ p.1 = 0 ∨ p.1 = 1) ∧
                              (∀ t ∈ Set.Icc (0 : ℝ) 1, k (t, 0) = F (f t)) ∧
                                (k =ᶠ[𝓝 (0, 0)] k₀) ∧
                                  (k =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse) ∧
                                    Nonempty
                                      (StripNormalData (EuclideanSpace ℝ (Fin n))
                                        (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z))) (E := E)
                                        (Set.range F) k) := by
  obtain ⟨Φ, hline, htarget, hzero, hclean⟩ :=
    exists_clean_ambient_chart_along_embedded_arc hF hembF hiF hf hinjf hif n (Module.finrank ℝ Z)
      hsheet hcodim hO hfO
  have hline₀ := hline (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
  have hline₁ := hline (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
  have hx₀ : F (f 0) ∈ Φ.target := by
    have h := Φ.map_source' hline₀
    rwa [hzero 0 hline₀] at h
  have hx₁ : F (f 1) ∈ Φ.target := by
    have h := Φ.map_source' hline₁
    rwa [hzero 1 hline₁] at h
  have hdim :
    Module.finrank ℝ Z = Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z))) :=
    finrank_euclideanSpace_fin.symm
  have hn₀ :=
    (TransverseCoordinates.corner_normalDerivative_ne_zero Φ hF hG hclean c₀ hc₀ hx₀ hcross₀ ht₀
        hdim hk₀ hU₀ h0U₀ hv₀ hr₀).1
  have hn₁ :=
    (TransverseCoordinates.corner_normalDerivative_ne_zero Φ hF hG hclean c₁ hc₁ hx₁ hcross₁ ht₁
        hdim hk₁ hU₁ h0U₁ hv₁ hr₁).1
  let k₁' := k₁ ∘ StripCoordinates.reverse
  let U₁' := StripCoordinates.reverse ⁻¹' U₁
  have hU₁' : IsOpen U₁' := hU₁.preimage StripCoordinates.contDiff_reverse.continuous
  have h1U₁' : (1, 0) ∈ U₁' := by
    change StripCoordinates.reverse (1, 0) ∈ U₁
    rw [StripCoordinates.reverse_one_zero]
    exact h0U₁
  have hk₁' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁' U₁' :=
    hk₁.comp StripCoordinates.contDiff_reverse.contMDiff.contMDiffOn (fun _ hp => hp)
  have hk₁zero : k₁ (0, 0) = F (f 1) := by simpa only [sub_zero] using hl₁.eq_of_nhds
  have hk₁Phi : k₁ (0, 0) ∈ Φ.target := hk₁zero.symm ▸ hx₁
  have hnormal :=
    (TransverseCoordinates.contMDiffOn_normalCoordinate Φ).contMDiffAt
      (Φ.open_target.mem_nhds hk₁Phi)
  have hH₁ : DifferentiableAt ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁) (0, 0) :=
    (hnormal.comp (0, 0) (hk₁.contMDiffAt (hU₁.mem_nhds h0U₁))).contDiffAt.differentiableAt
      (by simp)
  have hn₁' : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁') (1, 0) (0, 1) ≠ 0 := by
    change
      fderiv ℝ ((TransverseCoordinates.normalCoordinate Φ ∘ k₁) ∘ StripCoordinates.reverse) (1, 0)
          (0, 1) ≠
        0
    rw [StripCoordinates.vertical_derivative_reverse hH₁]
    exact hn₁
  have hcenter :
    Continuous
      (StripCoordinates.center :
        ℝ →
          StripCoordinates.Space (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z)))) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hmatch₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] fun t => Φ (StripCoordinates.center t) := by
    have hsource := hcenter.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₀)
    filter_upwards [hsource, hl₀] with t hs heq
    exact heq.trans (hzero t hs).symm
  have hrev : Filter.Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 0) := by
    have he : Filter.Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
      (show Continuous (fun t : ℝ => 1 - t) by fun_prop).continuousAt
    simpa only [sub_self] using he
  have hmatch₁ : (fun t : ℝ => k₁' (t, 0)) =ᶠ[𝓝 1] fun t => Φ (StripCoordinates.center t) := by
    have hsource := hcenter.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₁)
    have hleft := hl₁.comp_tendsto hrev
    filter_upwards [hsource, hleft] with t hs heq
    change k₁ (1 - t, 0) = Φ (StripCoordinates.center t)
    change k₁ (1 - t, 0) = F (f (1 - (1 - t))) at heq
    rw [heq, hzero t hs]
    congr 2
    ring
  obtain ⟨a, ha, V, hV, hrectV, k, hk, hinjk, hmap, _, hik, hcF, hkc, hkk₀, hkk₁, hnormal⟩ :=
    exists_native_clean_strip_matching_germs Φ hline hclean hk₀ hk₁' hU₀ hU₁' h0U₀ h1U₁' hmatch₀
      hmatch₁ hn₀ hn₁' (by simpa only [finrank_euclideanSpace_fin] using hdimZ)
  have hkc' : ∀ t ∈ Set.Icc (0 : ℝ) 1, k (t, 0) = F (f t) := by
    intro t ht
    exact (hkc t).trans (hzero t (hline ht))
  have hKV : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ V := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact hrectV ⟨ht, ⟨neg_nonpos.mpr ha.le, ha.le⟩⟩
  have havoidk : ∀ t ∈ Set.Ioo (0 : ℝ) 1, k (t, 0) ∉ Set.range G := by
    intro t ht
    rw [hkc' t ⟨ht.1.le, ht.2.le⟩]
    exact havoid t ht
  have hcontact₀ : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), k p ∈ Set.range G ↔ p.1 = 0 := by
    filter_upwards [hkk₀, hU₀.mem_nhds h0U₀] with p heq hp
    rw [heq]
    exact hcG₀ p hp
  have hcontact₁ : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), k p ∈ Set.range G ↔ p.1 = 1 := by
    filter_upwards [hkk₁, hU₁'.mem_nhds h1U₁'] with p heq hp
    have h : k p ∈ Set.range G ↔ (StripCoordinates.reverse p).1 = 0 := by
      rw [heq]
      exact hcG₁ (StripCoordinates.reverse p) hp
    change (k p ∈ Set.range G ↔ 1 - p.1 = 0) at h
    rw [sub_eq_zero] at h
    exact h.trans eq_comm
  obtain ⟨ε, hε, W, hW, hrectW, hWV, hcG⟩ :=
    exists_strip_neighborhood_with_exact_endpoint_contacts hk hV hKV
      (isCompact_range hG.continuous).isClosed havoidk hcontact₀ hcontact₁
  have hemb : Topology.IsClosedEmbedding (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) := by
    let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
    let : CompactSpace R :=
      isCompact_iff_compactSpace.mp
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
    apply
      (continuousOn_iff_continuous_domRestrict.mp
          (hk.continuousOn.mono (hrectW.trans hWV))).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjk (hWV (hrectW p.property)) (hWV (hrectW q.property)) hpq)
  exact
    ⟨ε, hε, W, hW, hrectW, k, hk.mono hWV, hinjk.mono hWV, fun _ hp => htarget (hmap (hWV hp)),
      hemb, fun p hp => hik p (hWV hp), fun p hp => hcF p (hWV hp), hcG, hkc', hkk₀, hkk₁,
      ⟨{  chart := Φ
          line := hline
          sheet := hclean
          center := hkc
          normal_nonzero := hnormal }⟩⟩

theorem exists_cleanStripPatch_of_tubular_arc_corners {E M D Z B N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [T2Space N] [CompactSpace N] [CompactSpace P] {F : N → M} {G : P → M}
    {f : ℝ → N} {g : ℝ → P} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G) (hembF : Topology.IsEmbedding F)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f) (hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t))
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞) (hd : ∀ t, d (t, 0) = g t)
    (hd₀ : ((0 : ℝ), (0 : B)) ∈ d.source) (hd₁ : ((1 : ℝ), (0 : B)) ∈ d.source)
    (hcross₀ : G (g 0) = F (f 0)) (hcross₁ : G (g 1) = F (f 1))
    (ht₀ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 0))))
    (ht₁ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 1))))
    (n : ℕ) (hsheet : 1 + n = Module.finrank ℝ D)
    (hcodim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (hdimZ : 2 ≤ Module.finrank ℝ Z) (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F (f t) ∉ Set.range G)
    (c₀ : CleanCornerPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) (G ∘ g))
    (c₁ :
      CleanCornerPatch (E := E) (Set.range F) (Set.range G) (fun t => F (f (1 - t)))
        (fun t => G (g (1 - t))))
    {O : Set M} (hO : IsOpen O) (hfO : Set.MapsTo (F ∘ f) (Set.Icc (0 : ℝ) 1) O) :
    ∃ k : CleanStripPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) c₀.map c₁.map,
      Nonempty
          (StripNormalData (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z))) (E := E) (Set.range F) k.map) ∧
        Set.MapsTo k.map k.domain O := by
  let d' := (NativeParametrization.translation ((1 : ℝ), (0 : B))).toPartialDiffeomorph.trans d
  have hd'₀ : (0 : ℝ × B) ∈ d'.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change 0 + ((1 : ℝ), (0 : B)) ∈ d.source
    rw [zero_add]
    exact hd₁
  have hd0 : d (0 : ℝ × B) = g 0 := hd 0
  have hd1 : d' (0 : ℝ × B) = g 1 := by
    change d (0 + ((1 : ℝ), (0 : B))) = g 1
    rw [zero_add, hd]
  have hcross₀' : G (d 0) = F (f 0) := by rw [hd0]; exact hcross₀
  have hcross₁' : G (d' 0) = F (f 1) := by rw [hd1]; exact hcross₁
  have ht₀' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))) := by
    rw [hd0]; exact ht₀
  have ht₁' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d' 0))) := by
    rw [hd1]; exact ht₁
  have hv₀ : ((1 : ℝ), (0 : B)) ≠ 0 := fun he => one_ne_zero (congrArg Prod.fst he)
  have hv₁ : ((-1 : ℝ), (0 : B)) ≠ 0 := by
    intro he
    have he' : (-1 : ℝ) = 0 := congrArg Prod.fst he
    norm_num at he'
  have hleft₀ : (fun t : ℝ => c₀.map (t, 0)) =ᶠ[𝓝 0] (F ∘ f) := by
    have haxis :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (c₀.open_domain.mem_nhds c₀.contains_zero)
    filter_upwards [haxis] with t ht
    exact c₀.axis_first t ht
  have hleft₁ : (fun t : ℝ => c₁.map (t, 0)) =ᶠ[𝓝 0] fun t => F (f (1 - t)) := by
    have haxis :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (c₁.open_domain.mem_nhds c₁.contains_zero)
    filter_upwards [haxis] with t ht
    exact c₁.axis_first t ht
  have hcurve₀ (s : ℝ) : d (s • ((1 : ℝ), (0 : B))) = g s := by
    simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using hd s
  have hcurve₁ (s : ℝ) : d' (s • ((-1 : ℝ), (0 : B))) = g (1 - s) := by
    change d (s • ((-1 : ℝ), (0 : B)) + (1, 0)) = g (1 - s)
    have he : s • ((-1 : ℝ), (0 : B)) + (1, 0) = (1 - s, 0) := by
      simp [smul_eq_mul, sub_eq_add_neg, add_comm]
    rw [he, hd]
  obtain
    ⟨ε, hε, W, hW, hrect, k, hk, hinj, hmap, hemb, hi, hfirst, hsecond, hcenter, hleft, hright,
      hnormal⟩ :=
    exists_strip_along_arc_matching_parametrized_corners hF hG hembF hiF hf hinjf hif d d' hd₀
      hd'₀ hcross₀' hcross₁' ht₀' ht₁' n hsheet hcodim hdimZ hv₀ hv₁ havoid c₀.smooth c₁.smooth
      c₀.open_domain c₁.open_domain c₀.contains_zero c₁.contains_zero hleft₀ hleft₁
      (fun s hs => (c₀.axis_second s hs).trans (congrArg G (hcurve₀ s).symm))
      (fun s hs => (c₁.axis_second s hs).trans (congrArg G (hcurve₁ s).symm))
      (fun p hp => (c₀.sheets p hp).2) (fun p hp => (c₁.sheets p hp).2) hO hfO
  let strip : CleanStripPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) c₀.map c₁.map :=
    { width := ε, width_pos := hε, domain := W, open_domain := hW, contains_strip := hrect,
      map := k, smooth := hk, injective := hinj, closed_embedding := hemb,
      derivative_injective := hi, first_sheet := hfirst, second_sheet := hsecond,
      center := hcenter, left_germ := hleft, right_germ := hright }
  exact ⟨strip, hnormal, hmap⟩

theorem exists_open_neighborhoods_with_coincidences_in {X Y M : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace M] [T2Space M] {K : Set X} {L : Set Y}
    (hK : IsCompact K) (hL : IsCompact L) {f : X → M} {g : Y → M} (hf : ∀ x ∈ K, ContinuousAt f x)
    (hg : ∀ y ∈ L, ContinuousAt g y) {O : Set (X × Y)} (hO : IsOpen O)
    (hcoinc : ∀ x ∈ K, ∀ y ∈ L, f x = g y → (x, y) ∈ O) :
    ∃ U : Set X,
      ∃ V : Set Y,
        IsOpen U ∧ IsOpen V ∧ K ⊆ U ∧ L ⊆ V ∧ ∀ x ∈ U, ∀ y ∈ V, f x = g y → (x, y) ∈ O := by
  let R : Set (X × Y) := {p | f p.1 ≠ g p.2} ∪ O
  have hKR : K ×ˢ L ⊆ interior R := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply mem_interior_iff_mem_nhds.mpr
    by_cases hxy : f x = g y
    · exact Filter.mem_of_superset (hO.mem_nhds (hcoinc x hx y hy hxy)) (fun _ hp => Or.inr hp)
    · have hfc : ContinuousAt (fun p : X × Y => f p.1) (x, y) := (hf x hx).comp continuousAt_fst
      have hgc : ContinuousAt (fun p : X × Y => g p.2) (x, y) := (hg y hy).comp continuousAt_snd
      have hne : ∀ᶠ p : X × Y in 𝓝 (x, y), f p.1 ≠ g p.2 := (hfc.ne_iff_eventually_ne hgc).mp hxy
      exact Filter.mem_of_superset hne (fun _ hp => Or.inl hp)
  obtain ⟨U, V, hU, hV, hKU, hLV, hUV⟩ := generalized_tube_lemma hK hL isOpen_interior hKR
  refine ⟨U, V, hU, hV, hKU, hLV, ?_⟩
  intro x hx y hy hxy
  exact (interior_subset (hUV ⟨hx, hy⟩)).resolve_left (fun hne => hne hxy)

theorem exists_open_corner_overlap {X Y D M : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace D] {k : X → M} {l : Y → M} {c : D → M} {a : X → D}
    {b : Y → D} {x₀ : X} {y₀ : Y} {W : Set D} (hW : IsOpen W) (hc : Set.InjOn c W)
    (ha : ContinuousAt a x₀) (hb : ContinuousAt b y₀) (haW : a x₀ ∈ W) (hbW : b y₀ ∈ W)
    (hk : k =ᶠ[𝓝 x₀] c ∘ a) (hl : l =ᶠ[𝓝 y₀] c ∘ b) :
    ∃ U : Set X,
      ∃ V : Set Y,
        IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ y₀ ∈ V ∧ ∀ x ∈ U, ∀ y ∈ V, k x = l y ↔ a x = b y := by
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (hk.and (ha.preimage_mem_nhds (hW.mem_nhds haW)))
  obtain ⟨V, hVsub, hV, hyV⟩ := mem_nhds_iff.mp (hl.and (hb.preimage_mem_nhds (hW.mem_nhds hbW)))
  refine ⟨U, V, hU, hV, hxU, hyV, ?_⟩
  intro x hx y hy
  obtain ⟨hkx, hax⟩ := hUsub hx
  obtain ⟨hly, hby⟩ := hVsub hy
  rw [hkx, hly]
  exact ⟨hc hax hby, congrArg c⟩

theorem exists_clean_strip_pair_neighborhoods {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hcoinc :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ δ : ℝ,
          0 < δ ∧
            ∃ U : Set (ℝ × ℝ),
              ∃ V : Set (ℝ × ℝ),
                IsOpen U ∧
                  IsOpen V ∧
                    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ U ∧
                      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-δ) δ ⊆ V ∧
                        U ⊆ k.domain ∧
                          V ⊆ l.domain ∧
                            ∀ p ∈ U,
                              ∀ q ∈ V,
                                k.map p = l.map q →
                                  p = q.swap ∨
                                    StripCoordinates.reverse p =
                                      (StripCoordinates.reverse q).swap := by
  have hswap : Continuous (Prod.swap : (ℝ × ℝ) → ℝ × ℝ) := by fun_prop
  have hrev := StripCoordinates.contDiff_reverse.continuous
  obtain ⟨U₀, V₀, hU₀, hV₀, h0U₀, h0V₀, hover₀⟩ :=
    exists_open_corner_overlap c₀.open_domain c₀.injective
      (continuousAt_id : ContinuousAt (id : (ℝ × ℝ) → ℝ × ℝ) (0, 0))
      (hswap.continuousAt (x := (0, 0))) c₀.contains_zero c₀.contains_zero k.left_germ l.left_germ
  obtain ⟨U₁, V₁, hU₁, hV₁, h1U₁, h1V₁, hover₁⟩ :=
    exists_open_corner_overlap c₁.open_domain c₁.injective (hrev.continuousAt (x := (1, 0)))
      ((hswap.comp hrev).continuousAt (x := (1, 0)))
      (by rw [StripCoordinates.reverse_one_zero]; exact c₁.contains_zero)
      (by
        change (StripCoordinates.reverse (1, 0)).swap ∈ c₁.domain
        rw [StripCoordinates.reverse_one_zero]; exact c₁.contains_zero)
      k.right_germ l.right_germ
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := CompactIccSpace.isCompact_Icc.prod isCompact_singleton
  have hKk : K ⊆ k.domain := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have hKl : K ⊆ l.domain := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  have hk : ∀ p ∈ K, ContinuousAt k.map p := fun p hp =>
    k.smooth.continuousOn.continuousAt (k.open_domain.mem_nhds (hKk hp))
  have hl : ∀ p ∈ K, ContinuousAt l.map p := fun p hp =>
    l.smooth.continuousOn.continuousAt (l.open_domain.mem_nhds (hKl hp))
  let O := (U₀ ×ˢ V₀) ∪ (U₁ ×ˢ V₁)
  have hO : IsOpen O := (hU₀.prod hV₀).union (hU₁.prod hV₁)
  have hcenter : ∀ p ∈ K, ∀ q ∈ K, k.map p = l.map q → (p, q) ∈ O := by
    rintro ⟨t, r⟩ ⟨ht, hr⟩ ⟨s, v⟩ ⟨hs, hv⟩ heq
    have hr0 : r = 0 := hr
    have hv0 : v = 0 := hv
    subst r
    subst v
    rw [k.center t ht, l.center s hs] at heq
    rcases hcoinc t ht s hs heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨h0U₀, h0V₀⟩
    · exact Or.inr ⟨h1U₁, h1V₁⟩
  obtain ⟨U', V', hU', hV', hKU', hKV', hcoinc'⟩ :=
    exists_open_neighborhoods_with_coincidences_in hK hK hk hl hO hcenter
  let U := U' ∩ k.domain
  let V := V' ∩ l.domain
  have hU : IsOpen U := hU'.inter k.open_domain
  have hV : IsOpen V := hV'.inter l.open_domain
  have hKU : K ⊆ U := fun p hp => ⟨hKU' hp, hKk hp⟩
  have hKV : K ⊆ V := fun p hp => ⟨hKV' hp, hKl hp⟩
  obtain ⟨ε, hε, hεU⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hU hKU
  obtain ⟨δ, hδ, hδV⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hV hKV
  have hrect {r : ℝ} {W : Set (ℝ × ℝ)} (h : Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 r ⊆ W) :
    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-r) r ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply h
    refine ⟨ht, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  refine
    ⟨ε, hε, δ, hδ, U, V, hU, hV, hrect hεU, hrect hδV, Set.inter_subset_right,
      Set.inter_subset_right, ?_⟩
  intro p hp q hq heq
  rcases hcoinc' p hp.1 q hq.1 heq with hleft | hright
  · exact Or.inl ((hover₀ p hleft.1 q hleft.2).mp heq)
  · exact Or.inr ((hover₁ p hright.1 q hright.2).mp heq)

def CleanStripPatch.restrict {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {S T : Set M} {a : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁) {ε : ℝ} (hε : 0 < ε)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hrect : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ U)
    (hUk : U ⊆ k.domain) : CleanStripPatch (E := E) S T a k₀ k₁ := by
  refine
    { width := ε
      width_pos := hε
      domain := U
      open_domain := hU
      contains_strip := hrect
      map := k.map
      smooth := k.smooth.mono hUk
      injective := k.injective.mono hUk
      closed_embedding := ?_
      derivative_injective := fun p hp => k.derivative_injective p (hUk hp)
      first_sheet := fun p hp => k.first_sheet p (hUk hp)
      second_sheet := fun p hp => k.second_sheet p (hUk hp)
      center := k.center
      left_germ := k.left_germ
      right_germ := k.right_germ }
  let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
  let : CompactSpace R :=
    isCompact_iff_compactSpace.mp
      (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
  have hc : Continuous (fun p : R => k.map p) :=
    continuousOn_iff_continuous_domRestrict.mp (k.smooth.continuousOn.mono (hrect.trans hUk))
  apply hc.isClosedEmbedding
  intro p q hpq
  exact Subtype.ext (k.injective (hUk (hrect p.property)) (hUk (hrect q.property)) hpq)

theorem exists_native_shared_corner_strip_pair_dim_two {E M D Z N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace D N]
    [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]
    [T2Space N] [CompactSpace N] [T2Space P] [CompactSpace P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hinjF : Function.Injective F) (hinjG : Function.Injective G)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hiG : ∀ y, Function.Injective (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)) (hdimD : 2 ≤ Module.finrank ℝ D)
    (hdimZ : 2 ≤ Module.finrank ℝ Z)
    (hcodim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      ∀ x y,
        G y = F x →
          Function.Surjective
            ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {x₀ x₁ : N} {y₀ y₁ : P} (hcross₀ : G y₀ = F x₀) (hcross₁ : G y₁ = F x₁) (hxy : x₀ ≠ x₁)
    (γ : Path x₀ x₁) (η : Path y₀ y₁) :
    ∃ f : C(ℝ, N),
      ∃ g : C(ℝ, P),
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f ∧
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) ∞ g ∧
            f 0 = x₀ ∧
              f 1 = x₁ ∧
                g 0 = y₀ ∧
                  g 1 = y₁ ∧
                    Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
                      Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
                        (∀ t ∈ Set.Icc (0 : ℝ) 1,
                            Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t)) ∧
                          (∀ t ∈ Set.Icc (0 : ℝ) 1,
                              Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) g t)) ∧
                            (∀ t ∈ Set.Ioo (0 : ℝ) 1, F (f t) ∉ Set.range G) ∧
                              (∀ t ∈ Set.Ioo (0 : ℝ) 1, G (g t) ∉ Set.range F) ∧
                                Set.range (fun t : unitInterval => F (f t)) ∩
                                      Set.range (fun t : unitInterval => G (g t)) =
                                    {F x₀, F x₁} ∧
                                  ∃ c₀ :
                                    CleanCornerPatch (E := E) (Set.range F) (Set.range G) (F ∘ f)
                                      (G ∘ g),
                                    ∃ c₁ :
                                      CleanCornerPatch (E := E) (Set.range F) (Set.range G)
                                        (fun t => F (f (1 - t))) (fun t => G (g (1 - t))),
                                      ∃ k :
                                        CleanStripPatch (E := E) (Set.range F) (Set.range G)
                                          (F ∘ f) c₀.map c₁.map,
                                        ∃ l :
                                          CleanStripPatch (E := E) (Set.range G) (Set.range F)
                                            (G ∘ g) c₀.swap.map c₁.swap.map,
                                          Nonempty
                                              (StripNormalData
                                                (EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1)))
                                                (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z)))
                                                (E := E) (Set.range F) k.map) ∧
                                            Nonempty
                                                (StripNormalData
                                                  (EuclideanSpace ℝ
                                                    (Fin (Module.finrank ℝ Z - 1)))
                                                  (EuclideanSpace ℝ (Fin (Module.finrank ℝ D)))
                                                  (E := E) (Set.range G) l.map) ∧
                                              (∀ p ∈ k.domain,
                                                  ∀ q ∈ l.domain,
                                                    k.map p = l.map q →
                                                      p = q.swap ∨
                                                        StripCoordinates.reverse p =
                                                          (StripCoordinates.reverse q).swap) ∧
                                                ∀ h : ℝ,
                                                  0 < h →
                                                    Nonempty
                                                      (CleanBigonBoundary (E := E) (Set.range F)
                                                        (Set.range G) (F ∘ f) (G ∘ g) k.map l.map
                                                        h) := by
  have hfinite : (Set.range F ∩ Set.range G).Finite :=
    finite_transverse_intersections hF hG hinjF hinjG hcodim ht
  have hSF : (F ⁻¹' Set.range G).Finite := by
    have hpre : F ⁻¹' (Set.range F ∩ Set.range G) = F ⁻¹' Set.range G := by
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff]
      exact and_iff_right (Set.mem_range_self z)
    rw [← hpre]
    exact hfinite.preimage hinjF.injOn
  have hSG : (G ⁻¹' Set.range F).Finite := by
    have hpre : G ⁻¹' (Set.range F ∩ Set.range G) = G ⁻¹' Set.range F := by
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff]
      exact and_iff_left (Set.mem_range_self z)
    rw [← hpre]
    exact hfinite.preimage hinjG.injOn
  have hy : y₀ ≠ y₁ := by
    intro heq
    apply hxy
    exact hinjF (hcross₀.symm.trans ((congrArg G heq).trans hcross₁))
  obtain ⟨f, hf, hf0, hf1, hembf, hif, havoidf, ρ, hρ, c, hsourceC, hzeroC, _⟩ :=
    exists_tubular_connecting_arc_avoiding_finite_with_global_zero γ hxy hdimD
      (Module.finrank ℝ D - 1) (by omega) hSF
  obtain ⟨g, hg, hg0, hg1, hembg, hig, havoidg, σ, hσ, d, hsourceD, hzeroD, _⟩ :=
    exists_tubular_connecting_arc_avoiding_finite_with_global_zero η hy hdimZ
      (Module.finrank ℝ Z - 1) (by omega) hSG
  have hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro t ht s hs heq
    exact congrArg Subtype.val (hembf.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) heq)
  have hinjg : Set.InjOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht s hs heq
    exact congrArg Subtype.val (hembg.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) heq)
  have hinter :
    Set.range (fun t : unitInterval => F (f t)) ∩ Set.range (fun t : unitInterval => G (g t)) =
      {F x₀, F x₁} := by
    ext w
    constructor
    · rintro ⟨⟨t, rfl⟩, ⟨s, hs⟩⟩
      by_cases ht0 : (t : ℝ) = 0
      · simp only [ht0, hf0]
        exact Set.mem_insert _ _
      by_cases ht1 : (t : ℝ) = 1
      · simp only [ht1, hf1]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      have hti : (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
      exact (havoidf t hti ⟨g s, hs⟩).elim
    · intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨⟨0, congrArg F hf0⟩, ⟨0, (congrArg G hg0).trans hcross₀⟩⟩
      · exact ⟨⟨1, congrArg F hf1⟩, ⟨1, (congrArg G hg1).trans hcross₁⟩⟩
  have hembF := (hF.continuous.isClosedEmbedding hinjF).isEmbedding
  have hembG := (hG.continuous.isClosedEmbedding hinjG).isEmbedding
  have hc₀ : ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1)))) ∈ c.source :=
    hsourceC ⟨by simp, Metric.mem_closedBall_self hρ.le⟩
  have hc₁ : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1)))) ∈ c.source :=
    hsourceC ⟨by simp, Metric.mem_closedBall_self hρ.le⟩
  have hd₀ : ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ Z - 1)))) ∈ d.source :=
    hsourceD ⟨by simp, Metric.mem_closedBall_self hσ.le⟩
  have hd₁ : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ Z - 1)))) ∈ d.source :=
    hsourceD ⟨by simp, Metric.mem_closedBall_self hσ.le⟩
  have hcross₀' : G (g 0) = F (f 0) := by rw [hf0, hg0]; exact hcross₀
  have hcross₁' : G (g 1) = F (f 1) := by rw [hf1, hg1]; exact hcross₁
  have ht₀ := ht (f 0) (g 0) hcross₀'
  have ht₁ := ht (f 1) (g 1) hcross₁'
  have hcoord :
    Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1))) +
        Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ Z - 1))) =
      Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
    omega
  have hcorner₀ :
    Nonempty (CleanCornerPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) (G ∘ g)) := by
    simpa only [zero_add, mul_one, Function.comp_def] using
      nonempty_cleanCornerPatch_of_tubular_arcs hF hG hembF hembG c d hzeroC hzeroD hc₀ hd₀
        hcross₀' hcoord ht₀ (σ := 1) (τ := 1) one_ne_zero one_ne_zero
  have hcorner₁ :
    Nonempty
      (CleanCornerPatch (E := E) (Set.range F) (Set.range G) (fun t => F (f (1 - t)))
        (fun t => G (g (1 - t)))) := by
    simpa only [mul_neg_one, ← sub_eq_add_neg] using
      nonempty_cleanCornerPatch_of_tubular_arcs hF hG hembF hembG c d hzeroC hzeroD hc₁ hd₁
        hcross₁' hcoord ht₁ (σ := -1) (τ := -1) (by norm_num) (by norm_num)
  obtain ⟨c₀⟩ := hcorner₀
  obtain ⟨c₁⟩ := hcorner₁
  obtain ⟨stripF, hnormalF, _⟩ :=
    exists_cleanStripPatch_of_tubular_arc_corners hF hG hembF hiF hf hinjf hif d hzeroD hd₀ hd₁
      hcross₀' hcross₁' ht₀ ht₁ (Module.finrank ℝ D - 1) (by omega) hcodim hdimZ havoidf c₀ c₁
      isOpen_univ (fun _ _ => Set.mem_univ _)
  let DF₀ : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)
  let DF₁ : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)
  let DG₀ : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 0)
  let DG₁ : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 1)
  have ht₀' : Function.Surjective (DG₀.coprod DF₀) :=
    TransverseCoordinates.surjective_coprod_swap DF₀ DG₀ ht₀
  have ht₁' : Function.Surjective (DG₁.coprod DF₁) :=
    TransverseCoordinates.surjective_coprod_swap DF₁ DG₁ ht₁
  have hcodim' : Module.finrank ℝ Z + Module.finrank ℝ D = Module.finrank ℝ E := by omega
  obtain ⟨stripG, hnormalG, _⟩ :=
    exists_cleanStripPatch_of_tubular_arc_corners hG hF hembG hiG hg hinjg hig c hzeroC hc₀ hc₁
      hcross₀'.symm hcross₁'.symm ht₀' ht₁' (Module.finrank ℝ Z - 1) (by omega) hcodim' hdimD
      havoidg c₀.swap c₁.swap isOpen_univ (fun _ _ => Set.mem_univ _)
  have hcoinc :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, (F ∘ f) t = (G ∘ g) s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
    intro t ht s hs heq
    have hmem : F (f t) ∈ ({F x₀, F x₁} : Set M) := by
      rw [← hinter]
      exact ⟨⟨⟨t, ht⟩, rfl⟩, ⟨⟨s, hs⟩, heq.symm⟩⟩
    change F (f t) = F x₀ ∨ F (f t) = F x₁ at hmem
    have h0 : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have h1 : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
    rcases hmem with hleft | hright
    · left
      constructor
      · exact hinjf ht h0 (hinjF (hleft.trans (congrArg F hf0).symm))
      · apply hinjg hs h0
        apply hinjG
        exact heq.symm.trans (hleft.trans ((congrArg G hg0).trans hcross₀).symm)
    · right
      constructor
      · exact hinjf ht h1 (hinjF (hright.trans (congrArg F hf1).symm))
      · apply hinjg hs h1
        apply hinjG
        exact heq.symm.trans (hright.trans ((congrArg G hg1).trans hcross₁).symm)
  obtain ⟨ε', hε', δ', hδ', U', V', hU', hV', hrectU', hrectV', hU'sub, hV'sub, hoverlap⟩ :=
    exists_clean_strip_pair_neighborhoods c₀ c₁ stripF stripG hcoinc
  let k' := stripF.restrict hε' hU' hrectU' hU'sub
  let l' := stripG.restrict hδ' hV' hrectV' hV'sub
  have hoverlap' :
    ∀ p ∈ k'.domain,
      ∀ q ∈ l'.domain,
        k'.map p = l'.map q →
          p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap :=
    hoverlap
  refine
    ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hembf, hembg, hif, hig, havoidf, havoidg, hinter, c₀, c₁,
      k', l', hnormalF, hnormalG, hoverlap', ?_⟩
  intro h hh
  exact nonempty_cleanBigonBoundary hh c₀ c₁ k' l' hoverlap'

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.nonempty_belt_tubularBigon {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, d.LowerLevel),
        ∃ q, g.Homotopic (ContinuousMap.const _ q))
    (g : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) {a b : ℝ → d.UpperLevel}
      {k l : (ℝ × ℝ) → d.UpperLevel} {h : ℝ},
      CleanBigonBoundary (E := RegularLevel.Model E) (Set.range g)
          (Set.range d.surgery.beltSphere) a b k l h →
        Nonempty
          (TubularBigon (E := RegularLevel.Model E) (Set.range g)
            (Set.range d.surgery.beltSphere) a b k l h 3) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro hg a b k l h B
  have hT : IsClosed (Set.range d.surgery.beltSphere) := d.belt_isClosedEmbedding.isClosed_range
  have hnullbelt :=
    d.chart.surgery_beltComplement_circle_nullhomotopies hf d.radius d.radius_pos d.block
      d.lower_regular d.surgery d.oldPiece_eq hindex (by omega) hnull
  exact
    B.nonempty_tubularBigon_of_complement_contractions g hg hT hnullbelt
      (by simp [RegularLevel.Model, hdim]) (by simp [RegularLevel.Model, hdim]) 3
      (by simp [RegularLevel.Model, hdim])

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_belt_tubular_strip_pair {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, d.LowerLevel),
        ∃ q, g.Homotopic (ContinuousMap.const _ q))
    (g : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := d.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          d.surgery.beltSphere y = g x →
            Function.Surjective
              ((mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x).coprod
                (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere y)))
      (x₀ x₁ : Hemisphere.Sphere 2)
      (y₀ y₁ : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates),
      d.surgery.beltSphere y₀ = g x₀ →
        d.surgery.beltSphere y₁ = g x₁ →
          x₀ ≠ x₁ →
            ∃ a b : ℝ → d.UpperLevel,
              a 0 = g x₀ ∧
                a 1 = g x₁ ∧
                  b 0 = g x₀ ∧
                    b 1 = g x₁ ∧
                      ∃ k₀ k₁ l₀ l₁ : (ℝ × ℝ) → d.UpperLevel,
                        ∃ k :
                          CleanStripPatch (E := RegularLevel.Model E) (Set.range g)
                            (Set.range d.surgery.beltSphere) a k₀ k₁,
                          ∃ l :
                            CleanStripPatch (E := RegularLevel.Model E)
                              (Set.range d.surgery.beltSphere) (Set.range g) b l₀ l₁,
                            Nonempty
                                (StripNormalData (EuclideanSpace ℝ (Fin 1))
                                  (EuclideanSpace ℝ (Fin 3)) (E := RegularLevel.Model E)
                                  (Set.range g) k.map) ∧
                              Nonempty
                                  (StripNormalData (EuclideanSpace ℝ (Fin 2))
                                    (EuclideanSpace ℝ (Fin 2)) (E := RegularLevel.Model E)
                                    (Set.range d.surgery.beltSphere) l.map) ∧
                                ∀ h : ℝ,
                                  0 < h →
                                    Nonempty
                                      (TubularBigon (E := RegularLevel.Model E)
                                        (Set.range g) (Set.range d.surgery.beltSphere) a b k.map
                                        l.map h 3) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1 := by
    have hh := d.chart.finrank_negative_add_positive
    omega
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) := ⟨hpos⟩
  intro hg hinj hi ht x₀ x₁ y₀ y₁ hcross₀ hcross₁ hxy
  have hpath₂ : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isPathConnected_sphere (by simp [← Module.finrank_eq_rank]) 0 (by norm_num)
  have hpath₃ : IsPathConnected (Metric.sphere (0 : d.chart.PositiveCoordinates) 1) :=
    isPathConnected_sphere (by rw [← Module.finrank_eq_rank, hpos]; norm_num) 0 (by norm_num)
  let γ : Path x₀ x₁ := (hpath₂.joinedIn x₀ x₀.property x₁ x₁.property).joined_subtype.somePath
  let η : Path y₀ y₁ := (hpath₃.joinedIn y₀ y₀.property y₁ y₁.property).joined_subtype.somePath
  have hG := d.belt_smooth hf 3
  have hiG := d.belt_derivative_injective hf 3
  obtain
    ⟨α, β, -, -, hα₀, hα₁, hβ₀, hβ₁, -, -, -, -, -, -, -, c₀, c₁, k, l, hnK, hnL, -, hboundary⟩ :=
    exists_native_shared_corner_strip_pair_dim_two hg hG hinj
      d.belt_isClosedEmbedding.injective hi hiG (by simp) (by simp)
      (by simp [RegularLevel.Model, hdim]) ht hcross₀ hcross₁ hxy γ η
  refine
    ⟨g ∘ α, d.surgery.beltSphere ∘ β, ?_, ?_, ?_, ?_, c₀.map, c₁.map, c₀.swap.map, c₁.swap.map, k,
      l, ?_, ?_, ?_⟩
  · change g (α 0) = g x₀
    rw [hα₀]
  · change g (α 1) = g x₁
    rw [hα₁]
  · change d.surgery.beltSphere (β 0) = g x₀
    rw [hβ₀, hcross₀]
  · change d.surgery.beltSphere (β 1) = g x₁
    rw [hβ₁, hcross₁]
  · have transport (m n : ℕ) (hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) - 1 = m)
      (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = n) :
      Nonempty
        (StripNormalData (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)) (E :=
          RegularLevel.Model E) (Set.range g) k.map) := by
      subst m
      subst n
      exact hnK
    exact transport 1 3 (by simp) (by simp)
  · have transport (m n : ℕ) (hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 = m)
      (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = n) :
      Nonempty
        (StripNormalData (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)) (E :=
          RegularLevel.Model E) (Set.range d.surgery.beltSphere) l.map) := by
      subst m
      subst n
      exact hnL
    exact transport 2 2 (by simp) (by simp)
  · intro h hh
    obtain ⟨B⟩ := hboundary h hh
    exact d.nonempty_belt_tubularBigon hf hdim hindex hnull g hg B

def FiberRestriction.embed {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : U →L[ℝ] V) : (X × U) →L[ℝ] (X × V) :=
  (ContinuousLinearMap.id ℝ X).prodMap i

def FiberRestriction.project {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : V →L[ℝ] U) : (X × V) →L[ℝ] (X × U) :=
  (ContinuousLinearMap.id ℝ X).prodMap r

theorem FiberRestriction.project_embed {X U V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i)
    (z : X × U) : project r (embed i z) = z :=
  Prod.ext rfl (hi z.2)

theorem FiberRestriction.embed_project_of_normal {X U V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i) {z : X × V}
    {w : X × U} (hz : z.2 = i w.2) : embed i (project r z) = z := by
  apply Prod.ext
  · rfl
  · change i (r z.2) = z.2
    rw [hz, hi]

def FiberRestriction.restrict {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i)
    (d : Diffeomorph 𝓘(ℝ, X × V) 𝓘(ℝ, X × V) (X × V) (X × V) ∞) (hnormal : ∀ z, (d z).2 = z.2) :
    Diffeomorph 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) (X × U) (X × U) ∞
    where
  toEquiv :=
    { toFun := fun z => project r (d (embed i z))
      invFun := fun z => project r (d.symm (embed i z))
      left_inv := by
        intro z
        have hfix := embed_project_of_normal i r hi (w := z) (hnormal (embed i z))
        change project r (d.symm (embed i (project r (d (embed i z))))) = z
        rw [hfix, d.symm_apply_apply, project_embed i r hi]
      right_inv := by
        intro z
        have hnormalInv : (d.symm (embed i z)).2 = i z.2 := by
          have he := hnormal (d.symm (embed i z))
          rw [d.apply_symm_apply] at he
          exact he.symm
        have hfix := embed_project_of_normal i r hi (w := z) hnormalInv
        change project r (d (embed i (project r (d.symm (embed i z))))) = z
        rw [hfix, d.apply_symm_apply, project_embed i r hi] }
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) ∞ (fun z => project r (d (embed i z)))
    exact (project r).contDiff.contMDiff.comp (d.contMDiff.comp (embed i).contDiff.contMDiff)
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) ∞ (fun z => project r (d.symm (embed i z)))
    exact (project r).contDiff.contMDiff.comp (d.symm.contMDiff.comp (embed i).contDiff.contMDiff)

theorem SmallPerturbation.lipschitzWith_slice {E : Type*} [NormedAddCommGroup E]
    {β : ℝ × E → ℝ} {k : ℝ≥0} (hβ : LipschitzWith k β) (t : ℝ) :
    LipschitzWith k (fun x : E => β (t, x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    Dist.dist (β (t, x)) (β (t, y)) ≤ (k : ℝ) * Dist.dist (t, x) (t, y) := hβ.dist_le_mul _ _
    _ = (k : ℝ) * Dist.dist x y := by
      rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ Dist.dist x y)]

theorem SmallPerturbation.exists_uniform_radius_bumpTranslation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : ℝ × E → ℝ}
    (hs : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ t : ℝ,
          ∀ a : E,
            ‖a‖ < ε →
              ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
                (∀ x, d x = x + β (t, x) • a) ∧ ∀ x ∉ tsupport (fun y : E => β (t, y)), d x = x :=
  by
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hs (by simp)
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  refine ⟨((k : ℝ) + 1)⁻¹, inv_pos.mpr hkpos, ?_⟩
  intro t a ha
  have hmul : ((k : ℝ) + 1) * ‖a‖ < 1 := by
    calc
      ((k : ℝ) + 1) * ‖a‖ < ((k : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ := mul_lt_mul_of_pos_left ha hkpos
      _ = 1 := mul_inv_cancel₀ hkpos.ne'
  have hsmall : k * ‖a‖₊ < 1 := by
    have hr : (k : ℝ) * ‖a‖ < 1 := by nlinarith [norm_nonneg a]
    exact hr
  have hslice : ContDiff ℝ ∞ (fun x : E => β (t, x)) :=
    hs.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨bumpTranslation hslice (lipschitzWith_slice hk t) a hsmall, fun _ => rfl, ?_⟩
  intro x hx
  apply bumpTranslation_eq_of_zero
  by_contra hne
  exact hx (subset_tsupport (fun y : E => β (t, y)) hne)

def SmallPerturbation.composeFamily {E : Type*} (B : ℕ → ℝ × E → E) : ℕ → ℝ × E → E
  | 0, p => p.2
  | n + 1, p => B n (p.1, composeFamily B n p)

theorem SmallPerturbation.contDiff_composeFamily {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : ℕ → ℝ × E → E} (hB : ∀ i, ContDiff ℝ ∞ (B i)) (n : ℕ) :
    ContDiff ℝ ∞ (composeFamily B n) := by
  induction n with
  | zero => exact contDiff_snd
  | succ n ih => exact (hB n).comp (contDiff_fst.prodMk ih)

theorem SmallPerturbation.composeFamily_zero {E : Type*} {B : ℕ → ℝ × E → E}
    (hB : ∀ i x, B i (0, x) = x) (n : ℕ) (x : E) : composeFamily B n (0, x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hB n _).trans ih

theorem SmallPerturbation.composeFamily_fixed {E : Type*} {B : ℕ → ℝ × E → E} {C : Set E}
    (hB : ∀ i t x, x ∉ C → B i (t, x) = x) (n : ℕ) (t : ℝ) {x : E} (hx : x ∉ C) :
    composeFamily B n (t, x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change B n (t, composeFamily B n (t, x)) = x
    rw [ih]
    exact hB n t x hx

theorem SmallPerturbation.composeFamily_preserves {E : Type*} {F : Type*}
    {B : ℕ → ℝ × E → E} {f : E → F} (hB : ∀ i t x, f (B i (t, x)) = f x) (n : ℕ) (t : ℝ) (x : E) :
    f (composeFamily B n (t, x)) = f x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hB n t _).trans ih

theorem SmallPerturbation.exists_diffeomorph_composeFamily {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : ℕ → ℝ × E → E}
    (hB : ∀ i t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = B i (t, x)) (n : ℕ) (t : ℝ) :
    ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = composeFamily B n (t, x) := by
  induction n with
  | zero => exact ⟨Diffeomorph.refl 𝓘(ℝ, E) E ∞, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    obtain ⟨e, he⟩ := hB n t
    refine ⟨d.trans e, ?_⟩
    intro x
    change e (d x) = B n (t, composeFamily B n (t, x))
    rw [he, hd]

def WhitneyPairModel.scaledBigonEmbedding (r : ℝ) (p : ℝ × ℝ) : Space :=
  bigonEmbedding (r * p.1, r ^ 2 * p.2)

theorem WhitneyPairModel.scaledBigonEmbedding_one (p : ℝ × ℝ) :
    scaledBigonEmbedding 1 p = bigonEmbedding p := by
  simp only [scaledBigonEmbedding, one_mul, one_pow, Prod.eta]

theorem WhitneyPairModel.continuous_scaledBigonEmbedding :
    Continuous (fun z : ℝ × (ℝ × ℝ) => scaledBigonEmbedding z.1 z.2) := by
  unfold scaledBigonEmbedding bigonEmbedding
  fun_prop

theorem WhitneyPairModel.exists_scaled_bigon_in_open {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : Set.MapsTo bigonEmbedding (bigon h) U) :
    ∃ r : ℝ, 1 < r ∧ Set.MapsTo (scaledBigonEmbedding r) (bigon h) U := by
  have hnear : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ bigon h, scaledBigonEmbedding r p ∈ U := by
    apply (isCompact_bigon hh).eventually_forall_of_forall_eventually
    intro p hp
    apply (continuous_scaledBigonEmbedding.continuousAt (x := (1, p))).preimage_mem_nhds
    apply hU.mem_nhds
    simpa only [scaledBigonEmbedding_one] using hKU hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hrball : (1 + ε / 2 : ℝ) ∈ Metric.ball 1 ε := by
    change Dist.dist (1 + ε / 2) 1 < ε
    rw [Real.dist_eq]
    have heq : 1 + ε / 2 - 1 = ε / 2 := by ring
    rw [heq, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact ⟨1 + ε / 2, by linarith, fun p hp => hball hrball p hp⟩

theorem WhitneyPairModel.enlarged_cap_parametrization {h r : ℝ} (hr : 0 < r) {p : ℝ × ℝ}
    (hp : 0 ≤ p.2 ∧ h * p.1 ^ 2 + p.2 ≤ h * r ^ 2) :
    ∃ q ∈ bigon h, scaledBigonEmbedding r q = bigonEmbedding p := by
  let q : ℝ × ℝ := (p.1 / r, p.2 / r ^ 2)
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hcalc : h * (p.1 / r) ^ 2 + p.2 / r ^ 2 = (h * p.1 ^ 2 + p.2) / r ^ 2 := by field_simp
  have hq : q ∈ bigon h := by
    refine ⟨div_nonneg hp.1 hr2.le, ?_⟩
    change h * (p.1 / r) ^ 2 + p.2 / r ^ 2 ≤ h
    rw [hcalc]
    exact (div_le_iff₀ hr2).mpr hp.2
  refine ⟨q, hq, ?_⟩
  apply congrArg bigonEmbedding
  apply Prod.ext
  · change r * (p.1 / r) = p.1
    field_simp
  · change r ^ 2 * (p.2 / r ^ 2) = p.2
    field_simp

def WhitneyPairModel.verticalGraph (B : ℝ → ℝ) (t s : ℝ) : Space :=
  ((s, t * B s), 0)

theorem WhitneyPairModel.exists_supported_graph_height {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : Set.MapsTo bigonEmbedding (bigon h) U) :
    ∃ B : ℝ → ℝ,
      ContDiff ℝ ∞ B ∧
        HasCompactSupport B ∧
          (∀ s, 0 ≤ B s) ∧
            (∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < B s) ∧
              ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ tsupport B, verticalGraph B t s ∈ U := by
  obtain ⟨r, hr, hscaled⟩ := exists_scaled_bigon_in_open hh hU hKU
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  let α : ContDiffBump (0 : ℝ) :=
    { rIn := 1
      rOut := r
      rIn_pos := zero_lt_one
      rIn_lt_rOut := hr }
  let B : ℝ → ℝ := fun s => α s * (h * (r ^ 2 - s ^ 2))
  have hB : ContDiff ℝ ∞ B := α.contDiff.mul (by fun_prop)
  have hcompact : HasCompactSupport B := α.hasCompactSupport.mul_right
  have hsupp : tsupport B ⊆ tsupport (α : ℝ → ℝ) := by
    apply closure_mono
    intro s hs hα
    apply hs
    change α s * (h * (r ^ 2 - s ^ 2)) = 0
    rw [hα, MulZeroClass.zero_mul]
  have hbound : ∀ s ∈ tsupport B, |s| ≤ r := by
    intro s hs
    have hx := hsupp hs
    rw [α.tsupport_eq] at hx
    change Dist.dist s 0 ≤ r at hx
    simpa only [Real.dist_eq, sub_zero] using hx
  have hheight {s : ℝ} (hs : |s| ≤ r) : 0 ≤ h * (r ^ 2 - s ^ 2) := by
    have hsq : s ^ 2 ≤ r ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) hrpos.le).mpr hs
    exact mul_nonneg hh.le (sub_nonneg.mpr hsq)
  have hnonneg : ∀ s, 0 ≤ B s := by
    intro s
    by_cases hs : α s = 0
    · simp only [B, hs, MulZeroClass.zero_mul, le_refl]
    have hmem : s ∈ Function.support α := hs
    rw [α.support_eq] at hmem
    have hsr : |s| ≤ r := by
      have hl : |s| < r := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hmem
      exact hl.le
    exact mul_nonneg α.nonneg (hheight hsr)
  refine ⟨B, hB, hcompact, hnonneg, ?_, ?_⟩
  · intro s hs
    have hα : α s = 1 :=
      α.one_of_mem_closedBall
        (by
          change Dist.dist s 0 ≤ 1
          simpa only [Real.dist_eq, sub_zero] using hs)
    change h * (1 - s ^ 2) < α s * (h * (r ^ 2 - s ^ 2))
    rw [hα, one_mul]
    have hgap : 0 < h * (r ^ 2 - 1) := mul_pos hh (by nlinarith [sq_nonneg (r - 1)])
    nlinarith
  · intro t ht s hs
    have hts : t * α s ≤ 1 := by
      calc
        t * α s ≤ 1 * α s := mul_le_mul_of_nonneg_right ht.2 α.nonneg
        _ ≤ 1 := by simpa only [one_mul] using (α.le_one (x := s))
    have hy : t * B s ≤ h * (r ^ 2 - s ^ 2) := by
      calc
        t * B s = (t * α s) * (h * (r ^ 2 - s ^ 2)) := by dsimp [B]; ring
        _ ≤ h * (r ^ 2 - s ^ 2) := mul_le_of_le_one_left (hheight (hbound s hs)) hts
    have hcap : 0 ≤ t * B s ∧ h * s ^ 2 + t * B s ≤ h * r ^ 2 :=
      ⟨mul_nonneg ht.1 (hnonneg s), by nlinarith⟩
    obtain ⟨q, hq, heq⟩ := enlarged_cap_parametrization (h := h) (p := (s, t * B s)) hrpos hcap
    have hmem := hscaled hq
    rw [heq] at hmem
    exact hmem

def WhitneyPairModel.graphTrace (B : ℝ → ℝ) : Set (ℝ × Space) :=
  (fun p : ℝ × ℝ => (p.1, verticalGraph B p.1 p.2)) '' (Set.Icc (0 : ℝ) 1 ×ˢ tsupport B)

theorem WhitneyPairModel.isCompact_graphTrace {B : ℝ → ℝ} (hB : Continuous B)
    (hcompact : HasCompactSupport B) : IsCompact (graphTrace B) := by
  apply (CompactIccSpace.isCompact_Icc.prod hcompact.isCompact).image
  unfold verticalGraph
  fun_prop

theorem WhitneyPairModel.exists_graph_motion_cutoff {B : ℝ → ℝ} (hB : ContDiff ℝ ∞ B)
    (hcompact : HasCompactSupport B) (hnonneg : ∀ s, 0 ≤ B s) {U : Set Space} (hU : IsOpen U)
    (htrace : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ tsupport B, verticalGraph B t s ∈ U) :
    ∃ β : ℝ × Space → ℝ,
      ContDiff ℝ ∞ β ∧
        HasCompactSupport β ∧
          tsupport β ⊆ Prod.snd ⁻¹' U ∧
            (∀ p, 0 ≤ β p) ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s : ℝ, β (t, verticalGraph B t s) = B s :=
  by
  have hCU : graphTrace B ⊆ Prod.snd ⁻¹' U := by
    rintro _ ⟨p, hp, rfl⟩
    exact htrace p.1 hp.1 p.2 hp.2
  obtain ⟨η, hη, hηcompact, hηsupport, hηone, hηrange⟩ :=
    exists_compact_smooth_cutoff (isCompact_graphTrace hB.continuous hcompact)
      (hU.preimage continuous_snd) hCU
  let β : ℝ × Space → ℝ := fun p => η p * B p.2.1.1
  have hβ : ContDiff ℝ ∞ β := hη.mul (hB.comp (by fun_prop))
  have hβcompact : HasCompactSupport β := hηcompact.mul_right
  have hsupp : tsupport β ⊆ tsupport η := by
    apply closure_mono
    intro p hp hηp
    apply hp
    change η p * B p.2.1.1 = 0
    rw [hηp, MulZeroClass.zero_mul]
  refine
    ⟨β, hβ, hβcompact, hsupp.trans hηsupport, fun p => mul_nonneg (hηrange p).1 (hnonneg _), ?_⟩
  intro t ht s
  by_cases hs : B s = 0
  · change η (t, verticalGraph B t s) * B s = B s
    rw [hs, MulZeroClass.mul_zero]
  have hpoint : (t, verticalGraph B t s) ∈ graphTrace B :=
    ⟨(t, s), ⟨ht, subset_tsupport B hs⟩, rfl⟩
  have hηpoint : η (t, verticalGraph B t s) = 1 := hηone.self_of_nhdsSet _ hpoint
  change η (t, verticalGraph B t s) * B s = B s
  rw [hηpoint, one_mul]

structure WhitneyPairModel.GraphMotionData (h : ℝ) (U : Set Space) where
  height : ℝ → ℝ
  smooth_height : ContDiff ℝ ∞ height
  compact_height : HasCompactSupport height
  nonneg_height : ∀ s, 0 ≤ height s
  above : ∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < height s
  trace_source : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ tsupport height, verticalGraph height t s ∈ U
  cutoff : ℝ × Space → ℝ
  smooth_cutoff : ContDiff ℝ ∞ cutoff
  compact_cutoff : HasCompactSupport cutoff
  support_cutoff : tsupport cutoff ⊆ Prod.snd ⁻¹' U
  nonneg_cutoff : ∀ p, 0 ≤ cutoff p
  tracking : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s, cutoff (t, verticalGraph height t s) = height s

theorem WhitneyPairModel.nonempty_graphMotionData {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : Set.MapsTo bigonEmbedding (bigon h) U) :
    Nonempty (GraphMotionData h U) := by
  obtain ⟨B, hB, hcompact, hnonneg, habove, htrace⟩ := exists_supported_graph_height hh hU hKU
  obtain ⟨β, hβ, hβcompact, hβsupport, hβnonneg, hβtrack⟩ :=
    exists_graph_motion_cutoff hB hcompact hnonneg hU htrace
  exact
    ⟨{  height := B
        smooth_height := hB
        compact_height := hcompact
        nonneg_height := hnonneg
        above := habove
        trace_source := htrace
        cutoff := β
        smooth_cutoff := hβ
        compact_cutoff := hβcompact
        support_cutoff := hβsupport
        nonneg_cutoff := hβnonneg
        tracking := hβtrack }⟩

def WhitneyPairModel.verticalVector (δ : ℝ) : Space :=
  ((0, δ), 0)

theorem WhitneyPairModel.norm_verticalVector {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖verticalVector δ‖ = δ := by
  simp [verticalVector, Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hδ, hδ]

def WhitneyPairModel.graphStep (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (p : ℝ × Space) :
    Space :=
  p.2 + β ((i : ℝ) * δ, p.2) • (Real.smoothTransition p.1 • verticalVector δ)

theorem WhitneyPairModel.contDiff_graphStep {β : ℝ × Space → ℝ} (hβ : ContDiff ℝ ∞ β)
    (δ : ℝ) (i : ℕ) : ContDiff ℝ ∞ (graphStep β δ i) := by
  have hθ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact
    contDiff_snd.add
      ((hβ.comp (contDiff_const.prodMk contDiff_snd)).smul
        ((hθ.comp contDiff_fst).smul contDiff_const))

theorem WhitneyPairModel.graphStep_zero (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (z : Space) :
    graphStep β δ i (0, z) = z := by
  simp only [graphStep, Real.smoothTransition.zero, zero_smul, smul_zero, add_zero]

theorem WhitneyPairModel.graphStep_horizontal (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ)
    (z : Space) : (graphStep β δ i (t, z)).1.1 = z.1.1 := by simp [graphStep, verticalVector]

theorem WhitneyPairModel.graphStep_normal (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ)
    (z : Space) : (graphStep β δ i (t, z)).2 = z.2 := by simp [graphStep, verticalVector]

theorem WhitneyPairModel.graphStep_fixed (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ)
    {z : Space} (hz : z ∉ Prod.snd '' tsupport β) : graphStep β δ i (t, z) = z := by
  have hzero : β ((i : ℝ) * δ, z) = 0 := by
    by_contra hne
    exact hz ⟨((i : ℝ) * δ, z), subset_tsupport β hne, rfl⟩
  simp only [graphStep, hzero, zero_smul, add_zero]

theorem WhitneyPairModel.exists_radius_graphStep {β : ℝ × Space → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ δ : ℝ,
          0 ≤ δ →
            δ < ε →
              ∀ i : ℕ,
                ∀ t : ℝ,
                  ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞,
                    ∀ z, d z = graphStep β δ i (t, z) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    SmallPerturbation.exists_uniform_radius_bumpTranslation hβ hcompact
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε i t
  have hnorm : ‖Real.smoothTransition t • verticalVector δ‖ ≤ δ := by
    rw [norm_smul, norm_verticalVector hδ, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact mul_le_of_le_one_left hδ (Real.smoothTransition.le_one t)
  obtain ⟨d, hd, _⟩ :=
    hsmall ((i : ℝ) * δ) (Real.smoothTransition t • verticalVector δ) (hnorm.trans_lt hδε)
  exact ⟨d, hd⟩

theorem WhitneyPairModel.graphStep_tracking {h : ℝ} {U : Set Space}
    (g : GraphMotionData h U) {δ : ℝ} {i : ℕ} (hi : (i : ℝ) * δ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    graphStep g.cutoff δ i (1, verticalGraph g.height ((i : ℝ) * δ) s) =
      verticalGraph g.height (((i : ℝ) + 1) * δ) s := by
  rw [graphStep, g.tracking _ hi, Real.smoothTransition.one, one_smul]
  ext <;> simp [verticalGraph, verticalVector, smul_eq_mul]
  ring

structure WhitneyPairModel.GraphMotion {h : ℝ} {U : Set Space}
    (g : GraphMotionData h U) where
  support : Set Space
  compact_support : IsCompact support
  support_subset : support ⊆ U
  family : ℝ × Space → Space
  smooth : ContDiff ℝ ∞ family
  initial : ∀ z, family (0, z) = z
  diffeomorph :
    ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞, ∀ z, d z = family (t, z)
  fixed : ∀ t z, z ∉ support → family (t, z) = z
  horizontal : ∀ t z, (family (t, z)).1.1 = z.1.1
  normal : ∀ t z, (family (t, z)).2 = z.2
  tracking : ∀ s, family (1, firstSheet (s, 0)) = verticalGraph g.height 1 s

theorem WhitneyPairModel.GraphMotionData.nonempty_graphMotion {h : ℝ}
    {U : Set WhitneyPairModel.Space} (g : WhitneyPairModel.GraphMotionData h U) :
    Nonempty (WhitneyPairModel.GraphMotion g) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    WhitneyPairModel.exists_radius_graphStep g.smooth_cutoff g.compact_cutoff
  obtain ⟨N, hN, hNsmall⟩ := Real.exists_nat_pos_inv_lt hε
  let δ : ℝ := (N : ℝ)⁻¹
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hδ : 0 ≤ δ := (inv_pos.mpr hNreal).le
  have htotal : (N : ℝ) * δ = 1 := mul_inv_cancel₀ hNreal.ne'
  let B : ℕ → ℝ × WhitneyPairModel.Space → WhitneyPairModel.Space :=
    WhitneyPairModel.graphStep g.cutoff δ
  let A : ℝ × WhitneyPairModel.Space → WhitneyPairModel.Space :=
    SmallPerturbation.composeFamily B N
  have htrack :
    ∀ j ≤ N,
      ∀ s,
        SmallPerturbation.composeFamily B j (1, WhitneyPairModel.firstSheet (s, 0)) =
          WhitneyPairModel.verticalGraph g.height ((j : ℝ) * δ) s := by
    intro j
    induction j with
    | zero =>
      intro _ s
      simp [SmallPerturbation.composeFamily, WhitneyPairModel.firstSheet,
        WhitneyPairModel.verticalGraph]
    | succ j ih =>
      intro hj s
      have hjN : j ≤ N := Nat.le_of_succ_le hj
      have htime : (j : ℝ) * δ ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨mul_nonneg (Nat.cast_nonneg j) hδ, ?_⟩
        calc
          (j : ℝ) * δ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjN) hδ
          _ = 1 := htotal
      change
        WhitneyPairModel.graphStep g.cutoff δ j
            (1,
              SmallPerturbation.composeFamily B j
                (1, WhitneyPairModel.firstSheet (s, 0))) =
          _
      rw [ih hjN s, WhitneyPairModel.graphStep_tracking g htime s, Nat.cast_add,
        Nat.cast_one]
  refine
    ⟨{  support := Prod.snd '' tsupport g.cutoff
        compact_support := g.compact_cutoff.isCompact.image continuous_snd
        support_subset := ?_
        family := A
        smooth :=
          SmallPerturbation.contDiff_composeFamily
            (fun i => WhitneyPairModel.contDiff_graphStep g.smooth_cutoff δ i) N
        initial :=
          SmallPerturbation.composeFamily_zero
            (WhitneyPairModel.graphStep_zero g.cutoff δ) N
        diffeomorph :=
          SmallPerturbation.exists_diffeomorph_composeFamily (hsmall δ hδ hNsmall) N
        fixed := fun t z hz =>
          SmallPerturbation.composeFamily_fixed
            (fun i t _ hz => WhitneyPairModel.graphStep_fixed g.cutoff δ i t hz) N t hz
        horizontal := fun t z =>
          SmallPerturbation.composeFamily_preserves (B := B) (f :=
            fun z : WhitneyPairModel.Space => z.1.1)
            (WhitneyPairModel.graphStep_horizontal g.cutoff δ) N t z
        normal := fun t z =>
          SmallPerturbation.composeFamily_preserves (B := B) (f :=
            fun z : WhitneyPairModel.Space => z.2)
            (WhitneyPairModel.graphStep_normal g.cutoff δ) N t z
        tracking := ?_ }⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact g.support_cutoff hp
  · intro s
    change
      SmallPerturbation.composeFamily B N (1, WhitneyPairModel.firstSheet (s, 0)) = _
    rw [htrack N le_rfl s, htotal]

theorem WhitneyPairModel.GraphMotion.firstSheet_ne_secondSheet {h : ℝ}
    {U : Set WhitneyPairModel.Space} {g : WhitneyPairModel.GraphMotionData h U}
    (a : WhitneyPairModel.GraphMotion g) (hh : 0 < h) (p q : WhitneyPairModel.Sheet) :
    a.family (1, WhitneyPairModel.firstSheet p) ≠ WhitneyPairModel.secondSheet h q := by
  intro heq
  have hst : p.1 = q.1 := by
    have he := congrArg (fun z : WhitneyPairModel.Space => z.1.1) heq
    rw [a.horizontal] at he
    exact he
  have hu : p.2 = 0 := by
    have he := congrArg (fun z : WhitneyPairModel.Space => z.2) heq
    rw [a.normal] at he
    exact congrArg Prod.fst he
  have hp : p = (q.1, 0) := Prod.ext hst hu
  rw [hp, a.tracking] at heq
  have ht : g.height q.1 = h * (1 - q.1 ^ 2) := by
    simpa only [WhitneyPairModel.verticalGraph, WhitneyPairModel.secondSheet,
      one_mul] using congrArg (fun z : WhitneyPairModel.Space => z.1.2) heq
  have hheight : 0 ≤ h * (1 - q.1 ^ 2) := ht ▸ g.nonneg_height q.1
  have hlevel : 0 ≤ 1 - q.1 ^ 2 := nonneg_of_mul_nonneg_right hheight hh
  have habs : |q.1| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (q.1 + 1)], by nlinarith [sq_nonneg (q.1 - 1)]⟩
  exact (g.above q.1 habs).ne ht.symm

abbrev RankThreeWhitneyModel.Lower :=
  EuclideanSpace ℝ (Fin 1)

abbrev RankThreeWhitneyModel.Upper :=
  EuclideanSpace ℝ (Fin 2)

abbrev RankThreeWhitneyModel.Space :=
  (ℝ × ℝ) × (Lower × Upper)

abbrev RankThreeWhitneyModel.LowerSheet :=
  ℝ × Lower

abbrev RankThreeWhitneyModel.UpperSheet :=
  ℝ × Upper

def RankThreeWhitneyModel.firstSheet (p : LowerSheet) : Space :=
  ((p.1, 0), (p.2, 0))

def RankThreeWhitneyModel.secondSheet (h : ℝ) (p : UpperSheet) : Space :=
  ((p.1, h * (1 - p.1 ^ 2)), (0, p.2))

theorem RankThreeWhitneyModel.contDiff_firstSheet : ContDiff ℝ ∞ firstSheet := by
  unfold firstSheet
  fun_prop

theorem RankThreeWhitneyModel.contDiff_secondSheet (h : ℝ) : ContDiff ℝ ∞ (secondSheet h) :=
  by
  unfold secondSheet
  fun_prop

def RankThreeWhitneyModel.firstSheetDerivative : LowerSheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Lower).prod 0).prod ((ContinuousLinearMap.snd ℝ ℝ Lower).prod 0)

def RankThreeWhitneyModel.secondSheetDerivative (h s : ℝ) : UpperSheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Upper).prod
        ((-2 * h * s) • ContinuousLinearMap.fst ℝ ℝ Upper)).prod
    ((0 : UpperSheet →L[ℝ] Lower).prod (ContinuousLinearMap.snd ℝ ℝ Upper))

theorem RankThreeWhitneyModel.firstSheetDerivative_apply (p : LowerSheet) :
    firstSheetDerivative p = ((p.1, 0), (p.2, 0)) :=
  rfl

theorem RankThreeWhitneyModel.secondSheetDerivative_apply (h s : ℝ) (p : UpperSheet) :
    secondSheetDerivative h s p = ((p.1, (-2 * h * s) * p.1), (0, p.2)) :=
  rfl

theorem RankThreeWhitneyModel.hasFDerivAt_firstSheet (p : LowerSheet) :
    HasFDerivAt firstSheet firstSheetDerivative p :=
  firstSheetDerivative.hasFDerivAt

theorem RankThreeWhitneyModel.hasFDerivAt_secondSheet (h : ℝ) (p : UpperSheet) :
    HasFDerivAt (secondSheet h) (secondSheetDerivative h p.1) p := by
  have hs := (ContinuousLinearMap.fst ℝ ℝ Upper).hasFDerivAt (x := p)
  have hu := (ContinuousLinearMap.snd ℝ ℝ Upper).hasFDerivAt (x := p)
  have ht := ((hasFDerivAt_const (1 : ℝ) p).sub (hs.pow 2)).const_mul h
  have hd := (hs.prodMk ht).prodMk ((hasFDerivAt_const (0 : Lower) p).prodMk hu)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [secondSheetDerivative, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', zero_apply, sub_apply, smul_apply, smul_eq_mul]
  congr 2
  norm_num [two_smul]
  ring

def RankThreeWhitneyModel.lowerSplit : (Lower × ℝ) ≃L[ℝ] WhitneyPairModel.Plane :=
  ContinuousLinearEquiv.ofFinrankEq
    (by simp [Lower, WhitneyPairModel.Plane, Module.finrank_prod])

def RankThreeWhitneyModel.lowerInclude : Lower →L[ℝ] WhitneyPairModel.Plane :=
  lowerSplit.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ Lower ℝ)

def RankThreeWhitneyModel.lowerProject : WhitneyPairModel.Plane →L[ℝ] Lower :=
  (ContinuousLinearMap.fst ℝ Lower ℝ).comp lowerSplit.symm.toContinuousLinearMap

theorem RankThreeWhitneyModel.lowerProject_include (u : Lower) :
    lowerProject (lowerInclude u) = u := by
  change (lowerSplit.symm (lowerSplit (u, 0))).1 = u
  rw [lowerSplit.symm_apply_apply]

def RankThreeWhitneyModel.normalInclude :
    (Lower × Upper) →L[ℝ] (WhitneyPairModel.Plane × WhitneyPairModel.Plane) :=
  lowerInclude.prodMap (ContinuousLinearMap.id ℝ Upper)

def RankThreeWhitneyModel.normalProject :
    (WhitneyPairModel.Plane × WhitneyPairModel.Plane) →L[ℝ] (Lower × Upper) :=
  lowerProject.prodMap (ContinuousLinearMap.id ℝ Upper)

theorem RankThreeWhitneyModel.normalProject_include :
    Function.LeftInverse normalProject normalInclude := fun z =>
  Prod.ext (lowerProject_include z.1) rfl

def RankThreeWhitneyModel.expand : Space →L[ℝ] WhitneyPairModel.Space :=
  FiberRestriction.embed normalInclude

def RankThreeWhitneyModel.collapse : WhitneyPairModel.Space →L[ℝ] Space :=
  FiberRestriction.project normalProject

theorem RankThreeWhitneyModel.collapse_expand (z : Space) : collapse (expand z) = z :=
  FiberRestriction.project_embed normalInclude normalProject normalProject_include z

theorem RankThreeWhitneyModel.expand_zero (p : ℝ × ℝ) : expand (p, 0) = (p, 0) :=
  Prod.ext rfl normalInclude.map_zero

theorem RankThreeWhitneyModel.collapse_zero (p : ℝ × ℝ) : collapse (p, 0) = (p, 0) :=
  Prod.ext rfl normalProject.map_zero

def RankThreeWhitneyModel.verticalGraph (B : ℝ → ℝ) (t s : ℝ) : Space :=
  ((s, t * B s), 0)

theorem RankThreeWhitneyModel.collapse_verticalGraph (B : ℝ → ℝ) (t s : ℝ) :
    collapse (WhitneyPairModel.verticalGraph B t s) = verticalGraph B t s :=
  collapse_zero _

structure RankThreeWhitneyModel.GraphMotion (h : ℝ) (U : Set Space) where
  height : ℝ → ℝ
  nonneg_height : ∀ s, 0 ≤ height s
  above : ∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < height s
  support : Set Space
  compact_support : IsCompact support
  support_subset : support ⊆ U
  family : ℝ × Space → Space
  smooth : ContDiff ℝ ∞ family
  initial : ∀ z, family (0, z) = z
  diffeomorph :
    ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞, ∀ z, d z = family (t, z)
  fixed : ∀ t z, z ∉ support → family (t, z) = z
  horizontal : ∀ t z, (family (t, z)).1.1 = z.1.1
  normal : ∀ t z, (family (t, z)).2 = z.2
  tracking : ∀ s, family (1, firstSheet (s, 0)) = verticalGraph height 1 s

theorem RankThreeWhitneyModel.nonempty_graphMotion {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : ∀ p ∈ WhitneyPairModel.bigon h, (p, (0 : Lower × Upper)) ∈ U) :
    Nonempty (GraphMotion h U) := by
  let V : Set WhitneyPairModel.Space := collapse ⁻¹' U
  have hV : IsOpen V := hU.preimage collapse.continuous
  have hKV :
    Set.MapsTo WhitneyPairModel.bigonEmbedding (WhitneyPairModel.bigon h) V := by
    intro p hp
    change collapse (p, 0) ∈ U
    rw [collapse_zero]
    exact hKU p hp
  obtain ⟨g⟩ := WhitneyPairModel.nonempty_graphMotionData hh hV hKV
  obtain ⟨a⟩ := g.nonempty_graphMotion
  let A : ℝ × Space → Space := fun p => collapse (a.family (p.1, expand p.2))
  have hA : ContDiff ℝ ∞ A :=
    collapse.contDiff.comp
      (a.smooth.comp (contDiff_fst.prodMk (expand.contDiff.comp contDiff_snd)))
  refine
    ⟨{  height := g.height
        nonneg_height := g.nonneg_height
        above := g.above
        support := collapse '' a.support
        compact_support := a.compact_support.image collapse.continuous
        support_subset := ?_
        family := A
        smooth := hA
        initial := ?_
        diffeomorph := ?_
        fixed := ?_
        horizontal := ?_
        normal := ?_
        tracking := ?_ }⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact a.support_subset hz
  · intro z
    change collapse (a.family (0, expand z)) = z
    rw [a.initial, collapse_expand]
  · intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hn : ∀ z, (d z).2 = z.2 := by
      intro z
      rw [hd]
      exact a.normal t z
    refine
      ⟨FiberRestriction.restrict normalInclude normalProject normalProject_include d hn, ?_⟩
    intro z
    change collapse (d (expand z)) = collapse (a.family (t, expand z))
    rw [hd]
  · intro t z hz
    have hz' : expand z ∉ a.support := fun hs => hz ⟨expand z, hs, collapse_expand z⟩
    change collapse (a.family (t, expand z)) = z
    rw [a.fixed t _ hz', collapse_expand]
  · intro t z
    change (a.family (t, expand z)).1.1 = z.1.1
    rw [a.horizontal]
    rfl
  · intro t z
    change normalProject (a.family (t, expand z)).2 = z.2
    rw [a.normal]
    exact normalProject_include z.2
  · intro s
    have he : expand (firstSheet (s, 0)) = WhitneyPairModel.firstSheet (s, 0) :=
      expand_zero (s, 0)
    change collapse (a.family (1, expand (firstSheet (s, 0)))) = verticalGraph g.height 1 s
    rw [he, a.tracking, collapse_verticalGraph]

theorem RankThreeWhitneyModel.GraphMotion.firstSheet_ne_secondSheet {h : ℝ}
    {U : Set RankThreeWhitneyModel.Space} (a : RankThreeWhitneyModel.GraphMotion h U)
    (hh : 0 < h) (p : RankThreeWhitneyModel.LowerSheet)
    (q : RankThreeWhitneyModel.UpperSheet) :
    a.family (1, RankThreeWhitneyModel.firstSheet p) ≠
      RankThreeWhitneyModel.secondSheet h q := by
  intro heq
  have hst : p.1 = q.1 := by
    have he := congrArg (fun z : RankThreeWhitneyModel.Space => z.1.1) heq
    rw [a.horizontal] at he
    exact he
  have hu : p.2 = 0 := by
    have he := congrArg (fun z : RankThreeWhitneyModel.Space => z.2) heq
    rw [a.normal] at he
    exact congrArg Prod.fst he
  have hp : p = (q.1, 0) := Prod.ext hst hu
  rw [hp, a.tracking] at heq
  have ht : a.height q.1 = h * (1 - q.1 ^ 2) := by
    simpa only [RankThreeWhitneyModel.verticalGraph,
      RankThreeWhitneyModel.secondSheet, one_mul] using
      congrArg (fun z : RankThreeWhitneyModel.Space => z.1.2) heq
  have hheight : 0 ≤ h * (1 - q.1 ^ 2) := ht ▸ a.nonneg_height q.1
  have hlevel : 0 ≤ 1 - q.1 ^ 2 := nonneg_of_mul_nonneg_right hheight hh
  have habs : |q.1| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (q.1 + 1)], by nlinarith [sq_nonneg (q.1 - 1)]⟩
  exact (a.above q.1 habs).ne ht.symm

structure TubularBigon.RankThreeTangentAdaptedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map) where
  base : (ℝ × ℝ) → ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] (ℝ × ℝ))
  normal :
    (ℝ × ℝ) →
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3))
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains : WhitneyPairModel.bigon h ⊆ domain
  smooth_base : ContDiffOn ℝ ∞ base domain
  smooth_normal : ContDiffOn ℝ ∞ normal domain
  normal_invertible : ∀ p ∈ domain, (normal p).IsInvertible
  lower_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : EuclideanSpace ℝ (Fin 1),
        FrameField.shearedBlock (base (2 * t - 1, 0)) (normal (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u)
  upper_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : EuclideanSpace ℝ (Fin 2),
        FrameField.shearedBlock (base (WhitneyPairModel.upperBoundaryArc h t))
            (normal (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v)
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      RankThreeWhitneyModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  coordinates : ∀ p, chart p = tube.chart (FrameField.shearedMap base normal p)
  target_subset : chart.target ⊆ tube.chart.target
  transition_derivative :
    ∀ p ∈ WhitneyPairModel.bigon h,
      HasFDerivAt (tube.chart.symm ∘ chart) (FrameField.shearedBlock (base p) (normal p))
        (p, 0)

theorem TubularBigon.nonempty_rankThreeTangentAdaptedChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeTangentAdaptedChart tube d e) := by
  obtain ⟨W, hW, hlo, O, hO, hKO, C, hC, hhi, hframe⟩ :=
    tube.exists_rankThree_adapted_frame_of_opposite_corner_signs d e hsign
  obtain ⟨Dlo, hDlo, hIDlo, hBlo⟩ :=
    d.exists_open_sheetBaseFrame_domain tube.chart
      (fun t ht => tube.lower_chart_center_mem_target d ht)
  obtain ⟨Dhi, hDhi, hIDhi, hBhi⟩ :=
    e.exists_open_sheetBaseFrame_domain tube.chart
      (fun t ht => tube.upper_chart_center_mem_target e ht)
  have htime (t y : ℝ) : WhitneyPairModel.arcTime (2 * t - 1, y) = t := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have htq (t : ℝ) :
    WhitneyPairModel.arcTime (WhitneyPairModel.upperBoundaryArc h t) = t := htime t _
  have htimeK :
    Set.MapsTo WhitneyPairModel.arcTime (WhitneyPairModel.bigon h)
      (Set.Icc (0 : ℝ) 1) := by
    intro p hp
    have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  let U := O ∩ WhitneyPairModel.arcTime ⁻¹' (Dlo ∩ Dhi)
  have hU : IsOpen U :=
    hO.inter ((hDlo.inter hDhi).preimage WhitneyPairModel.contDiff_arcTime.continuous)
  have hKU : WhitneyPairModel.bigon h ⊆ U := fun p hp =>
    ⟨hKO hp, hIDlo (htimeK hp), hIDhi (htimeK hp)⟩
  let A : (ℝ × ℝ) → ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] (ℝ × ℝ)) :=
    fun p =>
    (d.sheetBaseFrame tube.chart (WhitneyPairModel.arcTime p)).coprod
      (e.sheetBaseFrame tube.chart (WhitneyPairModel.arcTime p))
  let N :
    (ℝ × ℝ) →
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
    fun p => (W p).coprod (C p)
  have hA : ContDiffOn ℝ ∞ A U :=
    FrameField.contDiffOn_coprod
      (hBlo.comp WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.1))
      (hBhi.comp WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.2))
  have hN : ContDiffOn ℝ ∞ N U :=
    FrameField.contDiffOn_coprod hW.contDiffOn (hC.mono Set.inter_subset_left)
  have hiN : ∀ p ∈ U, (N p).IsInvertible := fun p hp =>
    FrameField.isInvertible_coprod_of_bijective _ _ (hframe p hp.1)
  have hlow :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : EuclideanSpace ℝ (Fin 1),
        FrameField.shearedBlock (A (2 * t - 1, 0)) (N (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u) := by
    intro t ht u
    have hWt : W (2 * t - 1, 0) = d.normalFrame tube.chart t := by
      have hg := (hlo t ht).eq_of_nhds
      dsimp only [Function.comp_apply] at hg
      rwa [htime] at hg
    rw [d.sheetDifferential_transverse_eq tube.chart ht (tube.lower_chart_center_mem_target d ht),
      FrameField.shearedBlock_apply]
    simp only [A, N, ContinuousLinearMap.coprod_apply, map_zero, add_zero, zero_add, htime, hWt]
  have hupp :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : EuclideanSpace ℝ (Fin 2),
        FrameField.shearedBlock (A (WhitneyPairModel.upperBoundaryArc h t))
            (N (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v) := by
    intro t ht v
    rw [e.sheetDifferential_transverse_eq tube.chart ht (tube.upper_chart_center_mem_target e ht),
      FrameField.shearedBlock_apply]
    simp only [A, N, ContinuousLinearMap.coprod_apply, map_zero, zero_add, htq, hhi t ht]
  have hz :
    WhitneyPairModel.bigon h ×ˢ {(0 : EuclideanSpace ℝ (Fin 3))} ⊆ tube.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, Φ, hsource, hformula, htarget, -, hderiv⟩ :=
    FrameField.exists_sheared_tubular_chart tube.chart
      (WhitneyPairModel.isCompact_bigon tube.height_pos) hU hKU hz hA hN
      (fun p hp => hiN p (hKU hp))
  refine
    ⟨{  base := A
        normal := N
        domain := U
        open_domain := hU
        contains := hKU
        smooth_base := hA
        smooth_normal := hN
        normal_invertible := hiN
        lower_transverse := hlow
        upper_transverse := hupp
        radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := ?_
        coordinates := hformula
        target_subset := htarget
        transition_derivative := hderiv }⟩
  intro p
  rw [hformula, FrameField.shearedMap_zero, tube.zero_section]

structure TubularBigon.TangentAdaptedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h)
    (d :
      StripNormalData WhitneyPairModel.Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData WhitneyPairModel.Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T
        l.map) where
  base : (ℝ × ℝ) → ((WhitneyPairModel.Plane × WhitneyPairModel.Plane) →L[ℝ] (ℝ × ℝ))
  normal :
    (ℝ × ℝ) →
      ((WhitneyPairModel.Plane × WhitneyPairModel.Plane) →L[ℝ]
        EuclideanSpace ℝ (Fin 4))
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains : WhitneyPairModel.bigon h ⊆ domain
  smooth_base : ContDiffOn ℝ ∞ base domain
  smooth_normal : ContDiffOn ℝ ∞ normal domain
  normal_invertible : ∀ p ∈ domain, (normal p).IsInvertible
  lower_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : WhitneyPairModel.Plane,
        FrameField.shearedBlock (base (2 * t - 1, 0)) (normal (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u)
  upper_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : WhitneyPairModel.Plane,
        FrameField.shearedBlock (base (WhitneyPairModel.upperBoundaryArc h t))
            (normal (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v)
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, WhitneyPairModel.Space) 𝓘(ℝ, E) WhitneyPairModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  coordinates : ∀ p, chart p = tube.chart (FrameField.shearedMap base normal p)
  target_subset : chart.target ⊆ tube.chart.target
  transition_derivative :
    ∀ p ∈ WhitneyPairModel.bigon h,
      HasFDerivAt (tube.chart.symm ∘ chart) (FrameField.shearedBlock (base p) (normal p))
        (p, 0)

def WhitneyPairModel.halfTimeDerivative {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : (ℝ × A) →L[ℝ] (ℝ × A) :=
  (((1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ A)).prod (ContinuousLinearMap.snd ℝ ℝ A)

theorem WhitneyPairModel.halfTimeDerivative_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (v : (ℝ × A)) : halfTimeDerivative v = (v.1 / 2, v.2) := by
  apply Prod.ext
  · change (1 / 2 : ℝ) * v.1 = v.1 / 2
    ring
  · rfl

def WhitneyPairModel.sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : (ℝ × A) :=
  halfTimeDerivative p + ((1 / 2 : ℝ), 0)

theorem WhitneyPairModel.sheetTimeCoordinates_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : sheetTimeCoordinates p = ((p.1 + 1) / 2, p.2) := by
  rw [sheetTimeCoordinates, halfTimeDerivative_apply]
  apply Prod.ext
  · change p.1 / 2 + 1 / 2 = (p.1 + 1) / 2
    ring
  · exact add_zero _

theorem WhitneyPairModel.sheetTimeCoordinates_center {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (t : ℝ) : sheetTimeCoordinates (2 * t - 1, (0 : A)) = (t, 0) := by
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · dsimp
    ring
  · rfl

theorem WhitneyPairModel.contDiff_sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : ContDiff ℝ ∞ (sheetTimeCoordinates (A := A)) :=
  (halfTimeDerivative (A := A)).contDiff.add contDiff_const

theorem WhitneyPairModel.hasFDerivAt_sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : HasFDerivAt sheetTimeCoordinates halfTimeDerivative p :=
  halfTimeDerivative.hasFDerivAt.add_const ((1 / 2 : ℝ), (0 : A))

def StripNormalData.sheetTransitionDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) : Set (ℝ × A) :=
  (ContinuousLinearMap.inl ℝ (ℝ × A) B) ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target)

theorem StripNormalData.isOpen_sheetTransitionDomain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    IsOpen (d.sheetTransitionDomain Ψ) := by
  have hO : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  exact hO.preimage (ContinuousLinearMap.inl ℝ (ℝ × A) B).continuous

theorem StripNormalData.contDiffOn_sheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetTransition Ψ) (d.sheetTransitionDomain Ψ) := by
  have hfull : ContDiffOn ℝ ∞ (Ψ.symm ∘ d.chart) (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    (Ψ.contMDiffOn_invFun.comp (d.chart.contMDiffOn_toFun.mono Set.inter_subset_left)
        (fun _ hp => hp.2)).contDiffOn
  exact hfull.comp (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffOn (fun _ hp => hp)

def StripNormalData.retimedSheetTransition {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    (ℝ × A) → ((ℝ × ℝ) × Z) :=
  d.sheetTransition Ψ ∘ WhitneyPairModel.sheetTimeCoordinates

def StripNormalData.retimedDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) : Set (ℝ × A) :=
  WhitneyPairModel.sheetTimeCoordinates ⁻¹' d.sheetTransitionDomain Ψ

theorem StripNormalData.isOpen_retimedDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    IsOpen (d.retimedDomain Ψ) :=
  (d.isOpen_sheetTransitionDomain Ψ).preimage
    WhitneyPairModel.contDiff_sheetTimeCoordinates.continuous

theorem StripNormalData.contDiffOn_retimedSheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.retimedSheetTransition Ψ) (d.retimedDomain Ψ) :=
  (d.contDiffOn_sheetTransition Ψ).comp
    WhitneyPairModel.contDiff_sheetTimeCoordinates.contDiffOn (fun _ hp => hp)

theorem StripNormalData.retimedDomain_contains_center {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (2 * t - 1, (0 : A)) ∈ d.retimedDomain Ψ := by
  change WhitneyPairModel.sheetTimeCoordinates (2 * t - 1, 0) ∈ d.sheetTransitionDomain Ψ
  rw [WhitneyPairModel.sheetTimeCoordinates_center]
  exact ⟨d.line ht, htarget⟩

theorem StripNormalData.hasFDerivAt_retimedSheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    HasFDerivAt (d.retimedSheetTransition Ψ)
      ((d.sheetDifferential Ψ t).comp WhitneyPairModel.halfTimeDerivative) (2 * t - 1, 0) :=
  by
  have hd :
    HasFDerivAt (d.sheetTransition Ψ) (d.sheetDifferential Ψ t)
      (WhitneyPairModel.sheetTimeCoordinates (2 * t - 1, 0)) := by
    rw [WhitneyPairModel.sheetTimeCoordinates_center]
    exact ((d.contDiffAt_sheetTransition Ψ ht htarget).differentiableAt (by simp)).hasFDerivAt
  exact hd.comp (2 * t - 1, (0 : A)) (WhitneyPairModel.hasFDerivAt_sheetTimeCoordinates _)

theorem TubularBigon.RankThreeTangentAdaptedChart.lower_model_tangent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))).comp
        RankThreeWhitneyModel.firstSheetDerivative =
      (d.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  have harc : d.sheetDifferential tube.chart t (v.1 / 2, 0) = ((v.1, 0), 0) := by
    rw [IntersectionCoordinates.map_first_axis _ (v.1 / 2),
      tube.lower_sheetDifferential_arc d ht]
    ext <;> simp [smul_eq_mul]
  change
    FrameField.shearedBlock _ _ (RankThreeWhitneyModel.firstSheetDerivative v) =
      d.sheetDifferential tube.chart t (WhitneyPairModel.halfTimeDerivative v)
  rw [WhitneyPairModel.halfTimeDerivative_apply]
  calc
    FrameField.shearedBlock _ _ (RankThreeWhitneyModel.firstSheetDerivative v) =
        FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))
            ((v.1, 0), 0) +
          FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))
            (0, (v.2, 0)) := by
      rw [← map_add]
      congr 1
      simp only [RankThreeWhitneyModel.firstSheetDerivative_apply, Prod.mk_add_mk, add_zero,
        zero_add]
    _ =
        d.sheetDifferential tube.chart t (v.1 / 2, 0) +
          d.sheetDifferential tube.chart t (0, v.2) := by
      rw [FrameField.shearedBlock_horizontal, c.lower_transverse t ht, harc]
    _ = d.sheetDifferential tube.chart t (v.1 / 2, v.2) := by
      rw [← map_add]
      congr 1
      simp

theorem TubularBigon.RankThreeTangentAdaptedChart.upper_model_tangent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (FrameField.shearedBlock (c.base (WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (WhitneyPairModel.upperBoundaryArc h t))).comp
        (RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1)) =
      (e.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  have harc :
    e.sheetDifferential tube.chart t (v.1 / 2, 0) = ((v.1, (-2 * h * (2 * t - 1)) * v.1), 0) := by
    rw [IntersectionCoordinates.map_first_axis _ (v.1 / 2),
      tube.upper_sheetDifferential_arc e ht]
    ext <;> simp [smul_eq_mul]
    ring
  change
    FrameField.shearedBlock _ _
        (RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1) v) =
      e.sheetDifferential tube.chart t (WhitneyPairModel.halfTimeDerivative v)
  rw [WhitneyPairModel.halfTimeDerivative_apply]
  calc
    FrameField.shearedBlock _ _
          (RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1) v) =
        FrameField.shearedBlock (c.base (WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (WhitneyPairModel.upperBoundaryArc h t))
            ((v.1, (-2 * h * (2 * t - 1)) * v.1), 0) +
          FrameField.shearedBlock (c.base (WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v.2)) := by
      rw [← map_add]
      congr 1
      simp only [RankThreeWhitneyModel.secondSheetDerivative_apply, Prod.mk_add_mk,
        add_zero, zero_add]
    _ =
        e.sheetDifferential tube.chart t (v.1 / 2, 0) +
          e.sheetDifferential tube.chart t (0, v.2) := by
      rw [FrameField.shearedBlock_horizontal, c.upper_transverse t ht, harc]
    _ = e.sheetDifferential tube.chart t (v.1 / 2, v.2) := by
      rw [← map_add]
      congr 1
      simp

def SheetCorrection.centerProjection {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] :
    (ℝ × A) →L[ℝ] (ℝ × A) :=
  (ContinuousLinearMap.fst ℝ ℝ A).prod (0 : (ℝ × A) →L[ℝ] A)

theorem SheetCorrection.centerProjection_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : ℝ × A) : centerProjection p = (p.1, 0) :=
  rfl

def SheetCorrection.centeredCorrection {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] (R G : (ℝ × A) → F) (p : ℝ × A) : F :=
  (R p - G p) - (R (centerProjection p) - G (centerProjection p))

theorem SheetCorrection.centeredCorrection_zero {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] (R G : (ℝ × A) → F) (s : ℝ) :
    centeredCorrection R G (s, 0) = 0 := by
  simp only [centeredCorrection, centerProjection_apply, sub_self]

theorem SheetCorrection.centeredCorrection_eq_sub {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] {R G : (ℝ × A) → F} {p : ℝ × A}
    (hcenter : R (p.1, 0) = G (p.1, 0)) : centeredCorrection R G p = R p - G p := by
  simp only [centeredCorrection, centerProjection_apply, hcenter, sub_self, sub_zero]

theorem SheetCorrection.contDiffOn_centeredCorrection {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F] {R G : (ℝ × A) → F}
    {D : Set (ℝ × A)} (hR : ContDiffOn ℝ ∞ R D) (hG : ContDiffOn ℝ ∞ G D) :
    ContDiffOn ℝ ∞ (centeredCorrection R G) (D ∩ centerProjection ⁻¹' D) :=
  ((hR.sub hG).mono Set.inter_subset_left).sub
    ((hR.sub hG).comp (centerProjection (A := A)).contDiff.contDiffOn (fun _ hp => hp.2))

theorem SheetCorrection.hasFDerivAt_centeredCorrection_zero {A F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R G : (ℝ × A) → F} {L : (ℝ × A) →L[ℝ] F} {s : ℝ} (hR : HasFDerivAt R L (s, 0))
    (hG : HasFDerivAt G L (s, 0)) :
    HasFDerivAt (centeredCorrection R G) (0 : (ℝ × A) →L[ℝ] F) (s, 0) := by
  have hdiff : HasFDerivAt (fun p => R p - G p) (0 : (ℝ × A) →L[ℝ] F) (s, (0 : A)) := by
    convert hR.sub hG using 1 <;>
      first
      | rfl
      | simp only [sub_self]
  have hcenter := hdiff.comp (s, (0 : A)) (centerProjection (A := A)).hasFDerivAt
  convert hdiff.sub hcenter using 1 <;>
    first
    | rfl
    | simp only [ContinuousLinearMap.zero_comp, sub_self]

def RankThreeWhitneyModel.lowerSheetCoordinates : Space →L[ℝ] LowerSheet :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Lower × Upper))).prod
    ((ContinuousLinearMap.fst ℝ Lower Upper).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Lower × Upper)))

def RankThreeWhitneyModel.upperSheetCoordinates : Space →L[ℝ] UpperSheet :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Lower × Upper))).prod
    ((ContinuousLinearMap.snd ℝ Lower Upper).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Lower × Upper)))

def RankThreeWhitneyModel.correctedSheetMap {F : Type*} [NormedAddCommGroup F]
    (G : Space → F) (Rlo : LowerSheet → F) (Rhi : UpperSheet → F) (h : ℝ) (p : Space) : F :=
  G p + SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) (lowerSheetCoordinates p) +
    SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) (upperSheetCoordinates p)

theorem RankThreeWhitneyModel.correctedSheetMap_zero {F : Type*} [NormedAddCommGroup F]
    (G : Space → F) (Rlo : LowerSheet → F) (Rhi : UpperSheet → F) (h : ℝ) (p : ℝ × ℝ) :
    correctedSheetMap G Rlo Rhi h (p, 0) = G (p, 0) := by
  change
    G (p, 0) + SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) (p.1, 0) +
        SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) (p.1, 0) =
      G (p, 0)
  rw [SheetCorrection.centeredCorrection_zero,
    SheetCorrection.centeredCorrection_zero, add_zero, add_zero]

theorem RankThreeWhitneyModel.correctedSheetMap_lower {F : Type*} [NormedAddCommGroup F]
    {G : Space → F} {Rlo : LowerSheet → F} {Rhi : UpperSheet → F} {h : ℝ} (q : LowerSheet)
    (hcenter : Rlo (q.1, 0) = G (firstSheet (q.1, 0))) :
    correctedSheetMap G Rlo Rhi h (firstSheet q) = Rlo q := by
  have hlo : lowerSheetCoordinates (firstSheet q) = q := rfl
  have hhi : upperSheetCoordinates (firstSheet q) = (q.1, 0) := rfl
  rw [correctedSheetMap, hlo, hhi, SheetCorrection.centeredCorrection_zero, add_zero,
    SheetCorrection.centeredCorrection_eq_sub hcenter]
  dsimp only [Function.comp_apply]
  abel

theorem RankThreeWhitneyModel.correctedSheetMap_upper {F : Type*} [NormedAddCommGroup F]
    {G : Space → F} {Rlo : LowerSheet → F} {Rhi : UpperSheet → F} {h : ℝ} (q : UpperSheet)
    (hcenter : Rhi (q.1, 0) = G (secondSheet h (q.1, 0))) :
    correctedSheetMap G Rlo Rhi h (secondSheet h q) = Rhi q := by
  have hlo : lowerSheetCoordinates (secondSheet h q) = (q.1, 0) := rfl
  have hhi : upperSheetCoordinates (secondSheet h q) = q := rfl
  rw [correctedSheetMap, hlo, hhi, SheetCorrection.centeredCorrection_zero, add_zero,
    SheetCorrection.centeredCorrection_eq_sub hcenter]
  dsimp only [Function.comp_apply]
  abel

def RankThreeWhitneyModel.correctionDomain (U : Set Space) (Dlo : Set LowerSheet)
    (Dhi : Set UpperSheet) : Set Space :=
  U ∩
    (lowerSheetCoordinates ⁻¹' (Dlo ∩ SheetCorrection.centerProjection ⁻¹' Dlo) ∩
      upperSheetCoordinates ⁻¹' (Dhi ∩ SheetCorrection.centerProjection ⁻¹' Dhi))

theorem RankThreeWhitneyModel.isOpen_correctionDomain {U : Set Space} {Dlo : Set LowerSheet}
    {Dhi : Set UpperSheet} (hU : IsOpen U) (hDlo : IsOpen Dlo) (hDhi : IsOpen Dhi) :
    IsOpen (correctionDomain U Dlo Dhi) :=
  hU.inter
    (((hDlo.inter (hDlo.preimage SheetCorrection.centerProjection.continuous)).preimage
          lowerSheetCoordinates.continuous).inter
      ((hDhi.inter (hDhi.preimage SheetCorrection.centerProjection.continuous)).preimage
        upperSheetCoordinates.continuous))

theorem RankThreeWhitneyModel.contDiffOn_correctedSheetMap {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Space → F} {Rlo : LowerSheet → F}
    {Rhi : UpperSheet → F} {h : ℝ} {U : Set Space} {Dlo : Set LowerSheet} {Dhi : Set UpperSheet}
    (hG : ContDiffOn ℝ ∞ G U) (hRlo : ContDiffOn ℝ ∞ Rlo Dlo)
    (hGlo : ContDiffOn ℝ ∞ (G ∘ firstSheet) Dlo) (hRhi : ContDiffOn ℝ ∞ Rhi Dhi)
    (hGhi : ContDiffOn ℝ ∞ (G ∘ secondSheet h) Dhi) :
    ContDiffOn ℝ ∞ (correctedSheetMap G Rlo Rhi h) (correctionDomain U Dlo Dhi) :=
  ((hG.mono Set.inter_subset_left).add
        ((SheetCorrection.contDiffOn_centeredCorrection hRlo hGlo).comp
          lowerSheetCoordinates.contDiff.contDiffOn (fun _ hp => hp.2.1))).add
    ((SheetCorrection.contDiffOn_centeredCorrection hRhi hGhi).comp
      upperSheetCoordinates.contDiff.contDiffOn (fun _ hp => hp.2.2))

theorem RankThreeWhitneyModel.hasFDerivAt_correctedSheetMap_zero {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Space → F} {Rlo : LowerSheet → F}
    {Rhi : UpperSheet → F} {h : ℝ} {p : ℝ × ℝ} {L : Space →L[ℝ] F} {Llo : LowerSheet →L[ℝ] F}
    {Lhi : UpperSheet →L[ℝ] F} (hG : HasFDerivAt G L (p, 0)) (hRlo : HasFDerivAt Rlo Llo (p.1, 0))
    (hGlo : HasFDerivAt (G ∘ firstSheet) Llo (p.1, 0)) (hRhi : HasFDerivAt Rhi Lhi (p.1, 0))
    (hGhi : HasFDerivAt (G ∘ secondSheet h) Lhi (p.1, 0)) :
    HasFDerivAt (correctedSheetMap G Rlo Rhi h) L (p, 0) := by
  have hlo :
    HasFDerivAt
      (SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) ∘ lowerSheetCoordinates)
      (0 : Space →L[ℝ] F) (p, 0) := by
    simpa only [ContinuousLinearMap.zero_comp] using
      (SheetCorrection.hasFDerivAt_centeredCorrection_zero hRlo hGlo).comp
        (p, (0 : Lower × Upper)) lowerSheetCoordinates.hasFDerivAt
  have hhi :
    HasFDerivAt
      (SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) ∘ upperSheetCoordinates)
      (0 : Space →L[ℝ] F) (p, 0) := by
    simpa only [ContinuousLinearMap.zero_comp] using
      (SheetCorrection.hasFDerivAt_centeredCorrection_zero hRhi hGhi).comp
        (p, (0 : Lower × Upper)) upperSheetCoordinates.hasFDerivAt
  convert (hG.add hlo).add hhi using 1 <;>
    first
    | rfl
    | simp only [add_zero]

def TubularBigon.RankThreeTangentAdaptedChart.shearedCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    RankThreeWhitneyModel.Space → ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  FrameField.shearedMap c.base c.normal

def TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    RankThreeWhitneyModel.Space → ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  RankThreeWhitneyModel.correctedSheetMap c.shearedCoordinates
    (d.retimedSheetTransition tube.chart) (e.retimedSheetTransition tube.chart) h

theorem TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) (p : ℝ × ℝ) :
    c.correctedCoordinates (p, 0) = (p, 0) := by
  rw [correctedCoordinates, RankThreeWhitneyModel.correctedSheetMap_zero]
  exact FrameField.shearedMap_zero c.base c.normal p

theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_shearedCoordinates_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) :
    HasFDerivAt c.shearedCoordinates (FrameField.shearedBlock (c.base p) (c.normal p))
      (p, 0) :=
  FrameField.hasFDerivAt_shearedMap_zero
    ((c.smooth_base.contDiffAt (c.open_domain.mem_nhds (c.contains hp))).differentiableAt
      (by simp))
    ((c.smooth_normal.contDiffAt (c.open_domain.mem_nhds (c.contains hp))).differentiableAt
      (by simp))

theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_sheared_lower {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasFDerivAt (c.shearedCoordinates ∘ RankThreeWhitneyModel.firstSheet)
      ((d.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative)
      (2 * t - 1, 0) := by
  have hd :=
    (c.hasFDerivAt_shearedCoordinates_zero (tube.lowerBoundaryArc_mem_bigon ht)).comp
      (2 * t - 1, (0 : RankThreeWhitneyModel.Lower))
      (RankThreeWhitneyModel.hasFDerivAt_firstSheet (2 * t - 1, 0))
  rwa [WhitneyPairModel.lowerBoundaryArc, c.lower_model_tangent ht] at hd

theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_sheared_upper {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasFDerivAt (c.shearedCoordinates ∘ RankThreeWhitneyModel.secondSheet h)
      ((e.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative)
      (2 * t - 1, 0) := by
  have hd :=
    (c.hasFDerivAt_shearedCoordinates_zero (tube.upperBoundaryArc_mem_bigon ht)).comp
      (2 * t - 1, (0 : RankThreeWhitneyModel.Upper))
      (RankThreeWhitneyModel.hasFDerivAt_secondSheet h (2 * t - 1, 0))
  rwa [c.upper_model_tangent ht] at hd

theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_correctedCoordinates_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) :
    HasFDerivAt c.correctedCoordinates (FrameField.shearedBlock (c.base p) (c.normal p))
      (p, 0) := by
  have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
  have ht : WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have htime : 2 * WhitneyPairModel.arcTime p - 1 = p.1 := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have hRlo :=
    d.hasFDerivAt_retimedSheetTransition tube.chart ht (tube.lower_chart_center_mem_target d ht)
  have hRhi :=
    e.hasFDerivAt_retimedSheetTransition tube.chart ht (tube.upper_chart_center_mem_target e ht)
  have hGlo := c.hasFDerivAt_sheared_lower ht
  have hGhi := c.hasFDerivAt_sheared_upper ht
  rw [htime] at hRlo hRhi hGlo hGhi
  exact
    RankThreeWhitneyModel.hasFDerivAt_correctedSheetMap_zero
      (c.hasFDerivAt_shearedCoordinates_zero hp) hRlo hGlo hRhi hGhi

theorem TubularBigon.RankThreeTangentAdaptedChart.retimed_lower_center_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.retimedSheetTransition tube.chart (s, 0)) =ᶠ[𝓝 (2 * t - 1)]
      (fun s => c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0))) := by
  have hct : ContinuousAt (fun s : ℝ => (s + 1) / 2) (2 * t - 1) := by fun_prop
  have heq : (2 * t - 1 + 1) / 2 = t := by ring
  have htime : Filter.Tendsto (fun s : ℝ => (s + 1) / 2) (𝓝 (2 * t - 1)) (𝓝 t) := by
    simpa only [heq] using hct.tendsto
  filter_upwards [(tube.lower_sheetTransition_center_germ d ht).comp_tendsto htime] with s hs
  change
    d.sheetTransition tube.chart (WhitneyPairModel.sheetTimeCoordinates (s, 0)) =
      FrameField.shearedMap c.base c.normal ((s, 0), 0)
  rw [WhitneyPairModel.sheetTimeCoordinates_apply, FrameField.shearedMap_zero]
  dsimp only [Function.comp_apply] at hs
  rw [hs]
  have hlin : 2 * ((s + 1) / 2) - 1 = s := by ring
  simp only [WhitneyPairModel.lowerBoundaryArc, hlin]

theorem TubularBigon.RankThreeTangentAdaptedChart.retimed_upper_center_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => e.retimedSheetTransition tube.chart (s, 0)) =ᶠ[𝓝 (2 * t - 1)]
      (fun s => c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))) := by
  have hct : ContinuousAt (fun s : ℝ => (s + 1) / 2) (2 * t - 1) := by fun_prop
  have heq : (2 * t - 1 + 1) / 2 = t := by ring
  have htime : Filter.Tendsto (fun s : ℝ => (s + 1) / 2) (𝓝 (2 * t - 1)) (𝓝 t) := by
    simpa only [heq] using hct.tendsto
  filter_upwards [(tube.upper_sheetTransition_center_germ e ht).comp_tendsto htime] with s hs
  change
    e.sheetTransition tube.chart (WhitneyPairModel.sheetTimeCoordinates (s, 0)) =
      FrameField.shearedMap c.base c.normal ((s, h * (1 - s ^ 2)), 0)
  rw [WhitneyPairModel.sheetTimeCoordinates_apply, FrameField.shearedMap_zero]
  dsimp only [Function.comp_apply] at hs
  rw [hs]
  have hlin : 2 * ((s + 1) / 2) - 1 = s := by ring
  simp only [WhitneyPairModel.upperBoundaryArc, hlin]

def TubularBigon.RankThreeTangentAdaptedChart.shearedDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.Space :=
  Prod.fst ⁻¹' c.domain

def TubularBigon.RankThreeTangentAdaptedChart.lowerCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.LowerSheet :=
  d.retimedDomain tube.chart ∩ RankThreeWhitneyModel.firstSheet ⁻¹' c.shearedDomain

def TubularBigon.RankThreeTangentAdaptedChart.upperCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.UpperSheet :=
  e.retimedDomain tube.chart ∩ RankThreeWhitneyModel.secondSheet h ⁻¹' c.shearedDomain

def TubularBigon.RankThreeTangentAdaptedChart.centerMatchingTimes {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) : Set ℝ :=
  interior
    {s |
      d.retimedSheetTransition tube.chart (s, 0) =
          c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0)) ∧
        e.retimedSheetTransition tube.chart (s, 0) =
          c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))}

def TubularBigon.RankThreeTangentAdaptedChart.nonlinearDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.Space :=
  RankThreeWhitneyModel.correctionDomain c.shearedDomain c.lowerCorrectionDomain
      c.upperCorrectionDomain ∩
    (fun p : RankThreeWhitneyModel.Space => p.1.1) ⁻¹' c.centerMatchingTimes

theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_shearedDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) : IsOpen c.shearedDomain :=
  c.open_domain.preimage continuous_fst

theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_lowerCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    IsOpen c.lowerCorrectionDomain :=
  (d.isOpen_retimedDomain tube.chart).inter
    (c.isOpen_shearedDomain.preimage RankThreeWhitneyModel.contDiff_firstSheet.continuous)

theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_upperCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    IsOpen c.upperCorrectionDomain :=
  (e.isOpen_retimedDomain tube.chart).inter
    (c.isOpen_shearedDomain.preimage
      (RankThreeWhitneyModel.contDiff_secondSheet h).continuous)

theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_nonlinearDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) : IsOpen c.nonlinearDomain :=
  (RankThreeWhitneyModel.isOpen_correctionDomain c.isOpen_shearedDomain
        c.isOpen_lowerCorrectionDomain c.isOpen_upperCorrectionDomain).inter
    (isOpen_interior.preimage (by fun_prop))

theorem TubularBigon.RankThreeTangentAdaptedChart.contDiffOn_correctedCoordinates
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    ContDiffOn ℝ ∞ c.correctedCoordinates c.nonlinearDomain := by
  have hG : ContDiffOn ℝ ∞ c.shearedCoordinates c.shearedDomain :=
    FrameField.contDiffOn_shearedMap c.smooth_base c.smooth_normal
  exact
    (RankThreeWhitneyModel.contDiffOn_correctedSheetMap hG
          ((d.contDiffOn_retimedSheetTransition tube.chart).mono Set.inter_subset_left)
          (hG.comp RankThreeWhitneyModel.contDiff_firstSheet.contDiffOn (fun _ hp => hp.2))
          ((e.contDiffOn_retimedSheetTransition tube.chart).mono Set.inter_subset_left)
          (hG.comp (RankThreeWhitneyModel.contDiff_secondSheet h).contDiffOn
            (fun _ hp => hp.2))).mono
      Set.inter_subset_left

theorem TubularBigon.RankThreeTangentAdaptedChart.centerMatchingTimes_contains {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 2 * t - 1 ∈ c.centerMatchingTimes :=
  mem_interior_iff_mem_nhds.mpr
    ((c.retimed_lower_center_germ ht).and (c.retimed_upper_center_germ ht))

theorem TubularBigon.RankThreeTangentAdaptedChart.lowerCorrectionDomain_contains_center
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (2 * t - 1, (0 : RankThreeWhitneyModel.Lower)) ∈ c.lowerCorrectionDomain := by
  refine
    ⟨d.retimedDomain_contains_center tube.chart ht (tube.lower_chart_center_mem_target d ht), ?_⟩
  exact c.contains (tube.lowerBoundaryArc_mem_bigon ht)

theorem TubularBigon.RankThreeTangentAdaptedChart.upperCorrectionDomain_contains_center
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (2 * t - 1, (0 : RankThreeWhitneyModel.Upper)) ∈ c.upperCorrectionDomain := by
  refine
    ⟨e.retimedDomain_contains_center tube.chart ht (tube.upper_chart_center_mem_target e ht), ?_⟩
  exact c.contains (tube.upperBoundaryArc_mem_bigon ht)

theorem TubularBigon.RankThreeTangentAdaptedChart.nonlinearDomain_contains_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) :
    (p, (0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)) ∈
      c.nonlinearDomain := by
  have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
  have ht : WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have htime : 2 * WhitneyPairModel.arcTime p - 1 = p.1 := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have hlo := c.lowerCorrectionDomain_contains_center ht
  have hhi := c.upperCorrectionDomain_contains_center ht
  have hmatch := c.centerMatchingTimes_contains ht
  rw [htime] at hlo hhi hmatch
  exact ⟨⟨c.contains hp, ⟨hlo, hlo⟩, ⟨hhi, hhi⟩⟩, hmatch⟩

theorem TubularBigon.RankThreeTangentAdaptedChart.lower_native_parameters {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.nonlinearDomain) :
    (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
        d.chart.source ∧
      d.chart (WhitneyPairModel.sheetTimeCoordinates q, 0) ∈ tube.chart.target :=
  hq.1.2.1.1.1

theorem TubularBigon.RankThreeTangentAdaptedChart.upper_native_parameters {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.nonlinearDomain) :
    (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 2))) ∈
        e.chart.source ∧
      e.chart (WhitneyPairModel.sheetTimeCoordinates q, 0) ∈ tube.chart.target :=
  hq.1.2.2.1.1

theorem TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_lower_of_mem_domain
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.nonlinearDomain) :
    c.correctedCoordinates (RankThreeWhitneyModel.firstSheet q) =
      d.retimedSheetTransition tube.chart q := by
  have hJ : q.1 ∈ c.centerMatchingTimes := hq.2
  have hm :=
    (show
        c.centerMatchingTimes ⊆
          {s : ℝ |
            d.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0)) ∧
              e.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))}
        from interior_subset)
      hJ
  exact RankThreeWhitneyModel.correctedSheetMap_lower q hm.1

theorem TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_upper_of_mem_domain
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.nonlinearDomain) :
    c.correctedCoordinates (RankThreeWhitneyModel.secondSheet h q) =
      e.retimedSheetTransition tube.chart q := by
  have hJ : q.1 ∈ c.centerMatchingTimes := hq.2
  have hm :=
    (show
        c.centerMatchingTimes ⊆
          {s : ℝ |
            d.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0)) ∧
              e.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))}
        from interior_subset)
      hJ
  exact RankThreeWhitneyModel.correctedSheetMap_upper q hm.2

structure TubularBigon.RankThreeSheetParametrizedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      RankThreeWhitneyModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  lower_source :
    ∀ q : RankThreeWhitneyModel.LowerSheet,
      RankThreeWhitneyModel.firstSheet q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
          d.chart.source
  upper_source :
    ∀ q : RankThreeWhitneyModel.UpperSheet,
      RankThreeWhitneyModel.secondSheet h q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 2))) ∈
          e.chart.source
  lower :
    ∀ q : RankThreeWhitneyModel.LowerSheet,
      RankThreeWhitneyModel.firstSheet q ∈ chart.source →
        chart (RankThreeWhitneyModel.firstSheet q) =
          d.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)
  upper :
    ∀ q : RankThreeWhitneyModel.UpperSheet,
      RankThreeWhitneyModel.secondSheet h q ∈ chart.source →
        chart (RankThreeWhitneyModel.secondSheet h q) =
          e.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)

theorem TubularBigon.RankThreeTangentAdaptedChart.nonempty_rankThreeSheetParametrizedChart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Nonempty (TubularBigon.RankThreeSheetParametrizedChart tube d e) := by
  have hinj :
    Set.InjOn c.correctedCoordinates
      (WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)}) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩ ⟨q, w⟩ ⟨hq, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [c.correctedCoordinates_zero, c.correctedCoordinates_zero] at heq
    exact Prod.ext (congrArg (fun v : (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3) => v.1) heq) rfl
  have hlocal :
    ∀
      p ∈
        WhitneyPairModel.bigon h ×ˢ
          {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)},
      IsLocalDiffeomorphAt 𝓘(ℝ, RankThreeWhitneyModel.Space)
        𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) ∞ c.correctedCoordinates p := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply
      isLocalDiffeomorphAt_of_contMDiffOn (D := RankThreeWhitneyModel.Space) (E :=
        (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) (M := (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3))
        c.isOpen_nonlinearDomain (c.nonlinearDomain_contains_zero hp)
        c.contDiffOn_correctedCoordinates.contMDiffOn
    rw [mfderiv_eq_fderiv, (c.hasFDerivAt_correctedCoordinates_zero hp).fderiv]
    exact
      FrameField.isInvertible_shearedBlock (c.base p) (c.normal p)
        (c.normal_invertible p (c.contains hp))
  have hzeroDomain :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      c.nonlinearDomain := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.nonlinearDomain_contains_zero hp
  obtain ⟨χ, hzeroχ, hχD, hχ⟩ :=
    exists_partialDiffeomorph_near_compact
      ((WhitneyPairModel.isCompact_bigon tube.height_pos).prod isCompact_singleton) hinj
      hlocal c.isOpen_nonlinearDomain hzeroDomain
  let Φ := χ.trans tube.chart
  have hzeroΦ :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      Φ.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hzeroχ ⟨hp, rfl⟩, ?_⟩
    change χ (p, 0) ∈ tube.chart.source
    rw [hχ, c.correctedCoordinates_zero]
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, hsource⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset
      (WhitneyPairModel.isCompact_bigon tube.height_pos) Φ.open_source hzeroΦ
  have hformula (p : RankThreeWhitneyModel.Space) :
    Φ p = tube.chart (c.correctedCoordinates p) := by
    change tube.chart (χ p) = tube.chart (c.correctedCoordinates p)
    rw [hχ]
  refine
    ⟨{  radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := ?_
        target_subset := fun _ hy => hy.1
        lower_source := fun q hq => (c.lower_native_parameters (hχD hq.1)).1
        upper_source := fun q hq => (c.upper_native_parameters (hχD hq.1)).1
        lower := ?_
        upper := ?_ }⟩
  · intro p
    rw [hformula, c.correctedCoordinates_zero, tube.zero_section]
  · intro q hq
    rw [hformula, c.correctedCoordinates_lower_of_mem_domain (hχD hq.1)]
    exact tube.chart.right_inv' (c.lower_native_parameters (hχD hq.1)).2
  · intro q hq
    rw [hformula, c.correctedCoordinates_upper_of_mem_domain (hχD hq.1)]
    exact tube.chart.right_inv' (c.upper_native_parameters (hχD hq.1)).2

theorem TubularBigon.nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeSheetParametrizedChart tube d e) := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeTangentAdaptedChart_of_opposite_corner_signs d e hsign
  exact c.nonempty_rankThreeSheetParametrizedChart

theorem TubularBigon.RankThreeSheetParametrizedChart.lower_mem_sheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.chart.source) :
    c.chart (RankThreeWhitneyModel.firstSheet q) ∈ S := by
  rw [c.lower q hq]
  exact (d.sheet _ (c.lower_source q hq)).mpr rfl

theorem TubularBigon.RankThreeSheetParametrizedChart.upper_mem_sheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.chart.source) :
    c.chart (RankThreeWhitneyModel.secondSheet h q) ∈ T := by
  rw [c.upper q hq]
  exact (e.sheet _ (c.upper_source q hq)).mpr rfl

theorem SheetRecognition.eventually_mem_sheet_iff {W D B E M : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞)
    (ψ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {S : Set M}
    (hsheet : ∀ q ∈ ψ.source, ψ q ∈ S ↔ q.2 = 0) {ι : D → W} (hι : Continuous ι) {σ τ : D → D}
    (hτ : Continuous τ) (hτσ : Function.LeftInverse τ σ) (hστ : Function.RightInverse τ σ)
    (hparam : ∀ q : D, ι q ∈ Φ.source → (σ q, (0 : B)) ∈ ψ.source ∧ Φ (ι q) = ψ (σ q, 0)) {q₀ : D}
    (hq₀ : ι q₀ ∈ Φ.source) : ∀ᶠ z in 𝓝 (ι q₀), z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ Set.range ι) := by
  let recover : W → W := fun z => ι (τ ((ψ.symm (Φ z)).1))
  have htarget : Φ (ι q₀) ∈ ψ.target := by
    rw [(hparam q₀ hq₀).2]
    exact ψ.map_source' (hparam q₀ hq₀).1
  have hΦ : ContinuousAt Φ (ι q₀) :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hq₀)).continuousAt
  have hψ : ContinuousAt ψ.symm (Φ (ι q₀)) :=
    (ψ.contMDiffOn_invFun.contMDiffAt (ψ.open_target.mem_nhds htarget)).continuousAt
  have hrec : ContinuousAt recover (ι q₀) :=
    hι.continuousAt.comp (hτ.continuousAt.comp (continuousAt_fst.comp (hψ.comp hΦ)))
  have hreczero : recover (ι q₀) = ι q₀ := by
    have hcoord : ψ.symm (Φ (ι q₀)) = (σ q₀, (0 : B)) := by
      rw [(hparam q₀ hq₀).2]
      exact ψ.left_inv' (hparam q₀ hq₀).1
    change ι (τ ((ψ.symm (Φ (ι q₀))).1)) = ι q₀
    rw [hcoord]
    exact congrArg ι (hτσ q₀)
  have hrecSource : ∀ᶠ z in 𝓝 (ι q₀), recover z ∈ Φ.source :=
    hrec.preimage_mem_nhds (by rw [hreczero]; exact Φ.open_source.mem_nhds hq₀)
  have htargetNear : ∀ᶠ z in 𝓝 (ι q₀), Φ z ∈ ψ.target :=
    hΦ.preimage_mem_nhds (ψ.open_target.mem_nhds htarget)
  filter_upwards [Φ.open_source.mem_nhds hq₀, htargetNear, hrecSource] with z hz hzψ hzrec
  refine ⟨hz, ?_⟩
  constructor
  · intro hzS
    let q := ψ.symm (Φ z)
    have hq : q ∈ ψ.source := ψ.map_target' hzψ
    have hqzero : q.2 = 0 :=
      (hsheet q hq).mp
        (by
          change ψ (ψ.symm (Φ z)) ∈ S
          have he : ψ (ψ.symm (Φ z)) = Φ z := ψ.right_inv' hzψ
          rw [he]
          exact hzS)
    have heq : Φ (recover z) = Φ z := by
      change Φ (ι (τ q.1)) = Φ z
      rw [(hparam (τ q.1) hzrec).2, hστ q.1]
      have hqeq : (q.1, (0 : B)) = q := by
        apply Prod.ext
        · rfl
        · exact hqzero.symm
      rw [hqeq]
      exact ψ.right_inv' hzψ
    exact ⟨τ q.1, Φ.toPartialEquiv.injOn hzrec hz heq⟩
  · rintro ⟨q, hqz⟩
    have hq : ι q ∈ Φ.source := hqz.symm ▸ hz
    rw [← hqz, (hparam q hq).2]
    exact (hsheet _ (hparam q hq).1).mpr rfl

def WhitneyPairModel.sheetTimeInverse {A : Type*} (q : (ℝ × A)) : (ℝ × A) :=
  (2 * q.1 - 1, q.2)

theorem WhitneyPairModel.contDiff_sheetTimeInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : ContDiff ℝ ∞ (sheetTimeInverse (A := A)) := by
  unfold sheetTimeInverse
  fun_prop

theorem WhitneyPairModel.sheetTimeInverse_leftInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : Function.LeftInverse (sheetTimeInverse (A := A)) sheetTimeCoordinates := by
  intro q
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · change 2 * ((q.1 + 1) / 2) - 1 = q.1
    ring
  · rfl

theorem WhitneyPairModel.sheetTimeInverse_rightInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : Function.RightInverse (sheetTimeInverse (A := A)) sheetTimeCoordinates := by
  intro q
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · change (2 * q.1 - 1 + 1) / 2 = q.1
    ring
  · rfl

theorem TubularBigon.RankThreeSheetParametrizedChart.eventually_lower_mem_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.chart.source) :
    ∀ᶠ z in 𝓝 (RankThreeWhitneyModel.firstSheet q),
      z ∈ c.chart.source ∧
        (c.chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet) :=
  SheetRecognition.eventually_mem_sheet_iff c.chart d.chart d.sheet
    RankThreeWhitneyModel.contDiff_firstSheet.continuous
    WhitneyPairModel.contDiff_sheetTimeInverse.continuous
    WhitneyPairModel.sheetTimeInverse_leftInverse
    WhitneyPairModel.sheetTimeInverse_rightInverse
    (fun q hq => ⟨c.lower_source q hq, c.lower q hq⟩) hq

theorem TubularBigon.RankThreeSheetParametrizedChart.eventually_upper_mem_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.chart.source) :
    ∀ᶠ z in 𝓝 (RankThreeWhitneyModel.secondSheet h q),
      z ∈ c.chart.source ∧
        (c.chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h)) :=
  SheetRecognition.eventually_mem_sheet_iff c.chart e.chart e.sheet
    (RankThreeWhitneyModel.contDiff_secondSheet h).continuous
    WhitneyPairModel.contDiff_sheetTimeInverse.continuous
    WhitneyPairModel.sheetTimeInverse_leftInverse
    WhitneyPairModel.sheetTimeInverse_rightInverse
    (fun q hq => ⟨c.upper_source q hq, c.upper q hq⟩) hq

structure TubularBigon.SheetParametrizedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h)
    (d :
      StripNormalData WhitneyPairModel.Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData WhitneyPairModel.Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T
        l.map) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, WhitneyPairModel.Space) 𝓘(ℝ, E) WhitneyPairModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  lower_source :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.firstSheet q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
          d.chart.source
  upper_source :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.secondSheet h q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
          e.chart.source
  lower :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.firstSheet q ∈ chart.source →
        chart (WhitneyPairModel.firstSheet q) =
          d.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)
  upper :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.secondSheet h q ∈ chart.source →
        chart (WhitneyPairModel.secondSheet h q) =
          e.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)

theorem TubularBigon.lower_center_mem_sheet {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k.map l.map h n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : tube.map (2 * t - 1, 0) ∈ S := by
  rw [tube.lower t ht, ← k.center t ht]
  exact
    (k.first_sheet (t, 0)
          (k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩)).mpr
      rfl

theorem TubularBigon.upper_center_mem_sheet {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k.map l.map h n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : tube.map (WhitneyPairModel.upperBoundaryArc h t) ∈ T := by
  change tube.map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ T
  rw [tube.upper t ht, ← l.center t ht]
  exact
    (l.first_sheet (t, 0)
          (l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩)).mpr
      rfl

theorem TubularBigon.map_mem_first_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k.map l.map h n) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) : tube.map p ∈ S ↔ p.2 = 0 := by
  constructor
  · intro hpS
    have hfront : p ∈ frontier (WhitneyPairModel.bigon h) := by
      rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
      exact ⟨hp, fun hi => tube.interior_avoids p hi (Or.inl hpS)⟩
    obtain ⟨t, ht, rfl | rfl⟩ :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos p).mp hfront
    · rfl
    · have hlt : (t, (0 : ℝ)) ∈ l.domain :=
        l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
      rw [tube.upper t ht, ← l.center t ht] at hpS
      rcases (l.second_sheet (t, 0) hlt).mp hpS with ht0 | ht1
      · change t = 0 at ht0
        rw [ht0]
        norm_num
      · change t = 1 at ht1
        rw [ht1]
        norm_num
  · intro hpzero
    have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    have ht : WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
      change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * WhitneyPairModel.arcTime p - 1 := by
      dsimp [WhitneyPairModel.arcTime]; ring
    have heq : p = (2 * WhitneyPairModel.arcTime p - 1, 0) := Prod.ext hbase hpzero
    rw [heq]
    exact tube.lower_center_mem_sheet ht

theorem TubularBigon.map_mem_second_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k.map l.map h n) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) : tube.map p ∈ T ↔ p.2 = h * (1 - p.1 ^ 2) := by
  constructor
  · intro hpT
    have hfront : p ∈ frontier (WhitneyPairModel.bigon h) := by
      rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
      exact ⟨hp, fun hi => tube.interior_avoids p hi (Or.inr hpT)⟩
    obtain ⟨t, ht, rfl | rfl⟩ :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos p).mp hfront
    · have hkt : (t, (0 : ℝ)) ∈ k.domain :=
        k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
      rw [tube.lower t ht, ← k.center t ht] at hpT
      rcases (k.second_sheet (t, 0) hkt).mp hpT with ht0 | ht1
      · change t = 0 at ht0
        rw [ht0]
        norm_num
      · change t = 1 at ht1
        rw [ht1]
        norm_num
    · rfl
  · intro hpupper
    have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    have ht : WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
      change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * WhitneyPairModel.arcTime p - 1 := by
      dsimp [WhitneyPairModel.arcTime]; ring
    have heq : p = WhitneyPairModel.upperBoundaryArc h (WhitneyPairModel.arcTime p) :=
      by
      apply Prod.ext hbase
      change p.2 = h * (1 - (2 * WhitneyPairModel.arcTime p - 1) ^ 2)
      rw [← hbase]
      exact hpupper
    rw [heq]
    exact tube.upper_center_mem_sheet ht

theorem SheetRecognition.exists_open_recognition_domain {W E M : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞)
    {S : Set M} {A K : Set W} (hS : IsClosed S) (hK : K ⊆ Φ.source)
    (hforward : ∀ z ∈ Φ.source, z ∈ A → Φ z ∈ S)
    (hlocal : ∀ z ∈ Φ.source, z ∈ A → ∀ᶠ w in 𝓝 z, w ∈ Φ.source ∧ (Φ w ∈ S ↔ w ∈ A))
    (hcontact : ∀ z ∈ K, Φ z ∈ S ↔ z ∈ A) :
    ∃ U : Set W, IsOpen U ∧ K ⊆ U ∧ U ⊆ Φ.source ∧ ∀ z ∈ U, Φ z ∈ S ↔ z ∈ A := by
  have hnear : ∀ z ∈ K, ∀ᶠ w in 𝓝 z, w ∈ Φ.source ∧ (Φ w ∈ S ↔ w ∈ A) := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact hlocal z (hK hz) hzA
    have hzS : Φ z ∉ S := fun hs => hzA ((hcontact z hz).mp hs)
    have hΦ : ContinuousAt Φ z :=
      (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hK hz))).continuousAt
    have havoid : ∀ᶠ w in 𝓝 z, Φ w ∉ S := hΦ.preimage_mem_nhds (hS.isOpen_compl.mem_nhds hzS)
    filter_upwards [Φ.open_source.mem_nhds (hK hz), havoid] with w hw hwS
    exact ⟨hw, ⟨fun hs => (hwS hs).elim, fun ha => (hwS (hforward w hw ha)).elim⟩⟩
  let U := interior {z : W | z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ A)}
  have hsub : U ⊆ {z : W | z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ A)} := interior_subset
  exact
    ⟨U, isOpen_interior, fun z hz => mem_interior_iff_mem_nhds.mpr (hnear z hz), fun _ hz =>
      (hsub hz).1, fun _ hz => (hsub hz).2⟩

theorem RankThreeWhitneyModel.zero_mem_firstSheet_iff (p : ℝ × ℝ) :
    (p, (0 : Lower × Upper)) ∈ Set.range firstSheet ↔ p.2 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact (congrArg (fun z : Space => z.1.2) hq).symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

theorem RankThreeWhitneyModel.zero_mem_secondSheet_iff (h : ℝ) (p : ℝ × ℝ) :
    (p, (0 : Lower × Upper)) ∈ Set.range (secondSheet h) ↔ p.2 = h * (1 - p.1 ^ 2) := by
  constructor
  · rintro ⟨q, hq⟩
    have hs : q.1 = p.1 := congrArg (fun z : Space => z.1.1) hq
    have ht : h * (1 - q.1 ^ 2) = p.2 := congrArg (fun z : Space => z.1.2) hq
    rw [hs] at ht
    exact ht.symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

theorem TubularBigon.RankThreeSheetParametrizedChart.exists_open_full_sheet_neighborhood
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e) (hS : IsClosed S)
    (hT : IsClosed T) :
    ∃ U : Set RankThreeWhitneyModel.Space,
      IsOpen U ∧
        WhitneyPairModel.bigon h ×ˢ
              {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
            U ∧
          U ⊆ c.chart.source ∧
            (∀ z ∈ U, c.chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet) ∧
              ∀ z ∈ U,
                c.chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h) := by
  have hzero :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      c.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩
  have hfirst :
    ∀
      z ∈
        WhitneyPairModel.bigon h ×ˢ
          {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)},
      c.chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact
      (tube.map_mem_first_iff hp).trans
        (RankThreeWhitneyModel.zero_mem_firstSheet_iff p).symm
  have hsecond :
    ∀
      z ∈
        WhitneyPairModel.bigon h ×ˢ
          {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)},
      c.chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact
      (tube.map_mem_second_iff hp).trans
        (RankThreeWhitneyModel.zero_mem_secondSheet_iff h p).symm
  obtain ⟨U, hU, hKU, hUsource, hUS⟩ :=
    SheetRecognition.exists_open_recognition_domain c.chart (A :=
      Set.range RankThreeWhitneyModel.firstSheet) hS hzero
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.lower_mem_sheet hz)
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.eventually_lower_mem_iff hz)
      hfirst
  obtain ⟨V, hV, hKV, -, hVT⟩ :=
    SheetRecognition.exists_open_recognition_domain c.chart (A :=
      Set.range (RankThreeWhitneyModel.secondSheet h)) hT hzero
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.upper_mem_sheet hz)
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.eventually_upper_mem_iff hz)
      hsecond
  exact
    ⟨U ∩ V, hU.inter hV, fun z hz => ⟨hKU hz, hKV hz⟩, fun _ hz => hUsource hz.1, fun z hz =>
      hUS z hz.1, fun z hz => hVT z hz.2⟩

def RankThreeWhitneyModel.nativeFirstSheet {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) : Set M :=
  Φ '' (Set.range firstSheet ∩ Φ.source)

def RankThreeWhitneyModel.nativeSecondSheet {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) (h : ℝ) : Set M :=
  Φ '' (Set.range (secondSheet h) ∩ Φ.source)

structure TubularBigon.RankThreeCompatibleChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      RankThreeWhitneyModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  first_sheet :
    ∀ z ∈ chart.source, chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet
  second_sheet :
    ∀ z ∈ chart.source, chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h)

theorem TubularBigon.RankThreeSheetParametrizedChart.nonempty_rankThreeCompatibleChart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e) (hS : IsClosed S)
    (hT : IsClosed T) : Nonempty (TubularBigon.RankThreeCompatibleChart tube) := by
  obtain ⟨U, hU, hKU, hUsource, hfirst, hsecond⟩ := c.exists_open_full_sheet_neighborhood hS hT
  have hlocal :
    IsLocalDiffeomorphOn 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E) ∞ c.chart U := fun z =>
    ⟨c.chart, hUsource z.property, fun _ _ => rfl⟩
  let Φ :=
    partialDiffeomorphOfInjectiveLocal hU (c.chart.toPartialEquiv.injOn.mono hUsource)
      hlocal
  have hzero :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      Φ.source :=
    hKU
  obtain ⟨ε, hε, hsource⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset
      (WhitneyPairModel.isCompact_bigon tube.height_pos) Φ.open_source hzero
  refine
    ⟨{  radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := c.zero_section
        target_subset := ?_
        first_sheet := hfirst
        second_sheet := hsecond }⟩
  intro y hy
  change y ∈ c.chart '' U at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact c.target_subset (c.chart.map_source' (hUsource hz))

theorem TubularBigon.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeCompatibleChart tube) := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs d e hsign
  exact c.nonempty_rankThreeCompatibleChart hS hT

theorem TubularBigon.RankThreeCompatibleChart.nativeFirstSheet_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    RankThreeWhitneyModel.nativeFirstSheet c.chart = S ∩ c.chart.target := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzModel, hzSource⟩, rfl⟩
    exact ⟨(c.first_sheet z hzSource).mpr hzModel, c.chart.map_source' hzSource⟩
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    refine ⟨c.chart.symm y, ⟨?_, hz⟩, hzy⟩
    apply (c.first_sheet _ hz).mp
    change c.chart (c.chart.symm y) ∈ S
    rw [hzy]
    exact hy.1

theorem TubularBigon.RankThreeCompatibleChart.nativeSecondSheet_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    RankThreeWhitneyModel.nativeSecondSheet c.chart h = T ∩ c.chart.target := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzModel, hzSource⟩, rfl⟩
    exact ⟨(c.second_sheet z hzSource).mpr hzModel, c.chart.map_source' hzSource⟩
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    refine ⟨c.chart.symm y, ⟨?_, hz⟩, hzy⟩
    apply (c.second_sheet _ hz).mp
    change c.chart (c.chart.symm y) ∈ T
    rw [hzy]
    exact hy.1

theorem RankThreeWhitneyModel.GraphMotion.exists_native_cancellation {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (Φ :
      PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) J
        RankThreeWhitneyModel.Space M ∞)
    {h : ℝ} (a : RankThreeWhitneyModel.GraphMotion h Φ.source) (hh : 0 < h) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    Disjoint
                      ((fun y => A (1, y)) '' RankThreeWhitneyModel.nativeFirstSheet Φ)
                      (RankThreeWhitneyModel.nativeSecondSheet Φ h) := by
  have hsource : ∀ t, Set.MapsTo (fun z => a.family (t, z)) Φ.source Φ.source := by
    intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hdfix : ∀ z ∉ a.support, d z = z := fun z hz => (hd z).trans (a.fixed t z hz)
    intro z hz
    change a.family (t, z) ∈ Φ.source
    rw [← hd z]
    exact SupportedDiffeomorph.mapsTo_source Φ d.toEquiv a.support_subset hdfix hz
  let A : ℝ × M → M := fun p =>
    SupportedDiffeomorph.extendMap Φ (fun z => a.family (p.1, z)) p.2
  have hcompact : IsCompact (Φ '' a.support) :=
    a.compact_support.image_of_continuousOn
      (Φ.contMDiffOn_toFun.continuousOn.mono a.support_subset)
  have htarget : Φ '' a.support ⊆ Φ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact Φ.map_source' (a.support_subset hz)
  have hfamily :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, RankThreeWhitneyModel.Space))
      𝓘(ℝ, RankThreeWhitneyModel.Space) ∞ a.family := by
    exact a.smooth.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  refine
    ⟨Φ '' a.support, hcompact, htarget, A,
      SupportedDiffeomorph.contMDiff_extendFamily Φ hfamily a.compact_support
        a.support_subset a.fixed hsource,
      ?_, ?_, ?_, ?_⟩
  · intro y
    have hzero : (fun z => a.family (0, z)) = id := funext a.initial
    change SupportedDiffeomorph.extendMap Φ (fun z => a.family (0, z)) y = y
    rw [hzero]
    exact SupportedDiffeomorph.extendMap_id Φ y
  · intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hdfix : ∀ z ∉ a.support, d z = z := fun z hz => (hd z).trans (a.fixed t z hz)
    refine ⟨SupportedDiffeomorph.extension Φ d a.compact_support a.support_subset hdfix, ?_⟩
    intro y
    change
      SupportedDiffeomorph.extendMap Φ (fun z => a.family (t, z)) y =
        SupportedDiffeomorph.extendMap Φ d y
    exact
      congrArg
        (fun f : RankThreeWhitneyModel.Space → RankThreeWhitneyModel.Space =>
          SupportedDiffeomorph.extendMap Φ f y)
        (funext (fun z => (hd z).symm))
  · intro t y hy
    exact SupportedDiffeomorph.extendMap_eq_of_notMem_image Φ (a.fixed t) hy
  · rw [Set.disjoint_left]
    intro y hy₁ hy₂
    obtain ⟨x, hx, hxy⟩ := hy₁
    obtain ⟨z, ⟨⟨p, hp⟩, hz⟩, hzx⟩ := hx
    obtain ⟨w, ⟨⟨q, hq⟩, hw⟩, hwy⟩ := hy₂
    have hleft : A (1, Φ z) = y := by rw [hzx]; exact hxy
    have hcomm : A (1, Φ z) = Φ (a.family (1, z)) :=
      SupportedDiffeomorph.extendMap_chart Φ (fun v => a.family (1, v)) hz
    have heq : a.family (1, z) = w :=
      Φ.toPartialEquiv.injOn (hsource 1 hz) hw (hcomm.symm.trans (hleft.trans hwy.symm))
    apply a.firstSheet_ne_secondSheet hh p q
    rw [hp, hq]
    exact heq

theorem RankThreeWhitneyModel.exists_supported_native_bigon_cancellation {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) {h : ℝ} (hh : 0 < h)
    (hsource : ∀ p ∈ WhitneyPairModel.bigon h, (p, (0 : Lower × Upper)) ∈ Φ.source) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    Disjoint ((fun y => A (1, y)) '' nativeFirstSheet Φ)
                      (nativeSecondSheet Φ h) := by
  obtain ⟨a⟩ := nonempty_graphMotion hh Φ.open_source hsource
  exact a.exists_native_cancellation Φ hh

theorem SupportedDiffeomorph.image_inter_eq_diff {X : Type*} (d : X ≃ X) {S T U : Set X}
    (hfix : ∀ x ∉ U, d x = x) (hdisjoint : Disjoint (d '' (S ∩ U)) (T ∩ U)) :
    (d '' S) ∩ T = (S ∩ T) \ U := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hyT⟩
    have hyU : y ∉ U := by
      intro hy
      have hxU : x ∈ U := by
        by_contra hnot
        have he : x = y := (hfix x hnot).symm.trans hxy
        exact hnot (he.symm ▸ hy)
      exact Set.disjoint_left.mp hdisjoint ⟨x, ⟨hx, hxU⟩, hxy⟩ ⟨hyT, hy⟩
    have he : x = y := d.injective (hxy.trans (hfix y hyU).symm)
    exact ⟨⟨he ▸ hx, hyT⟩, hyU⟩
  · rintro ⟨⟨hyS, hyT⟩, hyU⟩
    exact ⟨⟨y, hyS, hfix y hyU⟩, hyT⟩

theorem SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal {X Y : Type*}
    (d : X ≃ X) (F : Y → X) {T R : Set X} (hfix : ∀ y ∈ (Set.range F ∩ T) \ R, d y = y)
    (himage : (d '' Set.range F) ∩ T = (Set.range F ∩ T) \ R) :
    (d ∘ F) ⁻¹' T = (F ⁻¹' T) \ (F ⁻¹' R) := by
  ext x
  constructor
  · intro hx
    have hy : d (F x) ∈ (d '' Set.range F) ∩ T := ⟨⟨F x, ⟨x, rfl⟩, rfl⟩, hx⟩
    rw [himage] at hy
    have heq : F x = d (F x) := d.injective (hfix _ hy).symm
    change F x ∈ T ∧ F x ∉ R
    rw [heq]
    exact ⟨hy.1.2, hy.2⟩
  · intro hx
    have hy : F x ∈ (Set.range F ∩ T) \ R := ⟨⟨⟨x, rfl⟩, hx.1⟩, hx.2⟩
    change d (F x) ∈ T
    rw [hfix _ hy]
    exact hx.1

theorem SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {d : X → X} {F : Y → X} {K : Set X}
    (hK : IsClosed K) (hfix : ∀ y ∉ K, d y = y) (hF : Continuous F) {x : Y} (hx : F x ∉ K) :
    (d ∘ F) =ᶠ[𝓝 x] F := by
  filter_upwards [hF.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hx)] with y hy
  exact hfix _ hy

theorem RankThreeWhitneyModel.firstSheet_eq_secondSheet_iff {h : ℝ} (hh : 0 < h)
    (p : LowerSheet) (q : UpperSheet) :
    firstSheet p = secondSheet h q ↔ p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 0 ∧ (q.1 = -1 ∨ q.1 = 1) := by
  rcases p with ⟨s, u⟩
  rcases q with ⟨t, v⟩
  constructor
  · intro heq
    have hst : s = t := congrArg (fun z : Space => z.1.1) heq
    have ht : 0 = h * (1 - t ^ 2) := congrArg (fun z : Space => z.1.2) heq
    have hu : u = 0 := congrArg (fun z : Space => z.2.1) heq
    have hv : v = 0 := (congrArg (fun z : Space => z.2.2) heq).symm
    have hsq : t ^ 2 = 1 := by
      have hz := (mul_eq_zero.mp ht.symm).resolve_left hh.ne'
      linarith
    have hprod : (t + 1) * (t - 1) = 0 := by nlinarith
    refine ⟨hst, hu, hv, ?_⟩
    rcases mul_eq_zero.mp hprod with hm | hp
    · left
      linarith
    · right
      linarith
  · rintro ⟨hst, hu, hv, ht⟩
    change s = t at hst
    change u = 0 at hu
    change v = 0 at hv
    subst s
    subst u
    subst v
    rcases ht with ht | ht
    · change t = -1 at ht
      subst t
      simp [firstSheet, secondSheet]
    · change t = 1 at ht
      subst t
      simp [firstSheet, secondSheet]

theorem TubularBigon.RankThreeCompatibleChart.intersection_in_target_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    (S ∩ T) ∩ c.chart.target = {a 0, a 1} := by
  have hc0 : c.chart (RankThreeWhitneyModel.firstSheet (-1, 0)) = a 0 := by
    calc
      c.chart (RankThreeWhitneyModel.firstSheet (-1, 0)) = tube.map (-1, 0) :=
        c.zero_section (-1, 0)
      _ = a 0 := by simpa using tube.lower 0 (by simp)
  have hc1 : c.chart (RankThreeWhitneyModel.firstSheet (1, 0)) = a 1 := by
    calc
      c.chart (RankThreeWhitneyModel.firstSheet (1, 0)) = tube.map (1, 0) :=
        c.zero_section (1, 0)
      _ = a 1 := by
        have he := tube.lower 1 (by simp)
        norm_num at he
        exact he
  have hcorner :
    ∀ s : ℝ,
      s = -1 ∨ s = 1 →
        c.chart (RankThreeWhitneyModel.firstSheet (s, 0)) ∈ (S ∩ T) ∩ c.chart.target := by
    intro s hs
    have hb : (s, (0 : ℝ)) ∈ WhitneyPairModel.bigon h := by
      rcases hs with rfl | rfl <;> simp [WhitneyPairModel.bigon]
    have hsource : RankThreeWhitneyModel.firstSheet (s, 0) ∈ c.chart.source :=
      c.source_contains ⟨hb, Metric.mem_closedBall_self c.radius_pos.le⟩
    refine
      ⟨⟨(c.first_sheet _ hsource).mpr ⟨(s, 0), rfl⟩, (c.second_sheet _ hsource).mpr ?_⟩,
        c.chart.map_source' hsource⟩
    refine ⟨(s, 0), ?_⟩
    rcases hs with rfl | rfl <;>
      simp [RankThreeWhitneyModel.firstSheet, RankThreeWhitneyModel.secondSheet]
  ext y
  change y ∈ (S ∩ T) ∩ c.chart.target ↔ y = a 0 ∨ y = a 1
  constructor
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    have hlo : c.chart.symm y ∈ Set.range RankThreeWhitneyModel.firstSheet := by
      apply (c.first_sheet _ hz).mp
      change c.chart (c.chart.symm y) ∈ S
      rw [hzy]
      exact hy.1.1
    have hhi : c.chart.symm y ∈ Set.range (RankThreeWhitneyModel.secondSheet h) := by
      apply (c.second_sheet _ hz).mp
      change c.chart (c.chart.symm y) ∈ T
      rw [hzy]
      exact hy.1.2
    obtain ⟨p, hp⟩ := hlo
    obtain ⟨q, hq⟩ := hhi
    obtain ⟨hst, hu, _, hends⟩ :=
      (RankThreeWhitneyModel.firstSheet_eq_secondSheet_iff tube.height_pos p q).mp
        (hp.trans hq.symm)
    have hpq : p = (q.1, 0) := Prod.ext hst hu
    rw [hpq] at hp
    have hycorner : y = c.chart (RankThreeWhitneyModel.firstSheet (q.1, 0)) :=
      hzy.symm.trans (congrArg c.chart hp.symm)
    rcases hends with hm | hp
    · left
      rw [hm] at hycorner
      exact hycorner.trans hc0
    · right
      rw [hp] at hycorner
      exact hycorner.trans hc1
  · rintro (rfl | rfl)
    · rw [← hc0]
      exact hcorner (-1) (Or.inl rfl)
    · rw [← hc1]
      exact hcorner 1 (Or.inr rfl)

theorem TubularBigon.RankThreeCompatibleChart.exists_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) [T2Space M] :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ c.chart.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨K, hK, hKsource, A, hA, hzero, hdiff, hfix, hdisjoint⟩ :=
    RankThreeWhitneyModel.exists_supported_native_bigon_cancellation c.chart tube.height_pos
      (fun _ hp => c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩)
  rw [c.nativeFirstSheet_eq, c.nativeSecondSheet_eq] at hdisjoint
  obtain ⟨d, hd⟩ := hdiff 1
  have hdfix : ∀ y ∉ c.chart.target, d y = y := by
    intro y hy
    exact (hd y).symm.trans (hfix 1 y (fun h => hy (hKsource h)))
  have hdeq : (fun y => A (1, y)) = d := funext hd
  have hdisjoint' : Disjoint (d '' (S ∩ c.chart.target)) (T ∩ c.chart.target) := by
    rw [← hdeq]
    exact hdisjoint
  have hinter : (d '' S) ∩ T = (S ∩ T) \ c.chart.target :=
    SupportedDiffeomorph.image_inter_eq_diff d.toEquiv hdfix hdisjoint'
  refine ⟨K, hK, hKsource, A, hA, hzero, hdiff, hfix, ?_⟩
  rw [hdeq, hinter, ← c.intersection_in_target_eq]
  ext y
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  tauto

theorem TubularBigon.RankThreeCompatibleChart.exists_relative_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ c.chart.target ∧
          Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
                    (∀ t y, y ∉ K → A (t, y) = y) ∧
                      ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨K, hK, hKt, A, hA⟩ := c.exists_cancellation
  refine ⟨K, hK, hKt, ?_, A, hA⟩
  apply Set.disjoint_left.mpr
  intro y hyK hy
  have hc : y ∈ (S ∩ T) ∩ c.chart.target := ⟨hy.1, hKt hyK⟩
  rw [c.intersection_in_target_eq] at hc
  exact hy.2 hc

theorem TubularBigon.exists_rankThree_relative_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ tube.chart.target ∧
          Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = D y) ∧
                    (∀ t y, y ∉ K → A (t, y) = y) ∧
                      ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs d e hS hT hsign
  obtain ⟨K, hK, hKt, hd, A, hA⟩ := c.exists_relative_cancellation
  exact ⟨K, hK, hKt.trans c.target_subset, hd, A, hA⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_belt_whitney_cancellation_of_opposite_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : ManifoldMorse.MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g
            D.surgery.beltSphere x y)
      (x₀ x₁ : Hemisphere.Sphere 2),
      x₀ ∈ D.beltIntersectionPoints 2 g →
        x₁ ∈ D.beltIntersectionPoints 2 g →
          D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1 →
            ∃ K : Set D.UpperLevel,
              IsCompact K ∧
                Disjoint K ((Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁}) ∧
                  ∃ A : ℝ × D.UpperLevel → D.UpperLevel,
                    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, RegularLevel.Model E))
                        𝓘(ℝ, RegularLevel.Model E) ∞ A ∧
                      (∀ y, A (0, y) = y) ∧
                        (∀ t,
                            ∃ e :
                              Diffeomorph 𝓘(ℝ, RegularLevel.Model E)
                                𝓘(ℝ, RegularLevel.Model E) D.UpperLevel D.UpperLevel ∞,
                              ∀ y, A (t, y) = e y) ∧
                          (∀ t y, y ∉ K → A (t, y) = y) ∧
                            ((fun y => A (1, y)) '' Set.range g) ∩
                                Set.range D.surgery.beltSphere =
                              (Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁} := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  intro hg hinj hi ht x₀ x₁ hx₀ hx₁ hsign
  obtain ⟨y₀, hy₀⟩ := hx₀
  obtain ⟨y₁, hy₁⟩ := hx₁
  have hne : x₀ ≠ x₁ := by
    intro heq
    rw [heq] at hsign
    have hs : ∀ s : SignType, s * s ≠ -1 := by decide
    exact hs _ hsign
  obtain ⟨a, b, ha₀, ha₁, _, _, k₀, k₁, l₀, l₁, k, l, ⟨d⟩, ⟨e⟩, htube⟩ :=
    D.exists_belt_tubular_strip_pair hf hdim hindex hnull g hg hinj hi (fun x y hxy => ht x y hxy)
      x₀ x₁ y₀ y₁ hy₀ hy₁ hne
  obtain ⟨tube⟩ := htube 1 (by norm_num)
  have hcenter₀ : g x₀ = d.chart (StripCoordinates.center 0) :=
    ha₀.symm.trans ((k.center 0 (by simp)).symm.trans (d.center 0))
  have hcenter₁ : g x₁ = d.chart (StripCoordinates.center 1) :=
    ha₁.symm.trans ((k.center 1 (by simp)).symm.trans (d.center 1))
  have hcorner :=
    (D.opposite_beltIntersectionSigns_iff_Whitney_corners hf hdim hindex r g hg hinj hi ht tube d
          e x₀ x₁ hcenter₀ hcenter₁).mp
      hsign
  obtain ⟨K, hK, _, hdisjoint, A, hA, hA₀, hAt, hfix, hcancel⟩ :=
    tube.exists_rankThree_relative_cancellation d e (isCompact_range g.continuous).isClosed
      D.belt_isClosedEmbedding.isClosed_range hcorner
  rw [ha₀, ha₁] at hcancel hdisjoint
  exact ⟨K, hK, hdisjoint, A, hA, hA₀, hAt, hfix, hcancel⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.exists_signed_belt_cancellation_step {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g
            D.surgery.beltSphere x y)
      (x₀ x₁ : Hemisphere.Sphere 2),
      x₀ ∈ D.beltIntersectionPoints 2 g →
        x₁ ∈ D.beltIntersectionPoints 2 g →
          D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1 →
            ∃ e :
              Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
                D.UpperLevel D.UpperLevel ∞,
              ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
                SupportedDiffeomorph.IsotopicToIdentity e ∧
                  (∀ x, g' x = e (g x)) ∧
                    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g' ∧
                      Function.Injective g' ∧
                        (∀ x,
                            Function.Injective
                              (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x)) ∧
                          (∀ x y,
                              NativeTransversality.At (𝓡 2) (𝓡 3)
                                𝓘(ℝ, RegularLevel.Model E) g' D.surgery.beltSphere x y) ∧
                            D.beltIntersectionPoints 2 g' =
                                D.beltIntersectionPoints 2 g \ { x₀, x₁ } ∧
                              (∀ x ∈ D.beltIntersectionPoints 2 g',
                                  (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                                ∀ x ∈ D.beltIntersectionPoints 2 g',
                                  D.beltIntersectionSign 2 r g' x =
                                    D.beltIntersectionSign 2 r g x := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg hinj hi ht x₀ x₁ hx₀ hx₁ hsign
  obtain ⟨K, hK, hdis, A, hA, hA₀, hAt, hfix, hcancel⟩ :=
    D.exists_belt_whitney_cancellation_of_opposite_signs hf hdim hindex hnull r g hg hinj hi ht x₀
      x₁ hx₀ hx₁ hsign
  obtain ⟨e, he⟩ := hAt 1
  have hisotopy : SupportedDiffeomorph.IsotopicToIdentity e := ⟨A, hA, hA₀, he, hAt⟩
  have hfixe : ∀ y ∉ K, e y = y := fun y hy => (he y).symm.trans (hfix 1 y hy)
  have hfun : (fun y => A (1, y)) = e := funext he
  rw [hfun] at hcancel
  let g' : C(Hemisphere.Sphere 2, D.UpperLevel) := ⟨e ∘ g, e.continuous.comp g.continuous⟩
  have hg' : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g' := e.contMDiff.comp hg
  have hinj' : Function.Injective g' := e.injective.comp hinj
  have hi' : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x) := by
    intro x
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (e ∘ g) x)
    rw [mfderiv_comp x (e.mdifferentiable (by simp) _) (hg.mdifferentiableAt (by simp))]
    exact
      ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective (by trivial)).comp
        (hi x)
  have hfixR : ∀ y ∈ (Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁}, e y = y := by
    intro y hy
    exact hfixe y (fun hyK => Set.disjoint_left.mp hdis hyK hy)
  have hpre :=
    SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal e.toEquiv
      (g : Hemisphere.Sphere 2 → D.UpperLevel) hfixR hcancel
  have hp : (g : Hemisphere.Sphere 2 → D.UpperLevel) ⁻¹' {g x₀, g x₁} = { x₀, x₁ } := by
    ext x
    change (g x = g x₀ ∨ g x = g x₁) ↔ (x = x₀ ∨ x = x₁)
    exact or_congr hinj.eq_iff hinj.eq_iff
  have hpoints : D.beltIntersectionPoints 2 g' = D.beltIntersectionPoints 2 g \ { x₀, x₁ } :=
    hpre.trans
      (congrArg (fun s : Set (Hemisphere.Sphere 2) => D.beltIntersectionPoints 2 g \ s) hp)
  have hgerm :
    ∀ x ∈ D.beltIntersectionPoints 2 g',
      (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g := by
    intro x hx
    have hxold : x ∈ D.beltIntersectionPoints 2 g \ { x₀, x₁ } := hpoints ▸ hx
    have hy : g x ∈ (Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁} := by
      refine ⟨⟨⟨x, rfl⟩, hxold.1⟩, ?_⟩
      change x ∉ (g : Hemisphere.Sphere 2 → D.UpperLevel) ⁻¹' {g x₀, g x₁}
      rw [hp]
      exact hxold.2
    exact
      SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed hK.isClosed hfixe
        g.continuous (fun hyK => Set.disjoint_left.mp hdis hyK hy)
  have ht' :
    ∀ x y,
      NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g'
        D.surgery.beltSphere x y := by
    intro x y hxy
    have hx : x ∈ D.beltIntersectionPoints 2 g' := ⟨y, hxy⟩
    have hnear := hgerm x hx
    have hpoint : g' x = g x := hnear.eq_of_nhds
    have hder :
      (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] RegularLevel.Model E) =
        mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x :=
      hnear.mfderiv_eq
    change
      Function.Surjective
        ((mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x :
              EuclideanSpace ℝ (Fin 2) →L[ℝ] RegularLevel.Model E).coprod
          (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) D.surgery.beltSphere y :
            EuclideanSpace ℝ (Fin 3) →L[ℝ] RegularLevel.Model E))
    rw [hder]
    exact ht x y (hxy.trans hpoint)
  refine ⟨e, g', hisotopy, fun _ => rfl, hg', hinj', hi', ht', hpoints, hgerm, ?_⟩
  intro x hx
  have hnormal : (D.beltNormal ∘ g') =ᶠ[𝓝 x] (D.beltNormal ∘ g) := by
    filter_upwards [hgerm x hx] with z hz
    exact congrArg D.beltNormal hz
  have hder :
    (mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g') x :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates) =
      mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g) x :=
    hnormal.mfderiv_eq
  have hjac : D.beltIntersectionJacobian 2 r g' x = D.beltIntersectionJacobian 2 r g x :=
    congrArg
      (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates =>
        SphereNormalCoordinates.normalJacobian r x L)
      hder
  exact congrArg SignType.sign hjac

def ManifoldMorse.MorseSurgeryData.IsTransverseBeltSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel)) : Prop :=
  letI := RegularLevel.chartedSpace hf D.upper_regular
  letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧
    Function.Injective g ∧
      (∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x)) ∧
        ∀ x y,
          NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g
            D.surgery.beltSphere x y

theorem ManifoldMorse.MorseSurgeryData.finite_points_of_isTransverseBeltSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [T2Space M] [CompactSpace M] (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    {g : C(Hemisphere.Sphere 2, D.UpperLevel)}
    (hg : D.IsTransverseBeltSphere hf hdim hindex g) : (D.beltIntersectionPoints 2 g).Finite := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hs, hinj, _, ht⟩ := hg
  exact D.finite_beltIntersectionPoints hf 3 2 hindex g hs hinj ht

attribute [local instance 100] Classical.propDecidable in
abbrev ManifoldMorse.MorseSurgeryData.HandleDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :=
  MorseHandle.UnitDisk d.chart.NegativeCoordinates ×
    MorseHandle.UnitDisk d.chart.PositiveCoordinates

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.handleMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) : C(d.HandleDomain, M) :=
  d.chart.attachingHandleMap d.radius d.radius_pos d.block

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.handleFacePoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates)
    (v : MorseHandle.UnitDisk d.chart.PositiveCoordinates) : d.HandleDomain :=
  (⟨u, Metric.sphere_subset_closedBall u.property⟩, v)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.handleMap_core {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    d.handleMap (d.handleFacePoint u ⟨0, by simp⟩) = (d.surgery.attachingSphere u : M) := by
  rw [d.attaching_eq]
  rfl

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.coreMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(MorseHandle.UnitDisk d.chart.NegativeCoordinates, M) :=
  HandleCoreAttachment.core d.handleMap

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.coreMap_boundary {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    d.coreMap ⟨u, Metric.sphere_subset_closedBall u.property⟩ =
      (d.surgery.attachingSphere u : M) :=
  d.handleMap_core u

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.coreMap_lower_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (u : MorseHandle.UnitDisk d.chart.NegativeCoordinates) :
    f (d.coreMap u) ≤ f p - d.radius ^ 2 ↔ ‖(u : d.chart.NegativeCoordinates)‖ = 1 :=
  d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block (u, ⟨0, by simp⟩)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.coreMap_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] :
    Topology.IsClosedEmbedding d.coreMap := by
  apply d.coreMap.continuous.isClosedEmbedding
  intro x y hxy
  have heq :=
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block).injective hxy
  exact congrArg Prod.fst heq

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.coreUnionHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f) :
    ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) ≃ₕ
      { y : M // f y ≤ f p + d.radius ^ 2 } :=
  (ClosedHandleCore.unionHomotopyEquiv {y : M | f y ≤ f p - d.radius ^ 2} d.handleMap
        (isClosed_le hf continuous_const)
        (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
        (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)).trans
    d.attachmentHomeomorph.toHomotopyEquiv

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.coreCellPresentation {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    EmbeddedCellAttachment d.chart.NegativeCoordinates
      ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
  EmbeddedCellAttachment.ofUnion _ d.coreMap (isClosed_le hf continuous_const)
    d.coreMap_isClosedEmbedding d.coreMap_lower_iff

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.cellOldHomeomorph {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    { y : M // f y ≤ f p - d.radius ^ 2 } ≃ₜ (d.coreCellPresentation hf).old
    where
  toFun x := ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.coreBoundaryMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.NegativeCoordinates) 1, { y : M // f y ≤ f p - d.radius ^ 2 }) :=
  (⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩ :
        C(d.LowerLevel, { y : M // f y ≤ f p - d.radius ^ 2 })).comp
    d.surgery.attachingSphere

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.coreCell_attaching_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    (d.coreCellPresentation hf).attachingSphere =
      (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun.comp d.coreBoundaryMap := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  exact d.coreMap_boundary u

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.realizedLowerInclusion {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) :
    C({ y : M // f y ≤ f p - d.radius ^ 2 }, { y : M // f y ≤ f p + d.radius ^ 2 }) :=
  ⟨fun x => d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩,
    d.attachmentHomeomorph.continuous.comp (continuous_inclusion (fun _ hx => Or.inl hx))⟩

theorem AdaptedWindows.forward_limit_below_regular_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f) (x : { y : M // f y = a })
    {p : M} (hlim : Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p)) : f p < a := by
  obtain ⟨r, hr, q, hq, -, hqLim, hheight⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct (x : M)
  have hqp : q = p := tendsto_nhds_unique hqLim hlim
  have hh := (hheight (hreg x x.property)).1
  simpa only [hqp, x.property] using hh

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.place_one_handle_in_distinct_minimum_basins {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : ManifoldMorse.criticalPoints E f) (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v)) :
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ d :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data q).LowerLevel (S.data q).LowerLevel ∞,
      SupportedDiffeomorph.IsotopicToIdentity d ∧
        ∃ p r : ManifoldMorse.criticalPoints E f,
          MorseCancellation.nativeMorseIndex E f p = 0 ∧
            MorseCancellation.nativeMorseIndex E f r = 0 ∧
              p ≠ r ∧
                f p < S.toSurgeryWindows.lower q ∧
                  f r < S.toSurgeryWindows.lower q ∧
                    Filter.Tendsto
                        (fun t => S.flow t (d ((S.data q).surgery.attachingSphere u)).val)
                        Filter.atTop (𝓝 p.val) ∧
                      Filter.Tendsto
                          (fun t => S.flow t (d ((S.data q).surgery.attachingSphere v)).val)
                          Filter.atTop (𝓝 r.val) ∧
                        ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
                          Filter.Tendsto
                              (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
                              Filter.atTop (𝓝 p.val) ∨
                            Filter.Tendsto
                              (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
                              Filter.atTop (𝓝 r.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := RegularLevel.isManifold hf (S.data q).lower_regular
  let ι : C((S.data q).LowerLevel, { z : M // f z ≤ S.toSurgeryWindows.lower q }) :=
    ⟨fun x => ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩
  let α := (S.data q).surgery.attachingSphere
  have hxy : α u ≠ α v := by
    intro h
    have hh : (S.data q).coreBoundaryMap u = (S.data q).coreBoundaryMap v := congrArg ι h
    exact hnot (hh ▸ Joined.refl _)
  obtain ⟨d, hd, ⟨p, hp, hpu⟩, ⟨r, hr, hrv⟩⟩ :=
    MorseCancellation.exists_isotopic_two_points_in_dense (J := 𝓘(ℝ, RegularLevel.Model E))
      (S.dense_regular_level_minimum_basins hf (S.data q).lower_regular) hxy
  have hpq := S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α u)) hpu
  have hrq := S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α v)) hrv
  have hpr : p ≠ r := by
    intro h
    subst r
    let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
    have hnew : Joined (ι (d (α u))) (ι (d (α v))) :=
      MorseCancellation.joined_sublevel_of_common_forward_limit S.flow hf.continuous
        (FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent)
        (ι (d (α u))) (ι (d (α v))) hpq hpu hrv
    exact
      hnot
        (((MorseCancellation.isotopicToIdentity_joined hd (α u)).map ι.continuous).trans
          (hnew.trans ((MorseCancellation.isotopicToIdentity_joined hd (α v)).map ι.continuous).symm))
  refine ⟨d, hd, p, r, hp, hr, hpr, hpq, hrq, hpu, hrv, ?_⟩
  intro w
  have hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  have huv : u ≠ v := fun h => hxy (congrArg α h)
  rcases MorseCancellation.unitSphere_eq_two_points_of_finrank_one hindex u v huv w with h | h
  · subst w
    exact Or.inl hpu
  · subst w
    exact Or.inr hrv

theorem MorseCancellation.fderiv_beltPassage_upper_fst {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s w : ℝ) (u : N) (v : P) :
    (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s w).1 = (ρ * w) • u := by
  have hfirst : HasDerivAt (fun t : ℝ => (BeltPassage.upper ρ t u v).1) (ρ • u) s := by
    simpa only [BeltPassage.upper, id_eq, mul_one] using
      ((hasDerivAt_id s).const_mul ρ).smul_const u
  have hchain :
    fderiv ℝ (fun t => (BeltPassage.upper ρ t u v).1) s =
      (ContinuousLinearMap.fst ℝ N P).comp
        (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s) := by
    have hh :=
      fderiv_comp s (ContinuousLinearMap.fst ℝ N P).differentiableAt
        ((BeltPassage.contDiff_upper ρ u v).differentiable (by simp) s)
    rw [(ContinuousLinearMap.fst ℝ N P).fderiv] at hh
    exact hh
  have hh := congrArg (fun L : ℝ →L[ℝ] N => L w) hchain
  rw [hfirst.hasFDerivAt.fderiv] at hh
  change w • (ρ • u) = (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s w).1 at hh
  rw [smul_smul, mul_comm w ρ] at hh
  exact hh.symm

theorem MorseCancellation.injective_fderiv_beltPassage_upper {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : ρ ≠ 0) (s : ℝ)
    {u : N} (hu : u ≠ 0) (v : P) :
    Function.Injective (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s) := by
  intro a b hab
  have hh := congrArg Prod.fst hab
  rw [fderiv_beltPassage_upper_fst, fderiv_beltPassage_upper_fst] at hh
  exact mul_left_cancel₀ hρ (smul_left_injective ℝ hu hh)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltArc_derivative_injective {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (nativeBeltArc S q u v) s) := by
  have ht := nativeBeltArc_coordinates_mem_target S q u v hs
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  change
    Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        ((S.data q).chart.splitChart.symm ∘
          (fun t => BeltPassage.upper (S.data q).radius t u.val v.val))
        s)
  rw [mfderiv_comp s ((S.data q).chart.splitChart.symm.mdifferentiableAt (by simp) ht)
      ((BeltPassage.contDiff_upper (S.data q).radius u.val
            v.val).contMDiff.mdifferentiableAt
        (by simp)),
    mfderiv_eq_fderiv]
  exact
    (PartialChart.bijective_mfderiv (S.data q).chart.splitChart.symm ht).injective.comp
      (injective_fderiv_beltPassage_upper (S.data q).radius_pos.ne' s hu v.val)

theorem RegularLevel.contMDiffWithinAt_iff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) (S : Set X) (x : X) :
    letI := chartedSpace hf hreg
    ContMDiffWithinAt I 𝓘(ℝ, Model E) ∞ g S x ↔
      ContMDiffWithinAt I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) S x := by
  let _ := chartedSpace hf hreg
  constructor
  · intro hg
    exact (RegularLevel.contMDiff_inclusion hf hreg).contMDiffAt.comp_contMDiffWithinAt x hg
  · intro hg
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr hg.continuousWithinAt, ?_⟩
    let Φ := heightChart hf hreg (g x)
    have hΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) ∞ Φ (g x) :=
      Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (heightChart_mem_source hf hreg (g x)))
    have hcomp := hΦ.comp_contMDiffWithinAt x hg
    change ContMDiffWithinAt I 𝓘(ℝ, Model E) ∞ (fun y => (Φ (g y)).2) S x
    exact contDiff_snd.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hcomp

theorem RegularLevel.contMDiffOn_iff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) (S : Set X) :
    letI := chartedSpace hf hreg
    ContMDiffOn I 𝓘(ℝ, Model E) ∞ g S ↔ ContMDiffOn I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) S := by
  let _ := chartedSpace hf hreg
  exact
    forall_congr'
      (fun x => forall_congr' (fun _ => contMDiffWithinAt_iff_inclusion hf hreg I g S x))

attribute [local instance 100] Classical.propDecidable in
def MorseCancellation.nativeBeltLevelArc {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : ℝ) :
    (S.data q).UpperLevel :=
  if hs : |s| ≤ 1 then ⟨nativeBeltArc S q u v s, nativeBeltArc_height S q u v hs⟩
  else (S.data q).surgery.beltSphere v

theorem MorseCancellation.nativeBeltLevelArc_coe {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    (nativeBeltLevelArc S q u v s).val = nativeBeltArc S q u v s := by
  simp only [nativeBeltLevelArc, dif_pos hs]

theorem MorseCancellation.nativeBeltLevelArc_coe_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    (Subtype.val ∘ nativeBeltLevelArc S q u v) =ᶠ[𝓝 s] nativeBeltArc S q u v := by
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  exact nativeBeltLevelArc_coe S q u v (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)

theorem MorseCancellation.nativeBeltLevelArc_contMDiffOn {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} [FiniteDimensional ℝ E] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) ∞ (nativeBeltLevelArc S q u v)
      (Set.Ioo (-1 : ℝ) 1) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  apply
    (RegularLevel.contMDiffOn_iff_inclusion hf (S.data q).upper_regular 𝓘(ℝ, ℝ)
        (nativeBeltLevelArc S q u v) (Set.Ioo (-1 : ℝ) 1)).mpr
  apply (nativeBeltArc_contMDiffOn S q u v).congr
  intro s hs
  exact nativeBeltLevelArc_coe S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

theorem MorseCancellation.nativeBeltLevelArc_derivative_injective {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} [FiniteDimensional ℝ E] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) (nativeBeltLevelArc S q u v) s) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  have hg := nativeBeltLevelArc_coe_germ S q u v hs
  apply
    RegularLevel.injective_mfderiv_of_inclusion hf (S.data q).upper_regular 𝓘(ℝ, ℝ)
      (nativeBeltLevelArc S q u v) s
  · exact
      ((nativeBeltArc_contMDiffOn S q u v).contMDiffAt
            (Ioo_mem_nhds hs.1 hs.2)).congr_of_eventuallyEq
        hg
  · rw [hg.mfderiv_eq]
    exact nativeBeltArc_derivative_injective S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltLevelArc_normal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (q : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    (S.data q).beltNormal (nativeBeltLevelArc S q u v s) = ((S.data q).radius * s) • u.val := by
  change ((S.data q).chart.splitChart (nativeBeltLevelArc S q u v s).val).1 = _
  rw [nativeBeltLevelArc_coe S q u v hs]
  exact
    congrArg Prod.fst
      ((S.data q).chart.splitChart.right_inv' (nativeBeltArc_coordinates_mem_target S q u v hs))

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeBeltLevelArc_transverse {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f)
    (hq : nativeMorseIndex E f q = 1) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    Function.Surjective
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) (nativeBeltLevelArc S q u v) 0 :
            ℝ →L[ℝ] RegularLevel.Model E).coprod
        (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let d := S.data q
  let γ := nativeBeltLevelArc S q u v
  let L : ℝ →L[ℝ] d.chart.NegativeCoordinates :=
    ContinuousLinearMap.toSpanSingleton ℝ (d.radius • u.val)
  have hpoint : γ 0 = d.surgery.beltSphere v :=
    Subtype.ext
      ((nativeBeltLevelArc_coe S q u v (s := 0) (by simp)).trans (nativeBeltArc_zero S q u v))
  have hgerm : d.beltNormal ∘ γ =ᶠ[𝓝 (0 : ℝ)] L := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < 1 by norm_num)] with
      s hs
    change d.beltNormal (nativeBeltLevelArc S q u v s) = s • (d.radius • u.val)
    rw [nativeBeltLevelArc_normal S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩), smul_smul,
      mul_comm s d.radius]
  have hnormalDerivative :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ γ) 0 = L := by
    rw [hgerm.mfderiv_eq, mfderiv_eq_fderiv, L.fderiv]
  have hγ :=
    (nativeBeltLevelArc_contMDiffOn S hf q u v).contMDiffAt
      (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))
  have hnormal :=
    (d.contMDiffOn_beltNormal hf).contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  let A : ℝ →L[ℝ] RegularLevel.Model E :=
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) γ 0
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  let Q : RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
      (d.surgery.beltSphere v)
  have hnγ :
    MDifferentiableAt 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
      d.beltNormal (γ 0) := by
    rw [hpoint]
    exact hnormal.mdifferentiableAt (by simp)
  have hQA : Q.comp A = L := by
    have hh := mfderiv_comp 0 hnγ (hγ.mdifferentiableAt (by simp))
    rw [hpoint] at hh
    exact hh.symm.trans hnormalDerivative
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hLi : Function.Injective L := smul_left_injective ℝ (smul_ne_zero d.radius_pos.ne' hu)
  have hdim : Module.finrank ℝ ℝ = Module.finrank ℝ d.chart.NegativeCoordinates := by
    rw [Module.finrank_self]
    exact ((nativeMorseIndex_eq_chart d.chart).symm.trans hq).symm
  have hLs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) hdim).mp hLi
  have hQAs : Function.Surjective (Q.comp A) := hQA.symm ▸ hLs
  have hker : B.range = Q.ker := d.range_belt_derivative_eq_normal_kernel hf n v
  change Function.Surjective (A.coprod B)
  intro z
  obtain ⟨s, hs⟩ := hQAs (Q z)
  have hmem : z - A s ∈ Q.ker := by
    change Q (z - A s) = 0
    change Q (A s) = Q z at hs
    rw [map_sub, hs, sub_self]
  rw [← hker] at hmem
  obtain ⟨w, hw⟩ := hmem
  change B w = z - A s at hw
  refine ⟨(s, w), ?_⟩
  change A s + B w = z
  rw [hw]
  abel

theorem MorseCancellation.transverse_circle_of_arc_germ {D G H N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] {α : ℝ → N}
    {γ : Circle → N} {ψ : ℝ → Circle} (hγ : ContMDiff (𝓡 1) J ∞ γ)
    (hψ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ψ) (hgerm : γ ∘ ψ =ᶠ[𝓝 (0 : ℝ)] α) (B : D →L[ℝ] G)
    (htrans : Function.Surjective ((mfderiv 𝓘(ℝ, ℝ) J α 0 : ℝ →L[ℝ] G).coprod B)) :
    Function.Surjective ((mfderiv (𝓡 1) J γ (ψ 0) : EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod B) :=
  by
  let A : EuclideanSpace ℝ (Fin 1) →L[ℝ] G := mfderiv (𝓡 1) J γ (ψ 0)
  let P : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) ψ 0
  let A₀ : ℝ →L[ℝ] G := mfderiv 𝓘(ℝ, ℝ) J α 0
  have hc := mfderiv_comp 0 (hγ.mdifferentiableAt (by simp)) (hψ.mdifferentiableAt (by simp))
  have heq : A.comp P = A₀ := hc.symm.trans hgerm.mfderiv_eq
  intro y
  obtain ⟨⟨a, b⟩, hab⟩ := htrans y
  refine ⟨(P a, b), ?_⟩
  have ha := congrArg (fun L : ℝ →L[ℝ] G => L a) heq
  change A (P a) + B b = y
  change A (P a) = A₀ a at ha
  rw [ha]
  exact hab

theorem MorseCancellation.surjective_coprod_comp_left {A A' B G : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup A'] [NormedSpace ℝ A'] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : A →L[ℝ] G) (R : B →L[ℝ] G)
    (P : A' →L[ℝ] A) (hP : Function.Surjective P) (htrans : Function.Surjective (L.coprod R)) :
    Function.Surjective ((L.comp P).coprod R) := by
  intro y
  obtain ⟨⟨a, b⟩, hab⟩ := htrans y
  obtain ⟨a', ha⟩ := hP a
  refine ⟨(a', b), ?_⟩
  change L (P a') + R b = y
  rw [ha]
  exact hab

def MorseCancellation.euclideanTail (n : ℕ) :
    Hemisphere.Ambient (n + 1) →L[ℝ] Hemisphere.Ambient n :=
  ({    toFun := fun x => WithLp.toLp 2 (fun i : Fin n => x i.succ)
        map_add' := by intro x y; ext i; rfl
        map_smul' := by intro a x; ext i; rfl } :
      Hemisphere.Ambient (n + 1) →ₗ[ℝ] Hemisphere.Ambient n).toContinuousLinearMap

theorem MorseCancellation.euclideanTail_hemisphere {n : ℕ} (b : Bool) (x : Hemisphere.Ball n) :
    euclideanTail n (Hemisphere.point b x).val = x.val := by
  ext i
  rfl

theorem MorseCancellation.exists_belt_point_avoiding_smooth_image {E M D H Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace Y]
    [ChartedSpace H Y] [IsManifold I ∞ Y] [LindelofSpace Y] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] (g : Y → M)
    (hg : ContMDiff I 𝓘(ℝ, E) ∞ g) (hdim : Module.finrank ℝ D < n) :
    ∃ v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1,
      (d.surgery.beltSphere v).val ∉ Set.range g := by
  let b :=
    (stdOrthonormalBasis ℝ d.chart.PositiveCoordinates).reindex
      (finCongr (Fact.out : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1))
  let L : d.chart.PositiveCoordinates ≃ₗᵢ[ℝ] Hemisphere.Ambient (n + 1) := b.repr
  let P : M → Hemisphere.Ambient n := fun x =>
    euclideanTail n (d.radius⁻¹ • L (d.chart.splitChart x).2)
  let U : Set Y := g ⁻¹' d.chart.splitChart.source
  have hU : IsOpen U := d.chart.splitChart.open_source.preimage hg.continuous
  have hPg : ContMDiffOn I 𝓘(ℝ, Hemisphere.Ambient n) ∞ (P ∘ g) U := by
    have hc :
      ContMDiffOn I 𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
        (d.chart.splitChart ∘ g) U :=
      d.chart.splitChart.contMDiffOn_toFun.comp hg.contMDiffOn (fun _ hy => hy)
    let A :
      d.chart.NegativeCoordinates × d.chart.PositiveCoordinates →L[ℝ]
        Hemisphere.Ambient n :=
      (euclideanTail n).comp
        ((d.radius⁻¹ • L.toContinuousLinearEquiv.toContinuousLinearMap).comp
          (ContinuousLinearMap.snd ℝ d.chart.NegativeCoordinates d.chart.PositiveCoordinates))
    have hQ :
      ContDiff ℝ ∞
        (fun z : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates =>
          euclideanTail n (d.radius⁻¹ • L z.2)) :=
      A.contDiff
    exact hQ.contMDiff.comp_contMDiffOn hc
  have hdense :=
    GeneralPosition.dense_compl_manifold_image hU hPg
      (show Module.finrank ℝ D < Module.finrank ℝ (Hemisphere.Ambient n) by
        simpa only [Hemisphere.Ambient, finrank_euclideanSpace_fin] using hdim)
  obtain ⟨x, hxavoid, hxnorm⟩ := hdense.exists_dist_lt 0 (show (0 : ℝ) < 1 by norm_num)
  have hx : ‖x‖ < 1 := by simpa only [dist_zero_left] using hxnorm
  let xB : Hemisphere.Ball n := ⟨x, mem_closedBall_zero_iff.mpr hx.le⟩
  let w := Hemisphere.point Bool.true xB
  let v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1 :=
    ⟨L.symm w.val, by
      rw [mem_sphere_zero_iff_norm, L.symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp w.property⟩
  have hcoord : d.chart.splitChart (d.surgery.beltSphere v).val = (0, d.radius • v.val) := by
    rw [d.belt_eq, d.chart.beltCoreMap_coe]
    exact d.chart.splitChart.right_inv' (d.belt_model_mem_target v)
  have hproject : P (d.surgery.beltSphere v).val = x := by
    change
      euclideanTail n (d.radius⁻¹ • L (d.chart.splitChart (d.surgery.beltSphere v).val).2) = x
    rw [hcoord]
    change euclideanTail n (d.radius⁻¹ • L (d.radius • (L.symm w.val))) = x
    rw [L.map_smul, L.apply_symm_apply, smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul]
    exact euclideanTail_hemisphere Bool.true xB
  refine ⟨v, ?_⟩
  rintro ⟨y, hy⟩
  apply hxavoid
  refine ⟨y, ?_, ?_⟩
  · change g y ∈ d.chart.splitChart.source
    rw [hy]
    exact d.belt_mem_normalDomain v
  · change P (g y) = x
    rw [hy]
    exact hproject

theorem AdaptedWindows.exists_belt_point_reaching_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)] {a : ℝ} (hqa : f q < a)
    {d : ℕ}
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hdim : d < n) :
    ∃ v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
      ((S.data q).surgery.beltSphere v).val ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let K := MorseCancellation.LowBackwardBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := MorseCancellation.lowBackwardBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_low_backward_obstruction_images hf a hlow
  let G : K × V → M := fun z => g z.1 z.2
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ G :=
    MorseCancellation.contMDiff_discrete_family g hg
  have hrange : Set.range G = MorseCancellation.backwardLowBasins S a := by
    rw [hcover]
    exact MorseCancellation.range_discrete_family g
  obtain ⟨v, hv⟩ :=
    MorseCancellation.exists_belt_point_avoiding_smooth_image (S.data q) n G hG
      (show Module.finrank ℝ (Z × V) < n by
        simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim)
  have hforward := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere v)).mpr ⟨v, rfl⟩
  obtain ⟨p, hp, _, _, hback, _, _⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct ((S.data q).surgery.beltSphere v).val
  have hap : a < f p :=
    lt_of_not_ge
      (fun h =>
        hv
          (hrange.symm ▸
            (show ((S.data q).surgery.beltSphere v).val ∈ MorseCancellation.backwardLowBasins S a from
              ⟨⟨p, hp⟩, h, hback⟩)))
  exact
    ⟨v,
      FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
        hforward hap hqa⟩

theorem AdaptedWindows.joinedIn_level_minimum_basin_reaching_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    {a b : ℝ} (hpb : f p < b) (hba : b ≤ a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hlow :
      ∀ q : ManifoldMorse.criticalPoints E f,
        f q ≤ a → MorseCancellation.nativeMorseIndex E f q ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) {x y : M} (hxb : f x = b) (hyb : f y = b)
    (hx : Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val))
    (hy : Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p.val))
    (hxa : x ∈ FlowCancellation.levelBasin S.flow f a)
    (hya : y ∈ FlowCancellation.levelBasin S.flow f a) :
    JoinedIn
      {z : M |
        f z = b ∧
          Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val) ∧
            z ∈ FlowCancellation.levelBasin S.flow f a}
      x y := by
  let _ := S.finite.fintype
  let K := MorseCancellation.LowBackwardBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := MorseCancellation.lowBackwardBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_low_backward_obstruction_images hf a hlow
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun z : K × V => g z.1 z.2) :=
    MorseCancellation.contMDiff_discrete_family g hg
  let G : C(K × V, M) := ⟨fun z => g z.1 z.2, hG.continuous⟩
  have hrange : Set.range G = MorseCancellation.backwardLowBasins S a := by
    rw [hcover]
    exact MorseCancellation.range_discrete_family g
  have hclosed : IsClosed (Set.range G) := by
    rw [hrange]
    exact MorseCancellation.isClosed_backwardLowBasins S hf a
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : M) (hz : z ∈ FlowCancellation.levelBasin S.flow f a) : z ∉ Set.range G := by
    rw [hrange]
    intro hlowz
    have hc : z ∈ (FlowCancellation.levelBasin S.flow f a)ᶜ := by
      rw [MorseCancellation.levelBasin_compl_eq_endpoint_obstruction S hf ha]
      exact Or.inr hlowz
    exact hc hz
  let U : TopologicalSpace.Opens M :=
    ⟨{z | Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val)},
      S.isOpen_minimum_forward_basin hf p hp⟩
  let xU : U := ⟨x, hx⟩
  let yU : U := ⟨y, hy⟩
  have hjoined : Joined xU yU := (S.joinedIn_minimum_basin hf p hp hx hy).joined_subtype
  obtain ⟨η, -, havoid⟩ :=
    MorseCancellation.exists_smooth_path_avoiding_closed_image_in_open U hjoined.somePath G hG hclosed
      hdim' (hnot x hxa) (hnot y hya)
  have hcross (c : ℝ) (hbc : b ≤ c) (hca : c ≤ a) (u : unitInterval) :
    (η u).val ∈ FlowCancellation.levelBasin S.flow f c := by
    obtain ⟨q, hq, _, _, hback, _, _⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct (η u).val
    have hqa : a < f q :=
      lt_of_not_ge
        (fun h =>
          havoid u
            (hrange.symm ▸
              (show (η u).val ∈ MorseCancellation.backwardLowBasins S a from ⟨⟨q, hq⟩, h, hback⟩)))
    exact
      FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
        (η u).property (hca.trans_lt hqa) (hpb.trans_le hbc)
  let _ := RegularLevel.chartedSpace hf hb
  let xL : { z : M // f z = b } := ⟨x, hxb⟩
  let yL : { z : M // f z = b } := ⟨y, hyb⟩
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf hb S.smooth S.flow S.integral
      (fun z hz => S.descent z (hb z hz)) xL
  have hcont : Continuous (fun u : unitInterval => Φ.symm (η u).val) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous (continuous_subtype_val.comp η.continuous)
      (fun u => htarget.symm ▸ hcross b le_rfl hba u)
  have hlevelInverse (z : { w : M // f w = b }) : Φ.symm z.val = (z, 0) := by
    have hs : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hs
    rwa [he] at hi
  let γ : Path x y :=
    { toFun := fun u => (Φ.symm (η u).val).1.val
      continuous_toFun := continuous_subtype_val.comp (continuous_fst.comp hcont)
      source' := by
        rw [η.source]
        exact congrArg (fun z : { w : M // f w = b } × ℝ => z.1.val) (hlevelInverse xL)
      target' := by
        rw [η.target]
        exact congrArg (fun z : { w : M // f w = b } × ℝ => z.1.val) (hlevelInverse yL) }
  refine ⟨γ, fun u => ⟨(Φ.symm (η u).val).1.property, ?_, ?_⟩⟩
  · let z := Φ.symm (η u).val
    have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross b le_rfl hba u)
    have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
    have hlim : Filter.Tendsto (fun t => S.flow t (S.flow z.2 z.1.val)) Filter.atTop (𝓝 p.val) :=
      hflow.symm ▸ (η u).property
    exact (MorseCancellation.flow_time_atTop_limit_iff S.flow z.2 z.1.val p.val).mp hlim
  · let z := Φ.symm (η u).val
    have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross b le_rfl hba u)
    have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
    exact
      (FlowCancellation.levelBasin_flow_iff S.flow f a z.2 z.1.val).mp
        (hflow.symm ▸ hcross a hba le_rfl u)

theorem AdaptedWindows.exists_belt_arc_closing_path_reaching_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val))
    {a : ℝ} (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hv : ((S.data q).surgery.beltSphere v).val ∈ FlowCancellation.levelBasin S.flow f a)
    {d : ℕ}
    (hlow :
      ∀ z : ManifoldMorse.criticalPoints E f,
        f z ≤ a → MorseCancellation.nativeMorseIndex E f z ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) :
    ∃ r : ℝ,
      0 < r ∧
        r < 1 ∧
          (∀ s : ℝ,
              |s| ≤ r →
                MorseCancellation.nativeBeltArc S q u v s ∈
                  FlowCancellation.levelBasin S.flow f a) ∧
            (∀ s : ℝ,
                0 < |s| →
                  |s| ≤ r →
                    Filter.Tendsto (fun t => S.flow t (MorseCancellation.nativeBeltArc S q u v s))
                      Filter.atTop (𝓝 p.val)) ∧
              JoinedIn
                {z : M |
                  f z = S.toSurgeryWindows.upper q ∧
                    Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val) ∧
                      z ∈ FlowCancellation.levelBasin S.flow f a}
                (MorseCancellation.nativeBeltArc S q u v r) (MorseCancellation.nativeBeltArc S q u v (-r)) := by
  obtain ⟨ε, hε, hε1, hmin⟩ :=
    S.exists_two_sided_belt_branch_in_minimum_basin hf p q hp u v hbranches
  have hB : IsOpen (FlowCancellation.levelBasin S.flow f a) :=
    (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (ha z hz))).1
  have hα0 :
    MorseCancellation.nativeBeltArc S q u v 0 ∈ FlowCancellation.levelBasin S.flow f a := by
    rw [MorseCancellation.nativeBeltArc_zero]
    exact hv
  have hc : ContinuousAt (MorseCancellation.nativeBeltArc S q u v) 0 :=
    ((MorseCancellation.nativeBeltArc_contMDiffOn S q u v).contMDiffAt
        (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
          (show (0 : ℝ) < 1 by norm_num))).continuousAt
  have hnear :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      MorseCancellation.nativeBeltArc S q u v s ∈ FlowCancellation.levelBasin S.flow f a :=
    hc.preimage_mem_nhds (hB.mem_nhds hα0)
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hnear
  let r := Min.min (ε / 2) (δ / 2)
  have hr : 0 < r := lt_min (half_pos hε) (half_pos hδ)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrδ : r < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hr1 : r < 1 := hrε.trans_le hε1
  have hreach (s : ℝ) (hs : |s| ≤ r) :
    MorseCancellation.nativeBeltArc S q u v s ∈ FlowCancellation.levelBasin S.flow f a := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hs.trans_lt hrδ
  have hall (s : ℝ) (hs : 0 < |s|) (hsr : |s| ≤ r) :
    Filter.Tendsto (fun t => S.flow t (MorseCancellation.nativeBeltArc S q u v s)) Filter.atTop
      (𝓝 p.val) :=
    hmin s hs (hsr.trans_lt hrε)
  have hpb : f p < S.toSurgeryWindows.upper q :=
    (S.forward_limit_below_regular_level hf (S.data q).lower_regular
          ((S.data q).surgery.attachingSphere u) (hbranches u)).trans
      ((S.toSurgeryWindows.lower_lt_value q).trans (S.toSurgeryWindows.value_lt_upper q))
  have hpr : |r| = r := abs_of_pos hr
  have hmr : |-r| = r := by rw [abs_neg, hpr]
  refine ⟨r, hr, hr1, hreach, hall, ?_⟩
  exact
    S.joinedIn_level_minimum_basin_reaching_level hf p hp hpb hba ha (S.data q).upper_regular hlow
      hdim (MorseCancellation.nativeBeltArc_height S q u v (by rw [hpr]; exact hr1.le))
      (MorseCancellation.nativeBeltArc_height S q u v (by rw [hmr]; exact hr1.le))
      (hall r (hpr.symm ▸ hr) hpr.le) (hall (-r) (hmr.symm ▸ hr) hmr.le) (hreach r hpr.le)
      (hreach (-r) hmr.le)

theorem MorseCancellation.single_belt_intersection_of_arc_and_minimum_range {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {X : Type*}
    {γ : X → (S.data q).UpperLevel} (hγi : Function.Injective γ) {z₀ : X}
    (hzero : γ z₀ = (S.data q).surgery.beltSphere v) {r : ℝ} (hr1 : r ≤ 1)
    (himage :
      ∀ z,
        γ z ∈ nativeBeltLevelArc S q u v '' Set.Icc (-r) r ∨
          Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val)) :
    ∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w := by
  intro z w
  constructor
  · intro hzw
    rcases himage z with hshort | hmin
    · obtain ⟨s, hs, hsz⟩ := hshort
      have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hsw : nativeBeltArc S q u v s = ((S.data q).surgery.beltSphere w).val := by
        rw [← nativeBeltLevelArc_coe S q u v hs1]
        exact congrArg Subtype.val (hsz.trans hzw)
      obtain ⟨-, hvw⟩ := (nativeBeltArc_belt_eq_iff S q u v w hs1).mp hsw
      refine ⟨hγi ?_, hvw⟩
      exact hzw.trans ((congrArg (S.data q).surgery.beltSphere hvw).symm.trans hzero.symm)
    · have hqz := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩
      rw [hzw] at hmin
      exact False.elim (hpq (Subtype.ext (tendsto_nhds_unique hmin hqz)))
  · rintro ⟨rfl, rfl⟩
    exact hzero

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_single_belt_circle_in_open_with_image {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (hpq : p ≠ q) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (O : TopologicalSpace.Opens M) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hshortO : ∀ s ∈ Set.Icc (-r) r, MorseCancellation.nativeBeltArc S q u v s ∈ O)
    (hpath :
      JoinedIn
        {z : M |
          f z = S.toSurgeryWindows.upper q ∧
            Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val) ∧ z ∈ O}
        (MorseCancellation.nativeBeltArc S q u v r) (MorseCancellation.nativeBeltArc S q u v (-r)))
    (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ γ : C(Circle, (S.data q).UpperLevel),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧
        Function.Injective γ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
            (∀ z, (γ z).val ∈ O) ∧
              (∀ s ∈ Set.Icc (-r) r,
                  γ (Circle.exp (2 * Real.pi / (2 * r + 1) * (s + r))) =
                    MorseCancellation.nativeBeltLevelArc S q u v s) ∧
                (∀ z w,
                    γ z = (S.data q).surgery.beltSphere w ↔
                      z = Circle.exp (2 * Real.pi / (2 * r + 1) * r) ∧ v = w) ∧
                  ∀ z,
                    γ z ∈ MorseCancellation.nativeBeltLevelArc S q u v '' Set.Icc (-r) r ∨
                      Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let α := MorseCancellation.nativeBeltLevelArc S q u v
  let U : TopologicalSpace.Opens (S.data q).UpperLevel :=
    ⟨{z | Filter.Tendsto (fun t => S.flow t z.val) Filter.atTop (𝓝 p.val) ∧ z.val ∈ O},
      ((S.isOpen_minimum_forward_basin hf p hp).inter O.isOpen).preimage continuous_subtype_val⟩
  have hpr : |r| ≤ 1 := by rw [abs_of_pos hr]; exact hr1.le
  have hmr : |-r| ≤ 1 := by rw [abs_neg]; exact hpr
  have hplus : α r ∈ U := by
    change Filter.Tendsto (fun t => S.flow t (α r).val) Filter.atTop (𝓝 p.val) ∧ (α r).val ∈ O
    rw [MorseCancellation.nativeBeltLevelArc_coe S q u v hpr]
    exact hpath.source_mem.2
  have hminus : α (-r) ∈ U := by
    change
      Filter.Tendsto (fun t => S.flow t (α (-r)).val) Filter.atTop (𝓝 p.val) ∧ (α (-r)).val ∈ O
    rw [MorseCancellation.nativeBeltLevelArc_coe S q u v hmr]
    exact hpath.target_mem.2
  let η : Path (⟨α r, hplus⟩ : U) (⟨α (-r), hminus⟩ : U) :=
    { toFun := fun t => ⟨⟨hpath.somePath t, (hpath.somePath_mem t).1⟩, (hpath.somePath_mem t).2⟩
      continuous_toFun := (hpath.somePath.continuous.subtype_mk _).subtype_mk _
      source' :=
        Subtype.ext
          (Subtype.ext
            (hpath.somePath.source.trans (MorseCancellation.nativeBeltLevelArc_coe S q u v hpr).symm))
      target' :=
        Subtype.ext
          (Subtype.ext
            (hpath.somePath.target.trans (MorseCancellation.nativeBeltLevelArc_coe S q u v hmr).symm)) }
  have hαi : Set.InjOn α (Set.Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    apply MorseCancellation.nativeBeltArc_injOn S q u v hx hy
    have hh := congrArg Subtype.val hxy
    rw [MorseCancellation.nativeBeltLevelArc_coe S q u v (abs_le.mpr hx),
      MorseCancellation.nativeBeltLevelArc_coe S q u v (abs_le.mpr hy)] at hh
    exact hh
  have hdimL : 3 ≤ Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
    omega
  obtain ⟨γ, hγ, hγi, hγd, hshort, himage⟩ :=
    MorseCancellation.exists_embedded_circle_through_arc U hr hr1
      (MorseCancellation.nativeBeltLevelArc_contMDiffOn S hf q u v) hαi
      (fun _ hs => MorseCancellation.nativeBeltLevelArc_derivative_injective S hf q u v hs) hplus hminus
      η hdimL
  let z₀ := Circle.exp (2 * Real.pi / (2 * r + 1) * r)
  have hzero : γ z₀ = (S.data q).surgery.beltSphere v := by
    have hh := hshort 0 ⟨by linarith, hr.le⟩
    rw [zero_add] at hh
    apply Subtype.ext
    exact
      (congrArg Subtype.val hh).trans
        ((MorseCancellation.nativeBeltLevelArc_coe S q u v (s := 0) (by simp)).trans
          (MorseCancellation.nativeBeltArc_zero S q u v))
  have himage' (z : Circle) :
    γ z ∈ MorseCancellation.nativeBeltLevelArc S q u v '' Set.Icc (-r) r ∨
      Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) := by
    rcases himage (Set.mem_range_self z) with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz.1
  refine ⟨γ, hγ, hγi, hγd, ?_, hshort, ?_, himage'⟩
  · intro z
    rcases himage (Set.mem_range_self z) with hz | hz
    · obtain ⟨s, hs, hsz⟩ := hz
      rw [← hsz,
        MorseCancellation.nativeBeltLevelArc_coe S q u v
          (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)]
      exact hshortO s hs
    · exact hz.2
  · apply
      MorseCancellation.single_belt_intersection_of_arc_and_minimum_range S hf p q hpq u v hγi hzero
        hr1.le
    exact himage'

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_transverse_belt_circle_reaching_level_with_endpoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (hq : MorseCancellation.nativeMorseIndex E f q = 1) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val))
    {a : ℝ} (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hlow :
      ∀ z : ManifoldMorse.criticalPoints E f,
        f z ≤ a → MorseCancellation.nativeMorseIndex E f z ≤ d)
    (hdn : d < n) (hcut : 1 + d < Module.finrank ℝ E) (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
      ∃ γ : C(Circle, (S.data q).UpperLevel),
        ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧
          Function.Injective γ ∧
            (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
              (∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f a) ∧
                ∃ z₀ : Circle,
                  (∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w) ∧
                    (Function.Surjective
                        ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z₀ :
                              EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod
                          (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
                            (S.data q).surgery.beltSphere v))) ∧
                      ∀ z,
                        Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) ∨
                          Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 q.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  have hqa : f q < a := (S.toSurgeryWindows.value_lt_upper q).trans_le hba
  obtain ⟨v, hv⟩ := S.exists_belt_point_reaching_level hf q n hqa hlow hdn
  obtain ⟨r, hr, hr1, hreach, hmin, hpath⟩ :=
    S.exists_belt_arc_closing_path_reaching_level hf p q hp u v hbranches hba ha hv hlow hcut
  let O : TopologicalSpace.Opens M :=
    ⟨FlowCancellation.levelBasin S.flow f a,
      (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
          (fun z hz => S.descent z (ha z hz))).1⟩
  have hpq : p ≠ q := by
    intro heq
    have hh := hp
    rw [heq, hq] at hh
    exact Nat.one_ne_zero hh
  obtain ⟨γ, hγ, hγi, hγd, hγreach, hshort, hsingle, himage⟩ :=
    S.exists_single_belt_circle_in_open_with_image hf p q hp hpq u v O hr hr1
      (fun s hs => hreach s (abs_le.mpr hs)) hpath hdim
  let ψ : ℝ → Circle := fun t => Circle.exp (2 * Real.pi / (2 * r + 1) * (t + r))
  have hψ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ψ :=
    contMDiff_circleExp.comp (contDiff_const.mul (contDiff_id.add contDiff_const)).contMDiff
  have heq : γ ∘ ψ =ᶠ[𝓝 (0 : ℝ)] MorseCancellation.nativeBeltLevelArc S q u v := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hr) hr] with t ht
    exact hshort t ⟨ht.1.le, ht.2.le⟩
  have hendpoints (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) ∨
      Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 q.val) := by
    rcases himage z with hshortz | hzmin
    · obtain ⟨s, hs, hsz⟩ := hshortz
      have hsr : |s| ≤ r := abs_le.mpr hs
      have hs1 : |s| ≤ 1 := hsr.trans hr1.le
      by_cases hs0 : s = 0
      · right
        have hz : (γ z).val = ((S.data q).surgery.beltSphere v).val := by
          rw [← hsz, MorseCancellation.nativeBeltLevelArc_coe S q u v hs1, hs0,
            MorseCancellation.nativeBeltArc_zero]
        rw [hz]
        exact (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere v)).mpr ⟨v, rfl⟩
      · left
        rw [← hsz, MorseCancellation.nativeBeltLevelArc_coe S q u v hs1]
        exact hmin s (abs_pos.mpr hs0) hsr
    · exact Or.inl hzmin
  refine
    ⟨v, γ, hγ, hγi, hγd, hγreach, Circle.exp (2 * Real.pi / (2 * r + 1) * r), hsingle, ?_,
      hendpoints⟩
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v
  have hαtrans :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) (MorseCancellation.nativeBeltLevelArc S q u v)
              0 :
            ℝ →L[ℝ] RegularLevel.Model E).coprod
        B) :=
    MorseCancellation.nativeBeltLevelArc_transverse S hf q hq n u v
  have ht :
    Function.Surjective
      ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ (ψ 0) :
            EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod
        B) :=
    MorseCancellation.transverse_circle_of_arc_germ (D := EuclideanSpace ℝ (Fin n)) (J :=
      𝓘(ℝ, RegularLevel.Model E)) (α := MorseCancellation.nativeBeltLevelArc S q u v) (γ := γ)
      (ψ := ψ) hγ hψ heq B hαtrans
  have hp0 : ψ 0 = Circle.exp (2 * Real.pi / (2 * r + 1) * r) := by
    dsimp [ψ]
    rw [zero_add]
  rw [hp0] at ht
  exact ht

theorem AdaptedWindows.exists_native_level_basin_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) (za : { x : M // f x = a })
    (zb : { x : M // f x = b }) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    ∃ D :
      PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { x : M // f x = a } { x : M // f x = b } ∞,
      D.source = {x | x.val ∈ FlowCancellation.levelBasin S.flow f b} ∧
        D.target = {y | y.val ∈ FlowCancellation.levelBasin S.flow f a} ∧
          ∀ x ∈ D.source, ∃ t : ℝ, S.flow t x.val = (D x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf ha
  let _ := RegularLevel.isManifold hf hb
  let A := { x : M // f x = a }
  let B := { x : M // f x = b }
  obtain ⟨Φa, hsa, hta, hfa, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf ha S.smooth S.flow S.integral
      (fun x hx => S.descent x (ha x hx)) za
  obtain ⟨Φb, hsb, htb, hfb, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf hb S.smooth S.flow S.integral
      (fun x hx => S.descent x (hb x hx)) zb
  let U : Set A := {x | x.val ∈ FlowCancellation.levelBasin S.flow f b}
  let V : Set B := {x | x.val ∈ FlowCancellation.levelBasin S.flow f a}
  let P : A → B := fun x => (Φb.symm x.val).1
  let Q : B → A := fun y => (Φa.symm y.val).1
  have hU : IsOpen U := by
    have hh : IsOpen (FlowCancellation.levelBasin S.flow f b) := htb ▸ Φb.open_target
    exact hh.preimage continuous_subtype_val
  have hV : IsOpen V := by
    have hh : IsOpen (FlowCancellation.levelBasin S.flow f a) := hta ▸ Φa.open_target
    exact hh.preimage continuous_subtype_val
  have hPa (x : A) (t : ℝ) : Φa.symm (S.flow t x.val) = (x, t) := by
    have hs : (x, t) ∈ Φa.source := by rw [hsa]; trivial
    have hh : Φa.symm (Φa (x, t)) = (x, t) := Φa.left_inv' hs
    rwa [hfa] at hh
  have hPb (y : B) (t : ℝ) : Φb.symm (S.flow t y.val) = (y, t) := by
    have hs : (y, t) ∈ Φb.source := by rw [hsb]; trivial
    have hh : Φb.symm (Φb (y, t)) = (y, t) := Φb.left_inv' hs
    rwa [hfb] at hh
  have horbP (x : A) (hx : x ∈ U) : S.flow (-(Φb.symm x.val).2) x.val = (P x).val := by
    have hh : S.flow (Φb.symm x.val).2 (P x).val = x.val :=
      (hfb (Φb.symm x.val)).symm.trans (Φb.right_inv' (htb.symm ▸ hx))
    have hi := congrArg (S.flow (-(Φb.symm x.val).2)) hh
    rw [← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply] at hi
    exact hi.symm
  have horbQ (y : B) (hy : y ∈ V) : S.flow (-(Φa.symm y.val).2) y.val = (Q y).val := by
    have hh : S.flow (Φa.symm y.val).2 (Q y).val = y.val :=
      (hfa (Φa.symm y.val)).symm.trans (Φa.right_inv' (hta.symm ▸ hy))
    have hi := congrArg (S.flow (-(Φa.symm y.val).2)) hh
    rw [← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply] at hi
    exact hi.symm
  have hPU : Set.MapsTo P U V := by
    intro x hx
    have hxa : x.val ∈ FlowCancellation.levelBasin S.flow f a :=
      ⟨0, by simpa only [S.flow.map_zero_apply] using x.property⟩
    change (P x).val ∈ FlowCancellation.levelBasin S.flow f a
    exact
      horbP x hx ▸
        (FlowCancellation.levelBasin_flow_iff S.flow f a (-(Φb.symm x.val).2) x.val).mpr
          hxa
  have hQV : Set.MapsTo Q V U := by
    intro y hy
    have hyb : y.val ∈ FlowCancellation.levelBasin S.flow f b :=
      ⟨0, by simpa only [S.flow.map_zero_apply] using y.property⟩
    change (Q y).val ∈ FlowCancellation.levelBasin S.flow f b
    exact
      horbQ y hy ▸
        (FlowCancellation.levelBasin_flow_iff S.flow f b (-(Φa.symm y.val).2) y.val).mpr
          hyb
  have hQP (x : A) (hx : x ∈ U) : Q (P x) = x := by
    have hh := hPa x (-(Φb.symm x.val).2)
    rw [horbP x hx] at hh
    exact congrArg Prod.fst hh
  have hPQ (y : B) (hy : y ∈ V) : P (Q y) = y := by
    have hh := hPb y (-(Φa.symm y.val).2)
    rw [horbQ y hy] at hh
    exact congrArg Prod.fst hh
  have hPs :
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞ P U := by
    have hh :=
      Φb.contMDiffOn_invFun.comp (RegularLevel.contMDiff_inclusion hf ha).contMDiffOn
        (show Set.MapsTo (Subtype.val : A → M) U Φb.target from fun _ hx => htb.symm ▸ hx)
    exact contMDiff_fst.comp_contMDiffOn hh
  have hQs :
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞ Q V := by
    have hh :=
      Φa.contMDiffOn_invFun.comp (RegularLevel.contMDiff_inclusion hf hb).contMDiffOn
        (show Set.MapsTo (Subtype.val : B → M) V Φa.target from fun _ hy => hta.symm ▸ hy)
    exact contMDiff_fst.comp_contMDiffOn hh
  let D :
    PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) A B ∞ :=
    { toFun := P
      invFun := Q
      source := U
      target := V
      map_source' := hPU
      map_target' := hQV
      left_inv' := hQP
      right_inv' := hPQ
      open_source := hU
      open_target := hV
      contMDiffOn_toFun := hPs
      contMDiffOn_invFun := hQs }
  exact ⟨D, rfl, rfl, fun x hx => ⟨-(Φb.symm x.val).2, horbP x hx⟩⟩

theorem AdaptedWindows.belt_complement_reaches_lower_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (y : (S.data p).UpperLevel) (hy : y ∉ Set.range (S.data p).surgery.beltSphere) :
    y.val ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p) := by
  obtain ⟨a, ha, b, hb, hback, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct y.val
  have hyreg : y.val ∉ ManifoldMorse.criticalPoints E f :=
    (S.data p).upper_regular y.val y.property
  have hbelow : f b < S.toSurgeryWindows.lower p := by
    rcases lt_trichotomy (f b) (f p) with h | h | h
    · exact (S.toSurgeryWindows.value_lt_upper ⟨b, hb⟩).trans (S.separated ⟨b, hb⟩ p h)
    · have heq : b = p.val := S.distinct hb p.property h
      subst b
      exact (hy ((S.belt_basin_iff hf p y).mp hforward)).elim
    · have hup : f y.val < f b := by
        rw [y.property]
        exact (S.separated p ⟨b, hb⟩ h).trans (S.toSurgeryWindows.lower_lt_value ⟨b, hb⟩)
      exact (not_lt_of_ge hup.le (hheights hyreg).1).elim
  have hlow : S.toSurgeryWindows.lower p < f y.val := by
    rw [y.property]
    exact (S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)
  exact
    FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward (hlow.trans (hheights hyreg).2) hbelow

theorem AdaptedWindows.exists_belt_complement_lower_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        ∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  obtain ⟨P, hsource, -, horbit⟩ :=
    S.exists_native_level_basin_transport hf (S.data p).upper_regular (S.data p).lower_regular
      ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u)
  have hsrc (x : ((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel)) :
    x.val ∈ P.source := hsource.symm ▸ S.belt_complement_reaches_lower_level hf p x.val x.property
  let D :
    C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
      (S.data p).LowerLevel) :=
    ⟨fun x => P x.val,
      P.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val hsrc⟩
  refine ⟨D, fun x => horbit x.val (hsrc x), ?_⟩
  intro x y t hty
  obtain ⟨s, hs⟩ := horbit x.val (hsrc x)
  have hshared : S.flow 0 (D x).val = S.flow (s - t) y.val := by
    rw [S.flow.map_zero_apply]
    change (P x.val).val = S.flow (s - t) y.val
    rw [← hs, ← hty, ← S.flow.map_add, sub_add_cancel]
  apply Subtype.ext
  exact
    MorseCancellation.native_same_level_orbit_points hf S.smooth S.flow S.integral
      (fun z hz => S.descent z ((S.data p).lower_regular z hz)) (D x).property y.property hshared

def MorseCancellation.nativeUpperMeridianInComplement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (p : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) :
    C(Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1,
      ((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel))
    where
  toFun u := ⟨nativeUpperMeridian S p v s u, nativeUpperMeridian_avoids_belt S p v s hs u⟩
  continuous_toFun := (nativeUpperMeridian S p v s).continuous.subtype_mk _

theorem MorseCancellation.lower_transport_upperMeridian_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (p : ManifoldMorse.criticalPoints E f)
    (D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel))
    (hD : ∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) :
    D.comp (nativeUpperMeridianInComplement S p v s hs) = nativeLowerMeridian S p v s := by
  apply ContinuousMap.ext
  intro u
  exact
    hD (nativeUpperMeridianInComplement S p v s hs u) (nativeLowerMeridian S p v s u)
      (BeltPassage.time s) (nativeUpperMeridian_flow S p v s hs u)

theorem AdaptedWindows.exists_lower_transport_with_meridians {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
          ∀ (w : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
            (hs : 0 < (s : ℝ)),
            (D.comp (MorseCancellation.nativeUpperMeridianInComplement S p w s hs)).Homotopic
              (S.data p).surgery.attachingSphere := by
  obtain ⟨D, horbit, hunique⟩ := S.exists_belt_complement_lower_transport hf p u v
  refine ⟨D, horbit, hunique, ?_⟩
  intro w s hs
  rw [MorseCancellation.lower_transport_upperMeridian_eq S p D hunique w s hs]
  exact MorseCancellation.nativeLowerMeridian_homotopic_attaching S p w s

theorem AdaptedWindows.exists_lower_passage_homology_relation {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (H : C(ℝ × Hemisphere.Sphere 2, (S.data p).UpperLevel)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (x₀ : Hemisphere.Sphere 2)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : Hemisphere.Sphere 2,
          H (t, x) ∈ Set.range (S.data p).surgery.beltSphere ↔ t = τ ∧ x = x₀) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
          (∀ (w : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
              (hs : 0 < (s : ℝ)),
              (D.comp (MorseCancellation.nativeUpperMeridianInComplement S p w s hs)).Homotopic
                (S.data p).surgery.attachingSphere) ∧
            let G :=
              D.comp
                (PassageHomology.puncturedPassageTrace H
                  (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross)
            (∀ z : ({(τ, x₀)}ᶜ : Set (ℝ × Hemisphere.Sphere 2)),
                z.val.1 ∈ Set.Icc (0 : ℝ) 1 → ∃ t : ℝ, S.flow t (H z.val).val = (G z).val) ∧
              ∀ (ε : ℝ) (hε : 0 < ε) (hεx : ε < Real.exp τ),
                SingularMayerVietoris.singularHomologyMap
                    (G.comp (PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
                  SingularMayerVietoris.singularHomologyMap
                      (G.comp (PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
                    SingularMayerVietoris.singularHomologyMap
                      (G.comp (PassageHomology.cylinderLink τ x₀ ε hε hεx)) 2 := by
  obtain ⟨D, horbit, hunique, hmeridian⟩ := S.exists_lower_transport_with_meridians hf p u v
  refine ⟨D, horbit, hunique, hmeridian, ?_, ?_⟩
  · intro z hz
    have hh :=
      horbit
        (PassageHomology.puncturedPassageTrace H (Set.range (S.data p).surgery.beltSphere)
          hτ x₀ hcross z)
    rw [PassageHomology.puncturedPassageTrace_on_interval H
        (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross z hz] at hh
    exact hh
  · intro ε hε hεx
    exact
      PassageHomology.punctured_cylinder_trace_relation hτ x₀ hε hεx
        (D.comp
          (PassageHomology.puncturedPassageTrace H
            (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross))
        2 (by decide)
theorem PuncturedRadial.toSphere_fromSphere {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) (hr : 0 < r) (u : Metric.sphere (0 : N) 1) :
    toSphere (fromSphere r hr u) = u := by
  apply Subtype.ext
  change ‖r • (u : N)‖⁻¹ • (r • (u : N)) = (u : N)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one,
    inv_smul_smul₀ hr.ne']

def PuncturedRadial.deformation {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (r : ℝ)
    (hr : 0 < r) : (ContinuousMap.id (Space N)).Homotopy ((fromSphere r hr).comp toSphere)
    where
  toFun q := ⟨blendVector r q, blendVector_ne_zero r hr q⟩
  continuous_toFun := (continuous_blendVector r).subtype_mk _
  map_zero_left
    u := by
    apply Subtype.ext
    simp [blendVector]
  map_one_left
    u := by
    apply Subtype.ext
    simp [blendVector, fromSphere, toSphere, RadialExtension.direction, div_eq_mul_inv,
      smul_smul]

def PuncturedRadial.sphereHomotopyEquiv {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) : Metric.sphere (0 : N) 1 ≃ₕ Space N
    where
  toFun := fromSphere r hr
  invFun := toSphere
  left_inv := by
    have heq : toSphere.comp (fromSphere r hr) = ContinuousMap.id (Metric.sphere (0 : N) 1) :=
      ContinuousMap.ext (toSphere_fromSphere r hr)
    rw [heq]
  right_inv := ⟨(deformation r hr).symm⟩

def LocalDegree.linearSphereEquiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    Metric.sphere (0 : E) 1 ≃ₕ PuncturedRadial.Space F :=
  (PuncturedRadial.sphereHomotopyEquiv r hr).trans
    (puncturedLinearHomeomorph L).toHomotopyEquiv

def LocalDegree.BoundaryData.normalizedMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (b : LocalDegree.BoundaryData f L s) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1) :=
  PuncturedRadial.toSphere.comp b.map

def MorseCancellation.radialParameterChart (τ : ℝ) (u : (Hemisphere.Sphere 2)) :
    PartialDiffeomorph (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) (EuclideanSpace ℝ (Fin 3))
      (ℝ × (Hemisphere.Sphere 2)) ∞ := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let b := PassageHomology.cylinderPuncture τ u
  let T : Diffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞ :=
    { toEquiv :=
        { toFun := fun z => b + z
          invFun := fun z => z - b
          left_inv := fun z => add_sub_cancel_left b z
          right_inv := by intro z; simp }
      contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
      contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  exact
    T.toPartialDiffeomorph.trans
      (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).symm

theorem MorseCancellation.radialParameterChart_zero_mem_source (τ : ℝ)
    (u : (Hemisphere.Sphere 2)) :
    (0 : (EuclideanSpace ℝ (Fin 3))) ∈ (radialParameterChart τ u).source := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  change
    (0 : (EuclideanSpace ℝ (Fin 3))) ∈ Set.univ ∧
      PassageHomology.cylinderPuncture τ u + 0 ∈
        (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).target
  rw [add_zero, PassageHomology.radialCylinderChart_mem_target]
  exact
    ⟨Set.mem_univ _,
      norm_pos_iff.mp
        (by rw [PassageHomology.norm_cylinderPuncture]; exact Real.exp_pos τ)⟩

theorem MorseCancellation.radialParameterChart_zero (τ : ℝ) (u : (Hemisphere.Sphere 2)) :
    radialParameterChart τ u 0 = (τ, u) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  change
    (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).symm
        (PassageHomology.cylinderPuncture τ u + 0) =
      (τ, u)
  rw [add_zero]
  have heq :
    PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u (τ, u) =
      PassageHomology.cylinderPuncture τ u :=
    rfl
  rw [← heq]
  exact
    (PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).left_inv
      (PassageHomology.radialCylinderChart_mem_source (EuclideanSpace ℝ (Fin 3)) 2 u
        (τ, u))

theorem MorseCancellation.radialParameterChart_apply (τ : ℝ) (u : (Hemisphere.Sphere 2))
    (z : (EuclideanSpace ℝ (Fin 3))) (hz : PassageHomology.cylinderPuncture τ u + z ≠ 0) :
    radialParameterChart τ u z =
      (PassageHomology.radialCylinderHomeomorph (EuclideanSpace ℝ (Fin 3))).symm
        ⟨PassageHomology.cylinderPuncture τ u + z, hz⟩ := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact
    PassageHomology.radialCylinderChart_symm_eq (EuclideanSpace ℝ (Fin 3)) 2 u
      (PassageHomology.cylinderPuncture τ u + z) hz

theorem MorseCancellation.radialParameterChart_link (τ : ℝ) (u : (Hemisphere.Sphere 2)) (ε : ℝ)
    (hε : 0 < ε) (hεu : ε < Real.exp τ) (w : (Hemisphere.Sphere 2)) :
    radialParameterChart τ u (ε • w.val) =
      (PassageHomology.cylinderLink τ u ε hε hεu w).val := by
  have hz : PassageHomology.cylinderPuncture τ u + ε • w.val ≠ 0 :=
    (PassageHomology.linkingSphere (PassageHomology.cylinderPuncture τ u) ε hε
          (by rwa [PassageHomology.norm_cylinderPuncture]) w).property.1
  exact radialParameterChart_apply τ u (ε • w.val) hz

end Mathoverflow1973

end
