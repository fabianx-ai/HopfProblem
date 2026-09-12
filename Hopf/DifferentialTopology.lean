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
Original source lines 80--31127; see PROVENANCE.md.
-/

import Hopf.LibShims
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
import Mathlib

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

attribute [local instance] Smale.NativeEuclideanEmbedding.tangentSpaceT2

attribute [local instance] Smale.NativeEuclideanEmbedding.tangentSpaceT2

attribute [local instance] Smale.NativeEuclideanEmbedding.tangentSpaceT2

theorem MorseCancel.contMDiff_supported_division {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {χ D : M → ℝ}
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ) (hD : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D)
    (hsupp : ∀ x ∈ tsupport χ, D x ≠ 0) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => χ x / D x) := by
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact (hχ x).div₀ (hD x) (hsupp x hx)
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, zero_div]

theorem Degree.FlowCancellation.exists_excursion_interval {X : Type*} [TopologicalSpace X]
    {γ : ℝ → X} (hγ : Continuous γ) {K N : Set X} (hK : IsClosed K) (hKN : K ⊆ N) {a b t : ℝ}
    (ht : t ∈ Set.Icc a b) (ha : γ a ∈ N) (hb : γ b ∈ N) (hout : γ t ∉ N) :
    ∃ s u : ℝ, a ≤ s ∧ s < t ∧ t < u ∧ u ≤ b ∧ γ s ∈ N ∧ γ u ∈ N ∧ ∀ r ∈ Set.Ioo s u, γ r ∉ K := by
  let A := Insert.insert a (Set.Icc a t ∩ γ ⁻¹' K)
  let B := Insert.insert b (Set.Icc t b ∩ γ ⁻¹' K)
  have hA : IsCompact A := (CompactIccSpace.isCompact_Icc.inter_right (hK.preimage hγ)).insert a
  have hB : IsCompact B := (CompactIccSpace.isCompact_Icc.inter_right (hK.preimage hγ)).insert b
  obtain ⟨s, hs⟩ := hA.exists_isGreatest (Set.insert_nonempty _ _)
  obtain ⟨u, hu⟩ := hB.exists_isLeast (Set.insert_nonempty _ _)
  have has : a ≤ s := hs.2 (Set.mem_insert _ _)
  have hub : u ≤ b := hu.2 (Set.mem_insert _ _)
  have hst : s ≤ t := by
    rcases hs.1 with he | hh
    · exact he ▸ ht.1
    · exact hh.1.2
  have htu : t ≤ u := by
    rcases hu.1 with he | hh
    · exact he ▸ ht.2
    · exact hh.1.1
  have hsN : γ s ∈ N := by
    rcases hs.1 with he | hh
    · exact he ▸ ha
    · exact hKN hh.2
  have huN : γ u ∈ N := by
    rcases hu.1 with he | hh
    · exact he ▸ hb
    · exact hKN hh.2
  have hst' : s < t := lt_of_le_of_ne hst (fun he => hout (he ▸ hsN))
  have htu' : t < u := lt_of_le_of_ne htu (fun he => hout (he ▸ huN))
  refine ⟨s, u, has, hst', htu', hub, hsN, huN, ?_⟩
  intro r hr hrK
  by_cases hrt : r ≤ t
  · have hrA : r ∈ A := Or.inr ⟨⟨le_trans has hr.1.le, hrt⟩, hrK⟩
    exact (not_le_of_gt hr.1) (hs.2 hrA)
  · have hrB : r ∈ B := Or.inr ⟨⟨(lt_of_not_ge hrt).le, le_trans hr.2.le hub⟩, hrK⟩
    exact (not_le_of_gt hr.2) (hu.2 hrB)

theorem Degree.FlowCancellation.native_curve_eq_flow_on_closed_interval {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {γ : ℝ → M}
    (hγcont : Continuous γ) {a b c : ℝ} (hc : c ∈ Set.Ioo a b)
    (hγ : IsMIntegralCurveOn γ V (Set.Ioo a b)) : ∀ t ∈ Set.Icc a b, γ t = F (t - c) (γ c) := by
  have hF : IsMIntegralCurve (fun t => F (t - c) (γ c)) V := by
    have he : (fun t => F (t - c) (γ c)) = ((fun t => F t (γ c)) ∘ (· + -c)) := by
      funext t
      simp only [Function.comp_apply, sub_eq_add_neg]
    rw [he]
    exact (hcurve (γ c)).comp_add (-c)
  have heq : Set.EqOn γ (fun t => F (t - c) (γ c)) (Set.Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hc hV hγ (hF.isMIntegralCurveOn _)
      (by simp)
  have heqclosed := heq.closure hγcont hF.continuous
  rw [closure_Ioo (lt_trans hc.1 hc.2).ne] at heqclosed
  exact heqclosed

theorem Degree.FlowCancellation.native_no_return_of_supported_perturbation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V V' : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {K N U : Set M}
    (hK : IsClosed K) (hKN : K ⊆ N) (hNU : N ⊆ U) (hoff : ∀ x ∉ K, V' x = V x)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ V') {a b : ℝ} (ha : γ a ∈ N) (hb : γ b ∈ N) :
    ∀ t ∈ Set.Icc a b, γ t ∈ U := by
  intro t ht
  by_contra hout
  obtain ⟨s, u, -, hst, htu, -, hsN, huN, havoid⟩ :=
    exists_excursion_interval hγ.continuous hK hKN ht ha hb (fun hh => hout (hNU hh))
  have hold : IsMIntegralCurveOn γ V (Set.Ioo s u) := by
    intro r hr
    have hd := (hγ r).hasMFDerivWithinAt (s := Set.Ioo s u)
    rw [hoff (γ r) (havoid r hr)] at hd
    exact hd
  have heq :=
    native_curve_eq_flow_on_closed_interval hV F hcurve hγ.continuous
      (show t ∈ Set.Ioo s u from ⟨hst, htu⟩) hold
  have hs : γ s = F (s - t) (γ t) := heq s ⟨le_rfl, (lt_trans hst htu).le⟩
  have hu : γ u = F (u - t) (γ t) := heq u ⟨(lt_trans hst htu).le, le_rfl⟩
  have hend : F (u - s) (γ s) = γ u := by
    rw [hs, ← F.map_add, show u - s + (s - t) = u - t by ring, ← hu]
  have hmid : F (t - s) (γ s) = γ t := by
    rw [hs, ← F.map_add, show t - s + (s - t) = 0 by ring, F.map_zero_apply]
  have hh :=
    hnoreturn (γ s) hsN (u - s) (sub_nonneg.mpr (lt_trans hst htu).le) (hend ▸ huN) (t - s)
      ⟨sub_nonneg.mpr hst.le, sub_le_sub_right htu.le s⟩
  exact hout (hmid ▸ hh)

theorem MorseCancel.surgery_pair_inner_band_regular {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    {a b : ℝ} (ha : f p < a) (hb : b < f q) :
    ∀ z, f z ∈ Set.Icc a b → z ∉ Smale.ManifoldMorse.criticalPoints E f := by
  intro z hz hcrit
  exact hconsecutive ⟨z, hcrit⟩ ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩

theorem Smale.TransverseCoordinates.surjective_coprod_swap {D Z E : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : D →L[ℝ] E) (C : Z →L[ℝ] E) (h : Function.Surjective (A.coprod C)) :
    Function.Surjective (C.coprod A) := by
  intro w
  obtain ⟨⟨u, v⟩, huv⟩ := h w
  refine ⟨(v, u), ?_⟩
  change C v + A u = w
  rw [add_comm]
  exact huv

theorem Smale.FrameField.isInvertible_coprod_of_bijective {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] (G : D →L[ℝ] F)
    (C : Z →L[ℝ] F) (h : Function.Bijective (G.coprod C)) : (G.coprod C).IsInvertible := by
  let e := (LinearEquiv.ofBijective (G.coprod C).toLinearMap h).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

end Mathoverflow1973

end
