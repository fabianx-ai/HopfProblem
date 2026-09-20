/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Curve.CircleGluing
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
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Topology.MappingTorus.Wang

/-!
# Circle gluing along surgery windows

An embedded arc and an embedded return arc with matching endpoint germs glue to a smooth
embedded circle; the gluing construction itself is
`Lib/Geometry/Manifold/Curve/CircleGluing.lean`, and this file produces the two arcs inside a
prescribed open set and uses the resulting circle.

The declarations are: embedded arcs realising a prescribed path with prescribed endpoint germs
(`TopologicalSpace.Opens.exists_embedded_arc_with_local_germs`,
`exists_embedded_return_arc_inside_open`, `exists_disjoint_embedded_return_arc`,
`exists_embedded_circle_through_arc`), avoidance of the image of a second map by a relative
homotopy in the general-position range (`ManifoldImmersion.exists_relative_embedded_avoidance_*`),
and statements about the flow and the belt sphere of a surgery window
(`AdaptedWindows.*`, `FlowSuspension.*`, `ManifoldMorse.MorseSurgeryData.*`).

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6.

## Tags

Morse theory, Whitney trick, handle cancellation
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- A smooth curve defined near `t₀` with `a t₀` in an open set `S` is, near `t₀`, a globally
defined smooth curve in `S`. -/
theorem TopologicalSpace.Opens.exists_contMDiff_curve_with_germ {G H N : Type*} [NormedAddCommGroup G]
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

/-- In a manifold of dimension at least `3`, two immersed curve germs at distinct points of an
open set `S`, joined by a path in `S`, are the two ends of a single smooth arc in `S` which is an
embedding of `[0, 1]` and an immersion there, agreeing with the given germs near `0` and `1`. -/
theorem TopologicalSpace.Opens.exists_embedded_arc_with_local_germs {G H N : Type*}
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
  obtain ⟨a', ha', heqa⟩ := TopologicalSpace.Opens.exists_contMDiff_curve_with_germ S ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := TopologicalSpace.Opens.exists_contMDiff_curve_with_germ S hb hV h1V hb1
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

/-- Return-arc form of the previous statement: an embedded immersed arc `α` on `[-R, R]` whose
endpoints `α r` and `α (-r)` lie in an open `S` and are joined by a path in `S` admits a return
arc in `S`, embedded and immersed on `[0, 1]`, matching `α` near both ends. -/
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
    apply CircleGluing.injective_mfderiv_curve_translate
    · simpa only [zero_add] using
        (hα.contMDiffAt (Ioo_mem_nhds hp.1 hp.2)).mdifferentiableAt (by simp)
    · exact (zero_add r).symm ▸ hderiv r hp
  have hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1) := by
    apply CircleGluing.injective_mfderiv_curve_translate
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
    TopologicalSpace.Opens.exists_embedded_arc_with_local_germs S ha hb hU hV h0U h1V haS hbS hia hib hpath
      hxy hdim

/-- A return arc matching `α` near its two ends avoids the arc `α '' [-r, r]` on a closed
neighbourhood of `{0, 1}`, away from `0` and `1` themselves. -/
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

/-- Relative embedding with avoidance, for a closed obstacle: a map `f` of a surface into an
open set `U`, already embedded, immersed and avoiding the closed image of `g` outside `B` on
`K ∩ C`, is homotopic rel `C` to a map that is an embedding and an immersion on the whole of the
compact set `K` and avoids the image of `g` outside `B`.  The dimension hypotheses are the
general-position ones, `dim N ≥ 5` and `dim E + dim E' < dim N` (Hirsch, *Differential
Topology*, Ch. 3, Ch. 8). -/
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

/-- Variant of the preceding statement in which the obstacle is the image `g '' A` of a subset,
`f` is already an embedding and an immersion on `K`, and the new map is required to keep `K`
inside a prescribed open subset `O` of `U`. -/
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

/-- Version of `exists_relative_embedded_avoidance_in_open_of_isClosed_range` for a compact
source `Y`, where the closedness of the image of `g` is automatic. -/
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

/-- Combination of `exists_embedded_return_arc_inside_open` with avoidance: the return arc can
moreover be chosen to meet `α '' [-r, r]` only at its two endpoints. -/
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


/-- The inclusion of an open subset of a manifold is an immersion. -/
theorem TopologicalSpace.Opens.injective_mfderiv_subtype_val {E H M : Type*}
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

/-- Main gluing statement: in a manifold of dimension at least `3`, an embedded immersed arc
`α` on `[-R, R]` whose endpoints `α (±r)` lie in an open set `S` and are joined by a path in `S`
lies on a smoothly embedded circle `γ : Circle → N` which traverses `α` on `[-r, r]` and whose
remaining image is contained in `S`. -/
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
    exact (TopologicalSpace.Opens.injective_mfderiv_subtype_val S (b t)).comp (hbd t ht)
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

/-- If a flow cylinder `N × ℝ ≃ X` is given by `(z, t) ↦ F t (ι z)` and `B ⊆ X` is dense and
flow-invariant, then `ι ⁻¹' B` is dense in `N`. -/
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

/-- On a regular level, the points whose forward orbit converges to a critical point of index
`0` form a dense subset. -/
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

/-- The unit sphere of a one-dimensional real normed space has exactly two points: any point of
it equals one of two given distinct points. -/
theorem Metric.unitSphere_eq_two_points_of_finrank_eq_one {V : Type*} [NormedAddCommGroup V]
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
/-- Between two consecutive critical points there is a diffeomorphism of `M` carrying the
sublevel set below the upper window of `p` onto the sublevel set below the lower window of `q`,
restricting to a diffeomorphism of the two levels and moving every point along its orbit. -/
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
/-- A point of the upper level of the window at `p` has its backward orbit converging to `q`
exactly when it lies on the attaching sphere of `q` transported to that level. -/
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

/-- If, on a regular level between `q` and `p`, exactly one point both flows back to `p` and
flows forward through `D` to `q`, then the modified flow `G` has a connecting orbit from `p` to
`q`, and it is unique up to reparametrisation. -/
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

/-- If no point of the level both flows back to `p` and flows forward through `D` to `q`, then
the modified flow `G` has no connecting orbit from `p` to `q`. -/
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
/-- The normal coordinate of the belt sphere in the upper level has surjective derivative along
the belt sphere: the belt sphere is a regular level of that coordinate. -/
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
/-- The tangent space to the belt sphere is exactly the kernel of the derivative of the normal
coordinate: the belt sphere is cut out transversally by that coordinate. -/
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
/-- A map `g` of an `m`-sphere into the upper level that is transverse to the belt sphere at a
point meets it transversally in the strong sense: the derivative of the normal coordinate
composed with `g` is bijective there. -/
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

end
