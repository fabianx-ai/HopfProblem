/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
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
import Lib.Geometry.Manifold.Morse.MinimalSystem
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Topology.MappingTorus.Wang

/-!
# Circle gluing along surgery windows

Circle gluing on belt and attaching spheres (`CircleGluing`), the surgery band and inner-band lemmas of `MorseCancellation`, immersion avoidance (`ManifoldImmersion`), adapted windows, flow suspensions and the first `ManifoldMorse.MorseSurgeryData` rows.

Moved verbatim from the project stock file `Hopf/SingularHomology.lean` (integration 4,
`Lib/reports/integration-4/singhom-moves.md`); the families here are
`CircleGluing`, `MorseCancellation`, `ManifoldImmersion`, `NativeOpenSubmanifold`, `AdaptedWindows`, `FlowSuspension`, `ManifoldMorse.MorseSurgeryData`. The declarations keep their historical dotted names
and their order; the file order is the dependency order.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6.

## Twin

No Mathlib counterpart exists.

## Tags

Morse theory, Whitney trick, handle cancellation
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

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

end
