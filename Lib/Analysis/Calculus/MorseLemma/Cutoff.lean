/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma.PartitionOfUnity

/-!
# Smooth cutoff functions and extensions

In a finite-dimensional real normed space:

* `LineBundleTransport.exists_smooth_cutoff_near_closed`: for a closed `K` inside an open `U`
  there is a smooth `χ` with `tsupport χ ⊆ U` and `χ = 1` on a neighbourhood of `K`
  (smooth Urysohn lemma, cf. Lee, *Introduction to Smooth Manifolds*, Ch. 2);
* `LineBundleTransport.exists_smooth_extension_near_closed`: a function smooth on `U` agrees
  near `K` with a globally smooth function;
* `LineBundleTransport.exists_interval_cutoff`: a compactly supported smooth function equal to
  `1` on `[[a, b]]`;
* `SmoothMorseLemma.exists_contDiff_compactlySupported_eqOn_closedBall`,
  `SmoothMorseLemma.exists_contDiff_extension`,
  `SmoothMorseLemma.exists_contDiff_extension_preserving_derivatives`: the germ at `a` of a
  function smooth on an open `U ∋ a` is the germ of a globally smooth (compactly supported)
  function.

The namespace `LineBundleTransport` records the first consumer of these lemmas, not their
content.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- A smooth cutoff equal to `1` near a closed set exists. -/
theorem LineBundleTransport.exists_smooth_cutoff_near_closed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K U : Set E} (hK : IsClosed K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧
        tsupport χ ⊆ U ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ Set.EqOn χ (fun _ => 1) W := by
  classical
  let O : Bool → Set E := fun b => if b then Kᶜ else U
  have hOo (b : Bool) : IsOpen (O b) := by
    cases b
    · exact hU
    · exact hK.isOpen_compl
  have hOc : Set.univ ⊆ ⋃ b, O b := by
    intro x _
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Bool.true, fun hk => hx (hKU hk)⟩
  obtain ⟨W, hWo, hKW, hWU, ρ, hρ, hρone, -, -⟩ :=
    HolomorphicCousin.exists_smoothPartitionOfUnity_eq_one_near_closed (modelWithCornersSelf ℝ E)
      O hOo hOc Bool.false hK hKU
  exact ⟨ρ Bool.false, (ρ Bool.false).contMDiff.contDiff, hρ Bool.false, W, hWo, hKW, hWU, hρone⟩

/-- A smooth extension of a local section exists near a closed set. -/
theorem LineBundleTransport.exists_smooth_extension_near_closed {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K U : Set E} {f : E → F} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : E → F, ContDiff ℝ ∞ G ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ Set.EqOn G f W := by
  obtain ⟨χ, hχ, hχU, W, hWo, hKW, hWU, hχone⟩ := exists_smooth_cutoff_near_closed hK hU hKU
  let G : E → F := fun x => χ x • f x
  have hG : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞ G := by
    apply contMDiff_of_tsupport
    intro x hx
    have hxU : x ∈ U := hχU (tsupport_smul_subset_left χ f hx)
    exact hχ.contMDiff.contMDiffAt.smul ((hf.contDiffAt (hU.mem_nhds hxU)).contMDiffAt)
  refine ⟨G, hG.contDiff, W, hWo, hKW, hWU, ?_⟩
  intro x hx
  change χ x • f x = f x
  rw [hχone hx, one_smul]

/-- A smooth cutoff on an interval exists. -/
theorem LineBundleTransport.exists_interval_cutoff (a b : ℝ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ Set.EqOn χ (fun _ => 1) (Set.uIcc a b) := by
  obtain ⟨R, -, hR⟩ :=
    (isCompact_uIcc : IsCompact (Set.uIcc a b)).isBounded.subset_ball_lt (0 : ℝ) 0
  obtain ⟨χ, hχ, hχU, W, -, hKW, -, hχone⟩ :=
    exists_smooth_cutoff_near_closed (isCompact_uIcc : IsCompact (Set.uIcc a b)).isClosed
      Metric.isOpen_ball hR
  refine ⟨χ, hχ, ?_, hχone.mono hKW⟩
  exact
    (ProperSpace.isCompact_closedBall (0 : ℝ) R).of_isClosed_subset (isClosed_tsupport χ)
      (hχU.trans Metric.ball_subset_closedBall)

/-- A compactly supported `C^n` function agreeing on a closed ball exists. -/
theorem SmoothMorseLemma.exists_contDiff_compactlySupported_eqOn_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E}
    {a : E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ,
      ContDiff ℝ ∞ g ∧
        HasCompactSupport g ∧
          tsupport g ⊆ U ∧
            ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ U ∧ Set.EqOn g f (Metric.closedBall a r) := by
  obtain ⟨r, hr, hrU⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  let β : ContDiffBump a :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  have hβU : tsupport (β : E → ℝ) ⊆ U := by
    rw [β.tsupport_eq]
    exact hrU
  have hg : ContDiff ℝ ∞ (fun x => β x * f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport (β : E → ℝ)
    · exact β.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hβU hx)))
    · have hzero : (β : E → ℝ) =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      have hconst : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) x := contDiffAt_const
      apply hconst.congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      simp only [hy, Pi.zero_apply, MulZeroClass.zero_mul]
  refine
    ⟨fun x => β x * f x, hg, β.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans hβU,
      β.rIn, β.rIn_pos, ?_, ?_⟩
  · exact (Metric.closedBall_subset_closedBall β.rIn_lt_rOut.le).trans hrU
  · intro x hx
    change β x * f x = f x
    rw [β.one_of_mem_closedBall hx, one_mul]

/-- A `C^n` extension of a local germ exists. -/
theorem SmoothMorseLemma.exists_contDiff_extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E} {a : E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨g, hg, _, _, r, hr, _, he⟩ :=
    exists_contDiff_compactlySupported_eqOn_closedBall hf hU ha
  refine ⟨g, hg, ?_⟩
  filter_upwards [Metric.ball_mem_nhds a hr] with x hx
  exact he (Metric.ball_subset_closedBall hx)

/-- A `C^n` extension preserving derivatives exists. -/
theorem SmoothMorseLemma.exists_contDiff_extension_preserving_derivatives {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E}
    {a : E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ,
      ContDiff ℝ ∞ g ∧
        g =ᶠ[𝓝 a] f ∧
          g a = f a ∧
            fderiv ℝ g a = fderiv ℝ f a ∧
              fderiv ℝ (fderiv ℝ g) a = fderiv ℝ (fderiv ℝ f) a ∧
                ∀ n : ℕ, iteratedFDeriv ℝ n g =ᶠ[𝓝 a] iteratedFDeriv ℝ n f := by
  obtain ⟨g, hg, he⟩ := exists_contDiff_extension hf hU ha
  exact
    ⟨g, hg, he, he.self_of_nhds, he.fderiv_eq, he.fderiv.fderiv_eq, fun n =>
      he.iteratedFDeriv ℝ n⟩
