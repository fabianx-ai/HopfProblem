/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/



import Lib.Analysis.Complex.RiemannMapping
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Instances.RiemannSphere
import Mathlib

/-!
# The additive Cousin problem on an open cover of ℂ

Given a Cousin distribution on an open cover of `ℂ` (local holomorphic functions whose
differences are consistent), there is a global holomorphic solution — via the Cauchy–Green
transform and smooth partitions of unity (Forster §13–14; Hörmander Ch. I §1.2–1.4):

* `HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution` — the normalized global
  solution of the additive Cousin problem.

## Outline of the proof

1. *Smooth first step.*  A smooth partition of unity subordinate to the cover
   (`exists_smoothPartitionOfUnity_eq_one_near_closed`, `.normalized_near_closed`) gives a
   global smooth function with the prescribed local differences.
2. *Correcting to holomorphic.*  The ∂̄ of the smooth step is a globally defined (0,1)-form;
   the Cauchy–Green integral solves ∂̄u = that form, and holomorphicity of the correction
   follows from the ∂̄-equation.

## Main definitions and results

* `HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution` : the solution theorem.

## References

* [Otto Forster, *Lectures on Riemann Surfaces*][forster81], §13–14
* [Lars Hörmander, *An Introduction to Complex Analysis in Several Variables*][hormander66],
  Ch. I §1.2–1.4

## Tags

Cousin problem, Cauchy–Green, dolbeault, partition of unity
-/


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

/-! ### The partition cochain -/

/-- The divided difference of an analytic function is analytic. -/
theorem HolomorphicCousin.analyticOnNhd_dslope_zero {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R)) : AnalyticOnNhd ℂ (dslope f 0) (Metric.ball 0 R) :=
  (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mpr
    ((Complex.differentiableOn_dslope (Metric.ball_mem_nhds (0 : ℂ) hR)).mpr hf.differentiableOn)

/-- When `f 0 = 0`, multiplying the divided difference `dslope f 0 z` by `z` recovers `f z`. -/
theorem HolomorphicCousin.zero_mul_dslope {f : ℂ → ℂ} (hf : f 0 = 0) (z : ℂ) :
    z * dslope f 0 z = f z := by
  simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero hf z

/-- The cochain built from a partition of unity weighted cocycle. -/
def HolomorphicCousin.partitionCochain {ι E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : SmoothPartitionOfUnity ι I M Set.univ) (h : ι → ι → M → F) (i : ι) (x : M) : F :=
  ∑ᶠ k, ρ k x • h i k x

/-- A point in the finsupport lies in the cover element. -/
theorem HolomorphicCousin.mem_cover_of_mem_finsupport {ι E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {U : ι → Set M} {ρ : SmoothPartitionOfUnity ι I M Set.univ}
    (hρ : ρ.IsSubordinate U) {x : M} {k : ι} (hk : k ∈ ρ.finsupport x) : x ∈ U k := by
  apply hρ k
  apply subset_tsupport
  simpa only [ρ.mem_finsupport, Function.mem_support] using hk

/-- The partition cochain is smooth on each chart. -/
theorem HolomorphicCousin.partitionCochain_contMDiffOn {ι E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) {ρ : SmoothPartitionOfUnity ι I M Set.univ} (hρ : ρ.IsSubordinate U)
    {h : ι → ι → M → F} (hh : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) ∞ (h i j) (U i ∩ U j)) (i : ι) :
    ContMDiffOn I 𝓘(ℝ, F) ∞ (partitionCochain ρ h i) (U i) := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply ρ.contMDiffAt_finsum
  intro k hk
  exact (hh i k).contMDiffAt ((hU i).inter (hU k) |>.mem_nhds ⟨hx, hρ k hk⟩)

/-- The cochain difference recovers the cocycle on the overlap. -/
theorem HolomorphicCousin.partitionCochain_sub_eq {ι E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ι → Set M}
    {ρ : SmoothPartitionOfUnity ι I M Set.univ} (hρ : ρ.IsSubordinate U) {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (i j : ι) {x : M}
    (hi : x ∈ U i) (hj : x ∈ U j) :
    partitionCochain ρ h i x - partitionCochain ρ h j x = h i j x := by
  classical
  unfold partitionCochain
  rw [← ρ.sum_finsupport_smul_eq_finsum x (h i), ← ρ.sum_finsupport_smul_eq_finsum x (h j), ←
    Finset.sum_sub_distrib]
  calc
    (∑ k ∈ ρ.finsupport x, (ρ k x • h i k x - ρ k x • h j k x)) =
        ∑ k ∈ ρ.finsupport x, ρ k x • h i j x := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← smul_sub,
        sub_eq_iff_eq_add.mpr (hc i j k x hi hj (mem_cover_of_mem_finsupport hρ hk)).symm]
    _ = (∑ k ∈ ρ.finsupport x, ρ k x) • h i j x := (Finset.sum_smul ..).symm
    _ = h i j x := by rw [ρ.sum_finsupport x (Set.mem_univ x), one_smul]

/-- With a single weight the cochain is zero off the support. -/
theorem HolomorphicCousin.partitionCochain_eq_zero_of_weights_single {ι E H M F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ι → Set M} {ρ : SmoothPartitionOfUnity ι I M Set.univ} {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (j : ι) {x : M}
    (hj : x ∈ U j) (hρ0 : ∀ k, k ≠ j → ρ k x = 0) : partitionCochain ρ h j x = 0 := by
  have hdiag : h j j x = 0 := add_eq_left.mp (hc j j j x hj hj hj)
  have hz : ∀ k, ρ k x • h j k x = 0 := by
    intro k
    by_cases hkj : k = j
    · subst k
      rw [hdiag, smul_zero]
    · rw [hρ0 k hkj, zero_smul]
  simp only [partitionCochain, hz, finsum_zero]

/-- With a single weight the cochain equals the cocycle on the overlap. -/
theorem HolomorphicCousin.partitionCochain_eq_overlap_of_weights_single {ι E H M F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ι → Set M} {ρ : SmoothPartitionOfUnity ι I M Set.univ} (hρ : ρ.IsSubordinate U)
    {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (i j : ι) {x : M}
    (hi : x ∈ U i) (hj : x ∈ U j) (hρ0 : ∀ k, k ≠ j → ρ k x = 0) :
    partitionCochain ρ h i x = h i j x := by
  have he := partitionCochain_sub_eq hρ hc i j hi hj
  rwa [partitionCochain_eq_zero_of_weights_single hc j hj hρ0, sub_zero] at he

/-- A normalized smooth cochain bounding the cocycle exists. -/
theorem HolomorphicCousin.exists_normalized_smooth_cocycle_cochain {ι E H M F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] {U : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) {h : ι → ι → M → F}
    (hh : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) ∞ (h i j) (U i ∩ U j))
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (i₀ : ι)
    {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ (V : Set M) (s : ι → M → F),
      IsOpen V ∧
        K ⊆ V ∧
          V ⊆ U i₀ ∧
            (∀ i, ContMDiffOn I 𝓘(ℝ, F) ∞ (s i) (U i)) ∧
              (∀ i j x, x ∈ U i → x ∈ U j → s i x - s j x = h i j x) ∧
                Set.EqOn (s i₀) (fun _ => 0) V ∧ ∀ i, Set.EqOn (s i) (h i i₀) (U i ∩ V) := by
  obtain ⟨V, hVo, hKV, hVU, ρ, hρ, _, hρ0, _⟩ :=
    exists_smoothPartitionOfUnity_eq_one_near_closed I U hU
      (fun x _ => Set.mem_iUnion.mpr (hcover x)) i₀ hK hKU
  refine
    ⟨V, partitionCochain ρ h, hVo, hKV, hVU, partitionCochain_contMDiffOn hU hρ hh,
      fun i j _ hi hj => partitionCochain_sub_eq hρ hc i j hi hj, ?_, ?_⟩
  · intro x hx
    exact partitionCochain_eq_zero_of_weights_single hc i₀ (hVU hx) (fun k hk => hρ0 k hk x hx)
  · intro i x hx
    exact
      partitionCochain_eq_overlap_of_weights_single hρ hc i i₀ hx.1 (hVU hx.2)
        (fun k hk => hρ0 k hk x hx.2)

/-! ### The ∂̄ operator -/

/-- The ∂̄ operator as a real-linear map. -/
def HolomorphicCousin.dbarLinear : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / (2 : ℂ)) •
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) + Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I)

/-- ∂̄ computes the Wirtinger derivative. -/
@[simp]
theorem HolomorphicCousin.dbarLinear_apply (L : ℂ →L[ℝ] ℂ) :
    dbarLinear L = (L 1 + Complex.I * L Complex.I) / 2 := by
  simp only [dbarLinear, smul_apply, add_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

/-- The ∂̄ derivative of a function. -/
def HolomorphicCousin.dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

/-- ∂̄ agrees with the real-linear ∂̄ operator. -/
theorem HolomorphicCousin.dbar_eq_dbarLinear (f : ℂ → ℂ) (z : ℂ) :
    dbar f z = dbarLinear (fderiv ℝ f z) :=
  (dbarLinear_apply _).symm

/-- The Wirtinger operator commutes with complex scalar multiplication: `dbarLinear (c • L) = c * dbarLinear L`. -/
theorem HolomorphicCousin.dbarLinear_complex_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) :
    dbarLinear (c • L) = c * dbarLinear L := by
  simp only [dbarLinear_apply, smul_apply, smul_eq_mul]
  ring

/-- Vanishing of `dbar f z` is equivalent to the Cauchy–Riemann identity for the chosen real Fréchet derivative. -/
theorem HolomorphicCousin.dbar_eq_zero_iff (f : ℂ → ℂ) (z : ℂ) :
    dbar f z = 0 ↔ fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 := by
  constructor
  · intro h
    have hs : fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0 := by
      simpa only [dbar, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using h
    have hm := congrArg (fun w : ℂ => -Complex.I * w) hs
    simp only [mul_add, neg_mul, ← mul_assoc, Complex.I_mul_I, neg_neg,
      MulZeroClass.mul_zero] at hm
    linear_combination hm
  · intro h
    rw [dbar, h, ← mul_assoc, Complex.I_mul_I, neg_one_mul, add_neg_cancel, zero_div]

/-- Complex differentiability is equivalent to real differentiability together with vanishing of the Wirtinger derivative. -/
theorem HolomorphicCousin.differentiableAt_complex_iff_dbar {f : ℂ → ℂ} {z : ℂ} :
    DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ dbar f z = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real, dbar_eq_zero_iff]
  rfl

/-- A complex-differentiable function has `∂̄f = 0`. -/
theorem HolomorphicCousin.dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : dbar f z = 0 :=
  (differentiableAt_complex_iff_dbar.mp hf).2

/-- A real-differentiable function on an open subset of the complex plane is analytic there if its Wirtinger derivative vanishes. -/
theorem HolomorphicCousin.analyticOnNhd_of_dbar_eq_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) (hd : ∀ z ∈ U, dbar f z = 0) : AnalyticOnNhd ℂ f U := by
  apply (Complex.analyticOnNhd_iff_differentiableOn hU).mpr
  intro z hz
  exact
    ((differentiableAt_complex_iff_dbar).mpr
        ⟨(hf z hz).differentiableAt (hU.mem_nhds hz), hd z hz⟩).differentiableWithinAt

/-- ∂̄ of a difference is the difference of ∂̄. -/
theorem HolomorphicCousin.dbar_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dbar (fun w => f w - g w) z = dbar f z - dbar g z := by
  simp only [dbar_eq_dbarLinear, fderiv_fun_sub hf hg, map_sub]

/-- ∂̄ of `f ∘ (· − c)` is the shifted ∂̄. -/
theorem HolomorphicCousin.dbar_comp_const_sub {f : ℂ → ℂ} (a z : ℂ)
    (hf : DifferentiableAt ℝ f (a - z)) : dbar (fun w => f (a - w)) z = -dbar f (a - z) := by
  have hi : HasFDerivAt (fun w : ℂ => a - w) (-ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).const_sub a
  have he := (hf.hasFDerivAt.comp z hi).fderiv
  change fderiv ℝ (fun w => f (a - w)) z = _ at he
  simp only [dbar, he, ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_neg]
  ring

/-- ∂̄ of a smooth function is smooth. -/
theorem HolomorphicCousin.contDiffAt_dbar {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (dbar f) z := by
  have he : dbar f = dbarLinear ∘ fderiv ℝ f := funext (dbar_eq_dbarLinear f)
  rw [he]
  exact dbarLinear.contDiff.contDiffAt.comp z (hf.fderiv_right (by simp))

/-- ∂̄ of a sum with a holomorphic term is the ∂̄ of the remainder. -/
theorem HolomorphicCousin.dbar_eq_of_sub_differentiableAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hfg : DifferentiableAt ℂ (fun w => f w - g w) z) : dbar f z = dbar g z := by
  have he := dbar_eq_zero_of_differentiableAt hfg
  rw [dbar_sub hf hg] at he
  exact sub_eq_zero.mp he

/-! ### Local potentials for a cocycle -/

/-- A local smooth potential for the Cousin cocycle near a point. -/
structure HolomorphicCousin.LocalPotential (ι : Type*) where
  domain : ι → Set ℂ
  isOpen_domain : ∀ i, IsOpen (domain i)
  cover : ∀ z : ℂ, ∃ i, z ∈ domain i
  potential : ι → ℂ → ℂ
  smooth : ∀ i, ContDiffOn ℝ ∞ (potential i) (domain i)
  analytic_difference :
    ∀ i j, AnalyticOnNhd ℂ (fun z => potential i z - potential j z) (domain i ∩ domain j)

/-- A chosen cover index at a point. -/
def HolomorphicCousin.LocalPotential.indexAt {ι : Type*} (P : HolomorphicCousin.LocalPotential ι)
    (z : ℂ) : ι :=
  (P.cover z).choose

/-- The point lies in the chosen cover element. -/
theorem HolomorphicCousin.LocalPotential.mem_domain_indexAt {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (z : ℂ) : z ∈ P.domain (P.indexAt z) :=
  (P.cover z).choose_spec

/-- The local potential is smooth at the point. -/
theorem HolomorphicCousin.LocalPotential.smoothAt {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {z : ℂ} (hz : z ∈ P.domain i) :
    ContDiffAt ℝ ∞ (P.potential i) z :=
  (P.smooth i z hz).contDiffAt ((P.isOpen_domain i).mem_nhds hz)

/-- The forcing ∂̄-data of the local potential. -/
def HolomorphicCousin.LocalPotential.forcing {ι : Type*} (P : HolomorphicCousin.LocalPotential ι)
    (z : ℂ) : ℂ :=
  HolomorphicCousin.dbar (P.potential (P.indexAt z)) z

/-- The forcing computes the ∂̄ of the cochain correction. -/
theorem HolomorphicCousin.LocalPotential.forcing_eq {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {z : ℂ} (hz : z ∈ P.domain i) :
    P.forcing z = HolomorphicCousin.dbar (P.potential i) z := by
  exact
    HolomorphicCousin.dbar_eq_of_sub_differentiableAt
      ((P.smoothAt (P.mem_domain_indexAt z)).differentiableAt (by simp))
      ((P.smoothAt hz).differentiableAt (by simp))
      (P.analytic_difference (P.indexAt z) i z ⟨P.mem_domain_indexAt z, hz⟩).differentiableAt

/-- The forcing eventually equals the ∂̄ cochain term. -/
theorem HolomorphicCousin.LocalPotential.forcing_eventuallyEq {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {z : ℂ} (hz : z ∈ P.domain i) :
    P.forcing =ᶠ[𝓝 z] HolomorphicCousin.dbar (P.potential i) := by
  filter_upwards [(P.isOpen_domain i).mem_nhds hz] with w hw
  exact P.forcing_eq hw

/-- The forcing is smooth. -/
theorem HolomorphicCousin.LocalPotential.forcing_contDiff {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) : ContDiff ℝ ∞ P.forcing := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact
    (HolomorphicCousin.contDiffAt_dbar
          (P.smoothAt (P.mem_domain_indexAt z))).congr_of_eventuallyEq
      (P.forcing_eventuallyEq (P.mem_domain_indexAt z))

/-- The forcing vanishes on the normalization set. -/
theorem HolomorphicCousin.LocalPotential.forcing_eq_zero {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {z : ℂ} (hz : z ∈ P.domain i)
    (hs : DifferentiableAt ℂ (P.potential i) z) : P.forcing z = 0 := by
  rw [P.forcing_eq hz]
  exact HolomorphicCousin.dbar_eq_zero_of_differentiableAt hs

/-- The corrected difference of two local potentials is analytic. -/
theorem HolomorphicCousin.LocalPotential.corrected_difference {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (u : ℂ → ℂ) (i j : ι) (z : ℂ) :
    (P.potential i z - u z) - (P.potential j z - u z) = P.potential i z - P.potential j z := by
  ring

/-- The corrected local potential is analytic on the normalization. -/
theorem HolomorphicCousin.LocalPotential.corrected_analytic {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {u : ℂ → ℂ} (hu : Differentiable ℝ u)
    (hsolve : ∀ z, HolomorphicCousin.dbar u z = P.forcing z) (i : ι) :
    AnalyticOnNhd ℂ (fun z => P.potential i z - u z) (P.domain i) := by
  apply HolomorphicCousin.analyticOnNhd_of_dbar_eq_zero (P.isOpen_domain i)
  · exact ((P.smooth i).differentiableOn (by simp)).sub hu.differentiableOn
  · intro z hz
    rw [HolomorphicCousin.dbar_sub ((P.smoothAt hz).differentiableAt (by simp)) (hu z), hsolve,
      P.forcing_eq hz, sub_self]

/-- The forcing vanishes on the normalization set. -/
theorem HolomorphicCousin.LocalPotential.forcing_eq_zero_on_normalization {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {V : Set ℂ} (hV : IsOpen V)
    (hVi : V ⊆ P.domain i) (hzero : Set.EqOn (P.potential i) (fun _ => 0) V) :
    Set.EqOn P.forcing (fun _ => 0) V := by
  intro z hz
  apply P.forcing_eq_zero (hVi hz)
  apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hz] with w hw
  exact hzero hw

/-- The forcing's support is contained off the normalization. -/
theorem HolomorphicCousin.LocalPotential.forcing_tsupport_subset_of_normalization {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {V : Set ℂ} (hV : IsOpen V)
    (hVi : V ⊆ P.domain i) (hzero : Set.EqOn (P.potential i) (fun _ => 0) V) :
    tsupport P.forcing ⊆ Vᶜ := by
  apply closure_minimal ?_ hV.isClosed_compl
  intro z hz hzV
  exact hz (P.forcing_eq_zero_on_normalization hV hVi hzero hzV)

/-- A normalized local potential exists at every point. -/
theorem HolomorphicCousin.exists_normalized_cocycle_localPotential {ι : Type*} {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k → h i j z + h j k z = h i k z) (i₀ : ι) (R : ℝ)
    (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ P : LocalPotential ι,
      P.domain = U ∧
        (∀ i j z, z ∈ U i → z ∈ U j → P.potential i z - P.potential j z = h i j z) ∧
          (∃ V : Set ℂ,
              IsOpen V ∧
                (Metric.ball (0 : ℂ) R)ᶜ ⊆ V ∧
                  V ⊆ U i₀ ∧
                    Set.EqOn (P.potential i₀) (fun _ => 0) V ∧
                      ∀ i, Set.EqOn (P.potential i) (h i i₀) (U i ∩ V)) ∧
            tsupport P.forcing ⊆ Metric.ball (0 : ℂ) R ∧ HasCompactSupport P.forcing := by
  have hsmooth i j : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (h i j) (U i ∩ U j) :=
    ((hh i j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ |>.contMDiffOn
  obtain ⟨V, s, hVo, hRV, hVU, hs, htrans, hs0, hsOverlap⟩ :=
    exists_normalized_smooth_cocycle_cochain hU hcover hsmooth hc i₀
      Metric.isOpen_ball.isClosed_compl hRU
  let P : LocalPotential ι :=
    { domain := U
      isOpen_domain := hU
      cover := hcover
      potential := s
      smooth := fun i => (hs i).contDiffOn
      analytic_difference := fun i j =>
        (hh i j).congr ((hU i).inter (hU j)) (fun z hz => (htrans i j z hz.1 hz.2).symm) }
  have hsupport : tsupport P.forcing ⊆ Metric.ball (0 : ℂ) R := by
    have hsub := P.forcing_tsupport_subset_of_normalization hVo hVU hs0
    intro z hz
    by_contra hzR
    exact hsub hz (hRV hzR)
  have hcompact : HasCompactSupport P.forcing := by
    apply
      HasCompactSupport.of_support_subset_isCompact (ProperSpace.isCompact_closedBall (0 : ℂ) R)
    exact (subset_tsupport P.forcing).trans (hsupport.trans Metric.ball_subset_closedBall)
  exact ⟨P, rfl, htrans, ⟨V, hVo, hRV, hVU, hs0, hsOverlap⟩, hsupport, hcompact⟩

/-! ### The Cauchy–Green integral -/

/-- The kernel `1/z` is locally integrable. -/
theorem HolomorphicCousin.locallyIntegrable_complex_inv :
    MeasureTheory.LocallyIntegrable (fun z : ℂ => z⁻¹) := by
  refine
    MeasureTheory.locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
      (by simp [Complex.finrank_real_complex]) (by norm_num [Complex.finrank_real_complex]) ?_ ?_
  · filter_upwards with z
    simp only [norm_inv, Real.rpow_neg_one, one_mul, le_refl]
  · exact Measurable.aestronglyMeasurable (by fun_prop)

/-- The Cauchy–Green integral of a compactly supported function. -/
def HolomorphicCousin.cauchyGreen (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) * ∫ w : ℂ, w⁻¹ * f (z - w)

/-- The Cauchy–Green integral of a `C^n` kernel is `C^n`. -/
theorem HolomorphicCousin.contDiff_cauchyGreen {n : ℕ∞} {f : ℂ → ℂ} (hf : ContDiff ℝ n f)
    (hcf : HasCompactSupport f) : ContDiff ℝ n (cauchyGreen f) := by
  change
    ContDiff ℝ n
      (fun z => (1 / (Real.pi : ℂ)) * ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ] f) z)
  exact
    contDiff_const.mul
      (hcf.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_complex_inv
        hf)

/-- The Cauchy–Green integral is differentiable. -/
theorem HolomorphicCousin.hasFDerivAt_cauchyGreen {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) :
    HasFDerivAt (cauchyGreen f)
      ((1 / (Real.pi : ℂ)) •
        ((fun w : ℂ => w⁻¹) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ] fderiv ℝ f) z)
      z := by
  convert!
    (hcf.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_complex_inv
          hf z).const_mul
      (1 / (Real.pi : ℂ)) using
    1

/-- ∂̄ of a right-composed product. -/
theorem HolomorphicCousin.dbarLinear_precompR_mul (a : ℂ) (L : ℂ →L[ℝ] ℂ) :
    dbarLinear ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ a L) = a * dbarLinear L := by
  change dbarLinear (a • L) = a * dbarLinear L
  exact dbarLinear_complex_smul a L

/-- ∂̄ commutes with the Cauchy–Green integral. -/
theorem HolomorphicCousin.dbar_cauchyGreen_eq_cauchyGreen_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) : dbar (cauchyGreen f) z = cauchyGreen (dbar f) z := by
  have hi :
    MeasureTheory.Integrable
      (fun w : ℂ => (ContinuousLinearMap.mul ℝ ℂ).precompR ℂ w⁻¹ (fderiv ℝ f (z - w))) :=
    (hcf.fderiv ℝ).convolutionExists_right ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ)
      locallyIntegrable_complex_inv (hf.continuous_fderiv one_ne_zero) z
  rw [dbar_eq_dbarLinear, (hasFDerivAt_cauchyGreen hf hcf z).fderiv, dbarLinear_complex_smul,
    MeasureTheory.convolution_def, ← dbarLinear.integral_comp_comm hi]
  simp only [dbarLinear_precompR_mul, ← dbar_eq_dbarLinear, cauchyGreen]

/-! ### Polar decomposition of the Green kernel -/

/-- The unit-circle point at angle `θ`, used as the angular factor in polar coordinates. -/
def HolomorphicCousin.greenUnit (θ : ℝ) : ℂ :=
  circleMap 0 1 θ

/-- The angular unit vector is `cos θ + sin θ * I`. -/
theorem HolomorphicCousin.greenUnit_eq (θ : ℝ) :
    greenUnit θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  simp [greenUnit, circleMap, Complex.exp_mul_I]

/-- The green unit has norm one. -/
@[simp]
theorem HolomorphicCousin.norm_greenUnit (θ : ℝ) : ‖greenUnit θ‖ = 1 := by simp [greenUnit]

/-- The angular unit vector depends continuously on its real angle. -/
theorem HolomorphicCousin.continuous_greenUnit : Continuous greenUnit := by
  exact continuous_circleMap 0 1

/-- The polar coordinate inverse is the green unit scaled by the radius. -/
theorem HolomorphicCousin.polarCoord_symm_eq_greenUnit (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * greenUnit p.2 := by
  simp [Complex.polarCoord_symm_apply, greenUnit_eq]

/-- A real-linear map applied to a complex number in polar form. -/
theorem HolomorphicCousin.realLinear_apply_complex (D : ℂ →L[ℝ] ℂ) (z : ℂ) :
    D z = (z.re : ℂ) * D 1 + (z.im : ℂ) * D Complex.I := by
  calc
    D z = D (z.re • (1 : ℂ) + z.im • Complex.I) := by
      congr 1
      simp [Complex.real_smul]
    _ = (z.re : ℂ) * D 1 + (z.im : ℂ) * D Complex.I := by
      rw [map_add, map_smul, map_smul]
      simp [Complex.real_smul]

/-- A real-linear map splits into radial and angular parts. -/
theorem HolomorphicCousin.polar_realLinear_identity (D : ℂ →L[ℝ] ℂ) (z : ℂ) :
    D z + Complex.I * D (Complex.I * z) = Star.star z * (D 1 + Complex.I * D Complex.I) := by
  have hc : Star.star z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp
  rw [realLinear_apply_complex D z, realLinear_apply_complex D (Complex.I * z), hc]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, MulZeroClass.zero_mul,
    one_mul, zero_sub, zero_add, Complex.ofReal_neg]
  ring_nf
  simp [Complex.I_sq]

/-- The radial component of the Green kernel. -/
def HolomorphicCousin.greenRadial (φ : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ φ ((p.1 : ℂ) * greenUnit p.2) (greenUnit p.2)

/-- The angular component of the Green kernel. -/
def HolomorphicCousin.greenAngular (φ : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ φ ((p.1 : ℂ) * greenUnit p.2) (Complex.I * greenUnit p.2)

/-- The radial component is continuous. -/
theorem HolomorphicCousin.continuous_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (greenRadial φ) := by
  exact
    (hφ.continuous_fderiv_apply one_ne_zero).comp
      (((Complex.continuous_ofReal.comp continuous_fst).mul
            (continuous_greenUnit.comp continuous_snd)).prodMk
        (continuous_greenUnit.comp continuous_snd))

/-- The angular component is continuous. -/
theorem HolomorphicCousin.continuous_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (greenAngular φ) := by
  exact
    (hφ.continuous_fderiv_apply one_ne_zero).comp
      (((Complex.continuous_ofReal.comp continuous_fst).mul
            (continuous_greenUnit.comp continuous_snd)).prodMk
        (continuous_const.mul (continuous_greenUnit.comp continuous_snd)))

/-- The radial component is differentiable. -/
theorem HolomorphicCousin.hasDerivAt_green_radial {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ)
    (r θ : ℝ) : HasDerivAt (fun t : ℝ => φ ((t : ℂ) * greenUnit θ)) (greenRadial φ (r, θ)) r := by
  apply (hφ _).hasFDerivAt.comp_hasDerivAt
  simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (greenUnit θ)

/-- The angular component is differentiable. -/
theorem HolomorphicCousin.hasDerivAt_green_angular {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ)
    (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => φ ((r : ℂ) * greenUnit t)) ((r : ℂ) * greenAngular φ (r, θ)) θ := by
  have hu : HasDerivAt greenUnit (Complex.I * greenUnit θ) θ := by
    change HasDerivAt (circleMap 0 1) (Complex.I * circleMap 0 1 θ) θ
    simpa [mul_comm] using hasDerivAt_circleMap 0 1 θ
  have hd := (hφ _).hasFDerivAt.comp_hasDerivAt θ (hu.const_mul (r : ℂ))
  simpa only [Function.comp_def, ← Complex.real_smul, map_smul, greenAngular] using hd

/-- The radial integral of the Green kernel. -/
theorem HolomorphicCousin.integral_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (R θ : ℝ) :
    (∫ r in 0..R, greenRadial φ (r, θ)) = φ ((R : ℂ) * greenUnit θ) - φ 0 := by
  have hint :
    IntervalIntegrable (fun r => greenRadial φ (r, θ)) MeasureTheory.MeasureSpace.volume 0 R :=
    ((continuous_greenRadial hφ).comp (continuous_id.prodMk continuous_const)).intervalIntegrable
      _ _
  simpa using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hasDerivAt_green_radial (hφ.differentiable one_ne_zero) r θ) hint

/-- The angular integral of the Green kernel. -/
theorem HolomorphicCousin.integral_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) {r : ℝ}
    (hr : r ≠ 0) : (∫ θ in (-Real.pi)..Real.pi, greenAngular φ (r, θ)) = 0 := by
  have hint :
    IntervalIntegrable (fun θ => (r : ℂ) * greenAngular φ (r, θ))
      MeasureTheory.MeasureSpace.volume (-Real.pi) Real.pi :=
    (continuous_const.mul
          ((continuous_greenAngular hφ).comp
            (continuous_const.prodMk continuous_id))).intervalIntegrable
      _ _
  have heq :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => hasDerivAt_green_angular (hφ.differentiable one_ne_zero) r θ) hint
  have hend : greenUnit Real.pi = greenUnit (-Real.pi) := by simp [greenUnit_eq]
  have hz : (r : ℂ) * (∫ θ in (-Real.pi)..Real.pi, greenAngular φ (r, θ)) = 0 := by
    simpa only [intervalIntegral.integral_const_mul, hend, sub_self] using heq
  exact (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr hr)

/-- A radius bounding the Green support exists. -/
theorem HolomorphicCousin.exists_green_support_radius {φ : ℂ → ℂ} (hφ : HasCompactSupport φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → φ z = 0 ∧ fderiv ℝ φ z = 0 := by
  obtain ⟨R, hR, hs⟩ := hφ.isBounded.subset_ball_lt 0 (0 : ℂ)
  refine ⟨R, hR, ?_⟩
  intro z hz
  have hn : z ∉ tsupport φ := by
    intro hmem
    have hlt : ‖z‖ < R := by simpa using hs hmem
    exact not_lt_of_ge hz hlt
  exact ⟨image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn⟩

/-- The kernel is integrable on a polar rectangle. -/
theorem HolomorphicCousin.integrableOn_polarRectangle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi)) :
    MeasureTheory.IntegrableOn G (Set.Ioc 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  apply
    (hG.integrableOn_compact
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)).mono_set
  rintro ⟨r, θ⟩ ⟨hr, hθ⟩
  exact ⟨⟨hr.1.le, hr.2⟩, ⟨hθ.1.le, hθ.2.le⟩⟩

/-- The kernel is integrable on the polar target given radial support. -/
theorem HolomorphicCousin.integrableOn_polarTarget_of_radial_support {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) : MeasureTheory.IntegrableOn G polarCoord.target := by
  apply
    (integrableOn_polarRectangle hG).of_forall_sdiff_eq_zero
      polarCoord.open_target.measurableSet
  rintro ⟨r, θ⟩ ⟨hp, hnot⟩
  apply hzero
  by_contra hr
  exact hnot ⟨⟨hp.1, le_of_not_gt hr⟩, hp.2⟩

/-- The polar target integral equals the rectangle integral. -/
theorem HolomorphicCousin.integral_polarTarget_eq_rectangle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) = ∫ p in Set.Ioc 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p := by
  apply
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      polarCoord.open_target.measurableSet
  · rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    exact ⟨hr.1, hθ⟩
  · rintro ⟨r, θ⟩ ⟨hp, hnot⟩
    apply hzero
    by_contra hr
    exact hnot ⟨⟨hp.1, le_of_not_gt hr⟩, hp.2⟩

/-- The polar integral iterates radius then angle. -/
theorem HolomorphicCousin.integral_polarTarget_eq_radius_angle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) = ∫ r in 0..R, ∫ θ in (-Real.pi)..Real.pi, G (r, θ) := by
  rw [integral_polarTarget_eq_rectangle hzero]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod G
      (by
        simpa only [MeasureTheory.Measure.volume_eq_prod] using
          integrableOn_polarRectangle hG)]
  simp_rw [intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- The polar integral iterates angle then radius. -/
theorem HolomorphicCousin.integral_polarTarget_eq_angle_radius {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) = ∫ θ in (-Real.pi)..Real.pi, ∫ r in 0..R, G (r, θ) := by
  rw [integral_polarTarget_eq_rectangle hzero, MeasureTheory.Measure.volume_eq_prod, ←
    MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.integral_prod_symm G
      (by
        simpa only [MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict,
          ← MeasureTheory.Measure.volume_eq_prod] using
          integrableOn_polarRectangle hG)]
  simp_rw [intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- The polar integrand of the Green kernel. -/
theorem HolomorphicCousin.green_polar_integrand (φ : ℂ → ℂ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    p.1 • ((Complex.polarCoord.symm p)⁻¹ * dbar φ (Complex.polarCoord.symm p)) =
      (greenRadial φ p + Complex.I * greenAngular φ p) / 2 := by
  have hr : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  rw [polarCoord_symm_eq_greenUnit, Complex.real_smul, dbar]
  unfold greenRadial greenAngular
  rw [polar_realLinear_identity, Complex.star_def, ← Complex.inv_eq_conj (norm_greenUnit p.2)]
  field_simp

/-- The radial component vanishes past the support radius. -/
theorem HolomorphicCousin.greenRadial_radius_vanish {φ : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ∀ z : ℂ, R ≤ ‖z‖ → fderiv ℝ φ z = 0) :
    ∀ p : ℝ × ℝ, R < p.1 → greenRadial φ p = 0 := by
  intro p hp
  have hn : R ≤ ‖(p.1 : ℂ) * greenUnit p.2‖ := by
    simpa only [norm_mul, norm_greenUnit, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hR.trans hp)] using hp.le
  simp only [greenRadial, hz _ hn, zero_apply]

/-- The angular component vanishes past the support radius. -/
theorem HolomorphicCousin.greenAngular_radius_vanish {φ : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ∀ z : ℂ, R ≤ ‖z‖ → fderiv ℝ φ z = 0) :
    ∀ p : ℝ × ℝ, R < p.1 → greenAngular φ p = 0 := by
  intro p hp
  have hn : R ≤ ‖(p.1 : ℂ) * greenUnit p.2‖ := by
    simpa only [norm_mul, norm_greenUnit, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hR.trans hp)] using hp.le
  simp only [greenAngular, hz _ hn, zero_apply]

/-- The radial component is integrable. -/
theorem HolomorphicCousin.integrableOn_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : MeasureTheory.IntegrableOn (greenRadial φ) polarCoord.target := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  exact
    integrableOn_polarTarget_of_radial_support (continuous_greenRadial hφ).continuousOn
      (greenRadial_radius_vanish hR (fun z h => (hz z h).2))

/-- The angular component is integrable. -/
theorem HolomorphicCousin.integrableOn_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : MeasureTheory.IntegrableOn (greenAngular φ) polarCoord.target := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  exact
    integrableOn_polarTarget_of_radial_support (continuous_greenAngular hφ).continuousOn
      (greenAngular_radius_vanish hR (fun z h => (hz z h).2))

/-- The radial integral over the polar target. -/
theorem HolomorphicCousin.integral_greenRadial_polarTarget {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    (∫ p in polarCoord.target, greenRadial φ p) = -(2 * (Real.pi : ℂ)) * φ 0 := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  rw [integral_polarTarget_eq_angle_radius hR.le (continuous_greenRadial hφ).continuousOn
      (greenRadial_radius_vanish hR (fun z h => (hz z h).2))]
  have hend (θ : ℝ) : φ ((R : ℂ) * greenUnit θ) = 0 := by
    apply (hz _ _).1
    simp [abs_of_pos hR]
  simp_rw [integral_greenRadial hφ, hend, zero_sub]
  simp only [intervalIntegral.integral_const, Complex.real_smul, sub_neg_eq_add,
    Complex.ofReal_add]
  ring

/-- The angular integral over the polar target. -/
theorem HolomorphicCousin.integral_greenAngular_polarTarget {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : (∫ p in polarCoord.target, greenAngular φ p) = 0 := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  rw [integral_polarTarget_eq_radius_angle hR.le (continuous_greenAngular hφ).continuousOn
      (greenAngular_radius_vanish hR (fun z h => (hz z h).2))]
  apply intervalIntegral.integral_zero_ae
  filter_upwards with r hr
  have hr' : r ∈ Set.Ioc 0 R := by simpa only [Set.uIoc_of_le hR.le] using hr
  exact integral_greenAngular hφ hr'.1.ne'

/-! ### The ∂̄ solution -/

/-- The integral of `w⁻¹ * ∂̄φ` equals `−π * φ 0`. -/
theorem HolomorphicCousin.integral_inv_mul_dbar {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : (∫ w : ℂ, w⁻¹ * dbar φ w) = -(Real.pi : ℂ) * φ 0 := by
  rw [← Complex.integral_comp_polarCoord_symm]
  calc
    (∫ p in polarCoord.target,
          p.1 • ((Complex.polarCoord.symm p)⁻¹ * dbar φ (Complex.polarCoord.symm p))) =
        ∫ p in polarCoord.target, (greenRadial φ p + Complex.I * greenAngular φ p) / 2 := by
      apply MeasureTheory.setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      exact green_polar_integrand φ p hp.1
    _ =
        ((∫ p in polarCoord.target, greenRadial φ p) +
            Complex.I * (∫ p in polarCoord.target, greenAngular φ p)) /
          2 := by
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add (integrableOn_greenRadial hφ hc)
          ((integrableOn_greenAngular hφ hc).const_mul Complex.I),
        MeasureTheory.integral_const_mul]
    _ = -(Real.pi : ℂ) * φ 0 := by
      rw [integral_greenRadial_polarTarget hφ hc, integral_greenAngular_polarTarget hφ hc]
      ring

/-- For a compactly supported `C¹` function, the Cauchy–Green transform of its Wirtinger derivative recovers the function exactly. -/
theorem HolomorphicCousin.cauchyGreen_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) : cauchyGreen (dbar f) z = f z := by
  let φ : ℂ → ℂ := fun w => f (z - w)
  have hφ : ContDiff ℝ 1 φ := hf.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hcf.comp_homeomorph (Homeomorph.subLeft z)
  have hd : dbar φ = fun w => -dbar f (z - w) := by
    funext w
    exact dbar_comp_const_sub z w ((hf.differentiable one_ne_zero) (z - w))
  have he := integral_inv_mul_dbar hφ hcφ
  have he' : -(∫ w : ℂ, w⁻¹ * dbar f (z - w)) = -((Real.pi : ℂ) * f z) := by
    simpa only [hd, mul_neg, MeasureTheory.integral_neg, φ, sub_zero, neg_mul] using he
  have hi := neg_injective he'
  unfold cauchyGreen
  rw [hi, one_div, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

/-- ∂̄ of the Cauchy–Green integral is the function. -/
theorem HolomorphicCousin.dbar_cauchyGreen {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) : dbar (cauchyGreen f) z = f z := by
  rw [dbar_cauchyGreen_eq_cauchyGreen_dbar hf hcf, cauchyGreen_dbar hf hcf]

/-- The Cauchy–Green integral solves `∂̄u = f` for compactly supported `f`. -/
theorem HolomorphicCousin.cauchyGreen_smooth_dbar_solution {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) :
    ContDiff ℝ ∞ (cauchyGreen f) ∧ ∀ z, dbar (cauchyGreen f) z = f z := by
  refine ⟨contDiff_cauchyGreen hf hcf, ?_⟩
  exact dbar_cauchyGreen (hf.of_le (by simp)) hcf

/-- The Cauchy–Green integral extended at infinity. -/
def HolomorphicCousin.cauchyGreenInfinity (f : ℂ → ℂ) (u : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) * ∫ w : ℂ, u * (1 - w * u)⁻¹ * f w

/-- The extended Cauchy–Green integral vanishes at infinity. -/
@[simp]
theorem HolomorphicCousin.cauchyGreenInfinity_zero (f : ℂ → ℂ) : cauchyGreenInfinity f 0 = 0 := by
  simp [cauchyGreenInfinity]

/-- The area denominator is nonzero. -/
theorem HolomorphicCousin.area_denominator_ne_zero {R : ℝ} (hR : 0 < R)
    {u w : ℂ} (hu : u ∈ Metric.ball 0 R⁻¹) (hw : ‖w‖ ≤ R) : 1 - w * u ≠ 0 := by
  have hu' : ‖u‖ < R⁻¹ := by simpa using hu
  have hmul : ‖w * u‖ < 1 := by
    rw [norm_mul]
    calc
      ‖w‖ * ‖u‖ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg u)
      _ < R * R⁻¹ := (mul_lt_mul_of_pos_left hu' hR)
      _ = 1 := mul_inv_cancel₀ hR.ne'
  intro heq
  have hwu : w * u = 1 := (sub_eq_zero.mp heq).symm
  simp [hwu] at hmul

/-- A lower bound for the area denominator. -/
theorem HolomorphicCousin.area_denominator_lower_bound {R r : ℝ} (hR : 0 < R)
    {x w : ℂ} (hx : x ∈ Metric.ball 0 r) (hw : ‖w‖ ≤ R) : 1 - R * r ≤ ‖1 - w * x‖ := by
  have hx' : ‖x‖ ≤ r := le_of_lt (by simpa using hx)
  have hmul : ‖w * x‖ ≤ R * r := by
    rw [norm_mul]
    exact mul_le_mul hw hx' (norm_nonneg x) hR.le
  calc
    1 - R * r ≤ 1 - ‖w * x‖ := sub_le_sub_left hmul 1
    _ = ‖(1 : ℂ)‖ - ‖w * x‖ := by rw [NormOneClass.norm_one]
    _ ≤ ‖1 - w * x‖ := norm_sub_norm_le _ _

/-- The reciprocal area kernel is differentiable. -/
theorem HolomorphicCousin.area_reciprocal_kernel_hasDerivAt {w x : ℂ}
    (hne : 1 - w * x ≠ 0) : HasDerivAt (fun y : ℂ => y * (1 - w * y)⁻¹) (1 / (1 - w * x) ^ 2) x :=
  by
  have hn : HasDerivAt (fun y : ℂ => y) 1 x := hasDerivAt_id x
  have hd : HasDerivAt (fun y : ℂ => 1 - w * y) (-w) x := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id x).const_mul w).const_sub 1
  have hnum : (1 : ℂ) * (1 - w * x) - x * -w = 1 := by ring
  simpa only [Pi.div_apply, hnum, div_eq_mul_inv] using! hn.div hd hne

/-- The extended Cauchy–Green integral is differentiable. -/
theorem HolomorphicCousin.hasDerivAt_cauchyGreenInfinity {f : ℂ → ℂ} {R : ℝ}
    (hf : MeasureTheory.Integrable f) (hR : 0 < R) (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R)
    {u : ℂ} (hu : u ∈ Metric.ball 0 R⁻¹) :
    HasDerivAt (cauchyGreenInfinity f)
      ((1 / (Real.pi : ℂ)) * ∫ w : ℂ, (1 / (1 - w * u) ^ 2) * f w) u := by
  have hu' : ‖u‖ < R⁻¹ := by simpa using hu
  obtain ⟨r, hur, hrR⟩ := exists_between hu'
  have hsub : Metric.ball (0 : ℂ) r ⊆ Metric.ball 0 R⁻¹ := Metric.ball_subset_ball hrR.le
  have humem : u ∈ Metric.ball (0 : ℂ) r := by simpa using hur
  have hd : 0 < 1 - R * r := by
    have hlt : R * r < 1 := by
      calc
        R * r < R * R⁻¹ := mul_lt_mul_of_pos_left hrR hR
        _ = 1 := mul_inv_cancel₀ hR.ne'
    linarith
  have hmeas (x : ℂ) :
    MeasureTheory.AEStronglyMeasurable (fun w : ℂ => x * (1 - w * x)⁻¹ * f w)
      MeasureTheory.MeasureSpace.volume := by
    apply MeasureTheory.AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact Measurable.aestronglyMeasurable (by fun_prop)
  have hint : MeasureTheory.Integrable (fun w : ℂ => u * (1 - w * u)⁻¹ * f w) := by
    refine (hf.norm.const_mul (‖u‖ * (1 - R * r)⁻¹)).mono' (hmeas u) ?_
    filter_upwards with w
    by_cases hw : f w = 0
    · simp [hw]
    · have hwb := hbound w hw
      simp only [norm_mul, norm_inv]
      gcongr
      exact area_denominator_lower_bound hR humem hwb
  change HasDerivAt (fun x => cauchyGreenInfinity f x) _ u
  simp only [cauchyGreenInfinity]
  apply HasDerivAt.const_mul
  refine
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := fun x w : ℂ =>
        (1 / (1 - w * x) ^ 2) * f w) (bound := fun w : ℂ => ((1 - R * r) ^ 2)⁻¹ * ‖f w‖)
        (Metric.isOpen_ball.mem_nhds humem) (Filter.Eventually.of_forall hmeas) hint ?_ ?_ ?_
        ?_).2
  · apply MeasureTheory.AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards with w x hx
    by_cases hw : f w = 0
    · simp [hw]
    · have hwb := hbound w hw
      simp only [norm_mul, norm_inv, norm_pow, one_div]
      gcongr
      exact area_denominator_lower_bound hR hx hwb
  · exact hf.norm.const_mul _
  · filter_upwards with w x hx
    by_cases hw : f w = 0
    · simpa only [hw, MulZeroClass.mul_zero] using hasDerivAt_const x (0 : ℂ)
    · exact
        (area_reciprocal_kernel_hasDerivAt
              (area_denominator_ne_zero hR (hsub hx) (hbound w hw))).mul_const
          (f w)

/-- The extended integral is analytic for an integrable kernel. -/
theorem HolomorphicCousin.analyticOnNhd_cauchyGreenInfinity_of_integrable {f : ℂ → ℂ} {R : ℝ}
    (hf : MeasureTheory.Integrable f) (hR : 0 < R) (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R) :
    AnalyticOnNhd ℂ (cauchyGreenInfinity f) (Metric.ball 0 R⁻¹) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro u hu
  exact (hasDerivAt_cauchyGreenInfinity hf hR hbound hu).differentiableAt.differentiableWithinAt

/-- The extended Cauchy–Green integral is analytic. -/
theorem HolomorphicCousin.analyticOnNhd_cauchyGreenInfinity {f : ℂ → ℂ} {R : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < R)
    (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R) :
    AnalyticOnNhd ℂ (cauchyGreenInfinity f) (Metric.ball 0 R⁻¹) :=
  analyticOnNhd_cauchyGreenInfinity_of_integrable (hf.integrable_of_hasCompactSupport hfc) hR
    hbound

/-- The extended integral computes the `1/z` integral. -/
theorem HolomorphicCousin.cauchyGreenInfinity_inv (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    cauchyGreenInfinity f z⁻¹ = cauchyGreen f z := by
  unfold cauchyGreenInfinity cauchyGreen
  congr 1
  calc
    (∫ w : ℂ, z⁻¹ * (1 - w * z⁻¹)⁻¹ * f w) = ∫ w : ℂ, (z - w)⁻¹ * f w := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      have hden : 1 - w * z⁻¹ = (z - w) * z⁻¹ := by rw [sub_mul, mul_inv_cancel₀ hz]
      rw [hden, mul_inv_rev, inv_inv, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]
    _ = ∫ w : ℂ, w⁻¹ * f (z - w) := by
      simpa only [sub_sub_self] using
        MeasureTheory.integral_sub_left_eq_self (fun w : ℂ => w⁻¹ * f (z - w))
          MeasureTheory.MeasureSpace.volume z

/-! ### The corrected local solution -/

/-- The analytic correction of a local potential. -/
def HolomorphicCousin.LocalPotential.correctedPart {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (i : ι) (z : ℂ) : ℂ :=
  P.potential i z - HolomorphicCousin.cauchyGreen P.forcing z

/-- The corrected part is analytic. -/
theorem HolomorphicCousin.LocalPotential.correctedPart_analytic {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (hc : HasCompactSupport P.forcing) (i : ι) :
    AnalyticOnNhd ℂ (P.correctedPart i) (P.domain i) := by
  obtain ⟨hs, he⟩ := HolomorphicCousin.cauchyGreen_smooth_dbar_solution P.forcing_contDiff hc
  exact P.corrected_analytic (hs.differentiable (by simp)) he i

/-- The corrected part subtracts the Cauchy–Green solution. -/
theorem HolomorphicCousin.LocalPotential.correctedPart_sub {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (i j : ι) (z : ℂ) :
    P.correctedPart i z - P.correctedPart j z = P.potential i z - P.potential j z :=
  P.corrected_difference (HolomorphicCousin.cauchyGreen P.forcing) i j z

/-- The local potential corrected at infinity. -/
def HolomorphicCousin.LocalPotential.correctedInfinity {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (u : ℂ) : ℂ :=
  -HolomorphicCousin.cauchyGreenInfinity P.forcing u

/-- The corrected potential vanishes at infinity. -/
@[simp]
theorem HolomorphicCousin.LocalPotential.correctedInfinity_zero {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) : P.correctedInfinity 0 = 0 := by
  simp [correctedInfinity]

/-- The corrected potential is analytic at infinity. -/
theorem HolomorphicCousin.LocalPotential.correctedInfinity_analytic {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (hc : HasCompactSupport P.forcing) {R : ℝ}
    (hR : 0 < R) (hbound : ∀ z ∈ Function.support P.forcing, ‖z‖ ≤ R) :
    AnalyticOnNhd ℂ P.correctedInfinity (Metric.ball 0 R⁻¹) :=
  (HolomorphicCousin.analyticOnNhd_cauchyGreenInfinity P.forcing_contDiff.continuous hc hR
      hbound).neg

/-- The corrected part agrees with the infinity correction. -/
theorem HolomorphicCousin.LocalPotential.correctedPart_eq_infinity {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {z : ℂ} (hz : z ≠ 0)
    (hs : P.potential i z = 0) : P.correctedPart i z = P.correctedInfinity z⁻¹ := by
  simp only [correctedPart, hs, zero_sub, correctedInfinity,
    HolomorphicCousin.cauchyGreenInfinity_inv P.forcing hz]

/-! ### The Cousin solution -/

/-- A normalized holomorphic solution of the Cousin cocycle. -/
structure HolomorphicCousin.NormalizedCocycleSolution {ι : Type*} (U : ι → Set ℂ)
    (h : ι → ι → ℂ → ℂ) (i₀ : ι) (R : ℝ) where
  localPart : ι → ℂ → ℂ
  infinityPart : ℂ → ℂ
  local_analytic : ∀ i, AnalyticOnNhd ℂ (localPart i) (U i)
  infinity_analytic : AnalyticOnNhd ℂ infinityPart (Metric.ball 0 R⁻¹)
  infinity_zero : infinityPart 0 = 0
  equation : ∀ i j z, z ∈ U i → z ∈ U j → localPart i z - localPart j z = h i j z
  atInfinity : ∀ z, R < ‖z‖ → localPart i₀ z = infinityPart z⁻¹

/-- A normalized holomorphic solution of the additive Cousin problem exists. -/
theorem HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution {ι : Type*}
    {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k → h i j z + h j k z = h i k z) (i₀ : ι) {R : ℝ}
    (hR : 0 < R) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    Nonempty (NormalizedCocycleSolution U h i₀ R) := by
  obtain ⟨P, hPU, htrans, ⟨V, _, hRV, _, hs0, _⟩, hsupport, hcompact⟩ :=
    exists_normalized_cocycle_localPotential hU hcover hh hc i₀ R hRU
  have hbound : ∀ z ∈ Function.support P.forcing, ‖z‖ ≤ R := by
    intro z hz
    have hzR := hsupport (subset_tsupport P.forcing hz)
    exact (show ‖z‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hzR).le
  refine
    ⟨{  localPart := P.correctedPart
        infinityPart := P.correctedInfinity
        local_analytic := ?_
        infinity_analytic := P.correctedInfinity_analytic hcompact hR hbound
        infinity_zero := P.correctedInfinity_zero
        equation := ?_
        atInfinity := ?_ }⟩
  · intro i
    simpa only [hPU] using P.correctedPart_analytic hcompact i
  · intro i j z hi hj
    exact (P.correctedPart_sub i j z).trans (htrans i j z hi hj)
  · intro z hz
    apply P.correctedPart_eq_infinity (norm_pos_iff.mp (hR.trans hz))
    apply hs0
    apply hRV
    simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz.le

/-- A holomorphic solution of the cocycle with value `−1` on the normalization. -/
structure HolomorphicCousin.NegativeOneCocycleSolution {ι : Type*} (U : ι → Set ℂ)
    (h : ι → ι → ℂ → ℂ) (i₀ : ι) (R : ℝ) where
  localPart : ι → ℂ → ℂ
  infinityPart : ℂ → ℂ
  local_analytic : ∀ i, AnalyticOnNhd ℂ (localPart i) (U i)
  infinity_analytic : AnalyticOnNhd ℂ infinityPart (Metric.ball 0 R⁻¹)
  equation : ∀ i j z, z ∈ U i → z ∈ U j → localPart i z - localPart j z = h i j z
  atInfinity : ∀ z, R < ‖z‖ → localPart i₀ z = z⁻¹ * infinityPart z⁻¹

/-- A normalized solution gives the `−1` solution. -/
def HolomorphicCousin.NormalizedCocycleSolution.negativeOne {ι : Type*} {U : ι → Set ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ} (hR : 0 < R)
    (s : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R) :
    HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R
    where
  localPart := s.localPart
  infinityPart := dslope s.infinityPart 0
  local_analytic := s.local_analytic
  infinity_analytic :=
    HolomorphicCousin.analyticOnNhd_dslope_zero (inv_pos.mpr hR) s.infinity_analytic
  equation := s.equation
  atInfinity := by
    intro z hz
    rw [s.atInfinity z hz]
    exact (HolomorphicCousin.zero_mul_dslope s.infinity_zero z⁻¹).symm

/-- A `−1`-normalized holomorphic cocycle solution exists. -/
theorem HolomorphicCousin.exists_negativeOne_holomorphic_cocycle_solution {ι : Type*}
    {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k → h i j z + h j k z = h i k z) (i₀ : ι) {R : ℝ}
    (hR : 0 < R) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    Nonempty (NegativeOneCocycleSolution U h i₀ R) := by
  obtain ⟨s⟩ := exists_normalized_holomorphic_cocycle_solution hU hcover hh hc i₀ hR hRU
  exact ⟨s.negativeOne hR⟩
end Mathoverflow1973
