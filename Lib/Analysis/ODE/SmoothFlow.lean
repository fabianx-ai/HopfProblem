/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.Flow.HeightTranslating

/-!
# Smooth dependence of flows

For a `C^∞` vector field the flow depends `C^∞` on the initial point and on time
(`SmoothODE.*`, Lee Thm 9.12's smoothness conclusion), with coordinate-field helpers
(`MorseCancellation.coordinateField`).

## Main definitions and results

* `SmoothODE.*` : smooth dependence of the flow.

## References

* [John M. Lee, *Introduction to Smooth Manifolds*][lee13], Theorem 9.12

## Tags

ODE, smooth flow
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

theorem SmoothODE.exists_smooth_fixedPoint_germ {P E : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [CompleteSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P × E → E} {p : P} {x : E} (hF : ContDiffAt ℝ ∞ F (p, x)) (hfix : F (p, x) = x)
    (hsmall : ‖(fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E)‖ < 1) :
    ∃ g : P → E,
      g p = x ∧
        ContDiffAt ℝ ∞ g p ∧
          (∀ᶠ q in 𝓝 p, F (q, g q) = g q) ∧ ∀ᶠ v in 𝓝 (p, x), F v = v.2 ↔ g v.1 = v.2 := by
  let G : P × E → E := fun v => v.2 - F v
  have hG : ContDiffAt ℝ ∞ G (p, x) := contDiffAt_snd.sub hF
  have hdG : HasFDerivAt G (ContinuousLinearMap.snd ℝ P E - fderiv ℝ F (p, x)) (p, x) :=
    (ContinuousLinearMap.snd ℝ P E).hasFDerivAt.sub (hF.differentiableAt (by simp)).hasFDerivAt
  have hpartial :
    (fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E) =
      1 - (fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E) := by
    rw [hdG.fderiv]
    ext z
    rfl
  have hinv : ((fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [hpartial]
    obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hsmall
    exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩
  let g := hG.implicitFunction (by simp) hinv
  have hgp : g p = x := hG.implicitFunction_apply_self (by simp) hinv
  have hg : ContDiffAt ℝ ∞ g p := hG.contDiffAt_implicitFunction (by simp) hinv
  refine ⟨g, hgp, hg, ?_, ?_⟩
  · filter_upwards [hG.eventually_apply_implicitFunction (by simp) hinv] with q hq
    change g q - F (q, g q) = x - F (p, x) at hq
    rw [hfix, sub_self] at hq
    exact (sub_eq_zero.mp hq).symm
  · filter_upwards [hG.eventually_apply_eq_iff_implicitFunction (by simp) hinv] with v hv
    change (v.2 - F v = x - F (p, x) ↔ g v.1 = v.2) at hv
    rw [hfix, sub_self, sub_eq_zero] at hv
    exact eq_comm.trans hv

theorem SmoothODE.contDiffAt_of_continuous_fixedPoint {P E : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [CompleteSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P × E → E} {p : P} {x : E} (hF : ContDiffAt ℝ ∞ F (p, x)) (hfix : F (p, x) = x)
    (hsmall : ‖(fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E)‖ < 1) {g : P → E}
    (hg : ContinuousAt g p) (hgp : g p = x) (heq : ∀ᶠ q in 𝓝 p, F (q, g q) = g q) :
    ContDiffAt ℝ ∞ g p := by
  obtain ⟨ψ, -, hψ, -, huniq⟩ := exists_smooth_fixedPoint_germ hF hfix hsmall
  have hgraph : Filter.Tendsto (fun q => (q, g q)) (𝓝 p) (𝓝 (p, x)) := by
    have hh : Filter.Tendsto (fun q => (q, g q)) (𝓝 p) (𝓝 (p, g p)) := continuousAt_id.prodMk hg
    rwa [hgp] at hh
  apply hψ.congr_of_eventuallyEq
  filter_upwards [hgraph huniq, heq] with q hq hfixq
  exact ((hq.mp hfixq).symm)

theorem SmoothODE.exists_smooth_fixedPoint_neighborhood {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : P × E → E} {p : P} {x : E} (hF : ContDiff ℝ ∞ F)
    (hfix : F (p, x) = x)
    (hsmall : ‖(fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E)‖ < 1) :
    ∃ (U : Set P) (g : P → E),
      IsOpen U ∧ p ∈ U ∧ g p = x ∧ ContDiffOn ℝ ∞ g U ∧ ∀ q ∈ U, F (q, g q) = g q := by
  obtain ⟨g, hgp, hg, heq, -⟩ := exists_smooth_fixedPoint_germ hF.contDiffAt hfix hsmall
  let A (v : P × E) := (fderiv ℝ F v).comp (ContinuousLinearMap.inr ℝ P E)
  have hA : Continuous A := (hF.continuous_fderiv (by simp)).clm_comp continuous_const
  have hgraph : ContinuousAt (fun q => (q, g q)) p := continuousAt_id.prodMk hg.continuousAt
  have hn : ContinuousAt (fun q => ‖A (q, g q)‖) p := (hA.continuousAt.comp hgraph).norm
  have hbase : ‖A (p, g p)‖ < 1 := by simpa only [hgp, A] using hsmall
  have hsmall' : ∀ᶠ q in 𝓝 p, ‖A (q, g q)‖ < 1 := hn (eventually_lt_nhds hbase)
  have hg₁ : ContDiffAt ℝ 1 g p := hg.of_le (by simp)
  have hcont : ∀ᶠ q in 𝓝 p, ContinuousAt g q :=
    (hg₁.eventually (by simp)).mono (fun _ h => h.continuousAt)
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp ((heq.and hsmall').and hcont)
  refine ⟨U, g, hU, hpU, hgp, ?_, fun q hq => (hUsub hq).1.1⟩
  intro q hq
  apply
    (contDiffAt_of_continuous_fixedPoint hF.contDiffAt (hUsub hq).1.1 (hUsub hq).1.2 (hUsub hq).2
        rfl ?_).contDiffWithinAt
  filter_upwards [hU.mem_nhds hq] with r hr
  exact (hUsub hr).1.1

def SmoothODE.pathOperator {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩
      map_add' := by intro u v; ext t; exact map_add (A t) (u t) (v t)
      map_smul' := by intro r u; ext t; exact map_smul (A t) r (u t) } ‖A‖
    (by
      intro u
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      intro t
      exact
        ((A t).le_opNorm (u t)).trans
          (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t) (norm_nonneg _)
            (norm_nonneg _)))

theorem SmoothODE.norm_pathOperator_le {K E F : Type*} [TopologicalSpace K]
    [CompactSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : C(K, E →L[ℝ] F)) : ‖pathOperator A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact
    ((A t).le_opNorm (u t)).trans
      (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

def SmoothODE.pathOperatorCLM {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous
    { toFun := pathOperator
      map_add' := by intro A B; ext u t; rfl
      map_smul' := by intro r A; ext u t; rfl } 1
    (by
      intro A
      change ‖pathOperator A‖ ≤ 1 * ‖A‖
      rw [one_mul]
      exact norm_pathOperator_le A)

theorem SmoothODE.exists_quadratic_remainder_bound {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (R : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ x y : E, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdcont : Continuous (fderiv ℝ (fderiv ℝ f)) := hdf.continuous_fderiv (by simp)
  obtain ⟨C₀, hC₀⟩ :=
    (ProperSpace.isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hdcont.continuousOn
  let C := Max.max C₀ 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (z : E) (hz : z ∈ Metric.closedBall (0 : E) R) : ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C := by
    exact (hC₀ z hz).trans (by dsimp [C]; linarith [le_max_left C₀ 0])
  have hlip {x z : E} (hx : x ∈ Metric.closedBall (0 : E) R)
    (hz : z ∈ Metric.closedBall (0 : E) R) : ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖z - x‖ :=
    (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdf.differentiable (by simp) z) hbound hx hz
  refine ⟨C, hC, ?_⟩
  intro x y hx hy
  have hxR : x ∈ Metric.closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hyR : y ∈ Metric.closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hseg : segment ℝ x y ⊆ Metric.closedBall (0 : E) R :=
    (convex_closedBall _ _).segment_subset hxR hyR
  have hdist : segment ℝ x y ⊆ Metric.closedBall x ‖y - x‖ := by
    apply (convex_closedBall x ‖y - x‖).segment_subset
    · exact Metric.mem_closedBall_self (norm_nonneg _)
    · simp only [Metric.mem_closedBall, dist_eq_norm, le_refl]
  have hh :=
    (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
      (fun z _ => hf.differentiable (by simp) z)
      (fun z hz =>
        (hlip hxR (hseg hz)).trans
          (mul_le_mul_of_nonneg_left
            (show ‖z - x‖ ≤ ‖y - x‖ from by
              simpa only [Metric.mem_closedBall, dist_eq_norm] using hdist hz)
            hC.le))
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two, mul_assoc] using hh

def SmoothODE.pathDerivative {K E F : Type*} [TopologicalSpace K] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : C(E, F)) (hf : ContDiff ℝ ∞ f)
    (u : C(K, E)) : C(K, E →L[ℝ] F) :=
  ⟨fun t => fderiv ℝ f (u t), (hf.continuous_fderiv (by simp)).comp u.continuous⟩

theorem SmoothODE.hasFDerivAt_pathPostcomposition {K E F : Type*} [TopologicalSpace K]
    [CompactSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : C(E, F)) (hf : ContDiff ℝ ∞ f) (u : C(K, E)) :
    HasFDerivAt (fun v : C(K, E) => f.comp v) (pathOperator (pathDerivative f hf u)) u := by
  obtain ⟨C, hC, hrem⟩ := exists_quadratic_remainder_bound hf (‖u‖ + 1)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let δ := Min.min 1 (ε / C)
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε hC)
  filter_upwards [Metric.ball_mem_nhds (0 : C(K, E)) hδ] with h hh
  have hhnorm : ‖h‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hhnorm (min_le_left _ _)
  have hhε : C * ‖h‖ ≤ ε := by
    have hhdiv : ‖h‖ < ε / C := lt_of_lt_of_le hhnorm (min_le_right _ _)
    have hh' := (lt_div_iff₀ hC).mp hhdiv
    nlinarith
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg h))).mpr
  intro t
  change ‖f (u t + h t) - f (u t) - fderiv ℝ f (u t) (h t)‖ ≤ ε * ‖h‖
  have hxu : ‖u t‖ ≤ ‖u‖ + 1 := (u.norm_coe_le_norm t).trans (by linarith)
  have hyu : ‖u t + h t‖ ≤ ‖u‖ + 1 :=
    (norm_add_le _ _).trans (by linarith [u.norm_coe_le_norm t, h.norm_coe_le_norm t])
  have hr := hrem (u t) (u t + h t) hxu hyu
  simp only [add_sub_cancel_left] at hr
  calc
    _ ≤ C * ‖h t‖ ^ 2 := hr
    _ ≤ C * ‖h‖ ^ 2 :=
      (mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h.norm_coe_le_norm t)) hC.le)
    _ ≤ ε * ‖h‖ := by
      have hh' := mul_le_mul_of_nonneg_right hhε (norm_nonneg h)
      simpa only [pow_two, mul_assoc] using hh'

theorem SmoothODE.fderiv_pathPostcomposition {K E F : Type*} [TopologicalSpace K]
    [CompactSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : C(E, F)) (hf : ContDiff ℝ ∞ f) (u : C(K, E)) :
    fderiv ℝ (fun v : C(K, E) => f.comp v) u = pathOperator (pathDerivative f hf u) :=
  (hasFDerivAt_pathPostcomposition f hf u).fderiv

theorem SmoothODE.contDiff_pathPostcomposition_nat {K : Type v} [TopologicalSpace K]
    [CompactSpace K] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F],
      ∀ (f : C(E, F)), ContDiff ℝ ∞ f → ContDiff ℝ n (fun w : C(K, E) => f.comp w) := by
  induction n with
  | zero =>
    intro F _ _ f _
    exact contDiff_zero.mpr f.continuous_postcomp
  | succ n ih =>
    intro F _ _ f hf
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun w => (hasFDerivAt_pathPostcomposition f hf w).differentiableAt, by simp, ?_⟩
    let df : C(E, E →L[ℝ] F) := ⟨fderiv ℝ f, hf.continuous_fderiv (by simp)⟩
    have hdf : ContDiff ℝ ∞ df := hf.fderiv_right (by simp)
    have hi := ih df hdf
    have heq : fderiv ℝ (fun w : C(K, E) => f.comp w) = fun w => pathOperator (df.comp w) := by
      funext w
      rw [fderiv_pathPostcomposition f hf w]
      rfl
    rw [heq]
    exact (pathOperatorCLM (K := K) (E := E) (F := F)).contDiff.comp hi

theorem SmoothODE.contDiff_pathPostcomposition {K : Type v} [TopologicalSpace K]
    [CompactSpace K] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : C(E, F)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun w : C(K, E) => f.comp w) :=
  contDiff_infty.mpr (fun n => contDiff_pathPostcomposition_nat n f hf)

abbrev SmoothODE.PathTime :=
  Set.Icc (-2 : ℝ) 2

def SmoothODE.pathClamp : ℝ → PathTime :=
  Set.projIcc (-2) 2 (by norm_num)

theorem SmoothODE.continuous_pathClamp : Continuous pathClamp :=
  continuous_projIcc

def SmoothODE.pathExtend {E : Type*} [NormedAddCommGroup E] (u : C(PathTime, E)) : ℝ → E :=
  u ∘ pathClamp

theorem SmoothODE.continuous_pathExtend {E : Type*} [NormedAddCommGroup E]
    (u : C(PathTime, E)) : Continuous (pathExtend u) :=
  u.continuous.comp continuous_pathClamp

def SmoothODE.pathPrimitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (u : C(PathTime, E)) : C(PathTime, E) :=
  ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s,
    (intervalIntegral.differentiable_integral_of_continuous
          (continuous_pathExtend u)).continuous.comp
      continuous_subtype_val⟩

theorem SmoothODE.norm_pathPrimitive_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (u : C(PathTime, E)) : ‖pathPrimitive u‖ ≤ 2 * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg u))).mpr
  intro t
  have hh :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (t : ℝ)) (f :=
      pathExtend u) (fun s _ => u.norm_coe_le_norm (pathClamp s))
  have ht : |(t : ℝ)| ≤ 2 := abs_le.mpr t.property
  simp only [sub_zero] at hh
  change ‖∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s‖ ≤ 2 * ‖u‖
  simpa only [sub_zero, mul_comm] using hh.trans (mul_le_mul_of_nonneg_left ht (norm_nonneg u))

def SmoothODE.pathPrimitiveCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] : C(PathTime, E) →L[ℝ] C(PathTime, E) :=
  LinearMap.mkContinuous
    { toFun := pathPrimitive
      map_add' := by
        intro u v
        ext t
        change
          (∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s + pathExtend v s) =
            (∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s) + (∫ s in (0 : ℝ)..(t : ℝ), pathExtend v s)
        exact
          intervalIntegral.integral_add ((continuous_pathExtend u).intervalIntegrable _ _)
            ((continuous_pathExtend v).intervalIntegrable _ _)
      map_smul' := by
        intro r u
        ext t
        change
          (∫ s in (0 : ℝ)..(t : ℝ), r • pathExtend u s) =
            r • (∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s)
        exact intervalIntegral.integral_smul r (pathExtend u) }
    2 (fun u => norm_pathPrimitive_le u)

theorem SmoothODE.hasDerivAt_pathPrimitive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (u : C(PathTime, E)) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, pathExtend u s) (pathExtend u t) t :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_pathExtend u).intervalIntegrable _ _)
    (continuous_pathExtend u).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_pathExtend u).continuousAt

def SmoothODE.picardPathMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (v : C(E, E)) (q : (E × ℝ) × C(PathTime, E)) : C(PathTime, E) :=
  ContinuousMap.const PathTime q.1.1 + q.1.2 • pathPrimitiveCLM (v.comp q.2)

theorem SmoothODE.contDiff_picardPathMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (picardPathMap v) := by
  exact
    ((ContinuousLinearMap.const ℝ PathTime : E →L[ℝ] C(PathTime, E)).contDiff.comp
          contDiff_fst.fst).add
      (contDiff_fst.snd.smul
        ((pathPrimitiveCLM (E := E)).contDiff.comp
          ((contDiff_pathPostcomposition v hv).comp contDiff_snd)))

theorem SmoothODE.picardPathMap_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (v : C(E, E)) (x : E) (u : C(PathTime, E)) :
    picardPathMap v ((x, 0), u) = ContinuousMap.const PathTime x := by
  simp only [picardPathMap, zero_smul, add_zero]

theorem SmoothODE.picardPathMap_partial_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E)
    (u : C(PathTime, E)) :
    (fderiv ℝ (picardPathMap v) ((x, 0), u)).comp
        (ContinuousLinearMap.inr ℝ (E × ℝ) C(PathTime, E)) =
      0 := by
  have hQ := contDiff_picardPathMap v hv
  have hd :=
    (hQ.differentiable (by simp) ((x, 0), u)).hasFDerivAt.comp u
      ((hasFDerivAt_const (x, (0 : ℝ)) u).prodMk (hasFDerivAt_id u))
  change
    HasFDerivAt (fun w => picardPathMap v ((x, 0), w))
      ((fderiv ℝ (picardPathMap v) ((x, 0), u)).comp
        (ContinuousLinearMap.inr ℝ (E × ℝ) C(PathTime, E)))
      u at hd
  have he : (fun w => picardPathMap v ((x, 0), w)) = fun _ => ContinuousMap.const PathTime x :=
    funext (picardPathMap_zero v x)
  rw [he] at hd
  exact hd.unique (hasFDerivAt_const (ContinuousMap.const PathTime x) u)

theorem SmoothODE.exists_smooth_picard_paths {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    ∃ (U : Set (E × ℝ)) (u : E × ℝ → C(PathTime, E)),
      IsOpen U ∧
        (x, 0) ∈ U ∧
          u (x, 0) = ContinuousMap.const PathTime x ∧
            ContDiffOn ℝ ∞ u U ∧
              ∀ q ∈ U,
                ∀ t : PathTime,
                  u q t = q.1 + q.2 • (∫ s in (0 : ℝ)..(t : ℝ), v (u q (pathClamp s))) := by
  have hsmall :
    ‖(fderiv ℝ (picardPathMap v) ((x, 0), ContinuousMap.const PathTime x)).comp
          (ContinuousLinearMap.inr ℝ (E × ℝ) C(PathTime, E))‖ <
      1 := by
    rw [picardPathMap_partial_zero v hv x, norm_zero]
    exact zero_lt_one
  obtain ⟨U, u, hU, hx, hu, hcont, hfix⟩ :=
    exists_smooth_fixedPoint_neighborhood (contDiff_picardPathMap v hv)
      (picardPathMap_zero v x (ContinuousMap.const PathTime x)) hsmall
  refine ⟨U, u, hU, hx, hu, hcont, ?_⟩
  intro q hq t
  have hh := congrArg (fun w : C(PathTime, E) => w t) (hfix q hq)
  exact hh.symm

def SmoothODE.picardCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : C(E, E)) (p : E) (τ : ℝ) (u : C(PathTime, E)) (t : ℝ) : E :=
  p + τ • (∫ s in (0 : ℝ)..t, v (u (pathClamp s)))

theorem SmoothODE.picardCurve_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : C(E, E)) (p : E) (τ : ℝ) (u : C(PathTime, E)) : picardCurve v p τ u 0 = p := by
  simp only [picardCurve, intervalIntegral.integral_same, smul_zero, add_zero]

theorem SmoothODE.hasDerivAt_picardCurve {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (p : E) (τ : ℝ) (u : C(PathTime, E))
    (t : ℝ) : HasDerivAt (picardCurve v p τ u) (τ • v (u (pathClamp t))) t :=
  ((hasDerivAt_pathPrimitive (v.comp u) t).const_smul τ).const_add p

theorem SmoothODE.picardCurve_eq_path {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : C(E, E)) {p : E} {τ : ℝ} {u : C(PathTime, E)}
    (heq : ∀ t : PathTime, u t = p + τ • (∫ s in (0 : ℝ)..(t : ℝ), v (u (pathClamp s)))) {t : ℝ}
    (ht : t ∈ Set.Icc (-2 : ℝ) 2) : picardCurve v p τ u t = u (pathClamp t) := by
  have hc : pathClamp t = ⟨t, ht⟩ := Set.projIcc_of_mem _ ht
  rw [hc]
  exact (heq ⟨t, ht⟩).symm

theorem SmoothODE.hasDerivAt_picardCurve_of_fixedPoint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) {p : E} {τ : ℝ} {u : C(PathTime, E)}
    (heq : ∀ t : PathTime, u t = p + τ • (∫ s in (0 : ℝ)..(t : ℝ), v (u (pathClamp s)))) {t : ℝ}
    (ht : t ∈ Set.Icc (-2 : ℝ) 2) :
    HasDerivAt (picardCurve v p τ u) (τ • v (picardCurve v p τ u t)) t := by
  rw [picardCurve_eq_path v heq ht]
  exact hasDerivAt_picardCurve v p τ u t

theorem SmoothODE.exists_smooth_picard_endpoints {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    ∃ (U : Set (E × ℝ)) (u : E × ℝ → C(PathTime, E)) (g : E × ℝ → E),
      IsOpen U ∧
        (x, 0) ∈ U ∧
          u (x, 0) = ContinuousMap.const PathTime x ∧
            ContDiffOn ℝ ∞ u U ∧
              ContDiffOn ℝ ∞ g U ∧
                (∀ q, g q = u q ⟨1, by norm_num⟩) ∧
                  ∀ q ∈ U,
                    (picardCurve v q.1 q.2 (u q) 0 = q.1) ∧
                      (picardCurve v q.1 q.2 (u q) 1 = g q) ∧
                        (∀ t ∈ Set.Icc (-2 : ℝ) 2,
                            picardCurve v q.1 q.2 (u q) t = u q (pathClamp t)) ∧
                          ∀ t ∈ Set.Icc (-2 : ℝ) 2,
                            HasDerivAt (picardCurve v q.1 q.2 (u q))
                              (q.2 • v (picardCurve v q.1 q.2 (u q) t)) t := by
  obtain ⟨U, u, hU, hx, hux, hu, heq⟩ := exists_smooth_picard_paths v hv x
  let g (q : E × ℝ) := u q ⟨1, by norm_num⟩
  let L : C(PathTime, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ (⟨1, by norm_num⟩ : PathTime)
  have hg : ContDiffOn ℝ ∞ g U := L.contDiff.comp_contDiffOn hu
  refine ⟨U, u, g, hU, hx, hux, hu, hg, fun _ => rfl, ?_⟩
  intro q hq
  refine
    ⟨picardCurve_zero v _ _ _, ?_, fun t ht => picardCurve_eq_path v (heq q hq) ht, fun t ht =>
      hasDerivAt_picardCurve_of_fixedPoint v (heq q hq) ht⟩
  have hh := picardCurve_eq_path v (heq q hq) (t := 1) (by norm_num)
  have hc : pathClamp 1 = (⟨1, by norm_num⟩ : PathTime) := Set.projIcc_of_mem _ (by norm_num)
  exact hh.trans (congrArg (u q) hc)

theorem SmoothODE.ordinary_curve_eqOn_of_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : E → E} (hv : ContDiff ℝ 1 v) {γ η : ℝ → E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo a b) (hγ : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (v (γ t)) t)
    (hη : ∀ t ∈ Set.Ioo a b, HasDerivAt η (v (η t)) t) (heq : γ t₀ = η t₀) :
    Set.EqOn γ η (Set.Ioo a b) := by
  let V : (x : E) → TangentSpace 𝓘(ℝ, E) x := fun x => v x
  have hV :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    (tangentBundleModelSpaceDiffeomorph 𝓘(ℝ, E) 1).symm.contMDiff.comp
      (contDiff_id.prodMk hv).contMDiff
  have hγM : IsMIntegralCurveOn γ V (Set.Ioo a b) := by
    intro t ht
    exact (hγ t ht).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hηM : IsMIntegralCurveOn η V (Set.Ioo a b) := by
    intro t ht
    exact (hη t ht).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ hV hγM hηM heq

theorem SmoothODE.picard_endpoint_eq_local_solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) {p : E} {τ ε : ℝ} (hτ : |τ| < ε / 2)
    {u : C(PathTime, E)} {g : E} (hzero : picardCurve v p τ u 0 = p)
    (hend : picardCurve v p τ u 1 = g)
    (hcurve :
      ∀ t ∈ Set.Icc (-2 : ℝ) 2,
        HasDerivAt (picardCurve v p τ u) (τ • v (picardCurve v p τ u t)) t)
    {α : ℝ → E} (hαzero : α 0 = p) (hα : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt α (v (α t)) t) :
    g = α τ := by
  have hscaled : ContDiff ℝ 1 (fun y : E => τ • v y) := contDiff_const.smul (hv.of_le (by simp))
  have hη (r : ℝ) (hr : r ∈ Set.Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun s : ℝ => α (s * τ)) (τ • v (α (r * τ))) r := by
    have hrt : r * τ ∈ Set.Ioo (-ε) ε := by
      apply abs_lt.mp
      rw [abs_mul]
      have hrabs : |r| ≤ 2 := (abs_lt.mpr hr).le
      have hh := mul_le_mul_of_nonneg_right hrabs (abs_nonneg τ)
      linarith
    have hd := (hα (r * τ) hrt).scomp r ((hasDerivAt_id r).mul_const τ)
    change HasDerivAt (fun s : ℝ => α (s * τ)) ((1 * τ) • v (α (r * τ))) r at hd
    simpa only [one_mul] using hd
  have heq :=
    ordinary_curve_eqOn_of_contDiff hscaled (show (0 : ℝ) ∈ Set.Ioo (-2) 2 by norm_num)
      (fun t ht => hcurve t ⟨ht.1.le, ht.2.le⟩) hη
      (by simpa only [MulZeroClass.zero_mul] using hzero.trans hαzero.symm)
  have hh := heq (x := 1) (by norm_num)
  simpa only [hend, one_mul] using hh

theorem SmoothODE.contDiffAt_ordinary_localFlow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) {P : Set E}
    (hP : IsOpen P) {x : E} (hx : x ∈ P) {ε : ℝ} (hε : 0 < ε) {H : E × ℝ → E}
    (hinit : ∀ p ∈ P, H (p, 0) = p)
    (hH : ∀ p ∈ P, ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (fun s : ℝ => H (p, s)) (v (H (p, t))) t) :
    ContDiffAt ℝ ∞ H (x, 0) := by
  obtain ⟨U, u, g, hU, hxU, -, -, hg, -, hpaths⟩ := exists_smooth_picard_endpoints v hv x
  apply (hg.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq
  have hsmall : Set.Ioo (-(ε / 2)) (ε / 2) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (neg_lt_zero.mpr (half_pos hε)) (half_pos hε)
  filter_upwards [hU.mem_nhds hxU, prod_mem_nhds (hP.mem_nhds hx) hsmall] with q hq hqsmall
  obtain ⟨hzero, hend, -, hcurve⟩ := hpaths q hq
  exact
    (picard_endpoint_eq_local_solution v hv (abs_lt.mpr hqsmall.2) hzero hend hcurve
        (hinit q.1 hqsmall.1) (hH q.1 hqsmall.1)).symm

theorem DiskFraming.starConvex_thickening_zero {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {K : Set D} (hK : StarConvex ℝ (0 : D) K) (δ : ℝ) :
    StarConvex ℝ (0 : D) (Metric.thickening δ K) := by
  rw [starConvex_zero_iff]
  intro x hx a ha₀ ha₁
  obtain ⟨z, hz, hxz⟩ := Metric.mem_thickening_iff.mp hx
  apply Metric.mem_thickening_iff.mpr
  refine ⟨a • z, hK.smul_mem hz ha₀ ha₁, ?_⟩
  calc
    Dist.dist (a • x) (a • z) = a * Dist.dist x z := by
      simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha₀]
    _ ≤ Dist.dist x z := (mul_le_of_le_one_left dist_nonneg ha₁)
    _ < δ := hxz

theorem DiskFraming.exists_smooth_map_into_neighborhood {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] {K U : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : D → D,
      ContDiff ℝ ∞ ρ ∧
        Set.MapsTo ρ Set.univ U ∧ ∃ V : Set D, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ Set.EqOn ρ id V := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  let W := Metric.thickening δ K
  have hW : IsOpen W := Metric.isOpen_thickening
  have hKW : K ⊆ W := Metric.self_subset_thickening hδ K
  have hstarW : StarConvex ℝ (0 : D) W := starConvex_thickening_zero hstar δ
  obtain ⟨L, hL, hKL, hLW⟩ := exists_compact_between hK hW hKW
  obtain ⟨β, hβ, hβrange, hβsupport, hβone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (𝓘(ℝ, D)) (n := (⊤ : ℕ∞)) hW hL.isClosed hLW
  let ρ : D → D := fun x => β x • x
  refine
    ⟨ρ, hβ.contDiff.smul contDiff_id, ?_, interior L, isOpen_interior, hKL, fun x hx =>
      hδU (hLW (interior_subset hx)), ?_⟩
  · intro x _
    have hb := hβrange (Set.mem_range_self x)
    by_cases hx : x ∈ W
    · exact hδU (hstarW.smul_mem hx hb.1 hb.2)
    · have hb0 : β x = 0 := by
        by_contra hn
        have hxs : x ∈ Function.support β := hn
        rw [hβsupport] at hxs
        exact hx hxs
      change β x • x ∈ U
      rw [hb0, zero_smul]
      exact hKU hz
  · intro x hx
    change β x • x = x
    rw [(hβone x).mp (interior_subset hx), one_smul]

theorem exists_smooth_extension_near_starConvex {D G H N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    {f : D → N} {K U : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, D) J ∞ f U) :
    ∃ g : D → N,
      ContMDiff 𝓘(ℝ, D) J ∞ g ∧ ∃ V : Set D, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ Set.EqOn g f V := by
  obtain ⟨ρ, hρ, hρU, V, hV, hKV, hVU, hρid⟩ :=
    DiskFraming.exists_smooth_map_into_neighborhood hK hz hstar hU hKU
  refine ⟨f ∘ ρ, contMDiffOn_univ.mp (hf.comp hρ.contMDiff.contMDiffOn hρU), V, hV, hKV, hVU, ?_⟩
  intro x hx
  exact congrArg f (hρid hx)

theorem exists_smooth_extension_near_point {D G H N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    {f : D → N} {U : Set D} {x₀ : D} (hf : ContMDiffOn 𝓘(ℝ, D) J ∞ f U) (hU : IsOpen U)
    (hx₀ : x₀ ∈ U) : ∃ g : D → N, ContMDiff 𝓘(ℝ, D) J ∞ g ∧ g =ᶠ[𝓝 x₀] f := by
  let shift : D → D := fun x => x + x₀
  have hshift : ContDiff ℝ ∞ shift := contDiff_id.add contDiff_const
  have hf' : ContMDiffOn 𝓘(ℝ, D) J ∞ (f ∘ shift) (shift ⁻¹' U) :=
    hf.comp hshift.contMDiff.contMDiffOn (fun _ hx => hx)
  have hzero : ({0} : Set D) ⊆ shift ⁻¹' U := by
    intro x hx
    have hx0 : x = 0 := hx
    subst x
    simpa only [shift, Set.mem_preimage, zero_add] using hx₀
  obtain ⟨g, hg, V, hV, h0V, _, heq⟩ :=
    exists_smooth_extension_near_starConvex isCompact_singleton (Set.mem_singleton 0)
      (starConvex_singleton (0 : D)) (hU.preimage hshift.continuous) hzero hf'
  let g' : D → N := fun x => g (x - x₀)
  have hg' : ContMDiff 𝓘(ℝ, D) J ∞ g' := hg.comp (contDiff_id.sub contDiff_const).contMDiff
  have htime : Filter.Tendsto (fun x : D => x - x₀) (𝓝 x₀) (𝓝 0) := by
    have htime' : Filter.Tendsto (fun x : D => x - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀)) :=
      (continuous_id.sub continuous_const : Continuous (fun x : D => x - x₀)).continuousAt.tendsto
    rwa [sub_self] at htime'
  refine ⟨g', hg', ?_⟩
  filter_upwards [htime (hV.mem_nhds (h0V (Set.mem_singleton 0)))] with x hx
  change g (x - x₀) = f x
  simpa only [Function.comp_apply, shift, sub_add_cancel] using heq hx

theorem SmoothODE.contDiffAt_local_field_flow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {v : E → E} {O P : Set E} (hv : ContDiffOn ℝ ∞ v O)
    (hO : IsOpen O) {x : E} (hxO : x ∈ O) (hP : IsOpen P) (hxP : x ∈ P) {ε : ℝ} (hε : 0 < ε)
    {H : E × ℝ → E} (hc : ContinuousAt H (x, 0)) (hinit : ∀ p ∈ P, H (p, 0) = p)
    (hH : ∀ p ∈ P, ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (fun s : ℝ => H (p, s)) (v (H (p, t))) t) :
    ContDiffAt ℝ ∞ H (x, 0) := by
  obtain ⟨w, hwM, heq⟩ := exists_smooth_extension_near_point hv.contMDiffOn hO hxO
  have hw : ContDiff ℝ ∞ w := contMDiff_iff_contDiff.mp hwM
  have hevent : ∀ᶠ q in 𝓝 (x, (0 : ℝ)), w (H q) = v (H q) := by
    have heq' : w =ᶠ[𝓝 (H (x, 0))] v := by rwa [hinit x hxP]
    exact hc heq'
  have hdom : P ×ˢ Set.Ioo (-ε) ε ∈ 𝓝 (x, (0 : ℝ)) :=
    prod_mem_nhds (hP.mem_nhds hxP) (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)
  have hdom' : ∀ᶠ q in 𝓝 (x, (0 : ℝ)), q ∈ P ×ˢ Set.Ioo (-ε) ε := hdom
  obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff.mp (hdom'.and hevent)
  have hrect (p : E) (hp : p ∈ Metric.ball x δ) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
    (p, t) ∈ P ×ˢ Set.Ioo (-ε) ε ∧ w (H (p, t)) = v (H (p, t)) := by
    apply hsub
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hp, by simpa only [dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht⟩
  let W : C(E, E) := ⟨w, hw.continuous⟩
  apply contDiffAt_ordinary_localFlow W hw Metric.isOpen_ball (Metric.mem_ball_self hδ) hδ
  · intro p hp
    exact hinit p (hrect p hp 0 ⟨neg_lt_zero.mpr hδ, hδ⟩).1.1
  · intro p hp t ht
    have hh := hrect p hp t ht
    have hd := hH p hh.1.1 t hh.1.2
    change HasDerivAt (fun s => H (p, s)) (w (H (p, t))) t
    rw [hh.2]
    exact hd

def MorseCancellation.coordinateField {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞) (z : E) : E :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm V z

theorem MorseCancellation.coordinateField_chart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞) {x : M} (hx : x ∈ e.source) :
    coordinateField (V := V) e (e x) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (V x) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₂ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₂
  have hi := ContinuousLinearMap.inverse_eq (he.symm_comp_deriv hx) h₂
  let A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e'.symm (e' x)
  let B : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e' x
  have hAB : A.inverse = B := hi
  have hvx : (show E from V (e'.symm (e' x))) = V x :=
    congrArg (fun y : M => (show E from V y)) (e'.left_inv hx)
  change A.inverse (V (e'.symm (e' x))) = B (V x)
  rw [hAB]
  exact congrArg B hvx

theorem MorseCancellation.contDiffOn_coordinateField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M]
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞) :
    ContDiffOn ℝ ∞ (coordinateField (V := V) e) e.target := by
  apply contMDiffOn_vectorSpace_iff_contDiffOn.mp
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  intro z hz
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z).IsInvertible := ⟨he.symm.mfderiv hz, rfl⟩
  exact
    ((hV (e.symm z)).mpullback_vectorField_preimage
        ((e.symm.contMDiffOn z hz).contMDiffAt (e.open_target.mem_nhds hz)) hinv
        (by simp)).contMDiffWithinAt

theorem MorseCancellation.hasDerivAt_coordinate_integralCurve {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ V) {t : ℝ} (ht : γ t ∈ e.source) :
    HasDerivAt (e ∘ γ) (coordinateField (V := V) e (e (γ t))) t := by
  have he :=
    ((e.contMDiffOn (γ t) ht).contMDiffAt (e.open_source.mem_nhds ht)).mdifferentiableAt (by simp)
  have hd := he.hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (γ t) ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
      (NormedSpace.fromTangentSpace t r) • coordinateField (V := V) e (e (γ t))
  rw [map_smul, coordinateField_chart e ht]
  rfl

theorem SmoothODE.contMDiffAt_native_flow_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (p : M) :
    ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun q : M × ℝ => F q.2 q.1) (p, 0) := by
  let e := modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) p
  have hp : p ∈ e.source := mem_extChartAt_source p
  have hz : e p ∈ e.target := e.map_source' hp
  have he : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e p :=
    (e.contMDiffOn p hp).contMDiffAt (e.open_source.mem_nhds hp)
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm (e p) :=
    (e.symm.contMDiffOn (e p) hz).contMDiffAt (e.open_target.mem_nhds hz)
  let C (q : E × ℝ) : M := F q.2 (e.symm q.1)
  let H (q : E × ℝ) : E := e (C q)
  have hC0 : C (e p, 0) = p := by
    change F 0 (e.symm (e p)) = p
    rw [F.map_zero_apply]
    exact e.left_inv' hp
  have hFC : Continuous (fun q : ℝ × M => F q.1 q.2) := F.continuous continuous_fst continuous_snd
  have hic : ContinuousAt (fun q : E × ℝ => e.symm q.1) (e p, 0) :=
    hi.continuousAt.comp_of_eq
      (show ContinuousAt (Prod.fst : E × ℝ → E) (e p, 0) from continuousAt_fst) rfl
  have hC : ContinuousAt C (e p, 0) := hFC.continuousAt.comp (continuousAt_snd.prodMk hic)
  have hHC : ContinuousAt H (e p, 0) := by
    have heC : ContinuousAt e (C (e p, 0)) := by rw [hC0]; exact he.continuousAt
    exact heC.comp hC
  have htarget : ∀ᶠ q : E × ℝ in 𝓝 (e p, 0), q.1 ∈ e.target :=
    continuousAt_fst (e.open_target.mem_nhds hz)
  have hstay : ∀ᶠ q : E × ℝ in 𝓝 (e p, 0), C q ∈ e.source := by
    apply hC
    rw [hC0]
    exact e.open_source.mem_nhds hp
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp (htarget.and hstay)
  have hrect (z : E) (hz' : z ∈ Metric.ball (e p) δ) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
    z ∈ e.target ∧ C (z, t) ∈ e.source := by
    apply hδsub (y := (z, t))
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hz', by simpa only [dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht⟩
  have hinit (z : E) (hz' : z ∈ Metric.ball (e p) δ) : H (z, 0) = z := by
    change e (F 0 (e.symm z)) = z
    rw [F.map_zero_apply]
    exact e.right_inv' (hrect z hz' 0 ⟨neg_lt_zero.mpr hδ, hδ⟩).1
  have hODE (z : E) (hz' : z ∈ Metric.ball (e p) δ) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
    HasDerivAt (fun s => H (z, s)) (MorseCancellation.coordinateField (V := V) e (H (z, t))) t :=
    MorseCancellation.hasDerivAt_coordinate_integralCurve e (hcurve (e.symm z)) (hrect z hz' t ht).2
  have hH : ContDiffAt ℝ ∞ H (e p, 0) :=
    contDiffAt_local_field_flow (MorseCancellation.contDiffOn_coordinateField hV e) e.open_target hz
      Metric.isOpen_ball (Metric.mem_ball_self hδ) hδ hHC hinit hODE
  let A (q : M × ℝ) : E × ℝ := (e q.1, q.2)
  have hA : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞ A (p, 0) := by
    apply (contMDiffAt_prod_module_iff A).mpr
    have hefst :
      ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (e ∘ (Prod.fst : M × ℝ → M)) (p, 0) :=
      he.comp (p, 0) contMDiffAt_fst
    exact ⟨hefst, contMDiffAt_snd⟩
  have hHA : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (H ∘ A) (p, 0) :=
    hH.contMDiffAt.comp (p, 0) hA
  have hHA0 : (H ∘ A) (p, 0) = e p := congrArg e hC0
  have hi' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm ((H ∘ A) (p, 0)) := by
    rw [hHA0]
    exact hi
  apply (hi'.comp (p, 0) hHA).congr_of_eventuallyEq
  have hstart : ∀ᶠ q : M × ℝ in 𝓝 (p, 0), q.1 ∈ e.source :=
    continuousAt_fst (e.open_source.mem_nhds hp)
  have hfinish : ∀ᶠ q : M × ℝ in 𝓝 (p, 0), F q.2 q.1 ∈ e.source := by
    have hc : Continuous (fun q : M × ℝ => F q.2 q.1) :=
      F.continuous continuous_snd continuous_fst
    apply hc.continuousAt
    simpa only [F.map_zero_apply] using e.open_source.mem_nhds hp
  filter_upwards [hstart, hfinish] with q hq hFq
  have heq : e.symm (e q.1) = q.1 := e.left_inv' hq
  change F q.2 q.1 = e.symm (e (F q.2 (e.symm (e q.1))))
  rw [heq]
  exact (e.left_inv' hFq).symm

theorem SmoothODE.exists_uniform_smalltime_contMDiff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] (F : Flow ℝ M) (n : ℕ)
    (hzero :
      ∀ p : M, ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) (p, 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ioo (-ε) ε, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F t) := by
  let U : Set (M × ℝ) :=
    {q | ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun r : M × ℝ => F r.2 r.1) q}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    exact (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hq
  let T : Set ℝ := {t | ∀ p ∈ (Set.univ : Set M), (t, p) ∈ Prod.swap ⁻¹' U}
  have hT : IsOpen T :=
    MorsePerturbation.isOpen_forall_mem_compact isCompact_univ (hU.preimage continuous_swap)
  have h0 : (0 : ℝ) ∈ T := fun p _ => hzero p
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0)
  refine ⟨ε, hε, ?_⟩
  intro t ht p
  have htT : t ∈ T :=
    hεsub (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht)
  have hj : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) (p, t) :=
    htT p (Set.mem_univ p)
  have hι : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) n (fun x : M => (x, t)) p :=
    contMDiffAt_id.prodMk contMDiffAt_const
  have hh := hj.comp p hι
  exact hh

theorem SmoothODE.contMDiff_flow_time_of_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] (F : Flow ℝ M) (n : ℕ)
    (hzero :
      ∀ p : M, ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) (p, 0))
    (t : ℝ) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F t) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_uniform_smalltime_contMDiff F n hzero
  let S : Set ℝ := {s | ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F s)}
  have hstep {s u : ℝ} (hs : s ∈ S) (hu : Dist.dist u s < ε) : u ∈ S := by
    have hus : u - s ∈ Set.Ioo (-ε) ε := abs_lt.mp (by simpa only [Real.dist_eq] using hu)
    have hc := (hsmall (u - s) hus).comp hs
    have heq : (fun x => F (u - s) (F s x)) = F u := by
      funext x
      rw [← F.map_add, sub_add_cancel]
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F u)
    rw [← heq]
    exact hc
  have hS : IsOpen S :=
    isOpen_iff_mem_nhds.mpr fun s hs =>
      Filter.mem_of_superset (Metric.ball_mem_nhds s hε) (fun u hu => hstep hs hu)
  have hSc : IsOpen Sᶜ :=
    isOpen_iff_mem_nhds.mpr fun s hs =>
      Filter.mem_of_superset (Metric.ball_mem_nhds s hε)
        (fun u hu h =>
          hs
            (hstep h
              (by
                change Dist.dist u s < ε at hu
                rwa [dist_comm])))
  have h0 : (0 : ℝ) ∈ S := by
    have heq : F 0 = id := funext F.map_zero_apply
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F 0)
    rw [heq]
    exact contMDiff_id
  have hSuniv : S = Set.univ :=
    (show IsClopen S from ⟨isOpen_compl_iff.mp hSc, hS⟩).eq_univ ⟨0, h0⟩
  have ht : t ∈ S := by rw [hSuniv]; exact Set.mem_univ t
  exact ht

theorem SmoothODE.contMDiff_joint_flow_of_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] (F : Flow ℝ M) (n : ℕ)
    (hzero :
      ∀ p : M, ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) (p, 0)) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) := by
  intro q
  let A (r : M × ℝ) := (F q.2 r.1, r.2 - q.2)
  have hA : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) n A q :=
    ((contMDiff_flow_time_of_zero F n hzero q.2).contMDiffAt.comp q contMDiffAt_fst).prodMk
      (contMDiffAt_snd.sub contMDiffAt_const)
  have hG : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun r : M × ℝ => F r.2 r.1) (A q) := by
    simpa only [A, sub_self] using hzero (F q.2 q.1)
  have hc := hG.comp q hA
  have heq : ((fun r : M × ℝ => F r.2 r.1) ∘ A) = (fun r : M × ℝ => F r.2 r.1) := by
    funext r
    change F (r.2 - q.2) (F q.2 r.1) = F r.2 r.1
    rw [← F.map_add, sub_add_cancel]
  exact heq ▸ hc

theorem SmoothODE.contMDiff_native_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] [FiniteDimensional ℝ E] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun q : M × ℝ => F q.2 q.1) :=
  contMDiff_infty.mpr
    (fun n =>
      contMDiff_joint_flow_of_zero F n
        (fun p => contMDiffAt_infty.mp (contMDiffAt_native_flow_zero hV F hcurve p) n))

def SmoothODE.nativeFlowTimeDiffeomorph {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) (t : ℝ) : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M
    where
  toFun := F t
  invFun := F (-t)
  left_inv x := by rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  right_inv x := by rw [← F.map_add, add_neg_cancel, F.map_zero_apply]
  contMDiff_toFun := hs t
  contMDiff_invFun := hs (-t)

theorem SmoothODE.mfderiv_flow_time_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) (x : M) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) x (V x) = V (F t x) := by
  have hd := ((hs t).mdifferentiableAt (by simp) (x := F 0 x)).hasMFDerivAt.comp 0 (hF x 0)
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (F t ∘ fun s => F s x) 0
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) (F 0 x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (V (F 0 x)))) at hd
  rw [F.map_zero_apply] at hd
  have hcomm : (F t ∘ fun s => F s x) = (fun s => F s (F t x)) := by
    funext s
    change F t (F s x) = F s (F t x)
    rw [← F.map_add, ← F.map_add, add_comm]
  rw [hcomm] at hd
  have hd' := hF (F t x) 0
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => F s (F t x)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (F 0 (F t x)))) at hd'
  rw [F.map_zero_apply] at hd'
  have hh := hd.mfderiv.symm.trans hd'.mfderiv
  have hv := congrArg (fun A : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (F t x) => A 1) hh
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) x ((1 : ℝ) • V x) = (1 : ℝ) • V (F t x) at hv
  simpa only [one_smul] using hv

def SmoothODE.nativeFlowTimeDiffeomorph_of_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) :
    M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M :=
  nativeFlowTimeDiffeomorph F
    (fun _ => (contMDiff_native_flow hV F hF).comp (contMDiff_id.prodMk contMDiff_const)) t

theorem SmoothODE.mpullback_flow_time {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) (x : M) :
    VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) V x = V x := by
  let D := nativeFlowTimeDiffeomorph F hs t
  let e := D.toPartialDiffeomorph
  have hdiff : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨e.mdifferentiableOn (by simp), e.symm.mdifferentiableOn (by simp)⟩
  have hi : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) x).IsInvertible :=
    ⟨hdiff.mfderiv (Set.mem_univ x), rfl⟩
  rw [VectorField.mpullback_apply, ← mfderiv_flow_time_field F hs hF t x]
  exact hi.inverse_apply_self (V x)

theorem SmoothODE.partialChartField_flow_shift {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (Φ : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, E) B M ∞) (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (W : B → B)
    (hmodel : ∀ x ∈ Φ.target, V x = FlowConstruction.partialChartField Φ.symm W x) (t : ℝ)
    {x : M} (hx : x ∈ (Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).target) :
    V x =
      FlowConstruction.partialChartField
        (Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).symm W x := by
  have hxΦ : F (-t) x ∈ Φ.target := hx.2
  have hdiff : Φ.symm.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, B) :=
    ⟨Φ.symm.mdifferentiableOn (by simp), Φ.mdifferentiableOn (by simp)⟩
  have hinv : (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, B) Φ.symm Set.univ (F (-t) x)).IsInvertible := by
    rw [mfderivWithin_univ]
    exact ⟨hdiff.mfderiv hxΦ, rfl⟩
  have hh :=
    VectorField.mpullbackWithin_comp_of_left (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, B)) (f :=
      F (-t)) (g := (Φ.symm : M → B)) (V := fun y => (NormedSpace.fromTangentSpace y).symm (W y))
      (s := Set.univ) (t := Set.univ)
      ((hs (-t)).mdifferentiableAt (by simp)).mdifferentiableWithinAt (Set.mapsTo_univ _ _)
      (uniqueMDiffWithinAt_univ 𝓘(ℝ, E)) hinv
  simp only [VectorField.mpullbackWithin_univ] at hh
  change
    V x =
      VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, B) (Φ.symm ∘ F (-t))
        (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) x
  rw [hh, VectorField.mpullback_apply]
  change
    V x =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F (-t)) x).inverse
        (FlowConstruction.partialChartField Φ.symm W (F (-t) x))
  rw [← hmodel _ hxΦ]
  exact (mpullback_flow_time F hs hF (-t) x).symm
end Mathoverflow1973
