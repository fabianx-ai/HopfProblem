/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Replacing a function inside a chart

For a partial diffeomorphism `Φ : E → M` and functions `f : M → ℝ`, `b : E → ℝ`,
`LocalFunctionReplacement.replace Φ f b` is `b ∘ Φ⁻¹` on the image of `Φ` and `f` elsewhere.  If
`f ∘ Φ = b₀` on the source of `Φ` and `b₁ = b₀` outside a compact subset `K` of the source, then
`replace Φ f b₁` agrees with `f` outside `Φ '' K` (`replace_eq_off_support`), is smooth when `f` and
`b₁` are (`contMDiff_replace`), and its critical points inside the chart are the images of those of
`b₁` (`replace_critical_iff`).  This is the standard way to alter a function on a coordinate
neighbourhood, as in Milnor, *Lectures on the h-cobordism theorem*, §2 and §4.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- `replace Φ f b y` is `b (Φ.symm y)` for `y ∈ Φ.target` and `f y` otherwise: the function `f`
with `b`, read in the chart `Φ`, substituted on the image of `Φ`. -/
def LocalFunctionReplacement.replace {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) (y : M) : ℝ := by
  classical exact if y ∈ Φ.target then b (Φ.symm y) else f y

/-- For `y ∈ Φ.target`, `replace Φ f b y = b (Φ.symm y)`. -/
theorem LocalFunctionReplacement.replace_of_mem {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∈ Φ.target) :
    replace Φ f b y = b (Φ.symm y) := by simp [replace, hy]

/-- For `y ∉ Φ.target`, `replace Φ f b y = f y`. -/
theorem LocalFunctionReplacement.replace_of_notMem {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∉ Φ.target) :
    replace Φ f b y = f y := by simp [replace, hy]

/-- For `x ∈ Φ.source`, `replace Φ f b (Φ x) = b x`. -/
theorem LocalFunctionReplacement.replace_chart {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {x : E} (hx : x ∈ Φ.source) :
    replace Φ f b (Φ x) = b x := by
  rw [replace_of_mem Φ f b (Φ.map_source' hx)]
  exact congrArg b (Φ.left_inv' hx)

/-- Near a point `y ∈ Φ.target` the function `replace Φ f b` coincides with `b ∘ Φ.symm`. -/
theorem LocalFunctionReplacement.replace_germ_chart {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∈ Φ.target) :
    replace Φ f b =ᶠ[𝓝 y] b ∘ Φ.symm := by
  filter_upwards [Φ.open_target.mem_nhds hy] with z hz
  exact replace_of_mem Φ f b hz

/-- If `f (Φ x) = b x` for all `x ∈ Φ.source`, then `replace Φ f b = f`. -/
theorem LocalFunctionReplacement.replace_self {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ} {b : E → ℝ}
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b x) : replace Φ f b = f := by
  funext y
  by_cases hy : y ∈ Φ.target
  · rw [replace_of_mem Φ f b hy]
    exact (hmodel (Φ.symm y) (Φ.map_target' hy)).symm.trans (congrArg f (Φ.right_inv' hy))
  · exact replace_of_notMem Φ f b hy

/-- If `f (Φ x) = b₀ x` on `Φ.source` and `b₁ = b₀` outside `K`, then `replace Φ f b₁ y = f y` for
every `y ∉ Φ '' K`. -/
theorem LocalFunctionReplacement.replace_eq_off_support {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x) (hfix : ∀ x ∉ K, b₁ x = b₀ x) {y : M}
    (hy : y ∉ Φ '' K) : replace Φ f b₁ y = f y := by
  by_cases hyt : y ∈ Φ.target
  · have hx : Φ.symm y ∉ K := fun h => hy ⟨Φ.symm y, h, Φ.right_inv' hyt⟩
    rw [replace_of_mem Φ f b₁ hyt, hfix _ hx]
    exact (hmodel (Φ.symm y) (Φ.map_target' hyt)).symm.trans (congrArg f (Φ.right_inv' hyt))
  · exact replace_of_notMem Φ f b₁ hyt

/-- Let `M` be Hausdorff, `K ⊆ Φ.source` compact, `f (Φ x) = b₀ x` on `Φ.source` and `b₁ = b₀`
outside `K`. Then `replace Φ f b₁` coincides with `f` near every `y ∉ Φ '' K`. -/
theorem LocalFunctionReplacement.replace_germ_off_support {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) [T2Space M] {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x) {y : M} (hy : y ∉ Φ '' K) : replace Φ f b₁ =ᶠ[𝓝 y] f := by
  have hc : IsClosed (Φ '' K) :=
    (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
  filter_upwards [hc.isOpen_compl.mem_nhds hy] with z hz
  exact replace_eq_off_support Φ hmodel hfix hz

/-- Let `M` be Hausdorff, `f : M → ℝ` and `b₁ : E → ℝ` smooth, `K ⊆ Φ.source` compact, `f (Φ x) = b₀
x` on `Φ.source` and `b₁ = b₀` outside `K`. Then `replace Φ f b₁` is smooth. -/
theorem LocalFunctionReplacement.contMDiff_replace {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) [T2Space M] {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hb : ContDiff ℝ ∞ b₁) (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x) (hfix : ∀ x ∉ K, b₁ x = b₀ x) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (replace Φ f b₁) := by
  intro y
  by_cases hy : y ∈ Φ.target
  · have hs :=
      hb.contMDiff.contMDiffAt.comp y
        (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy))
    exact hs.congr_of_eventuallyEq (replace_germ_chart Φ f b₁ hy)
  · have hnot : y ∉ Φ '' K := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hKΦ hx))
    exact
      hf.contMDiffAt.congr_of_eventuallyEq (replace_germ_off_support Φ hK hKΦ hmodel hfix hnot)

/-- For smooth `b` and `y ∈ Φ.target`, the derivative of `replace Φ f b` vanishes at `y` iff the
derivative of `b` vanishes at `Φ.symm y`. -/
theorem LocalFunctionReplacement.replace_critical_iff {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) {b : E → ℝ} (hb : ContDiff ℝ ∞ b) {y : M}
    (hy : y ∈ Φ.target) : mfderiv I 𝓘(ℝ, ℝ) (replace Φ f b) y = 0 ↔ fderiv ℝ b (Φ.symm y) = 0 := by
  have hΦ : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ Φ.symm y := ⟨Φ.symm, hy, fun _ _ => rfl⟩
  have hsurj := (hΦ.mfderivToContinuousLinearEquiv (by simp)).surjective
  rw [(replace_germ_chart Φ f b hy).mfderiv_eq,
    mfderiv_comp y (hb.contMDiff.mdifferentiableAt (by simp))
      (Φ.symm.mdifferentiableAt (by simp) hy),
    mfderiv_eq_fderiv]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := hsurj v
    have he := congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L w) h
    change fderiv ℝ b (Φ.symm y) (mfderiv I 𝓘(ℝ, E) Φ.symm y w) = 0 at he
    change mfderiv I 𝓘(ℝ, E) Φ.symm y w = v at hw
    simpa only [hw, zero_apply] using he
  · intro h
    rw [h]
    rfl
