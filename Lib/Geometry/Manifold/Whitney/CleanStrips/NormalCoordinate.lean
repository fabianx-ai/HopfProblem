/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Morse.Existence

/-!
# The normal coordinate of a product chart

For a chart `Φ : D × B → M` of a manifold, `TransverseCoordinates.normalCoordinate Φ` is the
second coordinate `Prod.snd ∘ Φ⁻¹`, a submersion on the target of `Φ`. When the chart is clean for
a sheet `F` (a point of the chart lies on `F` exactly when its `B`-coordinate vanishes), the
normal coordinate vanishes along `F` and its derivative kills the tangent space of `F`; along the
zero section `x ↦ Φ (x, 0)` its kernel is exactly that tangent space
(`TransverseCoordinates.ker_normalDerivative_eq_range_zero_section`). This is the local normal
form of a submanifold as the zero set of a submersion (cf. Guillemin–Pollack,
*Differential topology*, §1.4).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace

noncomputable section

/-- The second coordinate of a chart `Φ : D × B ≃ M`, viewed as a function on the target of `Φ`; it
is the normal coordinate that cuts out the first sheet.
-/
def TransverseCoordinates.normalCoordinate {D B E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) : M → B :=
  Prod.snd ∘ Φ.symm

/-- The normal coordinate of a chart is smooth on the target of the chart. -/
theorem TransverseCoordinates.contMDiffOn_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, B) ∞ (normalCoordinate Φ) Φ.target := by
  have hs : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
  exact hs.comp_contMDiffOn Φ.contMDiffOn_invFun

/-- The derivative of the normal coordinate is the second projection composed with the derivative of
the inverse chart.
-/
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

/-- The derivative of the normal coordinate is surjective at every point of the target of the chart,
so the normal coordinate is a submersion there.
-/
theorem TransverseCoordinates.surjective_mfderiv_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {p : M} (hp : p ∈ Φ.target) :
    Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) p) := by
  rw [mfderiv_normalCoordinate Φ hp]
  exact
    (show Function.Surjective (ContinuousLinearMap.snd ℝ D B) from fun w => ⟨(0, w), rfl⟩).comp
      (PartialChart.bijective_mfderiv Φ.symm hp).2

/-- If the chart is clean for a sheet `F`, then the normal coordinate vanishes identically near
every parameter whose image lies in the chart's target: the sheet is contained in the zero set
of the normal coordinate.
-/
theorem TransverseCoordinates.normalCoordinate_sheet_eventually_zero {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {N : Type*} [TopologicalSpace N]
    {F : N → M} (hF : Continuous F) (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) {x : N}
    (hx : F x ∈ Φ.target) : (normalCoordinate Φ ∘ F) =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hF.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)] with y hy
  have hq : Φ.invFun (F y) ∈ Φ.source := Φ.map_target' hy
  exact (hclean _ hq).mp ⟨y, (Φ.right_inv' hy).symm⟩

/-- For a clean chart, the derivative of the normal coordinate annihilates the tangent space of the
sheet.
-/
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

/-- The derivative of the zero section `x ↦ Φ (x, 0)` of a chart is the derivative of the chart
restricted to the first factor.
-/
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

/-- Along the zero section the kernel of the derivative of the normal coordinate is exactly the
tangent space of the sheet.
-/
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

end
