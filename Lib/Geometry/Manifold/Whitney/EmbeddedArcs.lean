/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.FrameField

/-!
# Embedded arcs and clean strip pairs

The geometric preparation of the Whitney trick: normal coordinates along an embedded sphere,
embedded and tubular arcs joining two intersection points of two sheets while avoiding a finite
set, clean corner charts at the intersection points, clean ambient strip charts along an embedded
arc, strips matching prescribed corner germs, clean strip pairs, and the filling of the resulting
bigon boundary by an embedded Whitney disc with a tubular neighbourhood.

The arcs, the strips and the filled bigon are the data from which the Whitney trick builds the
isotopy cancelling a pair of intersection points of opposite sign; the dimension hypotheses are the
usual general-position ones (ambient dimension at least five, sheets of complementary dimension).

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6 (the Whitney lemma and the
  construction of the Whitney disc).

## Tags

Morse theory, Whitney trick, handle cancellation
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- The radial frame of the unit sphere at `x`: the map sending `(s, w)` to `s x` plus the image of
`w` in the tangent space of the sphere at `x`, for a chosen chart coefficient `C`. -/
def SphereNormalCoordinates.radialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (x : V)).coprod ((inclusionDerivative x).comp C)

/-- Composing the normal frame with an invertible change of chart coefficients gives the radial
frame. -/
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

/-- The radial frame is bijective when its chart coefficient is invertible: the radial direction and
the tangent space span the ambient space. -/
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

/-- The normal Jacobian and the determinant of the chart coefficient multiply to the determinant of
the radial frame read in the coordinates `j`. -/
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

/-- The radial frame at a chart point, assembled from the radial direction `c z` and the derivative
of the chart inverse at `z`. -/
def SphereNormalCoordinates.chartRadialFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞) (z : N) :
    (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (c z : V)).coprod (fderiv ℝ (fun w => (c w : V)) z)

/-- On the source of the chart, the chart radial frame is the radial frame with chart coefficient
the differential of the chart. -/
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

/-- The chart radial frame depends smoothly on the chart parameter. -/
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

/-- The chart radial frame is bijective at every point of the source of the chart. -/
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

/-- Along a continuous path inside a chart, the determinants of the chart radial frame at the two
endpoints have the same sign, so their product is positive. -/
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

/-- For a path inside one chart, the two endpoint normal Jacobians have opposite signs exactly when
the two endpoint determinants of the chart coefficients do: the chart radial frame contributes a
factor of constant sign. -/
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

/-- For an embedded sphere meeting a sheet cleanly in a chart, the two endpoint normal Jacobians of
the sphere have opposite signs exactly when the two endpoint determinants of a defining map of
the sheet, read along the centre line of the chart, do. -/
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
/-- For a Morse surgery in a six-manifold with a two-dimensional index, the two belt intersection
signs of an embedded two-sphere are opposite exactly when the two corner determinants of the
Whitney bigon between the sphere and the belt sphere are. -/
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

/-- The contraction of the plane towards the interior point `(0, h / 2)` of the bigon by the factor
`r`. -/
def WhitneyPairModel.innerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - r) • (0, h / 2) + r • p

/-- The contraction with factor one is the identity. -/
theorem WhitneyPairModel.innerBigonMap_one (h : ℝ) (p : ℝ × ℝ) : innerBigonMap h 1 p = p := by
  simp only [innerBigonMap, sub_self, zero_smul, one_smul, zero_add]

/-- The contraction depends smoothly on the factor and the point. -/
theorem WhitneyPairModel.contDiff_innerBigonMap (h : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => innerBigonMap h z.1 z.2) := by
  unfold innerBigonMap
  fun_prop

/-- For `r ≠ 0`, the contraction is a diffeomorphism of the plane. -/
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

/-- The differential of the contraction is bijective at every point, for `r ≠ 0`. -/
theorem WhitneyPairModel.bijective_mfderiv_innerBigonMap (h r : ℝ) (hr : r ≠ 0)
    (p : ℝ × ℝ) : Function.Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (innerBigonMap h r) p) :=
  PartialChart.bijective_mfderiv (innerBigonDiffeomorph h r hr).toPartialDiffeomorph
    (Set.mem_univ p)

/-- For `0 < r < 1`, the contraction carries the whole bigon into its interior. -/
theorem WhitneyPairModel.innerBigonMap_mem_interior {h r : ℝ} (hh : 0 < h)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    innerBigonMap h r p ∈ interior (bigon h) :=
  (convex_bigon hh.le).combo_interior_self_mem_interior (bigon_center_mem_interior hh) hp
    (sub_pos.mpr hr.2) hr.1.le (by ring)

/-- The collar of the bigon cut off by the contraction: the part of the bigon not covered by the
contracted interior. -/
def WhitneyPairModel.innerBigonCollar (h r : ℝ) : Set (ℝ × ℝ) :=
  bigon h \ innerBigonMap h r '' interior (bigon h)

/-- The inverse of the contraction `innerBigonMap h r`. -/
def WhitneyPairModel.inverseInnerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  r⁻¹ • (p - (1 - r) • (0, h / 2))

/-- The inverse contraction with factor one is the identity. -/
theorem WhitneyPairModel.inverseInnerBigonMap_one (h : ℝ) (p : ℝ × ℝ) :
    inverseInnerBigonMap h 1 p = p := by
  simp only [inverseInnerBigonMap, inv_one, sub_self, zero_smul, sub_zero, one_smul]

/-- The inverse contraction is a right inverse of the contraction, for `r ≠ 0`. -/
theorem WhitneyPairModel.inner_inverseInnerBigonMap (h r : ℝ) (hr : r ≠ 0) (p : ℝ × ℝ) :
    innerBigonMap h r (inverseInnerBigonMap h r p) = p :=
  (innerBigonDiffeomorph h r hr).apply_symm_apply p

/-- The inverse contraction is continuous in the factor and the point at factor one. -/
theorem WhitneyPairModel.continuousAt_inverseInnerBigonMap (h : ℝ) (p : ℝ × ℝ) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ) => inverseInnerBigonMap h z.1 z.2) (1, p) := by
  unfold inverseInnerBigonMap
  fun_prop (disch := norm_num)

/-- For `0 < r`, the collar cut off by the contraction is compact. -/
theorem WhitneyPairModel.isCompact_innerBigonCollar {h r : ℝ} (hh : 0 < h) (hr : r ≠ 0) :
    IsCompact (innerBigonCollar h r) := by
  have ho : IsOpen (innerBigonMap h r '' interior (bigon h)) :=
    (innerBigonDiffeomorph h r hr).toHomeomorph.isOpenMap _ isOpen_interior
  exact (isCompact_bigon hh).inter_right ho.isClosed_compl

/-- For `0 < r < 1`, a point of the bigon is carried into the collar exactly when it lies on the
boundary of the bigon. -/
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

/-- Any open neighbourhood of the boundary of the bigon contains the collar of some contraction,
which moreover pushes the boundary into the neighbourhood and into the interior of the bigon. -/
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

/-- A clean bigon boundary admits a contraction whose collar lies in the domain and whose composite
with the boundary map is, on a neighbourhood of the boundary of the bigon, a smooth injective
immersion into the interior avoiding the two sheets. -/
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

/-- If the complement of the two sheets has trivial fundamental group in the relevant range, the
contracted boundary map extends to a globally smooth map of the plane into that complement,
still injective and immersive near the boundary of the bigon. -/
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

/-- Under a dimension hypothesis making general position available, the extension of the previous
statement can be taken to be an embedding of the whole bigon, avoiding the first sheet. -/
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

/-- Refinement of the previous statement whose embedded extension additionally avoids the image of
the collar on the interior of the bigon, which is what makes the boundary and the filling glue. -/
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

/-- Gluing: an embedded filling of the bigon which agrees with the contracted boundary near the
boundary and avoids the collar can be repaired into an embedded filling that agrees with the
boundary map itself near the boundary and avoids both sheets in the interior. -/
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

/-- A clean bigon boundary in a manifold of dimension at least five, with a sheet of small enough
dimension and a simply connected complement, bounds an embedded Whitney disc: the bigon is
filled by an embedding avoiding the two sheets in its interior. -/
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

/-- In the same situation, the filled bigon carries a tubular neighbourhood: a tubular bigon of
codimension `n` exists. -/
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

/-- General-position perturbation in a chart: a smooth map can be moved by a compactly supported
weighted perturbation, keeping a prescribed open property, so that it becomes immersive along a
given family of base points. -/
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

/-- For a weighted chart perturbation, a tangent vector killed by the derivative of the weight is
killed by the derivative of the perturbed map exactly when it is killed by the derivative of the
original one. -/
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

/-- If a weight vanishes at `x` together with its derivative in the direction `v`, then so does any
smooth multiple of it. -/
theorem ChartMapPerturbation.fderiv_cutoff_mul_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ψ ρ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hρ : ContDiff ℝ ∞ ρ) {x v : E}
    (hx : ρ x = 0) (hv : fderiv ℝ ρ x v = 0) : fderiv ℝ (fun y => ψ y * ρ y) x v = 0 := by
  rw [fderiv_fun_mul (hψ.differentiable (by simp) x) (hρ.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul, hx, hv, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, add_zero]

/-- The perturbation with a cut-off weight preserves the condition that the differential of the map
and the derivative of the weight have no common kernel on the zero set of the weight. -/
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

/-- One step of the repair of the immersion property along the zero set of a weight: the map can be
perturbed inside one patch, relative to that zero set, to become immersive on the given compact
set together with the plateau of the patch. -/
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

/-- Iterating the repair step over a finite set of patches. -/
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

/-- The compact case of the repair: a smooth map can be made immersive at every point of the image
of a compact parameter family, by a homotopy relative to the zero set of the weight. -/
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

/-- The function `t (1 - t)`, which vanishes exactly at the two endpoints of the unit interval. -/
def CurveImmersion.endpointFunction (t : ℝ) : ℝ :=
  t * (1 - t)

/-- The endpoint function is smooth. -/
theorem CurveImmersion.contDiff_endpointFunction : ContDiff ℝ ∞ endpointFunction := by
  unfold endpointFunction
  fun_prop

/-- The endpoint function vanishes exactly at `0` and `1`. -/
theorem CurveImmersion.endpointFunction_eq_zero_iff (t : ℝ) :
    endpointFunction t = 0 ↔ t = 0 ∨ t = 1 := by
  rw [endpointFunction, mul_eq_zero, sub_eq_zero]
  exact or_congr Iff.rfl eq_comm

/-- The derivative of the endpoint function is `v ↦ v (1 - 2 t)`. -/
theorem CurveImmersion.fderiv_endpointFunction (t v : ℝ) :
    fderiv ℝ endpointFunction t v = v * (1 - 2 * t) := by
  have hd : HasDerivAt endpointFunction (1 * (1 - t) + t * (0 - 1)) t :=
    (hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  have heq : 1 * (1 - t) + t * (0 - 1) = 1 - 2 * t := by ring
  rw [heq] at hd
  rw [hd.hasFDerivAt.fderiv]
  rfl

/-- At a zero of the endpoint function the derivative is injective, since `1 - 2t = ±1` there. -/
theorem CurveImmersion.injective_endpointFunction_derivative {t : ℝ}
    (ht : endpointFunction t = 0) {v : ℝ} (hv : fderiv ℝ endpointFunction t v = 0) : v = 0 := by
  rw [fderiv_endpointFunction] at hv
  rcases (endpointFunction_eq_zero_iff t).mp ht with rfl | rfl
  · simpa using hv
  · norm_num at hv
    exact hv

/-- A smooth curve in a manifold of dimension at least two can be homotoped, relative to the two
endpoints, to a curve whose differential is injective at both endpoints. -/
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

/-- In a manifold of dimension at least two, every point of an open set is the starting point of a
nonconstant embedded arc contained in that open set. -/
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

/-- Two distinct points joined by a path in a manifold of dimension at least two are joined by an
embedded smooth arc whose interior avoids a prescribed finite set (general position for arcs). -/
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

/-- The connecting arc of the previous statement can be taken with a tubular neighbourhood of the
prescribed codimension whose image avoids the finite set except at the two endpoints. -/
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

/-- At a transverse intersection point of two tubular arcs there is a clean corner chart: a local
parametrisation of a neighbourhood of the intersection in which the two arcs are the two
coordinate axes. -/
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

/-- Packaged form of the previous statement: the clean corner patch at a transverse intersection of
two tubular arcs is nonempty. -/
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

/-- Along an embedded arc in an embedded sheet there is an ambient strip chart which is clean for
the sheet: the sheet is the zero set of the normal coordinate, and the centre line is the arc. -/
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

/-- At a transverse intersection, the differential of the normal coordinate of the sheet restricted
to the second sheet is bijective when the two sheets have complementary dimensions. -/
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

/-- Version of the previous statement for the second sheet read through a parametrisation. -/
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

/-- The line through `u`: the linear map `t ↦ t • u`. -/
def NativeParametrization.line {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (u : D) : ℝ →L[ℝ] D :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight u

/-- The line through `u` takes the value `t • u` at `t`. -/
theorem NativeParametrization.line_apply {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (u : D) (t : ℝ) : line u t = t • u :=
  rfl

/-- If a two-parameter map agrees near the origin along the vertical axis with a curve in the
direction `v`, then its vertical derivative at the origin is the derivative of that curve in the
direction `v`. -/
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

/-- A nonvanishing vertical derivative at a point persists on a neighbourhood. -/
theorem TransverseCoordinates.eventually_vertical_derivative_ne_zero {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {H : (ℝ × ℝ) → B} {p : ℝ × ℝ}
    (hH : ContDiffAt ℝ ∞ H p) (hn : fderiv ℝ H p (0, 1) ≠ 0) :
    ∀ᶠ q in 𝓝 p, fderiv ℝ H q (0, 1) ≠ 0 := by
  have hd : ContinuousAt (fderiv ℝ H) p := hH.continuousAt_fderiv (by simp)
  have hv : ContinuousAt (fun q => fderiv ℝ H q (0, 1)) p := hd.clm_apply continuousAt_const
  exact hv.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hn)

/-- At a clean corner whose vertical axis is a transverse parametrised arc, the vertical derivative
of the normal coordinate of the sheet is nonzero at the corner and stays nonzero nearby. -/
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

/-- Two germs of strips at the two ends, with the prescribed centre line and normal derivative, are
interpolated by a globally smooth strip having that centre line and that normal derivative
everywhere. -/
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

/-- A strip with nowhere-vanishing normal derivative along the centre line is an embedding on a thin
rectangle around it, is clean (the sheet is the zero set of the normal coordinate) and immersive
there. -/
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

/-- The normal derivative of a smooth strip is smooth. -/
theorem StripCoordinates.contDiff_normalDerivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (normalDerivative F) :=
  ((hF.snd.fderiv_right (by simp)).clm_apply contDiff_const).comp
    (contDiff_id.prodMk contDiff_const)

/-- The normal derivative at a parameter depends only on the germ of the strip at the corresponding
centre point. -/
theorem StripCoordinates.normalDerivative_congr_germ {A B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {F G : (ℝ × ℝ) → Space A B} {t : ℝ} (heq : F =ᶠ[𝓝 (t, 0)] G) :
    normalDerivative F t = normalDerivative G t := by
  have heq' : (fun p => (F p).2) =ᶠ[𝓝 (t, (0 : ℝ))] (fun p => (G p).2) := by
    filter_upwards [heq] with p hp
    exact congrArg Prod.snd hp
  have hd : fderiv ℝ (fun p => (F p).2) (t, 0) = fderiv ℝ (fun p => (G p).2) (t, 0) :=
    heq'.fderiv_eq
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] B => L (0, 1)) hd

/-- Combination of the previous two statements: two local germs with nonzero normal derivative at
the ends are joined by a globally smooth strip which keeps both germs and is a clean embedding
of a thin rectangle. -/
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

/-- Native form of the strip interpolation: inside an ambient chart clean for a sheet, two germs at
the two ends are joined by a clean embedded strip along the centre line with nowhere-vanishing
normal derivative. -/
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

/-- If a strip meets a closed set exactly at its two endpoint fibres near the ends and nowhere in
the open middle of the centre line, then it meets it exactly in those two fibres on a thin
rectangle. -/
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

/-- The main strip-existence statement: along an embedded arc in a sheet, transverse to a second
sheet at both endpoints with prescribed corner parametrisations, there is a clean embedded strip
having the given corner germs, meeting the first sheet exactly along the centre line and the
second sheet exactly in the two end fibres, and carrying strip normal data. -/
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

/-- Packaged form of the strip-existence statement: the clean strip patch along the arc, with its
strip normal data, exists between two given clean corner patches. -/
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

/-- Two compact sets whose coincidence pairs all lie in a given open set have open neighbourhoods
whose coincidence pairs still lie in that open set. -/
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

/-- If two maps agree near two points with the composites of a locally injective map with two
continuous maps, then on small neighbourhoods their coincidences are exactly the coincidences of
those two maps. -/
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

/-- Two clean strips along two arcs meeting only at the two shared corners have thin rectangular
neighbourhoods on which the only coincidences are the two corner identifications. -/
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

/-- The restriction of a clean strip patch to a thinner rectangle inside its domain. -/
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

/-- The main arc-pair statement in codimension two: two transverse intersection points of two
embedded sheets, joined by paths, are joined by embedded arcs, one in each sheet, meeting only
at the two intersection points, and carrying clean corner patches, clean strip patches and strip
normal data on both sides. -/
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
/-- In a six-manifold with a Morse surgery of index two, a clean bigon boundary between an embedded
two-sphere and the belt sphere bounds a tubular bigon of codimension three. -/
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
/-- In the same situation, the two arcs of the bigon boundary carry a clean strip pair with strip
normal data of ranks one and two, which is the input of the rank-three Whitney model. -/
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

/-- The inclusion `X × U → X × V` induced by a map of fibres. -/
def FiberRestriction.embed {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : U →L[ℝ] V) : (X × U) →L[ℝ] (X × V) :=
  (ContinuousLinearMap.id ℝ X).prodMap i

/-- The projection `X × V → X × U` induced by a map of fibres. -/
def FiberRestriction.project {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : V →L[ℝ] U) : (X × V) →L[ℝ] (X × U) :=
  (ContinuousLinearMap.id ℝ X).prodMap r

/-- Projecting after embedding is the identity when the fibre maps compose to the identity. -/
theorem FiberRestriction.project_embed {X U V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i)
    (z : X × U) : project r (embed i z) = z :=
  Prod.ext rfl (hi z.2)

/-- Embedding after projecting is the identity on points whose fibre coordinate is in the image of
the fibre inclusion. -/
theorem FiberRestriction.embed_project_of_normal {X U V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i) {z : X × V}
    {w : X × U} (hz : z.2 = i w.2) : embed i (project r z) = z := by
  apply Prod.ext
  · rfl
  · change i (r z.2) = z.2
    rw [hz, hi]

/-- The restriction to a subfibre of a diffeomorphism of `X × V` that preserves the fibre
coordinate. -/
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

/-- A slice of a Lipschitz function of two variables is Lipschitz with the same constant. -/
theorem SmallPerturbation.lipschitzWith_slice {E : Type*} [NormedAddCommGroup E]
    {β : ℝ × E → ℝ} {k : ℝ≥0} (hβ : LipschitzWith k β) (t : ℝ) :
    LipschitzWith k (fun x : E => β (t, x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    Dist.dist (β (t, x)) (β (t, y)) ≤ (k : ℝ) * Dist.dist (t, x) (t, y) := hβ.dist_le_mul _ _
    _ = (k : ℝ) * Dist.dist x y := by
      rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ Dist.dist x y)]

/-- For a compactly supported smooth weight there is a radius below which every translation by a
weighted vector is a diffeomorphism, uniformly in the time parameter, and is the identity off
the support of the weight. -/
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

/-- The composite of the first `n` members of a family of time-dependent maps. -/
def SmallPerturbation.composeFamily {E : Type*} (B : ℕ → ℝ × E → E) : ℕ → ℝ × E → E
  | 0, p => p.2
  | n + 1, p => B n (p.1, composeFamily B n p)

/-- A composite of smooth members of the family is smooth. -/
theorem SmallPerturbation.contDiff_composeFamily {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : ℕ → ℝ × E → E} (hB : ∀ i, ContDiff ℝ ∞ (B i)) (n : ℕ) :
    ContDiff ℝ ∞ (composeFamily B n) := by
  induction n with
  | zero => exact contDiff_snd
  | succ n ih => exact (hB n).comp (contDiff_fst.prodMk ih)

/-- If every member of the family is the identity at time zero, so is every composite. -/
theorem SmallPerturbation.composeFamily_zero {E : Type*} {B : ℕ → ℝ × E → E}
    (hB : ∀ i x, B i (0, x) = x) (n : ℕ) (x : E) : composeFamily B n (0, x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hB n _).trans ih

/-- If every member of the family fixes the complement of a set, so does every composite. -/
theorem SmallPerturbation.composeFamily_fixed {E : Type*} {B : ℕ → ℝ × E → E} {C : Set E}
    (hB : ∀ i t x, x ∉ C → B i (t, x) = x) (n : ℕ) (t : ℝ) {x : E} (hx : x ∉ C) :
    composeFamily B n (t, x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change B n (t, composeFamily B n (t, x)) = x
    rw [ih]
    exact hB n t x hx

/-- A quantity preserved by every member of the family is preserved by every composite. -/
theorem SmallPerturbation.composeFamily_preserves {E : Type*} {F : Type*}
    {B : ℕ → ℝ × E → E} {f : E → F} (hB : ∀ i t x, f (B i (t, x)) = f x) (n : ℕ) (t : ℝ) (x : E) :
    f (composeFamily B n (t, x)) = f x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hB n t _).trans ih

/-- If every member of the family is a diffeomorphism at every time, so is every composite. -/
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

end
