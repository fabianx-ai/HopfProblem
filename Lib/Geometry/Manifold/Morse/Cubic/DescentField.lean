/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.Cubic.Model
public import Lib.Geometry.Manifold.Morse.Cubic.EndpointChart
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The descent field of the cubic model and its linearisation at the critical points

`MorseCancellation.cubicDescent σ t (x, y) = (-(x² + t), -σ i * y i)` is a gradient-like field for
the cubic model: the derivative of `cubic σ t` along it is negative away from the critical points
(`cubicDescent_strict`) and it vanishes at them (`cubicDescent_zero_of_critical`).  Its transport
to a manifold by a chart is `nativeCubicDescent`.

At the critical point `(e a, 0)` of `cubic σ (-a²)` the Möbius substitution
`u = (s - e a) / (a + e s)` (`endpointFieldCoordinate`, on `endpointFieldDomain a e`) conjugates the
axis component `a² - s²` of the field to the linear field `-2 e a u`
(`endpointFieldCoordinate_pushforward`); with the identity on the transverse coordinates
(`endpointFieldProduct`) it conjugates `cubicDescent` to the linear field `endpointLinearField`
(`fderiv_endpointFieldProduct_cubic`, `exists_endpoint_field_product_chart`).  Hence a field which
is `endpointLinearField` in a chart `Q` is the cubic descent field in the chart
`Q ∘ endpointFieldProduct` (`partialChartField_of_model_conjugacy`,
`exists_native_cubic_field_endpoint`).  Cf. Milnor, *Lectures on the h-cobordism theorem*, §5
(the gradient-like field of the cancellation model).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The cubic descent field. -/
def MorseCancellation.cubicDescent {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : Model m :=
  (-(p.1 ^ 2 + t), fun i => -σ i * p.2 i)

/-- The differential of the cubic descent. -/
theorem MorseCancellation.differential_cubicDescent {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    differential σ t p (cubicDescent σ t p) = -(p.1 ^ 2 + t) ^ 2 - 2 * ∑ i, (σ i * p.2 i) ^ 2 := by
  rw [differential_apply]
  simp only [cubicDescent]
  have hs : (∑ i, 2 * σ i * p.2 i * (-σ i * p.2 i)) = -2 * ∑ i, (σ i * p.2 i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- The cubic descent is strict off the critical point. -/
theorem MorseCancellation.cubicDescent_strict {m : ℕ} (σ : Fin m → ℝ) {t : ℝ} {p : Model m}
    (hp : fderiv ℝ (cubic σ t) p ≠ 0) : fderiv ℝ (cubic σ t) p (cubicDescent σ t p) < 0 := by
  rw [fderiv_cubic, differential_cubicDescent]
  by_contra hh
  have hsum : 0 ≤ ∑ i, (σ i * p.2 i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hx : p.1 ^ 2 + t = 0 := by nlinarith [sq_nonneg (p.1 ^ 2 + t)]
  have hz : (∑ i, (σ i * p.2 i) ^ 2) = 0 := by
    have hle := le_of_not_gt hh
    rw [hx] at hle
    linarith
  have hy (i : Fin m) : σ i * p.2 i = 0 := by
    have hi :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (σ i * p.2 i))).mp hz i
        (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  apply hp
  rw [fderiv_cubic]
  apply ContinuousLinearMap.ext
  intro v
  rw [differential_apply, hx]
  simp only [MulZeroClass.zero_mul, zero_add, zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  calc
    2 * σ i * p.2 i * v.2 i = 2 * (σ i * p.2 i) * v.2 i := by ring
    _ = 0 := by rw [hy, MulZeroClass.mul_zero, MulZeroClass.zero_mul]

/-- The cubic descent vanishes at the critical point. -/
theorem MorseCancellation.cubicDescent_zero_of_critical {m : ℕ} (σ : Fin m → ℝ) {t : ℝ} {p : Model m}
    (hp : fderiv ℝ (cubic σ t) p = 0) : cubicDescent σ t p = 0 := by
  rw [fderiv_cubic] at hp
  have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) hp
  have hx' : p.1 ^ 2 + t = 0 := by simpa [differential_apply] using hx
  apply Prod.ext
  · simpa only [cubicDescent, Prod.fst_zero, neg_eq_zero] using hx'
  · funext i
    have hi := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) hp
    have hi' : 2 * σ i * p.2 i = 0 := by simpa [differential_apply, Pi.single_apply] using hi
    change -σ i * p.2 i = 0
    nlinarith

/-- The native cubic descent field. -/
def MorseCancellation.nativeCubicDescent {m : ℕ} (σ : Fin m → ℝ) {B M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞) (t : ℝ) :
    (x : M) → TangentSpace 𝓘(ℝ, B) x :=
  FlowConstruction.partialChartField Φ.symm (cubicDescent σ t)

/-- The field coordinate at a cubic endpoint. -/
def MorseCancellation.endpointFieldCoordinate (a e s : ℝ) : ℝ :=
  (s - e * a) / (a + e * s)

/-- The domain of the endpoint field coordinate. -/
def MorseCancellation.endpointFieldDomain (a e : ℝ) : Set ℝ :=
  {s | 0 < a + e * s}

/-- The endpoint field domain is open. -/
theorem MorseCancellation.endpointFieldDomain_open (a e : ℝ) : IsOpen (endpointFieldDomain a e) := by
  apply isOpen_lt continuous_const
  fun_prop

/-- The endpoint lies in the field domain. -/
theorem MorseCancellation.endpointField_mem_domain {a : ℝ} (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1) :
    e * a ∈ endpointFieldDomain a e := by
  change 0 < a + e * (e * a)
  have h : e * (e * a) = a := by rw [← mul_assoc, ← pow_two, he, one_mul]
  rw [h]
  linarith

/-- The endpoint field coordinate at the center. -/
theorem MorseCancellation.endpointFieldCoordinate_center (a e : ℝ) :
    endpointFieldCoordinate a e (e * a) = 0 := by simp [endpointFieldCoordinate]

/-- The endpoint field coordinate is smooth. -/
theorem MorseCancellation.contDiffOn_endpointFieldCoordinate (a e : ℝ) :
    ContDiffOn ℝ ∞ (endpointFieldCoordinate a e) (endpointFieldDomain a e) := by
  intro s hs
  exact
    ((contDiffAt_id.sub contDiffAt_const).div
        (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
        (ne_of_gt hs)).contDiffWithinAt

/-- The endpoint field coordinate is differentiable. -/
theorem MorseCancellation.hasDerivAt_endpointFieldCoordinate (a : ℝ) {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) :
    HasDerivAt (endpointFieldCoordinate a e) (2 * a / (a + e * s) ^ 2) s := by
  have hd :=
    ((hasDerivAt_id s).sub_const (e * a)).div (((hasDerivAt_id s).const_mul e).const_add a)
      (ne_of_gt hs)
  convert! hd using 1
  congr 1
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

/-- The endpoint field coordinate computes the pushforward. -/
theorem MorseCancellation.endpointFieldCoordinate_pushforward (a : ℝ) {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) :
    deriv (endpointFieldCoordinate a e) s * (a ^ 2 - s ^ 2) =
      (-2 * e * a) * endpointFieldCoordinate a e s := by
  rw [(hasDerivAt_endpointFieldCoordinate a he hs).deriv]
  unfold endpointFieldCoordinate
  have hn : a + e * s ≠ 0 := ne_of_gt hs
  field_simp
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

/-- An endpoint field scalar chart exists. -/
theorem MorseCancellation.exists_endpoint_field_scalar_chart {a : ℝ} (ha : 0 < a) {e : ℝ}
    (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      e * a ∈ P.source ∧
        P.source ⊆ endpointFieldDomain a e ∧
          (P : ℝ → ℝ) = endpointFieldCoordinate a e ∧ P (e * a) = 0 := by
  have hm := endpointField_mem_domain ha he
  have hd := (hasDerivAt_endpointFieldCoordinate a he hm).hasFDerivAt
  have hn : 2 * a / (a + e * (e * a)) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) ha.ne') (pow_ne_zero _ (ne_of_gt hm))
  have hi : Function.Injective (fderiv ℝ (endpointFieldCoordinate a e) (e * a)) := by
    rw [hd.fderiv]
    intro x y hxy
    change x * (2 * a / (a + e * (e * a)) ^ 2) = y * (2 * a / (a + e * (e * a)) ^ 2) at hxy
    exact mul_right_cancel₀ hn hxy
  let A : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (endpointFieldCoordinate a e) (e * a)).toLinearMap
        hi).toContinuousLinearEquiv
  obtain ⟨P, hp, hsub, hP⟩ :=
    exists_partialDiffeomorph_of_contDiffOn (endpointFieldDomain_open a e) hm
      (contDiffOn_endpointFieldCoordinate a e) ⟨A, rfl⟩
  exact ⟨P, hp, hsub, hP, by rw [hP, endpointFieldCoordinate_center]⟩

/-- The linear field at a cubic endpoint. -/
def MorseCancellation.endpointLinearField {m : ℕ} (σ : Fin m → ℝ) (a e : ℝ) (p : Model m) : Model m :=
  ((-2 * e * a) * p.1, fun i => -σ i * p.2 i)

/-- The product field at a cubic endpoint. -/
def MorseCancellation.endpointFieldProduct {m : ℕ} (a e : ℝ) (p : Model m) : Model m :=
  (endpointFieldCoordinate a e p.1, p.2)

/-- The endpoint product field's derivative on the cubic. -/
theorem MorseCancellation.fderiv_endpointFieldProduct_cubic {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) {e : ℝ}
    (he : e ^ 2 = 1) {p : Model m} (hp : p.1 ∈ endpointFieldDomain a e) :
    fderiv ℝ (endpointFieldProduct a e) p (cubicDescent σ (-(a ^ 2)) p) =
      endpointLinearField σ a e (endpointFieldProduct a e p) := by
  have hd :=
    ((hasDerivAt_endpointFieldCoordinate a he hp).comp_hasFDerivAt p
          (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (endpointFieldProduct a e) _ p at hd
  rw [hd.fderiv]
  apply Prod.ext
  · change
      (2 * a / (a + e * p.1) ^ 2) * (-(p.1 ^ 2 + -(a ^ 2))) =
        (-2 * e * a) * endpointFieldCoordinate a e p.1
    have hh := endpointFieldCoordinate_pushforward a he hp
    rw [(hasDerivAt_endpointFieldCoordinate a he hp).deriv] at hh
    convert! hh using 1; ring
  · rfl

/-- An endpoint field product chart exists. -/
theorem MorseCancellation.exists_endpoint_field_product_chart {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) (Model m) (Model m) ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧
        P (e * a, 0) = 0 ∧
          (P : Model m → Model m) = endpointFieldProduct a e ∧
            ∀ p ∈ P.source,
              fderiv ℝ P p (cubicDescent σ (-(a ^ 2)) p) = endpointLinearField σ a e (P p) := by
  obtain ⟨Q, hq, hsub, hQ, hzero⟩ := exists_endpoint_field_scalar_chart ha he
  let P := scalarProductChart (V := Fin m → ℝ) Q
  have hP : (P : Model m → Model m) = endpointFieldProduct a e := by
    funext p
    exact Prod.ext (congrFun hQ p.1) rfl
  refine ⟨P, ⟨hq, Set.mem_univ _⟩, ?_, hP, ?_⟩
  · rw [hP]
    simp [endpointFieldProduct, endpointFieldCoordinate_center]
  · intro p hp
    rw [hP]
    exact fderiv_endpointFieldProduct_cubic σ a he (hsub hp.1)

/-- A model-conjugate partial chart field. -/
theorem MorseCancellation.partialChartField_of_model_conjugacy {D F E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (P : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, F) D F ∞) (Q : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) F M ∞)
    (W : D → D) (U : F → F) (hpush : ∀ p ∈ P.source, fderiv ℝ P p (W p) = U (P p)) {x : M}
    (hx : x ∈ (P.trans Q).target) :
    FlowConstruction.partialChartField (P.trans Q).symm W x =
      FlowConstruction.partialChartField Q.symm U x := by
  have hxQ : x ∈ Q.target := hx.1
  have hxP : Q.symm x ∈ P.target := hx.2
  have hdiff : P.symm.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, D) :=
    ⟨P.symm.mdifferentiableOn (by simp), P.mdifferentiableOn (by simp)⟩
  have hinv : (mfderivWithin 𝓘(ℝ, F) 𝓘(ℝ, D) P.symm Set.univ (Q.symm x)).IsInvertible := by
    rw [mfderivWithin_univ]
    exact ⟨hdiff.mfderiv hxP, rfl⟩
  have hh :=
    VectorField.mpullbackWithin_comp_of_left (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, D)) (f :=
      (Q.symm : M → F)) (g := (P.symm : F → D)) (V := fun y =>
      (NormedSpace.fromTangentSpace y).symm (W y)) (s := Set.univ) (t := Set.univ)
      (Q.symm.mdifferentiableAt (by simp) hxQ).mdifferentiableWithinAt (Set.mapsTo_univ _ _)
      (uniqueMDiffWithinAt_univ 𝓘(ℝ, E)) hinv
  simp only [VectorField.mpullbackWithin_univ] at hh
  have hv :
    VectorField.mpullback 𝓘(ℝ, F) 𝓘(ℝ, D) P.symm
        (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) (Q.symm x) =
      (NormedSpace.fromTangentSpace (Q.symm x)).symm (U (Q.symm x)) := by
    change FlowConstruction.partialChartField P.symm W (Q.symm x) = _
    rw [FlowConstruction.partialChartField_eq_mfderiv_symm P.symm W hxP]
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ P (P.symm (Q.symm x)) (W (P.symm (Q.symm x))) = U (Q.symm x)
    have hp : P.symm (Q.symm x) ∈ P.source := P.map_target' hxP
    rw [hpush (P.symm (Q.symm x)) hp]
    exact congrArg U (P.right_inv' hxP)
  change
    VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, D) (P.symm ∘ Q.symm)
        (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) x =
      _
  rw [hh, VectorField.mpullback_apply, hv]
  rfl

/-- A native cubic field endpoint chart exists. -/
theorem MorseCancellation.exists_native_cubic_field_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1)
    (Q : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (h0 : (0 : Model m) ∈ Q.source)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel :
      ∀ x ∈ Q.target,
        V x = FlowConstruction.partialChartField Q.symm (endpointLinearField σ a e) x) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e * a, 0) = Q 0 ∧
          Φ.target ⊆ Q.target ∧
            (∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) ∧
              (Φ : Model m → M) = Q ∘ endpointFieldProduct a e := by
  obtain ⟨P, hp, hcenter, hP, hpush⟩ := exists_endpoint_field_product_chart σ ha he
  let Φ := P.trans Q
  have hsource : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source := by
    change (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧ P (e * a, 0) ∈ Q.source
    exact ⟨hp, hcenter.symm ▸ h0⟩
  refine ⟨Φ, hsource, ?_, fun _ hx => hx.1, ?_, ?_⟩
  · change Q (P (e * a, 0)) = Q 0
    rw [hcenter]
  · intro x hx
    rw [hmodel x hx.1]
    exact
      (partialChartField_of_model_conjugacy P Q (cubicDescent σ (-(a ^ 2)))
          (endpointLinearField σ a e) hpush hx).symm
  · change Q ∘ P = Q ∘ endpointFieldProduct a e
    rw [hP]
