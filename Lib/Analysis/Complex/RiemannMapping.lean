/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.RiemannMapping.Steps
import Lib.Analysis.Complex.SchwarzReflection
import Lib.Analysis.Complex.Mobius
import Lib.Geometry.Manifold.Instances.RiemannSphere

/-!
# The Riemann mapping theorem

Every simply connected proper domain `U ⊂ ℂ` is biholomorphic to the unit disc, and the
biholomorphism can be normalized at a point with derivative chosen; the boundary-extension
companions (`RiemannBoundary.*`) transport the map to the closed disc when the boundary is
an arc:

* `RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero` — the headline: a
  biholomorphism from `U` onto the unit disc, injective with nonvanishing derivative,
  vanishing at the chosen point (Ahlfors Ch. 6 §1; Rudin 14.8).

The proof is the Koebe derivative-maximization over a normal family; the computational steps
live in `Lib/Analysis/Complex/RiemannMapping/Steps.lean`. The boundary-extension lemmas
(`RiemannBoundary.*`, Carathéodory-style extension to the closed disc along boundary arcs)
are interleaved-dependent with the mapping core and share this file (lane-A
MayerVietoris-style merge, recorded in Lib/reports/A.md). `TriangleRiemannNormalization.*`
(normalized triangle parameters) round out the file.

## Outline of the proof

1. *Bounded injections form a normal family*; the supremum of derivatives at the base point
   is attained (`_root_.Complex.*` steps: locally uniform limits of injective holomorphic
   maps are injective or constant — `eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn`).
2. *The Koebe square trick:* if the image misses a disc, rescaling by a square root
   increases the derivative at the base point — contradiction with maximality.
3. *Surjectivity:* a non-surjective injection yields the missing-disc rescaling, so the
   extremal map is onto (`exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero`).
4. *Boundary extension:* along analytic boundary arcs the map extends to the closed disc
   (`RiemannBoundary.*`).

## Main definitions and results

* `RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero` : the Riemann mapping
  theorem with derivative normalization.
* `RiemannBoundary.*` : Carathéodory-style boundary extension along arcs.
* `TriangleRiemannNormalization.*` : normalized triangle parameters.

## References

* [Lars Ahlfors, *Complex Analysis*][ahlfors], Ch. 6 §1
* [Walter Rudin, *Real and Complex Analysis*][rudin87], Theorem 14.8

## Tags

Riemann mapping theorem, normal families, Koebe maximization, boundary extension
-/



open Set Function Filter Manifold Topology

open scoped ComplexConjugate ContDiff Interval NNReal UniformConvergence Uniformity

universe u v

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-- The disc coordinate: the affine identification of the triangle with the unit disc underlying the normalization of the Riemann mapping target (Ahlfors, Complex Analysis, Ch. 6). -/
def TriangleRiemannNormalization.discCoordinate {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (x : K) : ℂ :=
  e x

/-! ### Triangle normalization to the disc -/

/-- The disc coordinate is injective. -/
theorem TriangleRiemannNormalization.discCoordinate_injective {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) : Function.Injective (discCoordinate e) := by
  intro x y he
  exact e.injective (Subtype.ext he)

/-- Distinct disc coordinates stay distinct. -/
theorem TriangleRiemannNormalization.discCoordinate_ne {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) {x y : K} (hxy : x ≠ y) :
    discCoordinate e x ≠ discCoordinate e y := fun he => hxy (discCoordinate_injective e he)

/-- The disc coordinate has norm at most one. -/
theorem TriangleRiemannNormalization.discCoordinate_norm_le {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (x : K) : ‖discCoordinate e x‖ ≤ 1 := by
  simpa only [discCoordinate, Metric.mem_closedBall, dist_zero_right] using (e x).property

/-- The puncture map: the homeomorphism from the punctured triangle to the punctured disc obtained by removing the basepoint direction. -/
def TriangleRiemannNormalization.punctureMap {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) (x : {x : K | x ≠ pinf}) :
    RiemannSphere.closedDiscWithoutPole (discCoordinate e pinf) :=
  ⟨discCoordinate e x, discCoordinate_norm_le e x, discCoordinate_ne e x.property⟩

/-- The puncture map is an embedding. -/
theorem TriangleRiemannNormalization.punctureMap_isEmbedding {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    Topology.IsEmbedding (punctureMap e pinf) := by
  have hs :
    Topology.IsEmbedding
      (Subtype.val : RiemannSphere.closedDiscWithoutPole (discCoordinate e pinf) → ℂ) :=
    Topology.IsEmbedding.subtypeVal
  have he : Topology.IsEmbedding (fun x : {x : K | x ≠ pinf} => e (x : K)) :=
    e.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hv : Topology.IsEmbedding (Subtype.val : Metric.closedBall (0 : ℂ) 1 → ℂ) :=
    Topology.IsEmbedding.subtypeVal
  have hcomp : Topology.IsEmbedding (fun x : {x : K | x ≠ pinf} => (e (x : K) : ℂ)) := hv.comp he
  exact hs.of_comp_iff.mp hcomp

/-- The puncture map is surjective. -/
theorem TriangleRiemannNormalization.punctureMap_surjective {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    Function.Surjective (punctureMap e pinf) := by
  intro z
  let y : Metric.closedBall (0 : ℂ) 1 :=
    ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using z.property.1⟩
  have hx : e.symm y ≠ pinf := by
    intro he
    apply z.property.2
    have h := congrArg (discCoordinate e) he
    simpa only [discCoordinate, Homeomorph.apply_symm_apply] using h
  refine ⟨⟨e.symm y, hx⟩, ?_⟩
  apply Subtype.ext
  exact congrArg (fun w : Metric.closedBall (0 : ℂ) 1 => (w : ℂ)) (e.apply_symm_apply y)

/-- The punctured triangle is homeomorphic to its normalization. -/
def TriangleRiemannNormalization.punctureHomeomorph {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    {x : K | x ≠ pinf} ≃ₜ RiemannSphere.closedDiscWithoutPole (discCoordinate e pinf) :=
  (punctureMap_isEmbedding e pinf).toHomeomorphOfSurjective (punctureMap_surjective e pinf)

/-- The normalization homeomorphism: the final affine correction placing the mapping target in Riemann-mapping normal form (Ahlfors, Complex Analysis, Ch. 6, the normalization step). -/
def TriangleRiemannNormalization.normalizationHomeomorph {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1) (h0inf : p0 ≠ pinf)
    (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1) (h1 : ‖discCoordinate e p1‖ = 1)
    (hinf : ‖discCoordinate e pinf‖ = 1) :
    {x : K | x ≠ pinf} ≃ₜ
      RiemannSphere.closedOrientedHalfPlane
        (RiemannSphere.MobiusCircle.orientation (discCoordinate e p0) (discCoordinate e p1)
          (discCoordinate e pinf)) :=
  (punctureHomeomorph e pinf).trans
    (RiemannSphere.closedDiscHalfPlaneHomeomorph (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf)

/-- The normalization homeomorphism computes the disc coordinate. -/
@[simp]
theorem TriangleRiemannNormalization.normalizationHomeomorph_apply {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1)
    (x : {x : K | x ≠ pinf}) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf x : ℂ) =
      RiemannSphere.MobiusCircle.crossRatio (discCoordinate e p0) (discCoordinate e p1)
        (discCoordinate e pinf) (discCoordinate e x) := by
  exact
    RiemannSphere.closedDiscHalfPlaneHomeomorph_apply (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf
      (punctureHomeomorph e pinf x)

/-- The normalization sends the first vertex to `0`. -/
@[simp]
theorem TriangleRiemannNormalization.normalizationHomeomorph_first {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf ⟨p0, h0inf⟩ : ℂ) = 0 := by
  rw [normalizationHomeomorph_apply]
  exact RiemannSphere.MobiusCircle.crossRatio_at_zero _ _ _

/-- The normalization sends the second vertex to `1`. -/
@[simp]
theorem TriangleRiemannNormalization.normalizationHomeomorph_second {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf ⟨p1, h1inf⟩ : ℂ) = 1 := by
  rw [normalizationHomeomorph_apply]
  exact
    RiemannSphere.MobiusCircle.crossRatio_at_one (discCoordinate_ne e h01.symm)
      (discCoordinate_ne e h1inf)

/-- The strict half-plane corresponds to the interior. -/
theorem TriangleRiemannNormalization.normalizationHomeomorph_strict_iff {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1)
    (x : {x : K | x ≠ pinf}) :
    0 <
        RiemannSphere.MobiusCircle.orientation (discCoordinate e p0) (discCoordinate e p1)
            (discCoordinate e pinf) *
          (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf x : ℂ).im ↔
      ‖discCoordinate e x‖ < 1 := by
  exact
    RiemannSphere.closedDiscHalfPlaneHomeomorph_strict_iff (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf
      (punctureHomeomorph e pinf x)

/-- The normalization orientation factor is nonzero. -/
theorem TriangleRiemannNormalization.normalization_orientation_ne_zero {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1) :
    RiemannSphere.MobiusCircle.orientation (discCoordinate e p0) (discCoordinate e p1)
        (discCoordinate e pinf) ≠
      0 :=
  RiemannSphere.MobiusCircle.orientation_ne_zero h0 h1 hinf (discCoordinate_ne e h01.symm)
    (discCoordinate_ne e h1inf) (discCoordinate_ne e h0inf)

/-- Preimages of closed balls under the disc map are compact: properness of the Riemann mapping on the interior (Ahlfors, Complex Analysis, Ch. 6). -/
theorem RiemannMapping.isCompact_discHomeomorph_preimage_closedBall {U : Set ℂ}
    (e : U ≃ₜ Metric.ball (0 : ℂ) 1) {r : ℝ} (hr : r < 1) :
    IsCompact
      ((Subtype.val : U → ℂ) ''
        (e ⁻¹' ((Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ) ⁻¹' Metric.closedBall 0 r))) := by
  apply IsCompact.image _ continuous_subtype_val
  apply e.isCompact_preimage.mpr
  apply
    Topology.IsInducing.subtypeVal.isCompact_preimage' (ProperSpace.isCompact_closedBall _ _) ?_
  simpa only [Subtype.range_coe] using Metric.closedBall_subset_ball hr

/-- The disc map escapes to the boundary: points outside the source domain have images of norm tending to 1 along the map (boundary behaviour, Ahlfors, Complex Analysis, Ch. 6). -/
theorem RiemannMapping.tendsto_norm_discHomeomorph_of_notMem {U : Set ℂ}
    (e : U ≃ₜ Metric.ball (0 : ℂ) 1) {α : Type*} {l : Filter α} {z : α → U} {a : ℂ} (ha : a ∉ U)
    (hz : Filter.Tendsto (fun i => (z i : ℂ)) l (𝓝 a)) :
    Filter.Tendsto (fun i => ‖(e (z i) : ℂ)‖) l (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let K : Set ℂ :=
      (Subtype.val : U → ℂ) ''
        (e ⁻¹' ((Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ) ⁻¹' Metric.closedBall 0 r))
    have hK : IsCompact K := isCompact_discHomeomorph_preimage_closedBall e hr
    have haK : a ∉ K := by
      rintro ⟨w, _, hwa⟩
      exact ha (hwa ▸ w.property)
    have hevent : ∀ᶠ i in l, (z i : ℂ) ∉ K :=
      hz.eventually (hK.isClosed.isOpen_compl.mem_nhds haK)
    filter_upwards [hevent] with i hi
    apply lt_of_not_ge
    intro hle
    apply hi
    refine ⟨z i, ?_, rfl⟩
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hle
  · intro r hr
    apply Filter.Eventually.of_forall
    intro i
    have hi : ‖(e (z i) : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using (e (z i)).property
    exact hi.trans hr

/-! ### The logarithmic half-strip chart -/

/-- The disc-coordinate norm tends to `1` along cocompact filters. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_of_cocompact {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {α : Type*}
    {l : Filter α} {z : α → ℂ} (hz : Filter.Tendsto z l (Filter.cocompact ℂ))
    (hmem : ∀ᶠ i in l, z i ∈ D) : Filter.Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let K : Set ℂ :=
      (Subtype.val : D → ℂ) ''
        (e ⁻¹' ((Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ) ⁻¹' Metric.closedBall 0 r))
    have hK : IsCompact K := RiemannMapping.isCompact_discHomeomorph_preimage_closedBall e hr
    have hesc : ∀ᶠ i in l, z i ∉ K := hz.eventually hK.compl_mem_cocompact
    filter_upwards [hesc, hmem] with i hi him
    apply lt_of_not_ge
    intro hle
    apply hi
    refine ⟨⟨z i, him⟩, ?_, rfl⟩
    have hh := he ⟨z i, him⟩
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, ← hh] using hle
  · intro r hr
    filter_upwards [hmem] with i hi
    have hh := he ⟨z i, hi⟩
    have hb : ‖f (z i)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, ← hh] using (e ⟨z i, hi⟩).property
    exact hb.trans hr

/-- The disc norm tends to `1` as the norm tends to infinity. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_of_norm_atTop {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {α : Type*}
    {l : Filter α} {z : α → ℂ} (hz : Filter.Tendsto (fun i => ‖z i‖) l Filter.atTop)
    (hmem : ∀ᶠ i in l, z i ∈ D) : Filter.Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) := by
  apply tendsto_norm_discHomeomorph_of_cocompact e he _ hmem
  simpa only [Metric.cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hz

/-- The disc norm tends to `1` as the imaginary part tends to infinity. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_of_im_atTop {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {α : Type*}
    {l : Filter α} {z : α → ℂ} (hz : Filter.Tendsto (fun i => (z i).im) l Filter.atTop)
    (hmem : ∀ᶠ i in l, z i ∈ D) : Filter.Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) :=
  tendsto_norm_discHomeomorph_of_norm_atTop e he
    (Filter.tendsto_atTop_mono (fun i => Complex.im_le_norm (z i)) hz) hmem

/-- The logarithm identifying a half-strip with a half-plane: the standard biholomorphism used to normalize boundary strips (Ahlfors, Complex Analysis, Ch. 6; Rudin, Real and Complex Analysis, 14.8-adjacent steps). -/
def RiemannBoundary.logHalfStrip (a c : ℝ) (q : ℂ) : ℂ :=
  a - Complex.I * c * Complex.log q

/-- The real part of the logarithmic half-strip coordinate. -/
@[simp]
theorem RiemannBoundary.logHalfStrip_re (a c : ℝ) (q : ℂ) :
    (logHalfStrip a c q).re = a + c * q.arg := by
  simp [logHalfStrip, Complex.mul_re, Complex.mul_im, Complex.log_im]

/-- The imaginary part of the logarithmic half-strip coordinate. -/
@[simp]
theorem RiemannBoundary.logHalfStrip_im (a c : ℝ) (q : ℂ) :
    (logHalfStrip a c q).im = -c * Real.log ‖q‖ := by
  simp [logHalfStrip, Complex.mul_re, Complex.mul_im, Complex.log_re]

/-- The half-strip imaginary part tends to infinity. -/
theorem RiemannBoundary.tendsto_logHalfStrip_im_atTop (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun q : ℂ => (logHalfStrip a c q).im) (𝓝[≠] 0) Filter.atTop := by
  simp only [logHalfStrip_im]
  exact
    (Filter.tendsto_const_mul_atTop_of_neg (neg_neg_of_pos hc)).mpr
      (Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero)

/-- The disc norm along the half-strip tends to `1`. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_logHalfStrip {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (a : ℝ) {c : ℝ}
    (hc : 0 < c) (hmem : ∀ᶠ q in 𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ), logHalfStrip a c q ∈ D) :
    Filter.Tendsto (fun q => ‖f (logHalfStrip a c q)‖) (𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ)) (𝓝 1) := by
  apply tendsto_norm_discHomeomorph_of_im_atTop e he _ hmem
  apply (tendsto_logHalfStrip_im_atTop a hc).mono_left
  apply nhdsWithin_mono
  intro z hz
  change 0 < z.im at hz
  change z ≠ 0
  intro heq
  rw [heq, Complex.zero_im] at hz
  exact (lt_irrefl 0) hz

/-- The half-strip coordinate on the one-point domain. -/
def RiemannBoundary.onePointLogHalfStrip (a c : ℝ) (q : ℂ) : OnePoint ℂ :=
  if q = 0 then (OnePoint.infty) else (logHalfStrip a c q : OnePoint ℂ)

/-- The half-strip coordinate at the marked point. -/
@[simp]
theorem RiemannBoundary.onePointLogHalfStrip_zero (a c : ℝ) :
    onePointLogHalfStrip a c 0 = (OnePoint.infty) := by simp [onePointLogHalfStrip]

/-- The half-strip coordinate off the marked point. -/
theorem RiemannBoundary.onePointLogHalfStrip_of_ne_zero (a c : ℝ) {q : ℂ} (hq : q ≠ 0) :
    onePointLogHalfStrip a c q = (logHalfStrip a c q : OnePoint ℂ) := by
  simp [onePointLogHalfStrip, hq]

/-- The half-strip coordinate tends to infinity cocompactly. -/
theorem RiemannBoundary.tendsto_logHalfStrip_cocompact (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (logHalfStrip a c) (𝓝[≠] 0) (Filter.cocompact ℂ) := by
  have hn : Filter.Tendsto (fun q : ℂ => ‖logHalfStrip a c q‖) (𝓝[≠] 0) Filter.atTop :=
    Filter.tendsto_atTop_mono (fun q => Complex.im_le_norm (logHalfStrip a c q))
      (tendsto_logHalfStrip_im_atTop a hc)
  simpa only [Metric.cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hn

/-- The coerced half-strip coordinate tends to `∞`. -/
theorem RiemannBoundary.tendsto_coe_logHalfStrip_infty (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun q : ℂ => (logHalfStrip a c q : OnePoint ℂ)) (𝓝[≠] 0)
      (𝓝 (OnePoint.infty)) := by
  have hcoe : Filter.Tendsto ((↑) : ℂ → OnePoint ℂ) (Filter.cocompact ℂ) (𝓝 (OnePoint.infty)) := by
    simpa only [Filter.coclosedCompact_eq_cocompact] using (OnePoint.tendsto_coe_infty (X := ℂ))
  exact hcoe.comp (tendsto_logHalfStrip_cocompact a hc)

/-- The one-point half-strip coordinate is continuous at zero. -/
theorem RiemannBoundary.continuousAt_onePointLogHalfStrip_zero (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ContinuousAt (onePointLogHalfStrip a c) 0 := by
  rw [continuousAt_iff_punctured_nhds, onePointLogHalfStrip_zero]
  apply (tendsto_coe_logHalfStrip_infty a hc).congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (onePointLogHalfStrip_of_ne_zero a c hq).symm

/-- The one-point domain of the boundary chart. -/
def RiemannBoundary.onePointDomain (D : Set ℂ) : Set (OnePoint ℂ) :=
  ((↑) : ℂ → OnePoint ℂ) '' D

/-- A finite point lies in the one-point domain. -/
@[simp]
theorem RiemannBoundary.coe_mem_onePointDomain {D : Set ℂ} {z : ℂ} :
    (z : OnePoint ℂ) ∈ onePointDomain D ↔ z ∈ D := by exact OnePoint.coe_injective.mem_set_image

/-- `∞` is not in the one-point domain. -/
@[simp]
theorem RiemannBoundary.infty_notMem_onePointDomain (D : Set ℂ) :
    (OnePoint.infty) ∉ onePointDomain D :=
  OnePoint.infty_notMem_image_coe

/-- The one-point domain is open. -/
theorem RiemannBoundary.isOpen_onePointDomain {D : Set ℂ} (hD : IsOpen D) :
    IsOpen (onePointDomain D) :=
  OnePoint.isOpen_image_coe.mpr hD

/-- The one-point domain is homeomorphic to its model. -/
def RiemannBoundary.onePointDomainHomeomorph (D : Set ℂ) : D ≃ₜ onePointDomain D :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage D

/-- The one-point homeomorphism computes the coordinate. -/
@[simp]
theorem RiemannBoundary.onePointDomainHomeomorph_apply_coe (D : Set ℂ) (z : D) :
    (onePointDomainHomeomorph D z : OnePoint ℂ) = (z : ℂ) :=
  rfl

/-- The one-point domain is homeomorphic to the disc. -/
def RiemannBoundary.onePointDomainDiscHomeomorph {D : Set ℂ} (e : D ≃ₜ Metric.ball (0 : ℂ) 1) :
    onePointDomain D ≃ₜ Metric.ball (0 : ℂ) 1 :=
  (onePointDomainHomeomorph D).symm.trans e

/-- The disc homeomorphism computes the disc coordinate. -/
@[simp]
theorem RiemannBoundary.onePointDomainDiscHomeomorph_apply {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (z : D) :
    onePointDomainDiscHomeomorph e (onePointDomainHomeomorph D z) = e z := by
  simp [onePointDomainDiscHomeomorph]

/-- The disc homeomorphism computes on a representative. -/
theorem RiemannBoundary.onePointDomainDiscHomeomorph_representative {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (b : ℂ)
    (z : onePointDomain D) : (z : OnePoint ℂ).elim b f = (onePointDomainDiscHomeomorph e z : ℂ) :=
  by
  obtain ⟨w, rfl⟩ := (onePointDomainHomeomorph D).surjective z
  simpa only [onePointDomainHomeomorph_apply_coe, OnePoint.elim_some,
    onePointDomainDiscHomeomorph_apply] using he w

/-- `∞` is a frontier point of the cocompact one-point domain. -/
theorem RiemannBoundary.infty_mem_frontier_onePointDomain_of_cocompact {D : Set ℂ} {α : Type*}
    {l : Filter α} [Filter.NeBot l] {z : α → ℂ} (hz : Filter.Tendsto z l (Filter.cocompact ℂ))
    (hmem : ∀ᶠ i in l, z i ∈ D) : ((OnePoint.infty) : OnePoint ℂ) ∈ frontier (onePointDomain D) :=
  by
  have hcoe : Filter.Tendsto ((↑) : ℂ → OnePoint ℂ) (Filter.cocompact ℂ) (𝓝 (OnePoint.infty)) := by
    simpa only [Filter.coclosedCompact_eq_cocompact] using (OnePoint.tendsto_coe_infty (X := ℂ))
  have hcl : ((OnePoint.infty) : OnePoint ℂ) ∈ closure (onePointDomain D) := by
    apply isClosed_closure.mem_of_tendsto (hcoe.comp hz)
    filter_upwards [hmem] with i hi
    exact subset_closure (coe_mem_onePointDomain.mpr hi)
  exact ⟨hcl, fun hi => infty_notMem_onePointDomain D (interior_subset hi)⟩

/-! ### Normal families -/

/-- A bounded holomorphic family is uniformly equicontinuous on a thickening. -/
theorem RiemannMapping.uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : ι → E → F} {s U : Set E} {r : ℝ} (hr₀ : 0 < r)
    (hU : Metric.thickening r s ⊆ U) (hfd : ∀ i, DifferentiableOn ℂ (f i) U)
    (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) : UniformEquicontinuousOn f s := by
  have hsU : s ⊆ U := (Metric.self_subset_thickening hr₀ _).trans hU
  rw [(Metric.uniformity_basis_dist.inf_principal _).uniformEquicontinuousOn_iff
      Metric.uniformity_basis_dist_le]
  intro ε hε
  rcases hf with ⟨C, hC⟩
  rcases exists_pos_mul_lt hε (2 * C / r) with ⟨δ, hδ₀, hδ⟩
  use Min.min δ r, by positivity
  simp only [Set.mem_ofPred, Set.mem_inter_iff, Set.prodMk_mem_set_prod_eq]
  rintro x y ⟨hdist, hx, hy⟩ i
  rw [lt_min_iff] at hdist
  rw [Metric.thickening_eq_biUnion_ball, Set.iUnion₂_subset_iff] at hU
  calc
    Dist.dist (f i x) (f i y) ≤ (2 * C / r) * Dist.dist x y := by
      apply Complex.dist_le_div_mul_dist_of_mapsTo_ball
      · exact (hfd i).mono (hU _ hy)
      · intro z hz
        rw [Metric.mem_closedBall, two_mul]
        exact
          dist_le_norm_add_norm _ _ |>.trans <|
            add_le_add (hC _ _ <| hU y hy hz) (hC _ _ <| hsU hy)
      · exact hdist.2
    _ ≤ _ := by
      grw [hdist.1]
      · exact hδ.le
      · have := (norm_nonneg _).trans (hC i x (hsU hx))
        positivity

/-- A bounded holomorphic family is equicontinuous at a point. -/
theorem RiemannMapping.equicontinuousAt_of_forall_norm_le {ι E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ι → E → F} {U : Set E} {x : E}
    (hU : U ∈ 𝓝 x) (hfd : ∀ i, DifferentiableOn ℂ (f i) U) (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) :
    EquicontinuousAt f x := by
  rcases Metric.nhds_basis_ball.mem_iff.mp hU with ⟨r, hr₀, hr⟩
  have : Metric.thickening (r / 2) (Metric.ball x (r / 2)) ⊆ U := by
    grw [Metric.thickening_ball]
    rwa [add_halves]
  have :=
    uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le (by positivity) this hfd
        hf |>.equicontinuousOn
      x (by simpa)
  rwa [EquicontinuousWithinAt,
    nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds _ (by positivity))] at this

/-- An exhaustion of the domain by compact subsets. -/
def RiemannMapping.compactSubsets (U : Set ℂ) : Set (Set ℂ) :=
  {K | K ⊆ U ∧ IsCompact K}

/-- The function space of holomorphic maps to the disc. -/
abbrev RiemannMapping.FunctionSpace (U : Set ℂ) :=
  ℂ →ᵤ[compactSubsets U] ℂ

/-- Evaluation at a point of the domain. -/
def RiemannMapping.evaluation {U : Set ℂ} (f : FunctionSpace U) : ℂ → ℂ :=
  UniformOnFun.toFun (compactSubsets U) f

/-- The function-space uniformity is countably generated. -/
theorem RiemannMapping.uniformity_isCountablyGenerated {U : Set ℂ} (hUo : IsOpen U) :
    (𝓤 (FunctionSpace U)).IsCountablyGenerated := by
  have := hUo.locallyCompactSpace
  have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  let φ : CompactExhaustion U := Inhabited.default
  apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n => (↑) '' φ n)
  · intro n
    exact ⟨Set.image_val_subset, (φ.isCompact n).image continuous_subtype_val⟩
  · exact Set.monotone_image.comp φ.subset
  · rintro K ⟨hKU, hKc⟩
    lift K to Set U using hKU
    rw [← Subtype.isCompact_iff] at hKc
    exact (φ.exists_superset_of_isCompact hKc).imp fun n hn => by gcongr

/-- Locally uniform convergence implies pointwise evaluation convergence. -/
theorem RiemannMapping.evaluation_tendstoLocallyUniformlyOn {U : Set ℂ} (hUo : IsOpen U)
    {f : FunctionSpace U} {s : Set (FunctionSpace U)} :
    TendstoLocallyUniformlyOn evaluation (evaluation f) (𝓝[s] f) U := by
  have h : Filter.Tendsto id (𝓝[s] f) (𝓝 f) := Filter.tendsto_id'.mpr nhdsWithin_le_nhds
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo]
  intro K hKU hK
  exact (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp h) K ⟨hKU, hK⟩

/-- A bounded holomorphic family has compact closure. -/
theorem RiemannMapping.isCompact_closure_of_bounded_holomorphic {U : Set ℂ} (hUo : IsOpen U)
    {s : Set (FunctionSpace U)} (hsd : ∀ f ∈ s, DifferentiableOn ℂ (evaluation f) U)
    (hsb : ∃ C : ℝ, ∀ f ∈ s, ∀ z ∈ U, ‖evaluation f z‖ ≤ C) : IsCompact (closure s) := by
  obtain ⟨C, hC⟩ := hsb
  apply
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (𝔖 := compactSubsets U) (fun K hK => hK.2)
      (F := evaluation) .id
  · rintro K ⟨hKU, _⟩ z hz
    exact
      (equicontinuousAt_of_forall_norm_le (hUo.mem_nhds (hKU hz))
            (fun f : s => hsd f.val f.property)
            ⟨C, fun f z hz => hC f.val f.property z hz⟩).equicontinuousWithinAt
        K
  · intro K hK x hx
    exact
      ⟨Metric.closedBall 0 C, ProperSpace.isCompact_closedBall _ _, fun f hf => by
        simpa only [mem_closedBall_zero_iff] using hC f hf x (hK.1 hx)⟩

/-- The normalized class of injective disc maps with prescribed derivative data. -/
def RiemannMapping.normalizedClass (U : Set ℂ) (x₀ : ℂ) : Set (FunctionSpace U) :=
  {f |
    Set.MapsTo (evaluation f) U (Metric.ball 0 1) ∧
      Set.InjOn (evaluation f) U ∧
        DifferentiableOn ℂ (evaluation f) U ∧
          (∀ z ∈ U, deriv (evaluation f) z ≠ 0) ∧ evaluation f x₀ = 0}

/-- The normalized class has compact closure. -/
theorem RiemannMapping.normalizedClass_compact_closure {U : Set ℂ} (hUo : IsOpen U) (x₀ : ℂ) :
    IsCompact (closure (normalizedClass U x₀)) := by
  apply isCompact_closure_of_bounded_holomorphic hUo (fun f hf => hf.2.2.1)
  exact ⟨1, fun f hf z hz => (mem_ball_zero_iff.mp (hf.1 hz)).le⟩

/-- The closure of the normalized class. -/
theorem RiemannMapping.closure_normalizedClass {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    closure (normalizedClass U x₀) ⊆
      {f |
        Set.MapsTo (evaluation f) U (Metric.ball 0 1) ∧
          ((∃ C, Set.EqOn (evaluation f) (Function.const ℂ C) U) ∨ Set.InjOn (evaluation f) U) ∧
            DifferentiableOn ℂ (evaluation f) U ∧
              evaluation f x₀ = 0 ∧
                (Set.EqOn (deriv (evaluation f)) 0 U ∨ ∀ z ∈ U, deriv (evaluation f) z ≠ 0)} := by
  let := uniformity_isCountablyGenerated hUo
  intro f hf
  let : (𝓝[normalizedClass U x₀] f).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hf
  have htendsto :
    TendstoLocallyUniformlyOn evaluation (evaluation f) (𝓝[normalizedClass U x₀] f) U :=
    evaluation_tendstoLocallyUniformlyOn hUo
  have hFd : ∀ᶠ g in 𝓝[normalizedClass U x₀] f, DifferentiableOn ℂ (evaluation g) U :=
    eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.1
  have hdf : DifferentiableOn ℂ (evaluation f) U := htendsto.differentiableOn hFd hUo
  have hf_le : ∀ z ∈ U, ‖evaluation f z‖ ≤ 1 := by
    intro z hz
    refine le_of_tendsto (htendsto.tendsto_at hz).norm (eventually_mem_nhdsWithin.mono ?_)
    intro g hg
    exact (mem_ball_zero_iff.mp (hg.1 hz)).le
  have hfx₀ : evaluation f x₀ = 0 := by
    refine tendsto_nhds_unique (htendsto.tendsto_at hx₀) ?_
    refine tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun g hg => ?_)
    exact hg.2.2.2.2.symm
  refine ⟨?_, ?_, hdf, hfx₀, ?_⟩
  · by_contra hf_ball
    obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖evaluation f z‖ := by simpa [Set.MapsTo] using hf_ball
    have hm : IsMaxOn (fun z => ‖evaluation f z‖) U z := by
      intro y hy
      exact (hf_le y hy).trans hz
    have he : evaluation f x₀ = evaluation f z :=
      Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hdf hzU hm hx₀
    norm_num [← he, hfx₀] at hz
  · exact
      Complex.eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hUo hUc
        (eventually_mem_nhdsWithin.mono fun g hg => hg.2.1) hFd htendsto
  · apply
      Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn hUo hUc
        (eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.2.1)
        (hFd.mono fun g hg => hg.deriv hUo)
    exact htendsto.deriv hFd hUo

/-- The derivative norm is continuous on the closure. -/
theorem RiemannMapping.norm_deriv_continuousOn_closure {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ContinuousOn (fun f : FunctionSpace U => ‖deriv (evaluation f) x₀‖)
      (closure (normalizedClass U x₀)) := by
  have hc := closure_normalizedClass hUo hUc hx₀
  refine ContinuousOn.mono (ContinuousOn.norm fun f hf => ?_) hc
  refine
    TendstoLocallyUniformlyOn.tendsto_at
      (TendstoLocallyUniformlyOn.deriv (evaluation_tendstoLocallyUniformlyOn hUo) ?_ hUo) hx₀
  exact eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.1

/-- Existence of a maximal normalized map: the extremal map maximizing the derivative at the base point, the heart of the Riemann mapping theorem (Ahlfors, Complex Analysis, Ch. 6; Rudin, Real and Complex Analysis, Theorem 14.8). -/
theorem RiemannMapping.exists_maximal_normalizedMap {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) (hne : (normalizedClass U x₀).Nonempty) :
    ∃ f : FunctionSpace U,
      f ∈ normalizedClass U x₀ ∧
        ∀ g ∈ normalizedClass U x₀, ‖deriv (evaluation g) x₀‖ ≤ ‖deriv (evaluation f) x₀‖ := by
  obtain ⟨f, hf, hmax⟩ :=
    (normalizedClass_compact_closure hUo x₀).exists_isMaxOn hne.closure
      (norm_deriv_continuousOn_closure hUo hUc hx₀)
  have hpos : 0 < ‖deriv (evaluation f) x₀‖ := by
    obtain ⟨g, hg⟩ := hne
    exact (norm_pos_iff.mpr (hg.2.2.2.1 x₀ hx₀)).trans_le (hmax (subset_closure hg))
  obtain ⟨hmap, hinj, hdiff, hzero, hderiv⟩ := closure_normalizedClass hUo hUc hx₀ hf
  have hinj' : Set.InjOn (evaluation f) U := by
    apply hinj.resolve_left
    rintro ⟨C, hC⟩
    rw [(hC.eventuallyEq_of_mem (hUo.mem_nhds hx₀)).deriv_eq] at hpos
    change 0 < ‖deriv (fun _ : ℂ => C) x₀‖ at hpos
    simp only [deriv_const, norm_zero, lt_self_iff_false] at hpos
  have hderiv' : ∀ z ∈ U, deriv (evaluation f) z ≠ 0 := by
    apply hderiv.resolve_left
    intro hzero'
    have hz : deriv (evaluation f) x₀ = 0 := hzero' hx₀
    simp only [hz, norm_zero, lt_self_iff_false] at hpos
  exact ⟨f, ⟨hmap, hinj', hdiff, hderiv', hzero⟩, fun g hg => hmax (subset_closure hg)⟩

/-- The disc extension of a limit map. -/
def RiemannMapping.discExtension {U : Set ℂ} (f : ℂ → ℂ) (hf : Set.MapsTo f U (Metric.ball 0 1)) :
    ℂ → Complex.UnitDisc := by
  classical
    exact fun z =>
    if hz : z ∈ U then Complex.UnitDisc.mk (f z) (mem_ball_zero_iff.mp (hf hz)) else 0

/-- The disc extension computes the map. -/
@[simp]
theorem RiemannMapping.discExtension_coe {U : Set ℂ} (f : ℂ → ℂ)
    (hf : Set.MapsTo f U (Metric.ball 0 1)) {z : ℂ} (hz : z ∈ U) :
    (discExtension f hf z : ℂ) = f z := by
  simp only [discExtension, dif_pos hz, Complex.UnitDisc.coe_mk]

/-- The disc extension agrees with the map on the domain. -/
theorem RiemannMapping.discExtension_eqOn {U : Set ℂ} (f : ℂ → ℂ)
    (hf : Set.MapsTo f U (Metric.ball 0 1)) :
    Set.EqOn (Complex.UnitDisc.coe ∘ discExtension f hf) f U := fun _ hz =>
  discExtension_coe f hf hz

/-- The normalized class is nonempty. -/
theorem RiemannMapping.normalizedClass_nonempty {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    (normalizedClass U x₀).Nonempty := by
  obtain ⟨f, hf₀, hf_inj, hfd⟩ := Complex.exists_map_unitDisc_injOn_deriv_ne_zero₀ hUo hUc hU hx₀
  refine ⟨UniformOnFun.ofFun (compactSubsets U) (Complex.UnitDisc.coe ∘ f), ?_⟩
  refine ⟨fun z _ => (f z).property, ?_, ?_, hfd, ?_⟩
  · intro z hz w hw he
    exact hf_inj hz hw (Complex.UnitDisc.coe_injective he)
  · intro z hz
    exact (differentiableAt_of_deriv_ne_zero (hfd z hz)).differentiableWithinAt
  · change (f x₀ : ℂ) = 0
    rw [hf₀]
    rfl

/-- THE HEADLINE — the Riemann mapping theorem in normalized form: a simply connected proper domain admits a bijective holomorphic map onto the unit disc with nonvanishing derivative sending the base point to 0 (Rudin, Real and Complex Analysis, Theorem 14.8; Ahlfors, Complex Analysis, Ch. 6). -/
theorem RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f U ∧
        Set.BijOn f U (Metric.ball 0 1) ∧ (∀ z ∈ U, deriv f z ≠ 0) ∧ f x₀ = 0 := by
  obtain ⟨f, hf, hmax⟩ :=
    exists_maximal_normalizedMap hUo hUc.isPathConnected.isConnected.isPreconnected hx₀
      (normalizedClass_nonempty hUo hUc hU hx₀)
  obtain ⟨hfmap, hfinj, hfdiff, hfderiv, hfzero⟩ := hf
  refine ⟨evaluation f, hfdiff, ⟨hfmap, hfinj, ?_⟩, hfderiv, hfzero⟩
  by_contra hsurj
  let fDisc := discExtension (evaluation f) hfmap
  have hfeq : Set.EqOn (Complex.UnitDisc.coe ∘ fDisc) (evaluation f) U :=
    discExtension_eqOn (evaluation f) hfmap
  have hfdDisc : DifferentiableOn ℂ (Complex.UnitDisc.coe ∘ fDisc) U :=
    (differentiableOn_congr hfeq).mpr hfdiff
  have hfDisc0 : fDisc x₀ = 0 := by
    apply Complex.UnitDisc.coe_injective
    change (fDisc x₀ : ℂ) = 0
    exact (hfeq hx₀).trans hfzero
  have hfDiscInj : Set.InjOn fDisc U := by
    intro z hz w hw he
    apply hfinj hz hw
    exact (hfeq hz).symm.trans ((congrArg Complex.UnitDisc.coe he).trans (hfeq hw))
  have hfDiscDeriv : ∀ z ∈ U, deriv (Complex.UnitDisc.coe ∘ fDisc) z ≠ 0 := by
    intro z hz
    rw [(hfeq.eventuallyEq_of_mem (hUo.mem_nhds hz)).deriv_eq]
    exact hfderiv z hz
  have hfDiscSurj : ¬Set.SurjOn fDisc U Set.univ := by
    intro hs
    apply hsurj
    intro w hw
    obtain ⟨z, hz, he⟩ := hs (Set.mem_univ (Complex.UnitDisc.mk w (mem_ball_zero_iff.mp hw)))
    refine ⟨z, hz, ?_⟩
    exact (hfeq hz).symm.trans (congrArg Complex.UnitDisc.coe he)
  obtain ⟨g, hg₀, hginj, hgdiff, hgderiv, hglt⟩ :=
    Complex.exist_map_unitDisc_injOn_deriv_ne_zero_norm_deriv_gt hUo hUc hU hx₀ hfdDisc hfDisc0
      hfDiscInj hfDiscSurj hfDiscDeriv
  let gFun : FunctionSpace U := UniformOnFun.ofFun (compactSubsets U) (Complex.UnitDisc.coe ∘ g)
  have hgmem : gFun ∈ normalizedClass U x₀ := by
    refine ⟨fun z _ => (g z).property, ?_, hgdiff, hgderiv, ?_⟩
    · intro z hz w hw he
      exact hginj hz hw (Complex.UnitDisc.coe_injective he)
    · change (g x₀ : ℂ) = 0
      rw [hg₀]
      rfl
  have hle := hmax gFun hgmem
  have heDeriv : deriv (Complex.UnitDisc.coe ∘ fDisc) x₀ = deriv (evaluation f) x₀ :=
    (hfeq.eventuallyEq_of_mem (hUo.mem_nhds hx₀)).deriv_eq
  rw [heDeriv] at hglt
  exact hle.not_gt hglt

/-! ### The Riemann map -/

/-- A holomorphic map with nonvanishing derivative is a local diffeomorphism. -/
theorem RiemannMapping.isLocalDiffeomorphAt_of_deriv_ne_zero (U : TopologicalSpace.Opens ℂ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U : Set ℂ)) (hderiv : ∀ z ∈ U, deriv f z ≠ 0) {z : ℂ}
    (hz : z ∈ U) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f z := by
  have hfω : ContDiffOn ℂ ω f (U : Set ℂ) := hf.contDiffOn U.isOpen
  have hF (w : ℂ) (hw : w ∈ U) : ContDiffAt ℂ ω f w := hfω.contDiffAt (U.isOpen.mem_nhds hw)
  have hD (w : ℂ) (hw : w ∈ U) : HasDerivAt f (deriv f w) w :=
    hf.hasDerivAt (U.isOpen.mem_nhds hw)
  let e : OpenPartialHomeomorph ℂ ℂ :=
    ((hF z hz).toOpenPartialHomeomorph f ((hD z hz).hasFDerivAt_equiv (hderiv z hz))
          (by simp)).restr
      (U : Set ℂ)
  have heU : e.source ⊆ (U : Set ℂ) := by
    intro w hw
    dsimp only [e] at hw
    rw [OpenPartialHomeomorph.restr_source' _ _ U.isOpen] at hw
    exact hw.2
  have hze : z ∈ e.source := by
    dsimp only [e]
    rw [OpenPartialHomeomorph.restr_source' _ _ U.isOpen]
    exact
      ⟨(hF z hz).mem_toOpenPartialHomeomorph_source ((hD z hz).hasFDerivAt_equiv (hderiv z hz))
          (by simp),
        hz⟩
  refine
    ⟨{  toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := ?_
        contMDiffOn_invFun := ?_ }, hze, fun _ _ => rfl⟩
  · change ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f e.source
    exact (hfω.mono heU).contMDiffOn
  · apply ContDiffOn.contMDiffOn
    intro w hw
    have hwU := heU (e.map_target hw)
    exact
      (e.contDiffAt_symm hw ((hD _ hwU).hasFDerivAt_equiv (hderiv _ hwU))
          (hF _ hwU)).contDiffWithinAt

/-- The unit disc as a subtype. -/
def RiemannMapping.unitDisc : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- The Riemann map of the domain onto the disc. -/
def RiemannMapping.riemannMap (U : TopologicalSpace.Opens ℂ) (hUc : IsSimplyConnected (U : Set ℂ))
    (hU : (U : Set ℂ) ≠ Set.univ) (x₀ : U) : ℂ → ℂ :=
  (exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero U.isOpen hUc hU x₀.property).choose

/-- The Riemann map is the maximizing normalized map. -/
theorem RiemannMapping.riemannMap_spec (U : TopologicalSpace.Opens ℂ)
    (hUc : IsSimplyConnected (U : Set ℂ)) (hU : (U : Set ℂ) ≠ Set.univ) (x₀ : U) :
    DifferentiableOn ℂ (riemannMap U hUc hU x₀) (U : Set ℂ) ∧
      Set.BijOn (riemannMap U hUc hU x₀) (U : Set ℂ) (unitDisc : Set ℂ) ∧
        (∀ z ∈ U, deriv (riemannMap U hUc hU x₀) z ≠ 0) ∧ riemannMap U hUc hU x₀ x₀ = 0 :=
  (exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero U.isOpen hUc hU x₀.property).choose_spec

/-! ### Primitives on rectangles -/

/-- An open rectangle in the plane. -/
def RiemannBoundary.openRectangle (a b c d : ℝ) : Set ℂ :=
  {z | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d}

/-- The open rectangle is open. -/
theorem RiemannBoundary.isOpen_openRectangle (a b c d : ℝ) : IsOpen (openRectangle a b c d) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

/-- The open rectangle is convex. -/
theorem RiemannBoundary.convex_openRectangle (a b c d : ℝ) : Convex ℝ (openRectangle a b c d) :=
  ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).inter
    ((convex_halfSpace_im_gt c).inter (convex_halfSpace_im_lt d))

/-- A point with mixed coordinates lies in the open rectangle. -/
theorem RiemannBoundary.mixed_mem_openRectangle {a b c d : ℝ} {z w : ℂ}
    (hz : z ∈ openRectangle a b c d) (hw : w ∈ openRectangle a b c d) :
    z.re + w.im * Complex.I ∈ openRectangle a b c d := by
  simpa only [openRectangle, Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, MulZeroClass.mul_zero, MulZeroClass.zero_mul,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] using
    And.intro hz.1 hw.2

/-- The closed rectangle lies in the open rectangle. -/
theorem RiemannBoundary.rectangle_subset_openRectangle {a b c d : ℝ} {z w : ℂ}
    (hz : z ∈ openRectangle a b c d) (hw : w ∈ openRectangle a b c d) :
    Complex.Rectangle z w ⊆ openRectangle a b c d :=
  Complex.Convex.rectangle_subset (convex_openRectangle a b c d) hz hw
    (mixed_mem_openRectangle hz hw) (mixed_mem_openRectangle hw hz)

/-- A horizontal segment lies in the rectangle. -/
theorem RiemannBoundary.horizontal_segment_subset {a b c d : ℝ} {x₁ x₂ y : ℝ}
    (h₁ : (x₁ : ℂ) + y * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x₂ : ℂ) + y * Complex.I ∈ openRectangle a b c d) :
    (fun x : ℝ => (x : ℂ) + y * Complex.I) '' [[x₁, x₂]] ⊆ openRectangle a b c d := by
  convert rectangle_subset_openRectangle h₁ h₂ using 1
  simp [Complex.horizontalSegment_eq x₁ x₂ y, Complex.Rectangle]

/-- A vertical segment lies in the rectangle. -/
theorem RiemannBoundary.vertical_segment_subset {a b c d : ℝ} {x y₁ y₂ : ℝ}
    (h₁ : (x : ℂ) + y₁ * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x : ℂ) + y₂ * Complex.I ∈ openRectangle a b c d) :
    (fun y : ℝ => (x : ℂ) + y * Complex.I) '' [[y₁, y₂]] ⊆ openRectangle a b c d := by
  convert rectangle_subset_openRectangle h₁ h₂ using 1
  simp [Complex.verticalSegment_eq x y₁ y₂, Complex.Rectangle]

/-- The difference of wedge integrals over an open rectangle. -/
theorem RiemannBoundary.wedgeIntegral_sub_wedgeIntegral_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (openRectangle a b c d))
    (hf : Complex.IsConservativeOn f (openRectangle a b c d)) {p z w : ℂ}
    (hp : p ∈ openRectangle a b c d) (hz : z ∈ openRectangle a b c d)
    (hw : w ∈ openRectangle a b c d) :
    Complex.wedgeIntegral p w f - Complex.wedgeIntegral p z f = Complex.wedgeIntegral z w f := by
  have integrableHoriz (x₁ x₂ y : ℝ) (h₁ : (x₁ : ℂ) + y * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x₂ : ℂ) + y * Complex.I ∈ openRectangle a b c d) :
    IntervalIntegrable (fun x : ℝ => f (x + y * Complex.I)) MeasureTheory.MeasureSpace.volume x₁
      x₂ :=
    ((hc.mono (horizontal_segment_subset h₁ h₂)).comp (by fun_prop)
        (Set.mapsTo_image _ _)).intervalIntegrable
  have integrableVert (x y₁ y₂ : ℝ) (h₁ : (x : ℂ) + y₁ * Complex.I ∈ openRectangle a b c d)
    (h₂ : (x : ℂ) + y₂ * Complex.I ∈ openRectangle a b c d) :
    IntervalIntegrable (fun y : ℝ => f (x + y * Complex.I)) MeasureTheory.MeasureSpace.volume y₁
      y₂ :=
    ((hc.mono (vertical_segment_subset h₁ h₂)).comp (by fun_prop)
        (Set.mapsTo_image _ _)).intervalIntegrable
  have hHoriz :
    (∫ x in p.re..w.re, f (x + p.im * Complex.I)) =
      (∫ x in p.re..z.re, f (x + p.im * Complex.I)) +
        (∫ x in z.re..w.re, f (x + p.im * Complex.I)) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · apply integrableHoriz
      · simpa only [Complex.re_add_im] using hp
      · exact mixed_mem_openRectangle hz hp
    · apply integrableHoriz
      · exact mixed_mem_openRectangle hz hp
      · exact mixed_mem_openRectangle hw hp
  have hVert :
    Complex.I * (∫ y in p.im..w.im, f (w.re + y * Complex.I)) =
      Complex.I * (∫ y in p.im..z.im, f (w.re + y * Complex.I)) +
        Complex.I * (∫ y in z.im..w.im, f (w.re + y * Complex.I)) := by
    rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals]
    · apply integrableVert
      · exact mixed_mem_openRectangle hw hp
      · exact mixed_mem_openRectangle hw hz
    · apply integrableVert
      · exact mixed_mem_openRectangle hw hz
      · simpa only [Complex.re_add_im] using hw
  have hRect :=
    hf (z.re + p.im * Complex.I) (w.re + z.im * Complex.I)
      (rectangle_subset_openRectangle (mixed_mem_openRectangle hz hp)
        (mixed_mem_openRectangle hw hz))
  have hBoundary :
    (∫ x in z.re..w.re, f (x + p.im * Complex.I)) -
            (∫ x in z.re..w.re, f (x + z.im * Complex.I)) +
          Complex.I * (∫ y in p.im..z.im, f (w.re + y * Complex.I)) -
        Complex.I * (∫ y in p.im..z.im, f (z.re + y * Complex.I)) =
      0 := by
    simpa [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq] using hRect
  simp only [Complex.wedgeIntegral, smul_eq_mul]
  rw [hHoriz, hVert]
  linear_combination hBoundary

/-- The wedge integral is differentiable on the open rectangle. -/
theorem RiemannBoundary.hasDerivAt_wedgeIntegral_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d)) {p z : ℂ} (hp : p ∈ openRectangle a b c d)
    (hz : z ∈ openRectangle a b c d) :
    HasDerivAt (fun w => Complex.wedgeIntegral p w f) (f z) z := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (isOpen_openRectangle a b c d) z hz
  have hd : HasDerivAt (fun w => Complex.wedgeIntegral z w f) (f z) z :=
    (hf.isConservativeOn.mono hsub).hasDerivAt_wedgeIntegral (hf.continuousOn.mono hsub)
      (Metric.mem_ball_self hr)
  apply (hd.add_const (Complex.wedgeIntegral p z f)).congr_of_eventuallyEq
  filter_upwards [(isOpen_openRectangle a b c d).mem_nhds hz] with w hw
  exact
    sub_eq_iff_eq_add.mp
      (wedgeIntegral_sub_wedgeIntegral_openRectangle hf.continuousOn hf.isConservativeOn hp hz hw)

/-- A closed form is exact on the open rectangle. -/
theorem RiemannBoundary.isExactOn_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d)) :
    Complex.IsExactOn f (openRectangle a b c d) := by
  by_cases h : (openRectangle a b c d).Nonempty
  · obtain ⟨p, hp⟩ := h
    exact
      ⟨fun z => Complex.wedgeIntegral p z f, fun _ hz =>
        hasDerivAt_wedgeIntegral_openRectangle hf hp hz⟩
  · refine ⟨fun _ => 0, fun z hz => ?_⟩
    exact (h ⟨z, hz⟩).elim

/-- A Lipschitz extension primitive exists on the open rectangle. -/
theorem RiemannBoundary.exists_lipschitz_extension_primitive_openRectangle {a b c d : ℝ}
    {f : ℂ → ℂ} {F : ℂ → ℂ} {K : ℝ≥0} (hF : ∀ z ∈ openRectangle a b c d, HasDerivAt F (f z) z)
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖₊ ≤ K) :
    ∃ G : ℂ → ℂ,
      LipschitzWith (lipschitzExtensionConstant ℂ * K) G ∧
        Set.EqOn F G (openRectangle a b c d) ∧
          ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  have hLip : LipschitzOnWith K F (openRectangle a b c d) :=
    (convex_openRectangle a b c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (hF z hz).hasDerivWithinAt) hb
  obtain ⟨G, hG, heq⟩ := hLip.extend_finite_dimension
  refine ⟨G, hG, heq, fun z hz => ?_⟩
  apply (hF z hz).congr_of_eventuallyEq
  filter_upwards [(isOpen_openRectangle a b c d).mem_nhds hz] with w hw
  exact (heq hw).symm

/-- A continuous primitive exists on the open rectangle. -/
theorem RiemannBoundary.exists_continuous_primitive_openRectangle {a b c d : ℝ} {f : ℂ → ℂ}
    {K : ℝ≥0} (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖₊ ≤ K) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  obtain ⟨F, hF⟩ := isExactOn_openRectangle hf
  obtain ⟨G, hG, _, hd⟩ := exists_lipschitz_extension_primitive_openRectangle hF hb
  exact ⟨G, hG.continuous, hd⟩

/-- A bounded continuous primitive exists on the open rectangle. -/
theorem RiemannBoundary.exists_continuous_primitive_openRectangle_of_norm_le {a b c d : ℝ}
    {f : ℂ → ℂ} {M : ℝ} (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖ ≤ M) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  apply exists_continuous_primitive_openRectangle (K := M.toNNReal) hf
  intro z hz
  exact_mod_cast (hb z hz).trans (Real.le_coe_toNNReal M)

/-- The horizontal primitive is differentiable. -/
theorem RiemannBoundary.hasDerivAt_horizontal {F : ℂ → ℂ} {f : ℂ} {x y : ℝ}
    (hF : HasDerivAt F f ((x : ℂ) + y * Complex.I)) :
    HasDerivAt (fun t : ℝ => F (t + y * Complex.I)) f x := by
  have h := hF.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (y * Complex.I))
  simpa only [mul_one, Function.comp_def, id_eq] using h.comp_ofReal

/-- The upper limit converges uniformly on the filter. -/
theorem RiemannBoundary.upper_limit_tendstoUniformlyOnFilter {q : ℂ → ℂ} {x : ℝ}
    (hq : Filter.Tendsto q (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0)) :
    TendstoUniformlyOnFilter (fun y t : ℝ => q (t + y * Complex.I)) (fun _ => 0) (𝓝[>] 0) (𝓝 x) :=
  by
  have ht :
    Filter.Tendsto (fun p : ℝ × ℝ => (p.2 : ℂ) + p.1 * Complex.I) ((𝓝[>] 0) ×ˢ 𝓝 x)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h₁ : Filter.Tendsto (fun p : ℝ × ℝ => (p.1 : ℂ)) ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝 (0 : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          (Filter.tendsto_fst.mono_right nhdsWithin_le_nhds)
      have h₂ : Filter.Tendsto (fun p : ℝ × ℝ => (p.2 : ℂ)) ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝 (x : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp Filter.tendsto_snd
      simpa using h₂.add (h₁.mul_const Complex.I)
    · have hy : ∀ᶠ p : ℝ × ℝ in (𝓝[>] 0) ×ˢ 𝓝 x, 0 < p.1 :=
        Filter.tendsto_fst.eventually eventually_mem_nhdsWithin
      filter_upwards [hy] with p hp
      simpa using hp
  apply Metric.tendstoUniformlyOnFilter_iff.mpr
  intro ε hε
  simpa only [Function.comp_def, dist_zero_left, dist_zero_right] using
    Metric.tendsto_nhds.mp (hq.comp ht) ε hε

/-- The boundary trace difference is differentiable. -/
theorem RiemannBoundary.hasDerivAt_boundary_trace_sub {F G f g : ℂ → ℂ} {a b h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Ioo a b) (hF : Continuous F) (hG : Continuous G)
    (hFd :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt F (f (t + y * Complex.I)) (t + y * Complex.I))
    (hGd :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt G (g (t - y * Complex.I)) (t - y * Complex.I))
    (hjump :
      ∀ t ∈ Set.Ioo a b,
        Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 0)) :
    HasDerivAt (fun t : ℝ => F t - G t) 0 x := by
  let H : ℝ → ℝ → ℂ := fun y t => F (t + y * Complex.I) - G (t - y * Complex.I)
  let H' : ℝ → ℝ → ℂ := fun y t => f (t + y * Complex.I) - g (t - y * Complex.I)
  have hd : ∀ᶠ y in 𝓝[>] 0, ∀ t ∈ Set.Ioo a b, HasDerivAt (H y) (H' y t) t := by
    filter_upwards [Ioo_mem_nhdsGT hh] with y hy t ht
    have hu := hasDerivAt_horizontal (hFd t ht y hy)
    have hl : HasDerivAt (fun s : ℝ => G (s - y * Complex.I)) (g (t - y * Complex.I)) t := by
      have hi :=
        hasDerivAt_horizontal (y := -y)
          (by simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hGd t ht y hy)
      simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hi
    exact hu.sub hl
  have hdu : TendstoLocallyUniformlyOn H' (fun _ => 0) (𝓝[>] 0) (Set.Ioo a b) := by
    rw [tendstoLocallyUniformlyOn_iff_filter]
    intro t ht
    rw [isOpen_Ioo.nhdsWithin_eq ht]
    simpa only [H', map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      ← sub_eq_add_neg] using upper_limit_tendstoUniformlyOnFilter (hjump t ht)
  have hlim :
    ∀ t ∈ Set.Ioo a b, Filter.Tendsto (fun y => H y t) (𝓝[>] 0) (𝓝 (F (t : ℂ) - G (t : ℂ))) := by
    intro t _
    have hc : Continuous (fun y : ℝ => H y t) := by dsimp [H]; fun_prop
    simpa [H] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  exact hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo hdu hd hlim hx

/-- The boundary trace difference computes the jump. -/
theorem RiemannBoundary.boundary_trace_sub_eq {F G f g : ℂ → ℂ} {a b h x t : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) (hF : Continuous F) (hG : Continuous G)
    (hFd :
      ∀ s ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt F (f (s + y * Complex.I)) (s + y * Complex.I))
    (hGd :
      ∀ s ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt G (g (s - y * Complex.I)) (s - y * Complex.I))
    (hjump :
      ∀ s ∈ Set.Ioo a b,
        Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (s : ℂ)) (𝓝 0)) :
    F (x : ℂ) - G (x : ℂ) = F (t : ℂ) - G (t : ℂ) := by
  have hd (s : ℝ) (hs : s ∈ Set.Ioo a b) :=
    hasDerivAt_boundary_trace_sub hh hs hF hG hFd hGd hjump
  exact
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) hx ht

/-- A vanishing boundary jump gives an analytic extension. -/
theorem RiemannBoundary.exists_analytic_extension_of_vanishing_jump {f g : ℂ → ℂ} {a b h M N : ℝ}
    (hab : a < b) (hh : 0 < h) (hf : DifferentiableOn ℂ f (openRectangle a b 0 h))
    (hg : DifferentiableOn ℂ g (openRectangle a b (-h) 0))
    (hfb : ∀ z ∈ openRectangle a b 0 h, ‖f z‖ ≤ M)
    (hgb : ∀ z ∈ openRectangle a b (-h) 0, ‖g z‖ ≤ N)
    (hjump :
      ∀ x ∈ Set.Ioo a b,
        Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0)) :
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (openRectangle a b (-h) h) ∧
        Set.EqOn H f (openRectangle a b 0 h) ∧ Set.EqOn H g (openRectangle a b (-h) 0) := by
  obtain ⟨F, hFc, hFd⟩ := exists_continuous_primitive_openRectangle_of_norm_le hf hfb
  obtain ⟨G, hGc, hGd⟩ := exists_continuous_primitive_openRectangle_of_norm_le hg hgb
  let x₀ : ℝ := (a + b) / 2
  have hx₀ : x₀ ∈ Set.Ioo a b := by dsimp [x₀]; constructor <;> linarith
  let c : ℂ := F x₀ - G x₀
  have htrace : ∀ x ∈ Set.Ioo a b, F (x : ℂ) = G (x : ℂ) + c := by
    intro x hx
    have hdF :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt F (f (t + y * Complex.I)) (t + y * Complex.I) := by
      intro t ht y hy
      exact hFd _ (by simpa [openRectangle] using And.intro ht hy)
    have hdG :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt G (g (t - y * Complex.I)) (t - y * Complex.I) := by
      intro t ht y hy
      apply hGd
      simpa [openRectangle] using
        And.intro ht (show -y ∈ Set.Ioo (-h) 0 by constructor <;> linarith [hy.1, hy.2])
    have he := boundary_trace_sub_eq hh hx hx₀ hFc hGc hdF hdG hjump
    dsimp [c]
    linear_combination he
  let P := SchwarzReflection.pasteUpper F (fun z => G z + c)
  have hP : AnalyticOnNhd ℂ P (openRectangle a b (-h) h) := by
    apply
      SchwarzReflection.analyticOnNhd_pasteUpper (isOpen_openRectangle _ _ _ _) hFc.continuousOn
        (hGc.add continuous_const).continuousOn
    · intro z hz hpos
      exact (hFd z ⟨hz.1, hpos, hz.2.2⟩).differentiableAt
    · intro z hz hneg
      exact ((hGd z ⟨hz.1, hz.2.1, hneg⟩).add_const c).differentiableAt
    · intro z hz hzero
      change F z = G z + c
      have heq : (z.re : ℂ) = z := by exact Complex.ext (by simp) (by simpa using hzero.symm)
      simpa only [heq] using htrace z.re hz.1
  refine ⟨deriv P, hP.deriv, ?_, ?_⟩
  · intro z hz
    have hnear : P =ᶠ[𝓝 z] F := by
      filter_upwards [continuousAt_const.eventually_lt Complex.continuous_im.continuousAt
          hz.2.1] with
        w hw
      exact SchwarzReflection.pasteUpper_of_nonneg F (fun w => G w + c) hw.le
    exact ((hFd z hz).congr_of_eventuallyEq hnear).deriv
  · intro z hz
    have hnear : P =ᶠ[𝓝 z] (fun w => G w + c) := by
      filter_upwards [Complex.continuous_im.continuousAt.eventually_lt continuousAt_const
          hz.2.2] with
        w hw
      exact SchwarzReflection.pasteUpper_of_neg F (fun w => G w + c) hw
    exact (((hGd z hz).add_const c).congr_of_eventuallyEq hnear).deriv

/-- The norm of `z − 1/conj z`. -/
theorem RiemannBoundary.norm_sub_inv_conj (w : ℂ) : ‖w - (conj w)⁻¹‖ = |‖w‖ ^ 2 - 1| / ‖w‖ := by
  have heq : w - (conj w)⁻¹ = ((‖w‖ ^ 2 - 1 : ℝ) : ℂ) / conj w := by
    by_cases hw : w = 0
    · simp [hw]
    have hc : conj w ≠ 0 := by simpa using hw
    apply (eq_div_iff hc).mpr
    rw [sub_mul, inv_mul_cancel₀ hc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_sub, Complex.ofReal_one]
  rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]

/-- `z − 1/conj z` tends to zero as `|z|` tends to `1`. -/
theorem RiemannBoundary.tendsto_sub_inv_conj_of_norm {α : Type*} {l : Filter α} {f : α → ℂ}
    (hf : Filter.Tendsto (fun x => ‖f x‖) l (𝓝 1)) :
    Filter.Tendsto (fun x => f x - (conj (f x))⁻¹) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_sub_inv_conj]
  have hn : Filter.Tendsto (fun x => |‖f x‖ ^ 2 - 1|) l (𝓝 (0 : ℝ)) := by
    simpa using ((hf.pow 2).sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  have hdiv := hn.div hf one_ne_zero
  have hfun :
    ((fun x => |‖f x‖ ^ 2 - 1|) / (fun x => ‖f x‖)) = (fun x => |‖f x‖ ^ 2 - 1| / ‖f x‖) := by rfl
  rw [hfun] at hdiv
  simpa only [zero_div] using hdiv

/-- A modulus-one extension has norm one on the axis. -/
theorem RiemannBoundary.norm_axis_eq_one_of_extension {H f : ℂ → ℂ} {a b h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Ioo a b) (hH : ContinuousOn H (openRectangle a b (-h) h))
    (heq : Set.EqOn H f (openRectangle a b 0 h))
    (hmod : Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1)) :
    ‖H (x : ℂ)‖ = 1 := by
  have hxU : (x : ℂ) ∈ openRectangle a b (-h) h := by
    simpa [openRectangle] using
      And.intro hx (show (0 : ℝ) ∈ Set.Ioo (-h) h by constructor <;> linarith)
  have hHt : Filter.Tendsto (fun y : ℝ => ‖H (x + y * Complex.I)‖) (𝓝[>] 0) (𝓝 ‖H (x : ℂ)‖) := by
    have hcont := (hH.continuousAt ((isOpen_openRectangle _ _ _ _).mem_nhds hxU)).norm
    have ht : Filter.Tendsto (fun y : ℝ => (x : ℂ) + y * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have hc : Continuous (fun y : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    exact hcont.tendsto.comp ht
  have hft : Filter.Tendsto (fun y : ℝ => ‖f (x + y * Complex.I)‖) (𝓝[>] 0) (𝓝 1) := by
    apply hmod.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun y : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  have hevent :
    (fun y : ℝ => ‖H (x + y * Complex.I)‖) =ᶠ[𝓝[>] 0] (fun y : ℝ => ‖f (x + y * Complex.I)‖) := by
    filter_upwards [Ioo_mem_nhdsGT hh] with y hy
    rw [heq (by simpa [openRectangle] using And.intro hx hy)]
  exact tendsto_nhds_unique hHt (hft.congr' hevent.symm)

/-- A bounded modulus-one boundary trace gives an analytic extension. -/
theorem RiemannBoundary.exists_analytic_extension_of_modulus_one_bounded {f : ℂ → ℂ}
    {a b h M m : ℝ} (hab : a < b) (hh : 0 < h) (hm : 0 < m)
    (hf : DifferentiableOn ℂ f (openRectangle a b 0 h))
    (hfb : ∀ z ∈ openRectangle a b 0 h, ‖f z‖ ≤ M) (hfl : ∀ z ∈ openRectangle a b 0 h, m ≤ ‖f z‖)
    (hmod :
      ∀ x ∈ Set.Ioo a b, Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1)) :
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (openRectangle a b (-h) h) ∧
        Set.EqOn H f (openRectangle a b 0 h) ∧
          Set.EqOn H (fun z => (conj (f (conj z)))⁻¹) (openRectangle a b (-h) 0) ∧
            ∀ x ∈ Set.Ioo a b, ‖H (x : ℂ)‖ = 1 := by
  let g : ℂ → ℂ := fun z => (conj (f (conj z)))⁻¹
  have hconj : ∀ z ∈ openRectangle a b (-h) 0, conj z ∈ openRectangle a b 0 h := by
    intro z hz
    refine ⟨by simpa using hz.1, ?_⟩
    simp only [Complex.conj_im, Set.mem_Ioo]
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hnz : ∀ z ∈ openRectangle a b 0 h, f z ≠ 0 := by
    intro z hz heq
    have hb := hfl z hz
    rw [heq, norm_zero] at hb
    exact (not_le.mpr hm) hb
  have hg : DifferentiableOn ℂ g (openRectangle a b (-h) 0) := by
    intro z hz
    have hd :=
      (hf.differentiableAt ((isOpen_openRectangle _ _ _ _).mem_nhds (hconj z hz))).conj_conj
    have hd' : DifferentiableAt ℂ (fun w => conj (f (conj w))) z := by
      simpa only [Function.comp_def, starRingEnd_self_apply] using hd
    exact (hd'.inv (by simpa using hnz (conj z) (hconj z hz))).differentiableWithinAt
  have hgb : ∀ z ∈ openRectangle a b (-h) 0, ‖g z‖ ≤ m⁻¹ := by
    intro z hz
    simp only [g, norm_inv, Complex.norm_conj]
    exact (inv_le_inv₀ (hm.trans_le (hfl _ (hconj z hz))) hm).mpr (hfl _ (hconj z hz))
  have hjump :
    ∀ x ∈ Set.Ioo a b,
      Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0) := by
    intro x hx
    simpa only [g, starRingEnd_self_apply] using tendsto_sub_inv_conj_of_norm (hmod x hx)
  obtain ⟨H, hH, he, hl⟩ := exists_analytic_extension_of_vanishing_jump hab hh hf hg hfb hgb hjump
  exact
    ⟨H, hH, he, hl, fun x hx =>
      norm_axis_eq_one_of_extension hh hx hH.continuousOn he (hmod x hx)⟩

/-- Points of a centered rectangle are within twice the radius. -/
theorem RiemannBoundary.dist_lt_two_mul_of_mem_centeredRectangle {x r : ℝ} {z : ℂ}
    (hz : z ∈ openRectangle (x - r) (x + r) (-r) r) : Dist.dist z (x : ℂ) < 2 * r := by
  have hre : |(z - x).re| < r := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    exact abs_lt.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him : |(z - x).im| < r := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using abs_lt.mpr hz.2
  rw [dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im (z - x)).trans_lt (by linarith)

/-- A ball lies in the centered rectangle. -/
theorem RiemannBoundary.ball_subset_centeredRectangle (x r : ℝ) :
    Metric.ball (x : ℂ) r ⊆ openRectangle (x - r) (x + r) (-r) r := by
  intro z hz
  have hn : ‖z - x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hre := abs_lt.mp ((Complex.abs_re_le_norm (z - x)).trans_lt hn)
  have him := abs_lt.mp ((Complex.abs_im_le_norm (z - x)).trans_lt hn)
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero] at hre him
  exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, him⟩

/-- A modulus-one boundary trace gives an analytic extension. -/
theorem RiemannBoundary.exists_analytic_extension_of_modulus_one {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} {x : ℝ} (hx : (x : ℂ) ∈ U) (hf : DifferentiableOn ℂ f (U ∩ {z : ℂ | 0 < z.im}))
    (hmod :
      ∀ t : ℝ,
        (t : ℂ) ∈ U → Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1)) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (x : ℂ) r) ∧
          Set.EqOn H f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (conj z)))⁻¹)
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              ∀ t : ℝ, (t : ℂ) ∈ Metric.ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU (x : ℂ) hx
  obtain ⟨δ, hδ, hδf⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hmod x hx) (1 / 2) (by norm_num)
  let r : ℝ := Min.min ε δ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : 2 * r < ε := by
    have hm := min_le_left ε δ
    dsimp [r]
    linarith
  have hrδ : 2 * r < δ := by
    have hm := min_le_right ε δ
    dsimp [r]
    linarith
  have hrectU : openRectangle (x - r) (x + r) (-r) r ⊆ U := by
    intro z hz
    apply hεU
    exact (dist_lt_two_mul_of_mem_centeredRectangle hz).trans hrε
  have hu : openRectangle (x - r) (x + r) 0 r ⊆ U ∩ {z : ℂ | 0 < z.im} := by
    intro z hz
    exact ⟨hrectU ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩, hz.2.1⟩
  have hsize : ∀ z ∈ openRectangle (x - r) (x + r) 0 r, 1 / 2 ≤ ‖f z‖ ∧ ‖f z‖ ≤ 2 := by
    intro z hz
    have hzR : z ∈ openRectangle (x - r) (x + r) (-r) r := ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
    have he := hδf hz.2.1 ((dist_lt_two_mul_of_mem_centeredRectangle hzR).trans hrδ)
    rw [Real.dist_eq, abs_lt] at he
    constructor <;> linarith [he.1, he.2]
  have hmodR :
    ∀ t ∈ Set.Ioo (x - r) (x + r),
      Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1) := by
    intro t ht
    apply hmod
    apply hrectU
    simpa only [openRectangle, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im] using
      And.intro ht (show (0 : ℝ) ∈ Set.Ioo (-r) r by constructor <;> linarith)
  obtain ⟨H, hH, hHe, hHl, hHcircle⟩ :=
    exists_analytic_extension_of_modulus_one_bounded (by linarith) hr
      (show (0 : ℝ) < 1 / 2 by norm_num) (hf.mono hu) (fun z hz => (hsize z hz).2)
      (fun z hz => (hsize z hz).1) hmodR
  refine ⟨r, hr, H, hH.mono (ball_subset_centeredRectangle x r), ?_, ?_, ?_⟩
  · intro z hz
    have hzR := ball_subset_centeredRectangle x r hz.1
    exact hHe ⟨hzR.1, hz.2, hzR.2.2⟩
  · intro z hz
    have hzR := ball_subset_centeredRectangle x r hz.1
    exact hHl ⟨hzR.1, hzR.2.1, hz.2⟩
  · intro t ht
    have htR := ball_subset_centeredRectangle x r ht
    exact hHcircle t (by simpa only [Complex.ofReal_re] using htR.1)

/-- The disc norm tends to `1` approaching a non-member. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_nhdsWithin_of_notMem {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {a : ℂ}
    (ha : a ∉ D) : Filter.Tendsto (fun z => ‖f z‖) (𝓝[D] a) (𝓝 1) := by
  have hz :
    Filter.Tendsto (Subtype.val : D → ℂ) (Filter.comap (Subtype.val : D → ℂ) (𝓝[D] a)) (𝓝 a) :=
    Filter.tendsto_comap.mono_right nhdsWithin_le_nhds
  have ht := RiemannMapping.tendsto_norm_discHomeomorph_of_notMem e ha hz
  apply (Filter.tendsto_comap'_iff (i := (Subtype.val : D → ℂ)) ?_).mp
  · simpa only [Function.comp_def, he] using ht
  · simpa only [Subtype.range_coe] using (self_mem_nhdsWithin : D ∈ 𝓝[D] a)

/-- The disc norm tends to `1` in the boundary chart. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_in_boundary_chart {D U : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f φ : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (hU : IsOpen U)
    (hφ : ContinuousOn φ (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hside : Set.MapsTo φ (U ∩ {z : ℂ | 0 < z.im}) D) {x : ℝ} (hx : (x : ℂ) ∈ U)
    (hout : φ (x : ℂ) ∉ D) :
    Filter.Tendsto (fun z => ‖f (φ z)‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1) := by
  apply (tendsto_norm_discHomeomorph_nhdsWithin_of_notMem e he hout).comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc := hφ (x : ℂ) ⟨hx, by simp⟩
    apply hc.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Filter.tendsto_id.mono_right nhdsWithin_le_nhds
    · have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)
      filter_upwards [hnear, self_mem_nhdsWithin] with z hz hu
      exact ⟨hz, le_of_lt hu⟩
  · have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ) := mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)
    filter_upwards [hnear, self_mem_nhdsWithin] with z hz hu
    exact hside ⟨hz, hu⟩

/-! ### Boundary behavior at the upper half-plane -/

/-- The imaginary part of a scaled exponential. -/
theorem RiemannMapping.im_mul_exp_real (c : ℂ) (θ : ℝ) :
    (c * Complex.exp ((θ : ℂ) * Complex.I)).im = ‖c‖ * Real.sin (c.arg + θ) := by
  calc
    (c * Complex.exp ((θ : ℂ) * Complex.I)).im =
        (((‖c‖ : ℝ) : ℂ) *
            (Complex.exp ((c.arg : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I))).im := by
      rw [← mul_assoc, Complex.norm_mul_exp_arg_mul_I]
    _ = (((‖c‖ : ℝ) : ℂ) * Complex.exp (((c.arg + θ : ℝ) : ℂ) * Complex.I)).im := by
      rw [← Complex.exp_add]
      congr 3
      push_cast
      ring
    _ = ‖c‖ * Real.sin (c.arg + θ) := by rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- The imaginary part of a scaled exponential power. -/
theorem RiemannMapping.im_mul_exp_real_pow (c : ℂ) (θ : ℝ) (n : ℕ) :
    (c * Complex.exp ((θ : ℂ) * Complex.I) ^ n).im = ‖c‖ * Real.sin (c.arg + (n : ℝ) * θ) := by
  rw [← Complex.exp_nat_mul]
  have h : (n : ℂ) * ((θ : ℂ) * Complex.I) = (((n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact im_mul_exp_real c ((n : ℝ) * θ)

/-- A unit direction whose power lies in the upper half-plane exists. -/
theorem RiemannMapping.exists_unit_upperHalf_power_direction {c : ℂ} (hc : c ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) : ∃ v : ℂ, ‖v‖ = 1 ∧ 0 < v.im ∧ (c * v ^ n).im < 0 := by
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hc₀ : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hπ : 0 < Real.pi := Real.pi_pos
  have ha₁ : -Real.pi < c.arg := Complex.neg_pi_lt_arg c
  have ha₂ : c.arg ≤ Real.pi := Complex.arg_le_pi c
  have hπn : 2 * Real.pi ≤ Real.pi * n := by nlinarith
  by_cases ha : -(Real.pi / 2) < c.arg
  · let θ : ℝ := (3 * Real.pi / 2 - c.arg) / n
    have hθ₀ : 0 < θ := div_pos (by linarith) hn₀
    have hθπ : θ < Real.pi := by
      apply (div_lt_iff₀ hn₀).mpr
      linarith
    have hphase : c.arg + (n : ℝ) * θ = 3 * Real.pi / 2 := by
      dsimp [θ]
      rw [mul_comm (n : ℝ), div_mul_cancel₀ _ hn₀.ne']
      ring
    refine ⟨Complex.exp ((θ : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I θ, ?_, ?_⟩
    · rw [Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ
    · rw [im_mul_exp_real_pow, hphase]
      rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
        Real.sin_pi_div_two]
      linarith
  · have ha' : c.arg ≤ -(Real.pi / 2) := le_of_not_gt ha
    let θ : ℝ := (-Real.pi / 4 - c.arg) / n
    have hθ₀ : 0 < θ := div_pos (by linarith) hn₀
    have hθπ : θ < Real.pi := by
      apply (div_lt_iff₀ hn₀).mpr
      linarith
    have hphase : c.arg + (n : ℝ) * θ = -Real.pi / 4 := by
      dsimp [θ]
      rw [mul_comm (n : ℝ), div_mul_cancel₀ _ hn₀.ne']
      ring
    refine ⟨Complex.exp ((θ : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I θ, ?_, ?_⟩
    · rw [Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ
    · rw [im_mul_exp_real_pow, hphase]
      exact
        mul_neg_of_pos_of_neg hc₀ (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))

/-- A direction whose power lies in the upper half-plane exists. -/
theorem RiemannMapping.exists_upperHalf_power_direction {c : ℂ} (hc : c ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) : ∃ v : ℂ, 0 < v.im ∧ (c * v ^ n).im < 0 := by
  obtain ⟨v, _, hv, hcv⟩ := exists_unit_upperHalf_power_direction hc hn
  exact ⟨v, hv, hcv⟩

/-- The boundary ray converges to the vertex. -/
theorem RiemannMapping.tendsto_boundaryRay (a v : ℂ) :
    Filter.Tendsto (fun t : ℝ => a + (t : ℂ) * v) (𝓝[>] 0) (𝓝 a) := by
  have hc : Continuous (fun t : ℝ => a + (t : ℂ) * v) := by fun_prop
  simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

/-- The boundary ray has positive imaginary part. -/
theorem RiemannMapping.boundaryRay_im_pos {a v : ℂ} (ha : a.im = 0) (hv : 0 < v.im) {t : ℝ}
    (ht : 0 < t) : 0 < (a + (t : ℂ) * v).im := by
  simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha,
    MulZeroClass.zero_mul, MulZeroClass.mul_zero, add_zero, zero_add] using mul_pos ht hv

/-- The analytic order at an upper-half-plane boundary point is finite. -/
theorem RiemannMapping.analyticOrderAt_ne_top_of_upper_halfPlane {f : ℂ → ℂ} {a : ℂ}
    (ha : a.im = 0) (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) : analyticOrderAt f a ≠ ⊤ := by
  intro htop
  have hz := (tendsto_boundaryRay a Complex.I).eventually (analyticOrderAt_eq_top.mp htop)
  have hp := (tendsto_boundaryRay a Complex.I).eventually hupper
  have hfalse : ∀ᶠ t : ℝ in 𝓝[>] 0, False := by
    filter_upwards [self_mem_nhdsWithin, hz, hp] with t ht hzero hpos
    have hi := hpos (boundaryRay_im_pos ha (by simp) ht)
    simp only [hzero, Complex.zero_im, lt_self_iff_false] at hi
  obtain ⟨t, ht⟩ := hfalse.exists
  exact ht

/-- The leading coefficient has nonnegative imaginary part. -/
theorem RiemannMapping.nonneg_im_leading_of_upper_halfPlane {f u : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (ha : a.im = 0) (hu : ContinuousAt u a) (hfactor : ∀ᶠ z in 𝓝 a, f z = (z - a) ^ m * u z)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) {v : ℂ} (hv : 0 < v.im) :
    0 ≤ (v ^ m * u a).im := by
  have hray := tendsto_boundaryRay a v
  have hlimC :
    Filter.Tendsto (fun t : ℝ => v ^ m * u (a + (t : ℂ) * v)) (𝓝[>] 0) (𝓝 (v ^ m * u a)) :=
    tendsto_const_nhds.mul (hu.tendsto.comp hray)
  have hlim :
    Filter.Tendsto (fun t : ℝ => (v ^ m * u (a + (t : ℂ) * v)).im) (𝓝[>] 0)
      (𝓝 (v ^ m * u a).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hlimC
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, hray.eventually hfactor, hray.eventually hupper] with t ht
    hft hpos
  have hft' : (f (a + (t : ℂ) * v)).im = t ^ m * (v ^ m * u (a + (t : ℂ) * v)).im := by
    rw [hft, add_sub_cancel_left, mul_pow, mul_assoc]
    simp only [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      MulZeroClass.zero_mul, add_zero]
  have hp : 0 < t ^ m * (v ^ m * u (a + (t : ℂ) * v)).im := by
    rw [← hft']
    exact hpos (boundaryRay_im_pos ha hv ht)
  exact ((mul_pos_iff_of_pos_left (pow_pos ht m)).mp hp).le

/-- The analytic order at the boundary is one. -/
theorem RiemannMapping.analyticOrderAt_eq_one_of_upper_halfPlane {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (ha : a.im = 0) (hfa : f a = 0)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) : analyticOrderAt f a = 1 := by
  have hfin := analyticOrderAt_ne_top_of_upper_halfPlane ha hupper
  let m := analyticOrderNatAt f a
  have horder : (m : ℕ∞) = analyticOrderAt f a := Nat.cast_analyticOrderNatAt hfin
  have hm0 : m ≠ 0 := by
    intro hm
    have hf0 : analyticOrderAt f a = 0 := by simpa [hm] using horder.symm
    exact (hf.analyticOrderAt_ne_zero.mpr hfa) hf0
  obtain ⟨u, hu, hua, hfactor⟩ := hf.analyticOrderAt_eq_natCast.mp horder.symm
  have hm2 : ¬2 ≤ m := by
    intro hm
    obtain ⟨v, hv, hneg⟩ := exists_upperHalf_power_direction hua hm
    have hnonneg : 0 ≤ (v ^ m * u a).im :=
      nonneg_im_leading_of_upper_halfPlane ha hu.continuousAt
        (by simpa only [smul_eq_mul] using hfactor) hupper hv
    rw [mul_comm] at hneg
    exact hneg.not_ge hnonneg
  have hm : m = 1 := by omega
  rw [← horder, hm]
  rfl

/-- The derivative at an upper-half-plane boundary point is nonzero. -/
theorem RiemannMapping.deriv_ne_zero_of_upper_halfPlane {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (ha : a.im = 0) (hfa : f a = 0)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) : deriv f a ≠ 0 := by
  have ho := analyticOrderAt_eq_one_of_upper_halfPlane hf ha hfa hupper
  have hd := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp ho
  simpa only [iteratedDeriv_one] using hd.2

/-- The boundary logarithm near a vertex. -/
def RiemannMapping.boundaryLog (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  -Complex.I * Complex.log (f z / f a)

/-- The boundary logarithm computes on the point. -/
@[simp]
theorem RiemannMapping.boundaryLog_self {f : ℂ → ℂ} {a : ℂ} (hfa : f a ≠ 0) :
    boundaryLog f a a = 0 := by simp [boundaryLog, hfa]

/-- The boundary logarithm is analytic. -/
theorem RiemannMapping.analyticAt_boundaryLog {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hfa : f a ≠ 0) : AnalyticAt ℂ (boundaryLog f a) a := by
  have hratio : AnalyticAt ℂ (fun z => f z / f a) a := hf.div_const
  have hslit : f a / f a ∈ Complex.slitPlane := by simp [hfa]
  exact analyticAt_const.mul (hratio.clog hslit)

/-- The boundary logarithm is differentiable. -/
theorem RiemannMapping.hasDerivAt_boundaryLog {f : ℂ → ℂ} {a d : ℂ} (hf : HasDerivAt f d a)
    (hfa : f a ≠ 0) : HasDerivAt (boundaryLog f a) (-Complex.I * (d / f a)) a := by
  have hslit : f a / f a ∈ Complex.slitPlane := by simp [hfa]
  have hlog := (hf.div_const (f a)).clog hslit
  change HasDerivAt (fun z => -Complex.I * Complex.log (f z / f a)) (-Complex.I * (d / f a)) a
  simpa only [div_self hfa, div_one] using hlog.const_mul (-Complex.I)

/-- The boundary logarithm has positive imaginary part. -/
theorem RiemannMapping.im_boundaryLog_pos {f : ℂ → ℂ} {a z : ℂ} (hfa : ‖f a‖ = 1) (hfz : f z ≠ 0)
    (hz : ‖f z‖ < 1) : 0 < (boundaryLog f a z).im := by
  have hfa0 : f a ≠ 0 := by
    intro hzero
    simp [hzero] at hfa
  have hratio0 : 0 < ‖f z / f a‖ := norm_pos_iff.mpr (div_ne_zero hfz hfa0)
  have hratio1 : ‖f z / f a‖ < 1 := by simpa only [norm_div, hfa, div_one] using hz
  have hlog := Real.log_neg hratio0 hratio1
  simpa [boundaryLog, Complex.mul_im, Complex.log_re] using neg_pos.mpr hlog

/-- The disc map's derivative is nonzero at the boundary. -/
theorem RiemannMapping.deriv_ne_zero_of_upper_halfPlane_to_unitDisc {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (ha : a.im = 0) (hfa : ‖f a‖ = 1)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → ‖f z‖ < 1) : deriv f a ≠ 0 := by
  have hfa0 : f a ≠ 0 := by
    intro hzero
    simp [hzero] at hfa
  have hnz : ∀ᶠ z in 𝓝 a, f z ≠ 0 := hf.continuousAt.eventually_ne hfa0
  have hlogUpper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (boundaryLog f a z).im := by
    filter_upwards [hupper, hnz] with z hz hzne hzim
    exact im_boundaryLog_pos hfa hzne (hz hzim)
  have hlogDeriv :=
    deriv_ne_zero_of_upper_halfPlane (analyticAt_boundaryLog hf hfa0) ha (boundaryLog_self hfa0)
      hlogUpper
  intro hderiv
  apply hlogDeriv
  simpa [hderiv] using (hasDerivAt_boundaryLog hf.differentiableAt.hasDerivAt hfa0).deriv

/-- A boundary chart maps into a ball at the target. -/
theorem RiemannMapping.exists_boundary_chart_target_ball (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ w ∈ Metric.ball (e a) δ, w ∈ e.target ∧ e.symm w ∈ Metric.ball a r := by
  have hat := e.map_source ha
  have hinv : Filter.Tendsto e.symm (𝓝 (e a)) (𝓝 a) := by
    have h := (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hat)).tendsto
    rwa [e.left_inv ha] at h
  have hnear : ∀ᶠ w in 𝓝 (e a), w ∈ e.target ∧ e.symm w ∈ Metric.ball a r := by
    filter_upwards [e.open_target.mem_nhds hat, hinv.eventually (Metric.ball_mem_nhds a hr)] with
      w hw hb
    exact ⟨hw, hb⟩
  exact Metric.mem_nhds_iff.mp hnear

/-! ### Principal roots and sector maps -/

/-- The principal `n`-th root. -/
def RiemannBoundary.principalRoot (n : ℕ) (z : ℂ) : ℂ :=
  z ^ ((n : ℂ)⁻¹)

/-- The principal root raised to `n` is the argument. -/
@[simp]
theorem RiemannBoundary.principalRoot_pow {n : ℕ} (hn : 0 < n) (z : ℂ) :
    principalRoot n z ^ n = z :=
  Complex.cpow_nat_inv_pow z hn.ne'

/-- The principal root of zero is zero. -/
@[simp]
theorem RiemannBoundary.principalRoot_zero {n : ℕ} (hn : 0 < n) : principalRoot n 0 = 0 := by
  exact Complex.zero_cpow (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne'))

/-- The principal root is injective. -/
theorem RiemannBoundary.principalRoot_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (principalRoot n) := by
  intro z w h
  simpa only [principalRoot_pow hn] using congrArg (fun u : ℂ => u ^ n) h

/-- The principal root vanishes only at zero. -/
@[simp]
theorem RiemannBoundary.principalRoot_eq_zero_iff {n : ℕ} (hn : 0 < n) {z : ℂ} :
    principalRoot n z = 0 ↔ z = 0 := by
  have h : principalRoot n z = principalRoot n 0 ↔ z = 0 := (principalRoot_injective hn).eq_iff
  simpa only [principalRoot_zero hn] using h

/-- The norm of the principal root. -/
@[simp]
theorem RiemannBoundary.norm_principalRoot (n : ℕ) (z : ℂ) :
    ‖principalRoot n z‖ = ‖z‖ ^ ((n : ℝ)⁻¹) :=
  Complex.norm_cpow_inv_nat z n

/-- The principal root's exponent has positive real part on the sector. -/
theorem RiemannBoundary.principalRoot_exponent_re_pos {n : ℕ} (hn : 0 < n) :
    0 < ((n : ℂ)⁻¹).re := by
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re] using
    inv_pos.mpr (Nat.cast_pos.mpr hn : (0 : ℝ) < n)

/-- The principal root is continuous at zero. -/
theorem RiemannBoundary.continuousAt_principalRoot_zero {n : ℕ} (hn : 0 < n) :
    ContinuousAt (principalRoot n) 0 :=
  Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp))
    (principalRoot_exponent_re_pos hn)

/-- The principal root is continuous on the closed upper half-plane. -/
theorem RiemannBoundary.continuousOn_principalRoot_closedUpper {n : ℕ} (hn : 0 < n) :
    ContinuousOn (principalRoot n) {z : ℂ | 0 ≤ z.im} := by
  intro z _hz
  change ContinuousWithinAt (fun w : ℂ => w ^ ((n : ℂ)⁻¹)) _ z
  by_cases h : 0 ≤ z.re ∨ z.im ≠ 0
  · exact
      (Complex.continuousAt_cpow_const_of_re_pos h
          (principalRoot_exponent_re_pos hn)).continuousWithinAt
  push Not at h
  have hz0 : z ≠ 0 := fun hz => by simpa only [hz, Complex.zero_re, lt_self_iff_false] using h.1
  have hc :
    ContinuousWithinAt (fun w : ℂ => Complex.exp (Complex.log w * (n : ℂ)⁻¹)) {w : ℂ | 0 ≤ w.im}
      z :=
    Complex.continuous_exp.continuousAt.comp_continuousWithinAt
      ((Complex.continuousWithinAt_log_of_re_neg_of_im_zero h.1 h.2).mul_const _)
  exact
    hc.congr_of_eventuallyEq ((cpow_eq_nhds hz0).filter_mono nhdsWithin_le_nhds)
      (Complex.cpow_def_of_ne_zero hz0 _)

/-- The principal root is differentiable on the open upper half-plane. -/
theorem RiemannBoundary.differentiableOn_principalRoot_upper (n : ℕ) :
    DifferentiableOn ℂ (principalRoot n) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact
    ((differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ => w) z).cpow_const
        (Or.inr (ne_of_gt hz))).differentiableWithinAt

/-- The principal root is analytic on the upper half-plane. -/
theorem RiemannBoundary.analyticOnNhd_principalRoot_upper (n : ℕ) :
    AnalyticOnNhd ℂ (principalRoot n) {z : ℂ | 0 < z.im} :=
  (differentiableOn_principalRoot_upper n).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_im)

/-- The principal root of a nonnegative real is nonnegative. -/
theorem RiemannBoundary.principalRoot_ofReal_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    principalRoot n (x : ℂ) = (x ^ ((n : ℝ)⁻¹) : ℝ) := by
  simpa only [principalRoot, Complex.ofReal_inv, Complex.ofReal_natCast] using
    (Complex.ofReal_cpow hx ((n : ℝ)⁻¹)).symm

/-- The principal root of a nonpositive real has controlled argument. -/
theorem RiemannBoundary.principalRoot_ofReal_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    principalRoot n (x : ℂ) =
      ((-x) ^ ((n : ℝ)⁻¹) : ℝ) * Complex.exp ((Real.pi / (n : ℝ) : ℝ) * Complex.I) := by
  rw [principalRoot, Complex.ofReal_cpow_of_nonpos hx]
  have hr : (-(x : ℂ)) ^ ((n : ℂ)⁻¹) = ((-x) ^ ((n : ℝ)⁻¹) : ℝ) := by
    simpa only [principalRoot, Complex.ofReal_neg] using
      principalRoot_ofReal_nonneg n (neg_nonneg.mpr hx)
  rw [hr]
  congr 2
  simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

/-- The divided argument lies in the standard interval. -/
theorem RiemannBoundary.arg_div_nat_mem_Ioc {n : ℕ} (hn : 0 < n) (z : ℂ) :
    z.arg / (n : ℝ) ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · rw [lt_div_iff₀ hnR]
    have hl : -Real.pi * (n : ℝ) ≤ -Real.pi := by nlinarith [Real.pi_pos]
    exact hl.trans_lt (Complex.neg_pi_lt_arg z)
  · rw [div_le_iff₀ hnR]
    have hu : Real.pi ≤ Real.pi * (n : ℝ) := by nlinarith [Real.pi_pos]
    exact (Complex.arg_le_pi z).trans hu

/-- The argument of the principal root is the divided argument. -/
theorem RiemannBoundary.arg_principalRoot {n : ℕ} (hn : 0 < n) (z : ℂ) :
    Complex.arg (principalRoot n z) = z.arg / (n : ℝ) := by
  by_cases hz : z = 0
  · simp only [hz, principalRoot_zero hn, Complex.arg_zero, zero_div]
  have hpolar :
    principalRoot n z =
      (‖z‖ ^ ((n : ℝ)⁻¹) : ℝ) *
        (Real.cos (z.arg / (n : ℝ)) + Real.sin (z.arg / (n : ℝ)) * Complex.I) := by
    simpa only [principalRoot, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv] using
      Complex.cpow_ofReal z ((n : ℝ)⁻¹)
  rw [hpolar]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_mul_cos_add_sin_mul_I (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) ((n : ℝ)⁻¹))
      (arg_div_nat_mem_Ioc hn z)

/-- The principal root's argument lies in the open sector. -/
theorem RiemannBoundary.principalRoot_arg_mem_Ioo {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : 0 < z.im) :
    Complex.arg (principalRoot n z) ∈ Set.Ioo 0 (Real.pi / (n : ℝ)) := by
  rw [arg_principalRoot hn]
  have harg0 : z.arg ≠ 0 := fun h => (ne_of_gt hz) (Complex.arg_eq_zero_iff.mp h).2
  have harg : 0 < z.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) harg0.symm
  exact
    ⟨div_pos harg (Nat.cast_pos.mpr hn),
      (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hn)).mpr
        (Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hz)))⟩

/-- The principal-root power on the sector. -/
theorem RiemannBoundary.principalRoot_pow_of_sector {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z.arg ∈ Set.Icc 0 (Real.pi / (n : ℝ))) : principalRoot n (z ^ n) = z := by
  apply Complex.pow_cpow_nat_inv hn.ne' _ hz.2
  exact (neg_neg_of_pos (div_pos Real.pi_pos (Nat.cast_pos.mpr hn))).trans_le hz.1

/-- The cubic sector leaves angular slack. -/
theorem RiemannBoundary.cubic_sector_slack (w : ℂ) :
    3 * w.re - Real.sqrt 3 * w.im = (2 * Real.sqrt 3 * ‖w‖) * Real.sin (Real.pi / 3 - w.arg) := by
  rw [Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three]
  rw [← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  calc
    3 * (‖w‖ * Real.cos w.arg) - Real.sqrt 3 * (‖w‖ * Real.sin w.arg) =
        ‖w‖ * ((Real.sqrt 3 * Real.sqrt 3) * Real.cos w.arg - Real.sqrt 3 * Real.sin w.arg) := by
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    _ = _ := by ring

/-- The quartic sector leaves angular slack. -/
theorem RiemannBoundary.quartic_sector_slack (w : ℂ) :
    w.re - w.im = (Real.sqrt 2 * ‖w‖) * Real.sin (Real.pi / 4 - w.arg) := by
  rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
  rw [← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  calc
    ‖w‖ * Real.cos w.arg - ‖w‖ * Real.sin w.arg =
        (‖w‖ / 2) *
          ((Real.sqrt 2 * Real.sqrt 2) * Real.cos w.arg -
            (Real.sqrt 2 * Real.sqrt 2) * Real.sin w.arg) := by
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ = _ := by ring

/-- The cube root maps the upper half-plane to a sector. -/
theorem RiemannBoundary.principalRoot_three_upper {z : ℂ} (hz : 0 < z.im) :
    0 < (principalRoot 3 z).im ∧
      Real.sqrt 3 * (principalRoot 3 z).im < 3 * (principalRoot 3 z).re := by
  have ha := principalRoot_arg_mem_Ioo (by norm_num : 0 < 3) hz
  norm_num only [Nat.cast_ofNat] at ha
  have hw : principalRoot 3 z ≠ 0 := by
    rw [ne_eq, principalRoot_eq_zero_iff (by norm_num : 0 < 3)]
    exact fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hz
  constructor
  · rw [← Complex.norm_mul_sin_arg]
    exact
      mul_pos (norm_pos_iff.mpr hw)
        (Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos, ha.2]))
  · apply sub_pos.mp
    rw [cubic_sector_slack]
    exact
      mul_pos
        (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) (norm_pos_iff.mpr hw))
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.2]) (by linarith [Real.pi_pos, ha.1]))

/-- The cube root of a nonnegative real has zero imaginary part. -/
theorem RiemannBoundary.principalRoot_three_ofReal_nonneg_im {x : ℝ} (hx : 0 ≤ x) :
    (principalRoot 3 (x : ℂ)).im = 0 := by
  rw [principalRoot_ofReal_nonneg 3 hx]
  exact Complex.ofReal_im _

/-- The cube root of a nonpositive real lies on the sector boundary. -/
theorem RiemannBoundary.principalRoot_three_ofReal_nonpos_boundary {x : ℝ} (hx : x ≤ 0) :
    Real.sqrt 3 * (principalRoot 3 (x : ℂ)).im = 3 * (principalRoot 3 (x : ℂ)).re := by
  rw [principalRoot_ofReal_nonpos 3 hx]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    MulZeroClass.zero_mul, add_zero, sub_zero, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re, Nat.cast_ofNat, Real.sin_pi_div_three, Real.cos_pi_div_three]
  have hsq := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  calc
    Real.sqrt 3 * ((-x) ^ (3 : ℝ)⁻¹ * (Real.sqrt 3 / 2)) =
        (Real.sqrt 3 * Real.sqrt 3) * ((-x) ^ (3 : ℝ)⁻¹ / 2) := by ring
    _ = _ := by rw [hsq]; ring

/-- The cube root maps the real axis to the sector boundary. -/
theorem RiemannBoundary.principalRoot_three_real_boundary {z : ℂ} (hz : z.im = 0) :
    (principalRoot 3 z).im = 0 ∨
      Real.sqrt 3 * (principalRoot 3 z).im = 3 * (principalRoot 3 z).re := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  rcases le_total 0 z.re with hp | hn
  · exact Or.inl (principalRoot_three_ofReal_nonneg_im hp)
  · exact Or.inr (principalRoot_three_ofReal_nonpos_boundary hn)

/-! ### The rotated quartic root -/

/-- The rotation aligning the quartic root with the sector. -/
def RiemannBoundary.quarticRootRotation : ℂ :=
  Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- The real part of the quartic rotation. -/
@[simp]
theorem RiemannBoundary.quarticRootRotation_re : quarticRootRotation.re = Real.sqrt 2 / 2 := by
  simp only [quarticRootRotation, Complex.exp_ofReal_mul_I_re, neg_div, Real.cos_neg,
    Real.cos_pi_div_four]

/-- The imaginary part of the quartic rotation. -/
@[simp]
theorem RiemannBoundary.quarticRootRotation_im : quarticRootRotation.im = -(Real.sqrt 2 / 2) := by
  simp only [quarticRootRotation, Complex.exp_ofReal_mul_I_im, neg_div, Real.sin_neg,
    Real.sin_pi_div_four]

/-- The quartic rotation has norm one. -/
@[simp]
theorem RiemannBoundary.norm_quarticRootRotation : ‖quarticRootRotation‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The quartic rotation is nonzero. -/
theorem RiemannBoundary.quarticRootRotation_ne_zero : quarticRootRotation ≠ 0 :=
  Complex.exp_ne_zero _

/-- The fourth power of the quartic rotation. -/
@[simp]
theorem RiemannBoundary.quarticRootRotation_pow_four : quarticRootRotation ^ 4 = -1 := by
  rw [quarticRootRotation, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (4 : ℂ) * (((-Real.pi / 4 : ℝ) : ℂ) * Complex.I) = -(Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- The rotated principal fourth root. -/
def RiemannBoundary.rotatedPrincipalRootFour (z : ℂ) : ℂ :=
  quarticRootRotation * principalRoot 4 z

/-- The rotated fourth root raised to four. -/
@[simp]
theorem RiemannBoundary.rotatedPrincipalRootFour_pow (z : ℂ) :
    rotatedPrincipalRootFour z ^ 4 = -z := by
  rw [rotatedPrincipalRootFour, mul_pow, quarticRootRotation_pow_four,
    principalRoot_pow (by norm_num : 0 < 4)]
  ring

/-- The rotated fourth root of zero is zero. -/
@[simp]
theorem RiemannBoundary.rotatedPrincipalRootFour_zero : rotatedPrincipalRootFour 0 = 0 := by
  rw [rotatedPrincipalRootFour, principalRoot_zero (by norm_num : 0 < 4), MulZeroClass.mul_zero]

/-- The norm of the rotated fourth root. -/
@[simp]
theorem RiemannBoundary.norm_rotatedPrincipalRootFour (z : ℂ) :
    ‖rotatedPrincipalRootFour z‖ = ‖z‖ ^ (4 : ℝ)⁻¹ := by
  rw [rotatedPrincipalRootFour, norm_mul, norm_quarticRootRotation, one_mul, norm_principalRoot]
  norm_num only [Nat.cast_ofNat]

/-- The real part of the rotated fourth root. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_re (z : ℂ) :
    (rotatedPrincipalRootFour z).re =
      (Real.sqrt 2 / 2) * ((principalRoot 4 z).re + (principalRoot 4 z).im) := by
  simp only [rotatedPrincipalRootFour, Complex.mul_re, quarticRootRotation_re,
    quarticRootRotation_im]
  ring

/-- The imaginary part of the rotated fourth root. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_im (z : ℂ) :
    (rotatedPrincipalRootFour z).im =
      (Real.sqrt 2 / 2) * ((principalRoot 4 z).im - (principalRoot 4 z).re) := by
  simp only [rotatedPrincipalRootFour, Complex.mul_im, quarticRootRotation_re,
    quarticRootRotation_im]
  ring

/-- The sum of real and imaginary parts of the rotated fourth root. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_re_add_im (z : ℂ) :
    (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im =
      Real.sqrt 2 * (principalRoot 4 z).im := by
  rw [rotatedPrincipalRootFour_re, rotatedPrincipalRootFour_im]
  ring

/-- The rotated fourth root maps the upper half-plane into the sector. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_upper {z : ℂ} (hz : 0 < z.im) :
    (rotatedPrincipalRootFour z).im < 0 ∧
      0 < (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im := by
  have ha := principalRoot_arg_mem_Ioo (by norm_num : 0 < 4) hz
  norm_num only [Nat.cast_ofNat] at ha
  have hw : principalRoot 4 z ≠ 0 := by
    rw [ne_eq, principalRoot_eq_zero_iff (by norm_num : 0 < 4)]
    exact fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hz
  have hi : 0 < (principalRoot 4 z).im := by
    rw [← Complex.norm_mul_sin_arg]
    exact
      mul_pos (norm_pos_iff.mpr hw)
        (Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos, ha.2]))
  have hri : (principalRoot 4 z).im < (principalRoot 4 z).re := by
    apply sub_pos.mp
    rw [quartic_sector_slack]
    exact
      mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (norm_pos_iff.mpr hw))
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.2]) (by linarith [Real.pi_pos, ha.1]))
  constructor
  · rw [rotatedPrincipalRootFour_im]
    exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hri)
  · rw [rotatedPrincipalRootFour_re_add_im]
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hi

/-- The rotated fourth root of a nonnegative real lies on the boundary ray. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonneg_boundary {x : ℝ} (hx : 0 ≤ x) :
    (rotatedPrincipalRootFour (x : ℂ)).re + (rotatedPrincipalRootFour (x : ℂ)).im = 0 := by
  rw [rotatedPrincipalRootFour_re_add_im, principalRoot_ofReal_nonneg 4 hx]
  simp only [Complex.ofReal_im, MulZeroClass.mul_zero]

/-- The rotated fourth root of a nonpositive real has controlled imaginary part. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonpos_im {x : ℝ} (hx : x ≤ 0) :
    (rotatedPrincipalRootFour (x : ℂ)).im = 0 := by
  rw [rotatedPrincipalRootFour_im, principalRoot_ofReal_nonpos 4 hx]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    MulZeroClass.zero_mul, add_zero, sub_zero, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re, Nat.cast_ofNat, Real.sin_pi_div_four, Real.cos_pi_div_four,
    sub_self, MulZeroClass.mul_zero]

/-- The rotated fourth root maps the real axis to the sector boundary. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_real_boundary {z : ℂ} (hz : z.im = 0) :
    (rotatedPrincipalRootFour z).im = 0 ∨
      (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im = 0 := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  rcases le_total 0 z.re with hp | hn
  · exact Or.inr (rotatedPrincipalRootFour_ofReal_nonneg_boundary hp)
  · exact Or.inl (rotatedPrincipalRootFour_ofReal_nonpos_im hn)

/-- The rotated fourth root is continuous on the closed upper half-plane. -/
theorem RiemannBoundary.continuousOn_rotatedPrincipalRootFour_closedUpper :
    ContinuousOn rotatedPrincipalRootFour {z : ℂ | 0 ≤ z.im} :=
  continuousOn_const.mul (continuousOn_principalRoot_closedUpper (by norm_num : 0 < 4))

/-- The rotated fourth root is continuous at zero. -/
theorem RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero :
    ContinuousAt rotatedPrincipalRootFour 0 :=
  continuousAt_const.mul (continuousAt_principalRoot_zero (by norm_num : 0 < 4))

/-- The rotated fourth root is analytic on the upper half-plane. -/
theorem RiemannBoundary.analyticOnNhd_rotatedPrincipalRootFour_upper :
    AnalyticOnNhd ℂ rotatedPrincipalRootFour {z : ℂ | 0 < z.im} := by
  intro z hz
  exact analyticAt_const.mul (analyticOnNhd_principalRoot_upper 4 z hz)

/-! ### Conformal extension across the boundary -/

/-- Near the boundary point `|z|<1` is eventually the upper half-plane. -/
theorem RiemannBoundary.norm_lt_one_iff_im_pos_eventually {H k : ℂ → ℂ} {x : ℝ}
    (hH : ContinuousAt H (x : ℂ)) (hcenter : ‖H (x : ℂ)‖ = 1)
    (hk : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖k z‖ < 1) (hu : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → H z = k z)
    (hl : ∀ᶠ z in 𝓝 (x : ℂ), z.im < 0 → H z = (conj (k (conj z)))⁻¹)
    (hr : ∀ᶠ z in 𝓝 (x : ℂ), z.im = 0 → ‖H z‖ = 1) : ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  have hcenter0 : H (x : ℂ) ≠ 0 := by
    intro hzero
    simp [hzero] at hcenter
  have hnz := hH.eventually_ne hcenter0
  have hconj : Filter.Tendsto (conj : ℂ → ℂ) (𝓝 (x : ℂ)) (𝓝 (x : ℂ)) := by
    simpa only [Complex.conj_ofReal] using Complex.continuous_conj.tendsto (x : ℂ)
  have hkc := hconj.eventually hk
  filter_upwards [hk, hu, hl, hr, hnz, hkc] with z hzk hzu hzl hzr hzne hzconj
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · have hw : ‖k (conj z)‖ < 1 := hzconj (by simpa using hneg)
    have hw0 : k (conj z) ≠ 0 := by
      intro heq
      apply hzne
      rw [hzl hneg, heq]
      simp
    have hlarge : 1 < ‖H z‖ := by
      rw [hzl hneg, norm_inv, Complex.norm_conj]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hw0)).mpr hw
    exact iff_of_false (not_lt_of_ge hlarge.le) (not_lt_of_ge hneg.le)
  · rw [hzr hzero]
    simp only [lt_self_iff_false, hzero]
  · rw [hzu hpos]
    exact iff_of_true (hzk hpos) hpos

/-- A modulus-one boundary trace gives a conformal extension. -/
theorem RiemannBoundary.exists_conformal_extension_of_modulus_one {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} {x : ℝ} (hx : (x : ℂ) ∈ U) (hf : DifferentiableOn ℂ f (U ∩ {z : ℂ | 0 < z.im}))
    (hmod :
      ∀ t : ℝ,
        (t : ℂ) ∈ U → Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1))
    (hdisc : ∀ z ∈ U ∩ {z : ℂ | 0 < z.im}, ‖f z‖ < 1) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (x : ℂ) r) ∧
          Set.EqOn H f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (conj z)))⁻¹)
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H (x : ℂ)) (x : ℂ) ∧
                  deriv H (x : ℂ) ≠ 0 ∧ ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  obtain ⟨r, hr, H, hHa, hHe, hHl, hHc⟩ := exists_analytic_extension_of_modulus_one hU hx hf hmod
  have hHx := hHa (x : ℂ) (Metric.mem_ball_self hr)
  have hcenter := hHc x (Metric.mem_ball_self hr)
  have hk : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖f z‖ < 1 := by
    filter_upwards [hU.mem_nhds hx] with z hz hpos
    exact hdisc z ⟨hz, hpos⟩
  have hu : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → H z = f z := by
    filter_upwards [Metric.ball_mem_nhds (x : ℂ) hr] with z hz hpos
    exact hHe ⟨hz, hpos⟩
  have hl : ∀ᶠ z in 𝓝 (x : ℂ), z.im < 0 → H z = (conj (f (conj z)))⁻¹ := by
    filter_upwards [Metric.ball_mem_nhds (x : ℂ) hr] with z hz hneg
    exact hHl ⟨hz, hneg⟩
  have hreal : ∀ᶠ z in 𝓝 (x : ℂ), z.im = 0 → ‖H z‖ = 1 := by
    filter_upwards [Metric.ball_mem_nhds (x : ℂ) hr] with z hz hzero
    have heq : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hzero.symm)
    simpa only [heq] using hHc z.re (by simpa only [heq] using hz)
  have hinside : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖H z‖ < 1 := by
    filter_upwards [hu, hk] with z heq hz hpos
    rw [heq hpos]
    exact hz hpos
  have hnonzero :=
    RiemannMapping.deriv_ne_zero_of_upper_halfPlane_to_unitDisc hHx (by simp) hcenter hinside
  exact
    ⟨r, hr, H, hHa, hHe, hHl, hHc, hHx.hasStrictDerivAt, hnonzero,
      norm_lt_one_iff_im_pos_eventually hHx.continuousAt hcenter hk hu hl hreal⟩

/-- The disc map extends conformally in the half chart. -/
theorem RiemannBoundary.exists_conformal_extension_discHomeomorph_in_half_chart {D U : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f φ : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f D) (hφ : DifferentiableOn ℂ φ (U ∩ {z : ℂ | 0 < z.im}))
    (hφc : ContinuousOn φ (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hside : Set.MapsTo φ (U ∩ {z : ℂ | 0 < z.im}) D)
    (hout : ∀ t : ℝ, (t : ℂ) ∈ U → φ (t : ℂ) ∉ D) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (x : ℂ) r) ∧
          Set.EqOn H (f ∘ φ) (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (φ (conj z))))⁻¹)
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H (x : ℂ)) (x : ℂ) ∧
                  deriv H (x : ℂ) ≠ 0 ∧ ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  apply exists_conformal_extension_of_modulus_one hU hx (hf.comp hφ hside)
  · intro t ht
    exact tendsto_norm_discHomeomorph_in_boundary_chart e he hU hφc hside ht (hout t ht)
  · intro z hz
    have hp := hside hz
    have hv := he ⟨φ z, hp⟩
    simpa only [Function.comp_def, Metric.mem_ball, dist_zero_right, ← hv] using
      (e ⟨φ z, hp⟩).property

/-- The inverse disc homeomorphism at a boundary point. -/
def RiemannBoundary.discHomeomorphInverse {X : Type*} [TopologicalSpace X] {D : Set X}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (z : ℂ) : X := by
  classical
    exact
    if hz : z ∈ Metric.ball (0 : ℂ) 1 then (e.symm ⟨z, hz⟩ : X) else (e.symm ⟨0, by simp⟩ : X)

/-- The inverse disc map computes on the image. -/
theorem RiemannBoundary.discHomeomorphInverse_of_mem {X : Type*} [TopologicalSpace X] {D : Set X}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discHomeomorphInverse e z = (e.symm ⟨z, hz⟩ : X) := by
  simp only [discHomeomorphInverse, dif_pos hz]

/-- The inverse disc map converges in the boundary chart. -/
theorem RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart {X : Type*}
    [TopologicalSpace X] {D : Set X} (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : X → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) {φ : ℂ → X} {H : ℂ → ℂ} {d : ℂ} (hφ : ContinuousAt φ 0)
    (hH : HasStrictDerivAt H d 0) (hd : d ≠ 0)
    (hcoord : ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 → φ z ∈ D ∧ f (φ z) = H z) :
    Filter.Tendsto (discHomeomorphInverse e) (𝓝[Metric.ball (0 : ℂ) 1] (H 0)) (𝓝 (φ 0)) := by
  let k := hH.localInverse H d 0 hd
  have hk0 : k (H 0) = 0 := hH.eventually_left_inverse hd |>.self_of_nhds
  have hk : Filter.Tendsto k (𝓝 (H 0)) (𝓝 (0 : ℂ)) := by
    have ht : Filter.Tendsto k (𝓝 (H 0)) (𝓝 (k (H 0))) :=
      (hH.to_localInverse hd).hasDerivAt.continuousAt.tendsto
    rwa [hk0] at ht
  have ht : Filter.Tendsto (φ ∘ k) (𝓝[Metric.ball (0 : ℂ) 1] (H 0)) (𝓝 (φ 0)) :=
    (hφ.tendsto.comp hk).mono_left nhdsWithin_le_nhds
  have heq : discHomeomorphInverse e =ᶠ[𝓝[Metric.ball (0 : ℂ) 1] (H 0)] φ ∘ k := by
    have hright : ∀ᶠ y in 𝓝[Metric.ball (0 : ℂ) 1] (H 0), H (k y) = y :=
      (hH.eventually_right_inverse hd).filter_mono nhdsWithin_le_nhds
    have hparam :
      ∀ᶠ y in 𝓝[Metric.ball (0 : ℂ) 1] (H 0),
        ‖H (k y)‖ < 1 → φ (k y) ∈ D ∧ f (φ (k y)) = H (k y) :=
      (hk.eventually hcoord).filter_mono nhdsWithin_le_nhds
    filter_upwards [hright, hparam, self_mem_nhdsWithin] with y hy hcy hyD
    have hyn : ‖y‖ < 1 := by simpa using hyD
    obtain ⟨hmem, hval⟩ := hcy (by simpa only [hy] using hyn)
    have himage : e ⟨φ (k y), hmem⟩ = ⟨y, hyD⟩ := by
      apply Subtype.ext
      exact (he ⟨φ (k y), hmem⟩).symm.trans (hval.trans hy)
    rw [discHomeomorphInverse_of_mem e hyD]
    change (e.symm ⟨y, hyD⟩ : X) = φ (k y)
    have hinv : e.symm ⟨y, hyD⟩ = ⟨φ (k y), hmem⟩ := by rw [← himage, e.symm_apply_apply]
    exact congrArg Subtype.val hinv
  exact ht.congr' heq.symm

/-- A unit-circle point is in the closed unit ball. -/
theorem RiemannBoundary.unitCircle_mem_closure_unitBall {w : ℂ} (hw : ‖w‖ = 1) :
    w ∈ closure (Metric.ball (0 : ℂ) 1) := by
  rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  simpa only [Metric.mem_closedBall, dist_zero_right, hw] using le_rfl (a := (1 : ℝ))

/-- Boundary points with equal disc values are equal. -/
theorem RiemannBoundary.boundary_points_eq_of_equal_disc_values {X : Type*} [TopologicalSpace X]
    {D : Set X} [T2Space X] (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : X → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) {φ ψ : ℂ → X} {F G : ℂ → ℂ} {dF dG : ℂ}
    (hφ : ContinuousAt φ 0) (hψ : ContinuousAt ψ 0) (hF : HasStrictDerivAt F dF 0) (hdF : dF ≠ 0)
    (hG : HasStrictDerivAt G dG 0) (hdG : dG ≠ 0)
    (hcoordF : ∀ᶠ z in 𝓝 (0 : ℂ), ‖F z‖ < 1 → φ z ∈ D ∧ f (φ z) = F z)
    (hcoordG : ∀ᶠ z in 𝓝 (0 : ℂ), ‖G z‖ < 1 → ψ z ∈ D ∧ f (ψ z) = G z) (hcircle : ‖F 0‖ = 1)
    (hvalue : F 0 = G 0) : φ 0 = ψ 0 := by
  have : Filter.NeBot (𝓝[Metric.ball (0 : ℂ) 1] (F 0)) :=
    (mem_closure_iff_nhdsWithin_neBot).mp (unitCircle_mem_closure_unitBall hcircle)
  have htF := tendsto_discHomeomorphInverse_of_boundary_chart e he hφ hF hdF hcoordF
  have htG := tendsto_discHomeomorphInverse_of_boundary_chart e he hψ hG hdG hcoordG
  rw [← hvalue] at htG
  exact tendsto_nhds_unique htF htG

/-- The logarithm is continuous on the closed upper half-plane. -/
theorem RiemannBoundary.continuousWithinAt_log_closedUpper {q : ℂ} (hq : q ≠ 0) :
    ContinuousWithinAt Complex.log {z : ℂ | 0 ≤ z.im} q := by
  by_cases hi : q.im = 0
  · by_cases hr : 0 < q.re
    · exact (continuousAt_clog (Or.inl hr)).continuousWithinAt
    · have hre : q.re < 0 := by
        have hne : q.re ≠ 0 := by
          intro heq
          apply hq
          exact Complex.ext heq hi
        exact lt_of_le_of_ne (le_of_not_gt hr) hne
      exact Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre hi
  · exact (continuousAt_clog (Or.inr hi)).continuousWithinAt

/-- The half-strip logarithm is continuous on the closed upper half-plane. -/
theorem RiemannBoundary.continuousWithinAt_logHalfStrip_closedUpper (a c : ℝ) {q : ℂ}
    (hq : q ≠ 0) : ContinuousWithinAt (logHalfStrip a c) {z : ℂ | 0 ≤ z.im} q := by
  exact
    continuousWithinAt_const.sub
      (continuousWithinAt_const.mul (continuousWithinAt_log_closedUpper hq))

/-- The half-strip logarithm is analytic on the upper half-plane. -/
theorem RiemannBoundary.analyticOnNhd_logHalfStrip_upper (a c : ℝ) :
    AnalyticOnNhd ℂ (logHalfStrip a c) {z : ℂ | 0 < z.im} := by
  intro q hq
  exact analyticAt_const.sub (analyticAt_const.mul (analyticAt_clog (Or.inr (ne_of_gt hq))))

/-- The half-strip real part lies in the strip interval. -/
theorem RiemannBoundary.logHalfStrip_re_mem_Ioo (a : ℝ) {c : ℝ} (hc : 0 < c) {q : ℂ}
    (hq : 0 < q.im) : (logHalfStrip a c q).re ∈ Set.Ioo a (a + c * Real.pi) := by
  have harg0 : q.arg ≠ 0 := fun h => (ne_of_gt hq) (Complex.arg_eq_zero_iff.mp h).2
  have harg : 0 < q.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hq.le) harg0.symm
  have hargπ : q.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hq))
  rw [logHalfStrip_re]
  constructor <;> nlinarith

/-- The half-strip real part of a real input. -/
theorem RiemannBoundary.logHalfStrip_real_re (a c : ℝ) (t : ℝ) :
    (logHalfStrip a c (t : ℂ)).re = a ∨ (logHalfStrip a c (t : ℂ)).re = a + c * Real.pi := by
  by_cases ht : 0 ≤ t
  · left
    simp [logHalfStrip_re, Complex.arg_ofReal_of_nonneg ht]
  · right
    simp [logHalfStrip_re, Complex.arg_ofReal_of_neg (lt_of_not_ge ht)]

/-- A half-strip height bounding the radius exists. -/
theorem RiemannBoundary.exists_logHalfStrip_height_radius (a B : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ R > 0, ∀ q ∈ Metric.ball (0 : ℂ) R, q ≠ 0 → B < (logHalfStrip a c q).im := by
  have ht : ∀ᶠ q in 𝓝[≠] (0 : ℂ), B < (logHalfStrip a c q).im :=
    (tendsto_logHalfStrip_im_atTop a hc).eventually_gt_atTop B
  obtain ⟨R, hR, hs⟩ := Metric.mem_nhdsWithin_iff.mp ht
  exact ⟨R, hR, fun q hq hne => hs ⟨hq, hne⟩⟩

/-- The disc map extends conformally at an ideal vertex. -/
theorem RiemannBoundary.exists_conformal_extension_discHomeomorph_at_ideal_vertex {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ))
    (hf : DifferentiableOn ℂ f D) (a B : ℝ) {c : ℝ} (hc : 0 < c)
    (hstrip : ∀ z : ℂ, a < z.re → z.re < a + c * Real.pi → B < z.im → z ∈ D)
    (hedge : ∀ z : ℂ, B < z.im → (z.re = a ∨ z.re = a + c * Real.pi) → z ∉ D) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) r) ∧
          Set.EqOn H (f ∘ logHalfStrip a c) (Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (logHalfStrip a c (conj z))))⁻¹)
                (Metric.ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (0 : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H 0) 0 ∧
                  deriv H 0 ≠ 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  obtain ⟨R, hR, hheight⟩ := exists_logHalfStrip_height_radius a B hc
  let U : Set ℂ := Metric.ball (0 : ℂ) R
  have hU : IsOpen U := Metric.isOpen_ball
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hR
  have hside : Set.MapsTo (logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) D := by
    intro q hq
    have hq0 : q ≠ 0 := by
      intro heq
      have hi := hq.2
      rw [heq] at hi
      exact (lt_irrefl (0 : ℝ)) hi
    have hRe := logHalfStrip_re_mem_Ioo a hc hq.2
    exact hstrip _ hRe.1 hRe.2 (hheight q hq.1 hq0)
  have hφ : DifferentiableOn ℂ (logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) :=
    (analyticOnNhd_logHalfStrip_upper a c).differentiableOn.mono Set.inter_subset_right
  have hdiff : DifferentiableOn ℂ (f ∘ logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) :=
    hf.comp hφ hside
  have hmod :
    ∀ t : ℝ,
      (t : ℂ) ∈ U →
        Filter.Tendsto (fun q => ‖f (logHalfStrip a c q)‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ))
          (𝓝 1) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      apply tendsto_norm_discHomeomorph_logHalfStrip e he a hc
      have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h0U)
      filter_upwards [hnear, self_mem_nhdsWithin] with q hq hi
      exact hside ⟨hq, hi⟩
    · let V : Set ℂ := U \ {0}
      have hV : IsOpen V := hU.sdiff isClosed_singleton
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
      have htV : (t : ℂ) ∈ V := ⟨ht, htC⟩
      have hcont : ContinuousOn (logHalfStrip a c) (V ∩ {z : ℂ | 0 ≤ z.im}) := by
        intro q hq
        exact (continuousWithinAt_logHalfStrip_closedUpper a c hq.1.2).mono Set.inter_subset_right
      have hsideV : Set.MapsTo (logHalfStrip a c) (V ∩ {z : ℂ | 0 < z.im}) D := by
        intro q hq
        exact hside ⟨hq.1.1, hq.2⟩
      exact
        tendsto_norm_discHomeomorph_in_boundary_chart e he hV hcont hsideV htV
          (hedge _ (hheight _ ht htC) (logHalfStrip_real_re a c t))
  apply exists_conformal_extension_of_modulus_one hU h0U hdiff hmod
  intro q hq
  have hp := hside hq
  have hv := he ⟨logHalfStrip a c q, hp⟩
  simpa only [Function.comp_def, Metric.mem_ball, dist_zero_right, ← hv] using
    (e ⟨logHalfStrip a c q, hp⟩).property

/-! ### The disc compactification -/

/-- The map from the domain compactification to the closed disc. -/
def RiemannBoundary.discCompactificationMap {X : Type*} [TopologicalSpace X] {D : Set X}
    (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) : X → ℂ :=
  hD.extend (fun z : D => (e z : ℂ))

/-- The compactification map computes the disc coordinate. -/
theorem RiemannBoundary.discCompactificationMap_coe {X : Type*} [TopologicalSpace X] {D : Set X}
    (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (z : D) :
    discCompactificationMap hD e z = (e z : ℂ) :=
  hD.extend_eq (continuous_subtype_val.comp e.continuous) z

/-- The disc map has limits at every boundary point. -/
def RiemannBoundary.DiscBoundaryLimits {X : Type*} [TopologicalSpace X] {D : Set X}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) : Prop :=
  ∀ x ∉ D,
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto (fun z : D => (e z : ℂ)) (Filter.comap Subtype.val (𝓝 x)) (𝓝 w) ∧
          Filter.Tendsto (discHomeomorphInverse e) (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 x)

/-- The compactification map is continuous. -/
theorem RiemannBoundary.discCompactificationMap_continuous {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    Continuous (discCompactificationMap hD e) := by
  apply hD.continuous_extend
  intro x
  by_cases hx : x ∈ D
  · refine ⟨(e ⟨x, hx⟩ : ℂ), ?_⟩
    rw [← hD.isDenseInducing_val.nhds_eq_comap ⟨x, hx⟩]
    exact (continuous_subtype_val.comp e.continuous).continuousAt
  · obtain ⟨w, _, hw, _⟩ := hb x hx
    exact ⟨w, hw⟩

/-- The compactification map on a boundary point is the limit. -/
theorem RiemannBoundary.discCompactificationMap_boundary {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e)
    {x : X} (hx : x ∉ D) :
    ‖discCompactificationMap hD e x‖ = 1 ∧
      Filter.Tendsto (discHomeomorphInverse e)
        (𝓝[Metric.ball (0 : ℂ) 1] (discCompactificationMap hD e x)) (𝓝 x) := by
  obtain ⟨w, hw, ht, hi⟩ := hb x hx
  have he : discCompactificationMap hD e x = w := hD.extend_eq_of_tendsto ht
  rw [he]
  exact ⟨hw, hi⟩

/-- The compactification map has norm at most one. -/
theorem RiemannBoundary.discCompactificationMap_norm_le {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e)
    (x : X) : ‖discCompactificationMap hD e x‖ ≤ 1 := by
  by_cases hx : x ∈ D
  · rw [discCompactificationMap_coe hD e ⟨x, hx⟩]
    exact
      (show ‖(e ⟨x, hx⟩ : ℂ)‖ < 1 by
          simpa only [Metric.mem_ball, dist_zero_right] using (e ⟨x, hx⟩).property).le
  · exact ((discCompactificationMap_boundary hD e hb hx).1).le

/-- The compactification map is injective. -/
theorem RiemannBoundary.discCompactificationMap_injective {X : Type*} [TopologicalSpace X]
    {D : Set X} [T2Space X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1)
    (hb : DiscBoundaryLimits e) : Function.Injective (discCompactificationMap hD e) := by
  intro x y hxy
  by_cases hx : x ∈ D
  · by_cases hy : y ∈ D
    · apply congrArg Subtype.val (e.injective ?_ : (⟨x, hx⟩ : D) = ⟨y, hy⟩)
      apply Subtype.ext
      simpa only [discCompactificationMap_coe hD e ⟨x, hx⟩,
        discCompactificationMap_coe hD e ⟨y, hy⟩] using hxy
    · have hn := (discCompactificationMap_boundary hD e hb hy).1
      rw [← hxy, discCompactificationMap_coe hD e ⟨x, hx⟩] at hn
      have hlt : ‖(e ⟨x, hx⟩ : ℂ)‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using (e ⟨x, hx⟩).property
      exact (hlt.ne hn).elim
  · by_cases hy : y ∈ D
    · have hn := (discCompactificationMap_boundary hD e hb hx).1
      rw [hxy, discCompactificationMap_coe hD e ⟨y, hy⟩] at hn
      have hlt : ‖(e ⟨y, hy⟩ : ℂ)‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using (e ⟨y, hy⟩).property
      exact (hlt.ne hn).elim
    · obtain ⟨hn, ht⟩ := discCompactificationMap_boundary hD e hb hx
      have hu := (discCompactificationMap_boundary hD e hb hy).2
      rw [← hxy] at hu
      have : Filter.NeBot (𝓝[Metric.ball (0 : ℂ) 1] (discCompactificationMap hD e x)) :=
        mem_closure_iff_nhdsWithin_neBot.mp (unitCircle_mem_closure_unitBall hn)
      exact tendsto_nhds_unique ht hu

/-- The compactification map has range the closed disc. -/
theorem RiemannBoundary.discCompactificationMap_range {X : Type*} [TopologicalSpace X] {D : Set X}
    [CompactSpace X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    Set.range (discCompactificationMap hD e) = Metric.closedBall (0 : ℂ) 1 := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    simpa using discCompactificationMap_norm_le hD e hb x
  · have hclosed : IsClosed (Set.range (discCompactificationMap hD e)) :=
      (isCompact_range (discCompactificationMap_continuous hD e hb)).isClosed
    have hdisc : Metric.ball (0 : ℂ) 1 ⊆ Set.range (discCompactificationMap hD e) := by
      intro y hy
      refine ⟨(e.symm ⟨y, hy⟩ : X), ?_⟩
      rw [discCompactificationMap_coe, e.apply_symm_apply]
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact closure_minimal hdisc hclosed

/-- The domain compactification is homeomorphic to the closed disc. -/
def RiemannBoundary.closedDiscHomeomorph {X : Type*} [TopologicalSpace X] {D : Set X} [T2Space X]
    [CompactSpace X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    X ≃ₜ Metric.closedBall (0 : ℂ) 1 := by
  let F : X → Metric.closedBall (0 : ℂ) 1 := fun x =>
    ⟨discCompactificationMap hD e x, by simpa using discCompactificationMap_norm_le hD e hb x⟩
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      exact discCompactificationMap_injective hD e hb (congrArg Subtype.val hxy)
    · intro y
      have hy : (y : ℂ) ∈ Set.range (discCompactificationMap hD e) := by
        rw [discCompactificationMap_range hD e hb]
        exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  exact
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hF)
      ((discCompactificationMap_continuous hD e hb).subtype_mk _)

/-- The closed-disc homeomorphism computes the compactification map. -/
theorem RiemannBoundary.closedDiscHomeomorph_coe {X : Type*} [TopologicalSpace X] {D : Set X}
    [T2Space X] [CompactSpace X] (hD : Dense D) (e : D ≃ₜ Metric.ball (0 : ℂ) 1)
    (hb : DiscBoundaryLimits e) (z : D) : (closedDiscHomeomorph hD e hb z : ℂ) = (e z : ℂ) :=
  discCompactificationMap_coe hD e z

/-! ### The triangle side parameter -/

/-- The parameter along a triangle side. -/
def RiemannMapping.triangleSideParameter (e : OpenPartialHomeomorph ℂ ℂ) (a w : ℂ) : ℂ :=
  e.symm (w + e a)

/-- The side parameter at the vertex. -/
theorem RiemannMapping.triangleSideParameter_zero (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) : triangleSideParameter e a 0 = a := by
  simp only [triangleSideParameter, zero_add, e.left_inv ha]

/-- The side parameter is continuous at the vertex. -/
theorem RiemannMapping.continuousAt_triangleSideParameter_zero (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) : ContinuousAt (triangleSideParameter e a) 0 := by
  have hi := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (e.map_source ha))
  exact
    ContinuousAt.comp (g := e.symm) (f := fun w : ℂ => w + e a) (x := 0)
      (by simpa only [zero_add] using hi) (continuousAt_id.add_const (e a))

/-! ### The half-strip exponential -/

/-- The half-strip exponential coordinate. -/
def RiemannBoundary.halfStripExp (a c : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (z - a) / c)

/-- The half-strip logarithm inverts the exponential. -/
theorem RiemannBoundary.logHalfStrip_halfStripExp (a : ℝ) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z.re ∈ Set.Ioo a (a + c * Real.pi)) : logHalfStrip a c (halfStripExp a c z) = z := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have him : (Complex.I * (z - a) / c).im = (z.re - a) / c := by simp
  have hpos : 0 < (Complex.I * (z - a) / c).im := by
    rw [him]
    exact div_pos (sub_pos.mpr hz.1) hc
  have hpi : (Complex.I * (z - a) / c).im < Real.pi := by
    rw [him, div_lt_iff₀ hc]
    linarith [hz.2]
  rw [logHalfStrip, halfStripExp, Complex.log_exp (by linarith [Real.pi_pos]) hpi.le]
  field_simp
  ring_nf
  simp

/-- The norm of the half-strip exponential. -/
@[simp]
theorem RiemannBoundary.norm_halfStripExp (a c : ℝ) (z : ℂ) :
    ‖halfStripExp a c z‖ = Real.exp (-z.im / c) := by simp [halfStripExp, Complex.norm_exp]

/-- The half-strip exponential has positive imaginary part. -/
theorem RiemannBoundary.halfStripExp_im_pos (a : ℝ) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z.re ∈ Set.Ioo a (a + c * Real.pi)) : 0 < (halfStripExp a c z).im := by
  rw [halfStripExp, Complex.exp_im]
  apply mul_pos (Real.exp_pos _)
  apply Real.sin_pos_of_pos_of_lt_pi
  · simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.I_re, Complex.sub_im,
      Complex.ofReal_im, MulZeroClass.zero_mul, Complex.I_im, Complex.sub_re, Complex.ofReal_re,
      one_mul, zero_add]
    exact div_pos (sub_pos.mpr hz.1) hc
  · simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.I_re, Complex.sub_im,
      Complex.ofReal_im, MulZeroClass.zero_mul, Complex.I_im, Complex.sub_re, Complex.ofReal_re,
      one_mul, zero_add]
    rw [div_lt_iff₀ hc]
    linarith [hz.2]
