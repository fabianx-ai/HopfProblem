/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Transversality.Basic

/-!
# The tubular neighbourhood of a belt sphere and its meridians

For a Morse surgery datum `d` at a critical point of index `λ` in an `n`-manifold the belt
sphere `S^{n-λ-1}` in the upper level has a tubular neighbourhood parametrised by
`S^{n-λ-1} × (punctured λ-ball)` (`MorseCancellation.nativeBeltTubeSource`,
`nativeBeltTubeInComplement`); the *meridian* through a point `v` of the belt sphere is the
`(λ-1)`-sphere of radius `r` in the normal ball (`nativeBeltTubeMeridian`).  A map of a small
parameter ball into the belt neighbourhood is described by its `(v, normal)` coordinates
(`beltBallCoordinates`), and the restriction to the boundary of the parameter ball is
null-homotopic (`parameterBall_boundary_nullhomotopic`).  This is the local structure of the
belt sphere used in the cancellation theorem, cf. Milnor, *Lectures on the h-cobordism theorem*,
§5.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- The parametrisation `S(P) × (punctured unit ball of N) → belt source` of the tubular
neighbourhood of the belt sphere of a Morse surgery datum `d` in the chart coordinates
`(positive, negative)`, sending `(v, z)` to `(v, z)` inside the enlarged closed belt. -/
def MorseCancellation.nativeBeltTubeSource {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.PositiveCoordinates) 1 ×
        PuncturedBall.Space d.chart.NegativeCoordinates 1,
      d.chart.beltSource d.radius d.radius_pos)
    where
  toFun
    z :=
    ⟨(z.1, z.2.val),
      d.chart.enlarged_closed_belt_subset_source d.radius d.radius_pos d.block
        ⟨Set.mem_univ _, by
          rw [mem_closedBall_zero_iff]
          exact z.2.property.2.le.trans (by norm_num)⟩⟩
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The tubular neighbourhood of the belt sphere of `d`, parametrised by
`S(P) × (punctured unit ball of N)` through `nativeBeltTubeSource` and the belt neighbourhood
homeomorphism, lands in the complement of the belt sphere in the upper level, because the
normal coordinate is `d.radius • z ≠ 0`. -/
def MorseCancellation.nativeBeltTubeInComplement {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.PositiveCoordinates) 1 ×
        PuncturedBall.Space d.chart.NegativeCoordinates 1,
      ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel))
    where
  toFun
    z := by
    let y := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (nativeBeltTubeSource d z)
    refine ⟨y.val, ?_⟩
    intro hy
    have hz := (d.beltNormal_eq_zero_iff y.property).mpr hy
    have heq : d.beltNormal y.val = d.radius • z.2.val :=
      d.chart.beltNeighborhoodHomeomorph_normal d.radius d.radius_pos (nativeBeltTubeSource d z)
    rw [heq] at hz
    exact (smul_ne_zero d.radius_pos.ne' z.2.property.1) hz
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous.comp
            (nativeBeltTubeSource d).continuous)).subtype_mk
      _

/-- The meridian of the belt tube of `d` through the belt point `v` at normal radius `r`,
`0 < r < 1`: the `(λ - 1)`-sphere `S(N) → (belt sphere)ᶜ` given by `u ↦ (v, r • u)`. -/
def MorseCancellation.nativeBeltTubeMeridian {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    C(Metric.sphere (0 : d.chart.NegativeCoordinates) 1,
      ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) :=
  (nativeBeltTubeInComplement d).comp
    ((ContinuousMap.const _ v).prodMk (PuncturedBall.fromSphere 1 r hr hr1))

/-- The boundary sphere of the parameter ball: `S(A) → closedBall 0 r`, `u ↦ r • u` (`0 < r`). -/
def MorseCancellation.parameterBallBoundary {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] (r : ℝ)
    (hr : 0 < r) : C(Metric.sphere (0 : A) 1, Metric.closedBall (0 : A) r)
    where
  toFun
    u := ⟨r • u.val, by rw [mem_closedBall_zero_iff, LocalDegree.norm_radius_smul r hr u]⟩
  continuous_toFun := by
    have h : Continuous (fun u : Metric.sphere (0 : A) 1 => r • u.val) :=
      continuous_const.smul continuous_subtype_val
    exact h.subtype_mk _

/-- The centre `0` of the closed parameter ball of radius `r > 0`. -/
def MorseCancellation.parameterBallCenter {A : Type} [NormedAddCommGroup A] (r : ℝ) (hr : 0 < r) :
    Metric.closedBall (0 : A) r :=
  ⟨0, by simpa using hr.le⟩

/-- The radial homotopy `(t, u) ↦ (1 - t) • (r • u)` from `parameterBallBoundary r hr` to the
constant map at `parameterBallCenter r hr` inside the closed ball of radius `r`. -/
def MorseCancellation.parameterBallContraction {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (r : ℝ) (hr : 0 < r) :
    (parameterBallBoundary (A := A) r hr).Homotopy
      (ContinuousMap.const _ (parameterBallCenter r hr))
    where
  toFun
    z :=
    ⟨(1 - (z.1 : ℝ)) • (r • z.2.val),
      by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr z.1.property.2),
        LocalDegree.norm_radius_smul r hr z.2]
      exact mul_le_of_le_one_left hr.le (by linarith [z.1.property.1])⟩
  continuous_toFun := by
    have h :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : A) 1 => (1 - (z.1 : ℝ)) • (r • z.2.val)) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_const.smul (continuous_subtype_val.comp continuous_snd))
    exact h.subtype_mk _
  map_zero_left u := by apply Subtype.ext; simp [parameterBallBoundary]
  map_one_left u := by apply Subtype.ext; simp [parameterBallCenter]

/-- For every `g : C(closedBall 0 r, Y)`, the restriction `g ∘ parameterBallBoundary r hr` to the
boundary sphere is homotopic to the constant map at `g 0`. -/
theorem MorseCancellation.parameterBall_boundary_nullhomotopic {A : Type} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {Y : Type} [TopologicalSpace Y] (r : ℝ) (hr : 0 < r)
    (g : C(Metric.closedBall (0 : A) r, Y)) :
    (g.comp (parameterBallBoundary r hr)).Homotopic
      (ContinuousMap.const _ (g (parameterBallCenter r hr))) := by
  have h := (ContinuousMap.Homotopic.refl g).comp ⟨parameterBallContraction r hr⟩
  exact h

/-- Normalising commutes with positive scaling: `‖r • x‖⁻¹ • (r • x) = ‖x‖⁻¹ • x` for `0 < r`. -/
theorem MorseCancellation.normalized_pos_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℝ) (hr : 0 < r) (x : F) : ‖r • x‖⁻¹ • (r • x) = ‖x‖⁻¹ • x := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev, smul_smul, mul_assoc,
    inv_mul_cancel₀ hr.ne', mul_one]

/-- The chart coordinates `(belt component, normal component)` of a map
`F : C(closedBall 0 ε, beltTarget)` of a parameter ball into the belt neighbourhood of `d`,
obtained through the inverse belt neighbourhood homeomorphism. -/
def MorseCancellation.beltBallCoordinates {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} [NormedAddCommGroup A]
    (d : ManifoldMorse.MorseSurgeryData E f p) (ε : ℝ)
    (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius)) :
    C(Metric.closedBall (0 : A) ε,
      Metric.sphere (0 : d.chart.PositiveCoordinates) 1 × d.chart.NegativeCoordinates) :=
  ⟨fun z => ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm (F z)).val,
    continuous_subtype_val.comp
      ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm.continuous.comp
        F.continuous)⟩

/-- The normal component of `beltBallCoordinates d ε F z` is `d.radius⁻¹ • d.beltNormal (F z)`. -/
theorem MorseCancellation.beltBallCoordinates_normal {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (z : Metric.closedBall (0 : A) ε) :
    (beltBallCoordinates d ε F z).2 = d.radius⁻¹ • d.beltNormal (F z).val :=
  rfl

/-- The normalised-normal map `S(A) → punctured unit ball of N` of `F` on the boundary of the
parameter ball, under the hypotheses that all normal components of `F` have norm `< 1`
(`hsmall`) and are nonzero on the boundary sphere (`hne`). -/
def MorseCancellation.beltBallBoundaryNormal {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p) (ε : ℝ) (hε : 0 < ε)
    (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) :
    C(Metric.sphere (0 : A) 1, PuncturedBall.Space d.chart.NegativeCoordinates 1) :=
  ⟨fun u => ⟨(beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2, hne u, hsmall _⟩,
    ((beltBallCoordinates d ε F).continuous.snd.comp
          (parameterBallBoundary ε hε).continuous).subtype_mk
      _⟩

/-- The boundary sphere of the parameter ball mapped by `F` into the complement of the belt
sphere, written through the belt tube: `u ↦ nativeBeltTubeInComplement d (belt part, normal part)`
of `F (parameterBallBoundary ε hε u)`. -/
def MorseCancellation.beltBallBoundaryInComplement {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) :
    C(Metric.sphere (0 : A) 1, ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) :=
  (nativeBeltTubeInComplement d).comp
    (((ContinuousMap.fst.comp (beltBallCoordinates d ε F)).comp
          (parameterBallBoundary ε hε)).prodMk
      (beltBallBoundaryNormal d ε hε F hsmall hne))

/-- The underlying point of `beltBallBoundaryInComplement d ε hε F hsmall hne u` is
`F (parameterBallBoundary ε hε u)`. -/
theorem MorseCancellation.beltBallBoundaryInComplement_coe {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (u : Metric.sphere (0 : A) 1) :
    (beltBallBoundaryInComplement d ε hε F hsmall hne u).val =
      (F (parameterBallBoundary ε hε u)).val := by
  let y := F (parameterBallBoundary ε hε u)
  let e := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
  change
    (e
          (nativeBeltTubeSource d
            ((e.symm y).val.1, (beltBallBoundaryNormal d ε hε F hsmall hne u)))).val =
      y.val
  have hs :
    nativeBeltTubeSource d ((e.symm y).val.1, (beltBallBoundaryNormal d ε hε F hsmall hne u)) =
      e.symm y := by
    apply Subtype.ext
    rfl
  rw [hs, e.apply_symm_apply]

/-- The normalisation of `beltBallBoundaryNormal d ε hε F hsmall hne u` in the unit sphere is the
normalised belt normal `‖n‖⁻¹ • n` of `n = d.beltNormal (F (parameterBallBoundary ε hε u))`. -/
theorem MorseCancellation.beltBallBoundary_normalized_coe {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (u : Metric.sphere (0 : A) 1) :
    (PuncturedBall.toSphere 1 (beltBallBoundaryNormal d ε hε F hsmall hne u)).val =
      ‖d.beltNormal (F (parameterBallBoundary ε hε u)).val‖⁻¹ •
        d.beltNormal (F (parameterBallBoundary ε hε u)).val := by
  change
    ‖d.radius⁻¹ • d.beltNormal (F (parameterBallBoundary ε hε u)).val‖⁻¹ •
        (d.radius⁻¹ • d.beltNormal (F (parameterBallBoundary ε hε u)).val) =
      _
  exact normalized_pos_smul d.radius⁻¹ (inv_pos.mpr d.radius_pos) _

/-- Let `G : A → d.UpperLevel` be continuous on a neighbourhood `t` of `0` with `G 0` on the belt
sphere of `d` at `v`.  Then there is a neighbourhood `s ⊆ t` of `0` on which `G` is continuous,
takes values in the belt normal domain and has normal component `d.radius⁻¹ • d.beltNormal (G z)`
of norm `< 1`. -/
theorem MorseCancellation.exists_small_native_belt_neighborhood {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (G : A → d.UpperLevel) (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) {t : Set A}
    (ht : t ∈ 𝓝 (0 : A)) (hc : ContinuousOn G t) (hcenter : G 0 = d.surgery.beltSphere v) :
    ∃ s : Set A,
      s ∈ 𝓝 (0 : A) ∧
        s ⊆ t ∧
          ContinuousOn G s ∧
            (∀ z ∈ s, G z ∈ d.beltNormalDomain) ∧
              (∀ z ∈ s, ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1) := by
  have hG : ContinuousAt G 0 := hc.continuousAt ht
  have hdomain : G 0 ∈ d.beltNormalDomain := hcenter ▸ d.belt_mem_normalDomain v
  have hsplit : ContinuousAt d.chart.splitChart (G 0).val :=
    d.chart.splitChart.contMDiffOn_toFun.continuousOn.continuousAt
      (d.chart.splitChart.open_source.mem_nhds hdomain)
  have hGM : ContinuousAt (fun z : A => (G z).val) 0 :=
    (continuous_subtype_val : Continuous (Subtype.val : d.UpperLevel → M)).continuousAt.comp hG
  have hsplitG : ContinuousAt (fun z : A => d.chart.splitChart (G z).val) 0 :=
    ContinuousAt.comp (f := fun z : A => (G z).val) hsplit hGM
  have hnormal : ContinuousAt (fun z => d.beltNormal (G z)) 0 := by
    change ContinuousAt (fun z : A => (d.chart.splitChart (G z).val).1) 0
    exact hsplitG.fst
  have hsize : ContinuousAt (fun z => ‖d.radius⁻¹ • d.beltNormal (G z)‖) 0 :=
    (hnormal.const_smul d.radius⁻¹).norm
  have hzero : ‖d.radius⁻¹ • d.beltNormal (G 0)‖ < 1 := by
    rw [hcenter, d.beltNormal_belt, smul_zero, norm_zero]
    norm_num
  have h₀ : G ⁻¹' d.beltNormalDomain ∈ 𝓝 (0 : A) :=
    hG.preimage_mem_nhds (d.isOpen_beltNormalDomain.mem_nhds hdomain)
  have h₁ : {z : A | ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1} ∈ 𝓝 (0 : A) :=
    hsize.preimage_mem_nhds (Iio_mem_nhds hzero)
  let s := t ∩ (G ⁻¹' d.beltNormalDomain ∩ {z : A | ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1})
  refine
    ⟨s, Filter.inter_mem ht (Filter.inter_mem h₀ h₁), Set.inter_subset_left,
      hc.mono Set.inter_subset_left, ?_, ?_⟩
  · intro z hz
    exact hz.2.1
  · intro z hz
    exact hz.2.2

end
