/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
/-!
# Belt-sphere neighbourhood coordinates of a Morse chart

For a signed Morse chart at a critical point `p`, the ambient handle map parametrises a
neighbourhood of the belt sphere in the upper level set `f = f p + ρ²` by the unit sphere of the
positive directions times the negative directions; this is a homeomorphism onto an open subset.
For Morse surgery data the negative component of the splitting chart is a smooth normal coordinate
which cuts the belt sphere out of the upper level set and whose derivative annihilates the tangent
spaces of the belt sphere.

## Main definitions and results

* `ManifoldMorse.SignedMorseChart.beltNeighborhoodHomeomorph`
* `ManifoldMorse.MorseSurgeryData.beltNormal`, `ManifoldMorse.MorseSurgeryData.beltNormal_eq_zero_iff`,
  `ManifoldMorse.MorseSurgeryData.beltNormal_derivative_comp_belt`

## References

* cf. J. Milnor, *Lectures on the h-cobordism theorem*, §3.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


/-- The ambient handle map carries the unit sphere of the first factor into the level
`-‖·‖² + ‖·‖² = -ρ²` of the Morse quadratic form.
-/
theorem MorseHandle.ambientMap_lower_sphere {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (u : Metric.sphere (0 : N) 1) (v : P) :
    -‖(ambientMap ρ ((u : N), v)).1‖ ^ 2 + ‖(ambientMap ρ ((u : N), v)).2‖ ^ 2 = -(ρ ^ 2) := by
  have hA : 0 < ρ * Real.sqrt (1 + ‖v‖ ^ 2) := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  simp only [ambientMap, norm_smul, Real.norm_eq_abs, abs_of_pos hA, abs_of_pos hρ,
    mem_sphere_zero_iff_norm.mp u.property, mul_one, mul_pow,
    Real.sq_sqrt (show 0 ≤ 1 + ‖v‖ ^ 2 by positivity)]
  ring

/-- The ambient handle map carries the unit sphere times a ball of radius `3/2` into the product of
two balls of radius `2 ρ`.
-/
theorem MorseHandle.ambientMap_sphere_mem_product {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (u : Metric.sphere (0 : N) 1) (v : P) (hv : ‖v‖ ≤ (3 / 2 : ℝ)) :
    ambientMap ρ ((u : N), v) ∈
      Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  have hA : 0 < ρ * Real.sqrt (1 + ‖v‖ ^ 2) := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hs : Real.sqrt (1 + ‖v‖ ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [norm_nonneg v]⟩
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * Real.sqrt (1 + ‖v‖ ^ 2)) • (u : N)‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hA, mem_sphere_zero_iff_norm.mp u.property,
      mul_one]
    calc
      _ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hs hρ.le
      _ = _ := mul_comm _ _
  · rw [mem_closedBall_zero_iff]
    change ‖ρ • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hm := mul_le_mul_of_nonneg_left hv hρ.le
    linarith

/-- On the level `-‖z.1‖² + ‖z.2‖² = -ρ²` the first component of the inverse handle map is a unit
vector.
-/
theorem MorseHandle.norm_ambientInverse_fst_of_lower {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P)
    (hz : -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 = -(ρ ^ 2)) : ‖(ambientInverse ρ z).1‖ = 1 := by
  let A : ℝ := ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)
  have hA : 0 < A := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hA₂ : A ^ 2 = ρ ^ 2 + ‖z.2‖ ^ 2 := inverse_scale_sq hρ z.2
  have hn : ‖z.1‖ = A := by nlinarith [norm_nonneg z.1]
  change ‖A⁻¹ • z.1‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA), hn, inv_mul_cancel₀ hA.ne']

attribute [local instance 100] Classical.propDecidable in
/-- The belt coordinates of a signed Morse chart before restriction: the ambient handle map applied
to a unit vector in the positive directions and a vector in the negative directions, with the
two factors exchanged.
-/
def ManifoldMorse.SignedMorseChart.beltRawCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ)
    (z : PuncturedHandle.UnitSphere c.PositiveCoordinates × c.NegativeCoordinates) :
    c.NegativeCoordinates × c.PositiveCoordinates :=
  (MorseHandle.ambientMap ρ ((z.1 : c.PositiveCoordinates), z.2)).swap

attribute [local instance 100] Classical.propDecidable in
/-- The raw belt coordinates are continuous for positive radius. -/
theorem ManifoldMorse.SignedMorseChart.continuous_beltRawCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltRawCoordinates ρ) :=
  continuous_swap.comp
    ((MorseHandle.ambientHomeomorph ρ hρ).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

attribute [local instance 100] Classical.propDecidable in
/-- The open set of unit vectors and normal vectors whose raw belt coordinates lie in the target of
the splitting chart.
-/
def ManifoldMorse.SignedMorseChart.beltSource {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    TopologicalSpace.Opens
      (PuncturedHandle.UnitSphere c.PositiveCoordinates × c.NegativeCoordinates) :=
  ⟨c.beltRawCoordinates ρ ⁻¹' c.splitChart.target,
    c.splitChart.open_target.preimage (c.continuous_beltRawCoordinates ρ hρ)⟩

attribute [local instance 100] Classical.propDecidable in
/-- The open subset of the upper level set lying in the source of the splitting chart. -/
def ManifoldMorse.SignedMorseChart.beltTarget {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) :
    TopologicalSpace.Opens { y : M // f y = f p + ρ ^ 2 } :=
  ⟨Subtype.val ⁻¹' c.splitChart.source, c.splitChart.open_source.preimage continuous_subtype_val⟩

attribute [local instance 100] Classical.propDecidable in
/-- The parametrisation of a neighbourhood of the belt sphere inside the upper level set, by the
unit sphere of the positive directions times the negative directions.
-/
def ManifoldMorse.SignedMorseChart.beltNeighborhoodMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.beltSource ρ hρ) : c.beltTarget ρ :=
  ⟨⟨c.splitChart.symm (c.beltRawCoordinates ρ z.val),
      by
      rw [c.splitChart_inverse_equation z.property]
      have hh := MorseHandle.ambientMap_lower_sphere hρ z.val.1 z.val.2
      change
        -‖(c.beltRawCoordinates ρ z.val).2‖ ^ 2 + ‖(c.beltRawCoordinates ρ z.val).1‖ ^ 2 =
          -(ρ ^ 2) at hh
      linarith⟩,
    c.splitChart.map_target' z.property⟩

attribute [local instance 100] Classical.propDecidable in
/-- The belt neighbourhood parametrisation is continuous. -/
theorem ManifoldMorse.SignedMorseChart.continuous_beltNeighborhoodMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltNeighborhoodMap ρ hρ) := by
  have hc :
    Continuous (fun z : c.beltSource ρ hρ => c.splitChart.symm (c.beltRawCoordinates ρ z.val)) :=
    c.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous
      ((c.continuous_beltRawCoordinates ρ hρ).comp continuous_subtype_val) (fun z => z.property)
  exact (hc.subtype_mk _).subtype_mk _

attribute [local instance 100] Classical.propDecidable in
/-- The inverse belt coordinates of a point of the manifold, read through the splitting chart and
the inverse handle map.
-/
def ManifoldMorse.SignedMorseChart.beltInverseCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (y : M) :
    c.PositiveCoordinates × c.NegativeCoordinates :=
  MorseHandle.ambientInverse ρ (c.splitChart y).swap

attribute [local instance 100] Classical.propDecidable in
/-- The inverse belt coordinates are continuous on the source of the splitting chart. -/
theorem ManifoldMorse.SignedMorseChart.continuousOn_beltInverseCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    ContinuousOn (c.beltInverseCoordinates ρ) c.splitChart.source :=
  (MorseHandle.ambientHomeomorph ρ hρ).symm.continuous.comp_continuousOn
    (continuous_swap.comp_continuousOn c.splitChart.contMDiffOn_toFun.continuousOn)

attribute [local instance 100] Classical.propDecidable in
/-- The inverse belt coordinates undo the belt neighbourhood parametrisation. -/
theorem ManifoldMorse.SignedMorseChart.beltInverseCoordinates_neighborhoodMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.beltSource ρ hρ) :
    c.beltInverseCoordinates ρ ((c.beltNeighborhoodMap ρ hρ z).val : M) =
      ((z.val.1 : c.PositiveCoordinates), z.val.2) := by
  have hr :
    c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val)) =
      c.beltRawCoordinates ρ z.val :=
    c.splitChart.right_inv' z.property
  change
    MorseHandle.ambientInverse ρ
        (c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val))).swap =
      _
  rw [hr]
  exact MorseHandle.ambientInverse_ambientMap hρ _

attribute [local instance 100] Classical.propDecidable in
/-- On the upper level set the first inverse belt coordinate is a unit vector. -/
theorem ManifoldMorse.SignedMorseChart.norm_beltInverseCoordinates_fst {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (y : { y : M // f y = f p + ρ ^ 2 }) (hy : (y : M) ∈ c.splitChart.source) :
    ‖(c.beltInverseCoordinates ρ y).1‖ = 1 := by
  apply MorseHandle.norm_ambientInverse_fst_of_lower hρ
  have hh := c.splitChart_equation hy
  rw [y.property] at hh
  change -‖(c.splitChart (y : M)).2‖ ^ 2 + ‖(c.splitChart (y : M)).1‖ ^ 2 = -(ρ ^ 2)
  linarith

attribute [local instance 100] Classical.propDecidable in
/-- The inverse of the belt neighbourhood parametrisation. -/
def ManifoldMorse.SignedMorseChart.beltNeighborhoodInverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (y : c.beltTarget ρ) : c.beltSource ρ hρ := by
  let v : PuncturedHandle.UnitSphere c.PositiveCoordinates :=
    ⟨(c.beltInverseCoordinates ρ (y.val : M)).1,
      mem_sphere_zero_iff_norm.mpr (c.norm_beltInverseCoordinates_fst ρ hρ y.val y.property)⟩
  refine ⟨(v, (c.beltInverseCoordinates ρ (y.val : M)).2), ?_⟩
  change
    (MorseHandle.ambientMap ρ
          (MorseHandle.ambientInverse ρ (c.splitChart (y.val : M)).swap)).swap ∈
      c.splitChart.target
  rw [MorseHandle.ambientMap_ambientInverse hρ, Prod.swap_swap]
  exact c.splitChart.map_source' y.property

attribute [local instance 100] Classical.propDecidable in
/-- The inverse belt neighbourhood parametrisation is continuous. -/
theorem ManifoldMorse.SignedMorseChart.continuous_beltNeighborhoodInverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltNeighborhoodInverse ρ hρ) := by
  have hc : Continuous (fun y : c.beltTarget ρ => c.beltInverseCoordinates ρ (y.val : M)) :=
    (c.continuousOn_beltInverseCoordinates ρ hρ).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.property)
  exact ((hc.fst.subtype_mk _).prodMk hc.snd).subtype_mk _

attribute [local instance 100] Classical.propDecidable in
/-- The belt neighbourhood parametrisation as a homeomorphism: a neighbourhood of the belt sphere in
the upper level set is the product of the belt sphere with a disc of normal directions (Milnor,
h-cobordism theorem, §3).
-/
def ManifoldMorse.SignedMorseChart.beltNeighborhoodHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    c.beltSource ρ hρ ≃ₜ c.beltTarget ρ
    where
  toFun := c.beltNeighborhoodMap ρ hρ
  invFun := c.beltNeighborhoodInverse ρ hρ
  left_inv
    z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst (c.beltInverseCoordinates_neighborhoodMap ρ hρ z))
    · exact
        congrArg (fun w : c.PositiveCoordinates × c.NegativeCoordinates => w.2)
          (c.beltInverseCoordinates_neighborhoodMap ρ hρ z)
  right_inv
    y := by
    apply Subtype.ext
    apply Subtype.ext
    change
      c.splitChart.symm
          (MorseHandle.ambientMap ρ
              (MorseHandle.ambientInverse ρ (c.splitChart (y.val : M)).swap)).swap =
        (y.val : M)
    rw [MorseHandle.ambientMap_ambientInverse hρ, Prod.swap_swap]
    exact c.splitChart.left_inv' y.property
  continuous_toFun := c.continuous_beltNeighborhoodMap ρ hρ
  continuous_invFun := c.continuous_beltNeighborhoodInverse ρ hρ

attribute [local instance 100] Classical.propDecidable in
/-- If the splitting chart contains the block of radius `2 ρ`, its belt source contains the whole
unit sphere times the closed ball of radius `3/2`.
-/
theorem ManifoldMorse.SignedMorseChart.enlarged_closed_belt_subset_source {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    (Set.univ : Set (PuncturedHandle.UnitSphere c.PositiveCoordinates)) ×ˢ
        Metric.closedBall (0 : c.NegativeCoordinates) (3 / 2 : ℝ) ⊆
      c.beltSource ρ hρ := by
  rintro ⟨v, u⟩ ⟨_, hu⟩
  have hh :=
    MorseHandle.ambientMap_sphere_mem_product hρ v u (mem_closedBall_zero_iff.mp hu)
  exact hblock ⟨hh.2, hh.1⟩

attribute [local instance 100] Classical.propDecidable in
/-- The negative split coordinate of a point of the belt neighbourhood is `ρ` times its normal
parameter; so the second factor of the parametrisation is the normal coordinate.
-/
theorem ManifoldMorse.SignedMorseChart.beltNeighborhoodHomeomorph_normal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.beltSource ρ hρ) :
    (c.splitChart ((c.beltNeighborhoodHomeomorph ρ hρ z).val : M)).1 = ρ • z.val.2 := by
  have hr :
    c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val)) =
      c.beltRawCoordinates ρ z.val :=
    c.splitChart.right_inv' z.property
  change (c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val))).1 = _
  rw [hr]
  rfl

attribute [local instance 100] Classical.propDecidable in
/-- The part of the upper level set lying in the source of the splitting chart, where the belt
normal coordinate is defined.
-/
def ManifoldMorse.MorseSurgeryData.beltNormalDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) : Set d.UpperLevel :=
  (Subtype.val : d.UpperLevel → M) ⁻¹' d.chart.splitChart.source

attribute [local instance 100] Classical.propDecidable in
/-- The normal coordinate of the belt sphere: the negative component of the splitting chart, which
cuts the belt sphere out of the upper level set.
-/
def ManifoldMorse.MorseSurgeryData.beltNormal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    d.UpperLevel → d.chart.NegativeCoordinates := fun x => (d.chart.splitChart (x : M)).1

attribute [local instance 100] Classical.propDecidable in
/-- The domain of the belt normal coordinate is open. -/
theorem ManifoldMorse.MorseSurgeryData.isOpen_beltNormalDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) : IsOpen d.beltNormalDomain :=
  d.chart.splitChart.open_source.preimage continuous_subtype_val

attribute [local instance 100] Classical.propDecidable in
/-- The model points of the belt sphere lie in the target of the splitting chart. -/
theorem ManifoldMorse.MorseSurgeryData.belt_model_mem_target {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    (0, d.radius • (v : d.chart.PositiveCoordinates)) ∈ d.chart.splitChart.target := by
  apply d.block
  constructor
  · simpa only [Metric.mem_closedBall, dist_self] using
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) d.radius_pos.le)
  · have hv : ‖(v : d.chart.PositiveCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos d.radius_pos, hv, mul_one]
    linarith [d.radius_pos]

attribute [local instance 100] Classical.propDecidable in
/-- The belt sphere lies in the domain of the belt normal coordinate. -/
theorem ManifoldMorse.MorseSurgeryData.belt_mem_normalDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.surgery.beltSphere v ∈ d.beltNormalDomain := by
  change (d.surgery.beltSphere v : M) ∈ d.chart.splitChart.source
  rw [d.belt_eq, d.chart.beltCoreMap_coe]
  exact d.chart.splitChart.map_target' (d.belt_model_mem_target v)

attribute [local instance 100] Classical.propDecidable in
/-- The split coordinates of a point of the belt sphere are `(0, radius • v)`: the belt sphere is
the sphere of radius `radius` in the positive directions.
-/
theorem ManifoldMorse.MorseSurgeryData.belt_split_coordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.chart.splitChart (d.surgery.beltSphere v : M) =
      (0, d.radius • (v : d.chart.PositiveCoordinates)) := by
  rw [d.belt_eq, d.chart.beltCoreMap_coe]
  exact d.chart.splitChart.right_inv' (d.belt_model_mem_target v)

attribute [local instance 100] Classical.propDecidable in
/-- The belt normal coordinate vanishes on the belt sphere. -/
theorem ManifoldMorse.MorseSurgeryData.beltNormal_belt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltNormal (d.surgery.beltSphere v) = 0 := by
  change (d.chart.splitChart (d.surgery.beltSphere v : M)).1 = 0
  rw [d.belt_split_coordinates]

attribute [local instance 100] Classical.propDecidable in
/-- On its domain the belt normal coordinate vanishes exactly on the belt sphere, so the belt sphere
is cut out cleanly by that coordinate.
-/
theorem ManifoldMorse.MorseSurgeryData.beltNormal_eq_zero_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) {x : d.UpperLevel}
    (hx : x ∈ d.beltNormalDomain) : d.beltNormal x = 0 ↔ x ∈ Set.range d.surgery.beltSphere := by
  constructor
  · intro hzero
    let z := d.chart.splitChart (x : M)
    have hz₁ : z.1 = 0 := hzero
    have heq := d.chart.splitChart_equation hx
    change f (x : M) = f p - ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 at heq
    rw [hz₁, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, x.property] at heq
    have hnorm : ‖z.2‖ = d.radius := by nlinarith [norm_nonneg z.2, d.radius_pos]
    let v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates :=
      ⟨d.radius⁻¹ • z.2, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr d.radius_pos), hnorm, inv_mul_cancel₀ d.radius_pos.ne']⟩
    refine ⟨v, Subtype.ext ?_⟩
    rw [d.belt_eq, d.chart.beltCoreMap_coe]
    change d.chart.splitChart.symm (0, d.radius • (d.radius⁻¹ • z.2)) = (x : M)
    rw [smul_smul, mul_inv_cancel₀ d.radius_pos.ne', one_smul]
    have hz : (0, z.2) = z := Prod.ext hz₁.symm rfl
    rw [hz]
    exact d.chart.splitChart.left_inv' hx
  · rintro ⟨v, rfl⟩
    exact d.beltNormal_belt v

attribute [local instance 100] Classical.propDecidable in
/-- The belt normal coordinate is smooth on its domain. -/
theorem ManifoldMorse.MorseSurgeryData.contMDiffOn_beltNormal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ d.beltNormal
      d.beltNormalDomain := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  have hcoords :
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E)
      𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
      (d.chart.splitChart ∘ (Subtype.val : d.UpperLevel → M)) d.beltNormalDomain :=
    d.chart.splitChart.contMDiffOn_toFun.comp
      (RegularLevel.contMDiff_inclusion hf d.upper_regular).contMDiffOn (fun _ hx => hx)
  exact contDiff_fst.contMDiff.comp_contMDiffOn hcoords

attribute [local instance 100] Classical.propDecidable in
/-- The derivative of the belt normal coordinate annihilates the tangent space of the belt sphere,
that coordinate being constant along it.
-/
theorem ManifoldMorse.MorseSurgeryData.beltNormal_derivative_comp_belt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
            (d.surgery.beltSphere v)).comp
        (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v) =
      0 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  have hnormal :=
    (d.contMDiffOn_beltNormal hf).contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  have heq : d.beltNormal ∘ d.surgery.beltSphere = fun _ => 0 := funext d.beltNormal_belt
  have hzero :
    mfderiv (𝓡 n) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ d.surgery.beltSphere) v = 0 :=
    by rw [heq, mfderiv_const]
  have hchain :=
    mfderiv_comp v (hnormal.mdifferentiableAt (by simp))
      ((d.belt_smooth hf n).mdifferentiableAt (by simp))
  exact hchain.symm.trans hzero
