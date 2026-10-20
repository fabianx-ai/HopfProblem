/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SignedMorseChart
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Splitting a signed Morse chart into negative and positive coordinates

The weights `w : ι → ℝ` with values `±1` split `ι → ℝ` as `ℝ^{w = -1} × ℝ^{w ≠ -1}`
(`MorseHandle.splitCoordinates`), in which `∑ i, w i * z i ^ 2 = -‖z₋‖² + ‖z₊‖²`. A signed Morse
chart composed with this splitting is the split chart, in which
`f = f x - ‖u‖² + ‖v‖²` (`ManifoldMorse.SignedMorseChart.splitChart_equation`); its rank count
`dim ℝ^- + dim ℝ^+ = dim E` gives the index. The closed product blocks
`D^-(R) × D^+(R)` pulled back by the split chart (`MorseCancellation.morseClosedBlock`) are
compact neighbourhoods of the critical point on which `f` lies in `[f x - R², f x + R²]`
(the handle model, Milnor, *Lectures on the h-cobordism theorem*, §3).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The negative eigenspace of a signed form. -/
abbrev MorseHandle.Negative {ι : Type*} (w : ι → ℝ) :=
  { i // w i = -1 }

/-- The positive eigenspace of a signed form. -/
abbrev MorseHandle.Positive {ι : Type*} (w : ι → ℝ) :=
  { i // w i ≠ -1 }

/-- The negative coordinates of a Morse chart. -/
abbrev MorseHandle.NegativeSpace {ι : Type*} (w : ι → ℝ) :=
  EuclideanSpace ℝ (Negative w)

/-- The positive coordinates of a Morse chart. -/
abbrev MorseHandle.PositiveSpace {ι : Type*} (w : ι → ℝ) :=
  EuclideanSpace ℝ (Positive w)

attribute [local instance 100] Classical.propDecidable in
/-- The space splits as negative times positive. -/
def MorseHandle.splitLinearEquiv {ι : Type*} (w : ι → ℝ) :
    (ι → ℝ) ≃ₗ[ℝ] (NegativeSpace w × PositiveSpace w) := by
  let e : (ι → ℝ) ≃ₗ[ℝ] ((Negative w → ℝ) × (Positive w → ℝ)) :=
    { toEquiv := Equiv.piEquivPiSubtypeProd (fun i => w i = -1) (fun _ => ℝ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact
    e.trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (Negative w → ℝ)).symm
        (WithLp.linearEquiv 2 ℝ (Positive w → ℝ)).symm)

attribute [local instance 100] Classical.propDecidable in
/-- The split coordinates of a point. -/
def MorseHandle.splitCoordinates {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    (ι → ℝ) ≃L[ℝ] (NegativeSpace w × PositiveSpace w) :=
  (splitLinearEquiv w).toContinuousLinearEquiv

attribute [local instance 100] Classical.propDecidable in
/-- The signed quadratic form is `‖−‖² − ‖+‖²` on the split. -/
theorem MorseHandle.signedSum_eq_norms {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    ∑ i, w i * (z i) ^ 2 = -‖(splitCoordinates w z).1‖ ^ 2 + ‖(splitCoordinates w z).2‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hneg : (∑ i : Negative w, w i.1 * (z i.1) ^ 2) = -∑ i : Negative w, (z i.1) ^ 2 := by
    calc
      _ = ∑ i : Negative w, -(z i.1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [i.2, neg_one_mul]
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hpos : (∑ i : Positive w, w i.1 * (z i.1) ^ 2) = ∑ i : Positive w, (z i.1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(hw i.1).resolve_left i.2, one_mul]
  calc
    ∑ i, w i * (z i) ^ 2 =
        (∑ i : Negative w, w i.1 * (z i.1) ^ 2) + ∑ i : Positive w, w i.1 * (z i.1) ^ 2 :=
      (Fintype.sum_subtype_add_sum_subtype (fun i => w i = -1) (fun i => w i * (z i) ^ 2)).symm
    _ = _ := by rw [hneg, hpos]; rfl

attribute [local instance 100] Classical.propDecidable in
/-- The split of a signed-sum pair computes the norms. -/
theorem MorseHandle.signedSum_symm_eq_norms {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : NegativeSpace w × PositiveSpace w) :
    ∑ i, w i * ((splitCoordinates w).symm z i) ^ 2 = -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    signedSum_eq_norms w hw ((splitCoordinates w).symm z)

/-- The negative coordinate space of a signed Morse chart. -/
abbrev ManifoldMorse.SignedMorseChart.NegativeCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) :=
  MorseHandle.NegativeSpace c.weights

/-- The positive coordinate space of a signed Morse chart. -/
abbrev ManifoldMorse.SignedMorseChart.PositiveCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) :=
  MorseHandle.PositiveSpace c.weights

attribute [local instance 100] Classical.propDecidable in
/-- The negative and positive ranks sum to the dimension. -/
theorem ManifoldMorse.SignedMorseChart.finrank_negative_add_positive {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) :
    Module.finrank ℝ c.NegativeCoordinates + Module.finrank ℝ c.PositiveCoordinates =
      Module.finrank ℝ E := by
  have h := (MorseHandle.splitLinearEquiv c.weights).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using h.symm

attribute [local instance 100] Classical.propDecidable in
/-- The signed Morse chart split into negative and positive factors. -/
def ManifoldMorse.SignedMorseChart.splitChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) M
      (c.NegativeCoordinates × c.PositiveCoordinates) ∞ :=
  c.chart.trans (MorseHandle.splitCoordinates c.weights).toDiffeomorph.toPartialDiffeomorph

attribute [local instance 100] Classical.propDecidable in
/-- Membership in the split chart's source. -/
theorem ManifoldMorse.SignedMorseChart.splitChart_mem_source {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) : x ∈ c.splitChart.source :=
  ⟨c.mem_source, Set.mem_univ _⟩

attribute [local instance 100] Classical.propDecidable in
/-- The split chart is centered at the critical point. -/
@[simp]
theorem ManifoldMorse.SignedMorseChart.splitChart_center {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) : c.splitChart x = 0 := by
  change MorseHandle.splitCoordinates c.weights (c.chart x) = 0
  rw [c.center, map_zero]

attribute [local instance 100] Classical.propDecidable in
/-- In the split chart the function is the signed norm sum. -/
theorem ManifoldMorse.SignedMorseChart.splitChart_equation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) {y : M}
    (hy : y ∈ c.splitChart.source) :
    f y = f x - ‖(c.splitChart y).1‖ ^ 2 + ‖(c.splitChart y).2‖ ^ 2 := by
  rw [c.equation y hy.1, MorseHandle.signedSum_eq_norms c.weights c.signs]
  change f x + (-‖(c.splitChart y).1‖ ^ 2 + ‖(c.splitChart y).2‖ ^ 2) = _
  ring

attribute [local instance 100] Classical.propDecidable in
/-- The inverse split chart computes the function as the signed sum. -/
theorem ManifoldMorse.SignedMorseChart.splitChart_inverse_equation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x)
    {y : c.NegativeCoordinates × c.PositiveCoordinates} (hy : y ∈ c.splitChart.target) :
    f (c.splitChart.symm y) = f x - ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
  change f (c.chart.symm ((MorseHandle.splitCoordinates c.weights).symm y)) = _
  rw [c.inverse_equation ((MorseHandle.splitCoordinates c.weights).symm y) hy.2,
    MorseHandle.signedSum_symm_eq_norms c.weights c.signs]
  ring

attribute [local instance 100] Classical.propDecidable in
/-- A closed product block exists inside the split chart. -/
theorem ManifoldMorse.SignedMorseChart.exists_closed_productBlock {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) :
    ∃ r > (0 : ℝ),
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target := by
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.toOpenPartialHomeomorph.map_source c.splitChart_mem_source
  obtain ⟨r, hr, hsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (c.splitChart.open_target.mem_nhds hzero)
  refine ⟨r, hr, ?_⟩
  rw [closedBall_prod_same]
  exact hsub

attribute [local instance 100] Classical.propDecidable in
/-- A closed product block in split Morse coordinates. -/
def MorseCancellation.morseClosedBlock {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ) : Set M :=
  c.splitChart.symm ''
    (Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
      Metric.closedBall (0 : c.PositiveCoordinates) R)

attribute [local instance 100] Classical.propDecidable in
/-- The closed Morse block lies in the chart source. -/
theorem MorseCancellation.morseClosedBlock_subset_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target) :
    morseClosedBlock c R ⊆ c.splitChart.source := by
  rintro x ⟨z, hz, rfl⟩
  exact c.splitChart.map_target' (hblock hz)

attribute [local instance 100] Classical.propDecidable in
/-- The closed Morse block's height bound. -/
theorem MorseCancellation.morseClosedBlock_height {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target) :
    morseClosedBlock c R ⊆ f ⁻¹' Set.Icc (f p - R ^ 2) (f p + R ^ 2) := by
  rintro x ⟨z, hz, rfl⟩
  have hn : ‖z.1‖ ≤ R := mem_closedBall_zero_iff.mp hz.1
  have hp : ‖z.2‖ ≤ R := mem_closedBall_zero_iff.mp hz.2
  have hn2 : ‖z.1‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hp2 : ‖z.2‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  change f (c.splitChart.symm z) ∈ Set.Icc (f p - R ^ 2) (f p + R ^ 2)
  rw [c.splitChart_inverse_equation (hblock hz)]
  constructor <;> nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]

attribute [local instance 100] Classical.propDecidable in
/-- The closed Morse block is a neighborhood of the critical point. -/
theorem MorseCancellation.morseClosedBlock_mem_nhds {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target)
    {z : c.NegativeCoordinates × c.PositiveCoordinates} (hn : ‖z.1‖ < R) (hp : ‖z.2‖ < R) :
    morseClosedBlock c R ∈ 𝓝 (c.splitChart.symm z) := by
  have hz : z ∈ c.splitChart.target :=
    hblock ⟨mem_closedBall_zero_iff.mpr hn.le, mem_closedBall_zero_iff.mpr hp.le⟩
  have hx : c.splitChart.symm z ∈ c.splitChart.source := c.splitChart.map_target' hz
  have hc : c.splitChart (c.splitChart.symm z) = z := c.splitChart.right_inv' hz
  have ho :
    Metric.ball (0 : c.NegativeCoordinates) R ×ˢ Metric.ball (0 : c.PositiveCoordinates) R ∈
      𝓝 (c.splitChart (c.splitChart.symm z)) := by
    rw [hc]
    exact
      (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
        ⟨mem_ball_zero_iff.mpr hn, mem_ball_zero_iff.mpr hp⟩
  have hnear := (c.splitChart.toOpenPartialHomeomorph.continuousAt hx) ho
  filter_upwards [c.splitChart.open_source.mem_nhds hx, hnear] with y hy hcy
  exact
    ⟨c.splitChart y, ⟨Metric.ball_subset_closedBall hcy.1, Metric.ball_subset_closedBall hcy.2⟩,
      c.splitChart.left_inv' hy⟩

attribute [local instance 100] Classical.propDecidable in
/-- The closed Morse block is compact. -/
theorem MorseCancellation.isCompact_morseClosedBlock {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [FiniteDimensional ℝ E] (c : ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target) :
    IsCompact (morseClosedBlock c R) :=
  (ProperSpace.isCompact_closedBall (0 : c.NegativeCoordinates) R).prod
      (ProperSpace.isCompact_closedBall (0 : c.PositiveCoordinates) R) |>.image_of_continuousOn
    (c.splitChart.symm.contMDiffOn_toFun.continuousOn.mono hblock)
