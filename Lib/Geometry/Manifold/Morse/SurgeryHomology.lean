/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Analysis.ODE.SmoothFlow
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle
import Lib.Geometry.Manifold.Collar
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.ConnectionCancellation
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.Topology.Homotopy.LoopSubdivision
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.Geometry.Manifold.Whitney.BigonModel
import Lib.Topology.Homotopy.CellAttachment
import Lib.Topology.Homotopy.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.Algebra.Module.IntegerPresentation
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.Topology.OnePointCollapse
import Lib.Geometry.Manifold.Morse.MinimalSystem
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.AlgebraicTopology.SingularHomology.OnePointCover

/-!
# Homology of Morse surgery data

The exact sequences of a Morse surgery step (`ManifoldMorse.MorseSurgeryData.morse_exact_at_lower`,
`ManifoldMorse.MorseSurgeryData.morseConnectingMap`), ordered surgery windows
(`ManifoldMorse.SurgeryWindows.point`, `ManifoldMorse.SurgeryWindows.BandData`), belt-face
coordinates and attaching collapses, finite signed cancellation of belt intersections, radial
fillings, and the index-two and index-three presentations of the middle homology
(`ManifoldMorse.SurgeryWindows.middlePresentation`, `ManifoldMorse.SurgeryWindows.middleMatrix`).

Moved verbatim from `Hopf/SphereTopology.lean` (base `304a0fea`); see
`Lib/reports/integration-4/spheretop-moves.md` for the per-declaration receipt.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

theorem ManifoldMorse.MorseSurgeryData.attachingSphere_pathConnected {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    PathConnectedSpace (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by omega)) _ zero_le_one)

def ManifoldMorse.SurgeryWindows.values {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) : Finset ℝ :=
  (S.finite.image f).toFinset

def ManifoldMorse.SurgeryWindows.count {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) : ℕ :=
  S.values.card

def ManifoldMorse.SurgeryWindows.point {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) :
    Fin S.count ≃ ManifoldMorse.criticalPoints E f :=
  ((S.values.orderIsoOfFin rfl).toEquiv.trans
        (Equiv.setCongr (S.finite.image f).coe_toFinset)).trans
    (Equiv.Set.imageOfInjOn f (ManifoldMorse.criticalPoints E f) S.distinct).symm

theorem ManifoldMorse.SurgeryWindows.point_value {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (i : Fin S.count) :
    f (S.point i) = S.values.orderEmbOfFin rfl i := by
  let e := Equiv.Set.imageOfInjOn f (ManifoldMorse.criticalPoints E f) S.distinct
  let v : f '' ManifoldMorse.criticalPoints E f :=
    Equiv.setCongr (S.finite.image f).coe_toFinset (S.values.orderIsoOfFin rfl i)
  have h :=
    congrArg (fun x : f '' ManifoldMorse.criticalPoints E f => (x : ℝ))
      (e.apply_symm_apply v)
  exact h

theorem ManifoldMorse.SurgeryWindows.point_strictMono {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) :
    StrictMono (fun i : Fin S.count => f (S.point i)) := by
  intro i j hij
  change f (S.point i) < f (S.point j)
  rw [S.point_value, S.point_value]
  exact (S.values.orderEmbOfFin rfl).strictMono hij

theorem ManifoldMorse.SurgeryWindows.point_consecutive {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) (hij : i.val + 1 = j.val) :
    ∀ r : ManifoldMorse.criticalPoints E f, ¬(f (S.point i) < f r ∧ f r < f (S.point j)) := by
  intro r hr
  obtain ⟨k, rfl⟩ := S.point.surjective r
  have hik : i < k := S.point_strictMono.lt_iff_lt.mp hr.1
  have hkj : k < j := S.point_strictMono.lt_iff_lt.mp hr.2
  have hik' : i.val < k.val := hik
  have hkj' : k.val < j.val := hkj
  omega

theorem ManifoldMorse.SurgeryWindows.ordered_windows {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) (hij : i < j) :
    S.upper (S.point i) < S.lower (S.point j) :=
  S.upper_lt_lower _ _ (S.point_strictMono hij)

theorem ManifoldMorse.SurgeryWindows.consecutive_regular {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) (hij : i.val + 1 = j.val) :
    ∀ x,
      f x ∈ Set.Icc (S.upper (S.point i)) (S.lower (S.point j)) →
        x ∉ ManifoldMorse.criticalPoints E f :=
  S.regular_between _ _ (S.point_consecutive i j hij)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SurgeryWindows.exists_consecutiveBandBridge {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (i j : Fin S.count)
    (hij : i.val + 1 = j.val) :
    letI := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ b :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data (S.point i)).UpperLevel (S.data (S.point j)).LowerLevel ∞,
        D '' {x : M | f x ≤ S.upper (S.point i)} = {x : M | f x ≤ S.lower (S.point j)} ∧
          ∀ x : (S.data (S.point i)).UpperLevel, (b x : M) = D x := by
  have hlt : i < j := by change i.val < j.val; omega
  exact S.exists_bandBridge hf _ _ (S.point_strictMono hlt) (S.point_consecutive i j hij)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.positive_eq_zero_of_localMax {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hmax : IsLocalMax f p)
    (v : c.PositiveCoordinates) : v = 0 := by
  by_contra hv
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨U, hUmax, hU, hpU⟩ := _root_.mem_nhds_iff.mp hmax
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hU hpU
  let z : c.PositiveCoordinates := (r / ‖v‖) • v
  have hz : ‖z‖ = r := by
    rw [show z = (r / ‖v‖) • v from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hnorm), div_mul_cancel₀ _ hnorm.ne']
  have hpoint :=
    hblock
      (show ((0 : c.NegativeCoordinates), z) ∈ Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r from
        ⟨by simpa only [mem_closedBall_zero_iff, norm_zero] using hr.le,
          mem_closedBall_zero_iff.mpr hz.le⟩)
  have hh := hUmax hpoint.2
  change f (c.splitChart.symm ((0 : c.NegativeCoordinates), z)) ≤ f p at hh
  rw [c.splitChart_inverse_equation hpoint.1, norm_zero, hz] at hh
  nlinarith [sq_pos_of_pos hr]

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SignedMorseChart.subsingleton_positive_of_localMax {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hmax : IsLocalMax f p) :
    Subsingleton c.PositiveCoordinates :=
  ⟨fun u v =>
    (c.positive_eq_zero_of_localMax hmax u).trans (c.positive_eq_zero_of_localMax hmax v).symm⟩

def ManifoldMorse.SurgeryWindows.first {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count) :
    ManifoldMorse.criticalPoints E f :=
  S.point ⟨0, h⟩

def ManifoldMorse.SurgeryWindows.last {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count) :
    ManifoldMorse.criticalPoints E f :=
  S.point ⟨S.count - 1, Nat.sub_lt h zero_lt_one⟩

theorem ManifoldMorse.SurgeryWindows.value_first_le {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count)
    (p : ManifoldMorse.criticalPoints E f) : f (S.first h) ≤ f p := by
  have hle : (⟨0, h⟩ : Fin S.count) ≤ S.point.symm p := Nat.zero_le _
  simpa only [first, Equiv.apply_symm_apply] using S.point_strictMono.monotone hle

theorem ManifoldMorse.SurgeryWindows.value_le_last {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count)
    (p : ManifoldMorse.criticalPoints E f) : f p ≤ f (S.last h) := by
  have hle : S.point.symm p ≤ (⟨S.count - 1, Nat.sub_lt h zero_lt_one⟩ : Fin S.count) :=
    Nat.le_sub_one_of_lt (S.point.symm p).isLt
  simpa only [last, Equiv.apply_symm_apply] using S.point_strictMono.monotone hle

theorem ManifoldMorse.SurgeryWindows.count_pos {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [Nonempty M] : 0 < S.count := by
  obtain ⟨p, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuous.continuousOn
  have hp : p ∈ ManifoldMorse.criticalPoints E f :=
    ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun x => hmin (Set.mem_univ x)))
  exact lt_of_le_of_lt (Nat.zero_le _) (S.point.symm ⟨p, hp⟩).isLt

theorem ManifoldMorse.SurgeryWindows.first_globalMin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) (x : M) : f (S.first h) ≤ f x := by
  obtain ⟨p, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn ⟨x, Set.mem_univ x⟩ hf.continuous.continuousOn
  have hp : p ∈ ManifoldMorse.criticalPoints E f :=
    ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun y => hmin (Set.mem_univ y)))
  exact (S.value_first_le h ⟨p, hp⟩).trans (hmin (Set.mem_univ x))

theorem ManifoldMorse.SurgeryWindows.last_globalMax {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) (x : M) : f x ≤ f (S.last h) := by
  obtain ⟨p, -, hmax⟩ :=
    isCompact_univ.exists_isMaxOn ⟨x, Set.mem_univ x⟩ hf.continuous.continuousOn
  have hp : p ∈ ManifoldMorse.criticalPoints E f :=
    ManifoldMorse.mem_criticalPoints_of_localMax hf
      (Filter.Eventually.of_forall (fun y => hmax (Set.mem_univ y)))
  exact (hmax (Set.mem_univ x)).trans (S.value_le_last h ⟨p, hp⟩)

theorem ManifoldMorse.SurgeryWindows.unique_first {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) (x : M) (hx : f x ≤ f (S.first h)) :
    x = (S.first h).val := by
  have hxcrit : x ∈ ManifoldMorse.criticalPoints E f :=
    ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun y => hx.trans (S.first_globalMin hf h y)))
  exact S.distinct hxcrit (S.first h).property (le_antisymm hx (S.first_globalMin hf h x))

theorem ManifoldMorse.SurgeryWindows.last_upper_univ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    {x : M | f x ≤ S.upper (S.last h)} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (S.last_globalMax hf h x).trans (S.value_lt_upper (S.last h)).le

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SurgeryWindows.first_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    Module.finrank ℝ (S.data (S.first h)).chart.NegativeCoordinates = 0 := by
  let :=
    (S.data (S.first h)).chart.subsingleton_negative_of_localMin
      (Filter.Eventually.of_forall (S.first_globalMin hf h))
  exact Module.finrank_zero_of_subsingleton

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.SurgeryWindows.last_index_dimension {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    Module.finrank ℝ (S.data (S.last h)).chart.NegativeCoordinates = Module.finrank ℝ E := by
  let :=
    (S.data (S.last h)).chart.subsingleton_positive_of_localMax
      (Filter.Eventually.of_forall (S.last_globalMax hf h))
  have hz : Module.finrank ℝ (S.data (S.last h)).chart.PositiveCoordinates = 0 :=
    Module.finrank_zero_of_subsingleton
  simpa only [hz, add_zero] using (S.data (S.last h)).chart.finrank_negative_add_positive

theorem ManifoldMorse.SurgeryWindows.nonempty_firstSublevelDisk {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [FiniteDimensional ℝ E] [T2Space M] (h : 0 < S.count) :
    Nonempty (SublevelDisk (Module.finrank ℝ E) f (S.upper (S.first h))) := by
  apply
    (S.data (S.first h)).chart.nonempty_sublevelDisk_before_next_critical hf (S.unique_first hf h)
      (S.value_lt_upper (S.first h))
  intro x hxlo hxhi hxcrit
  have hxlower : S.lower (S.first h) ≤ f x := (S.lower_lt_value (S.first h)).le.trans hxlo.le
  have hxp := S.isolated (S.first h) x hxcrit ⟨hxlower, hxhi⟩
  rw [hxp] at hxlo
  exact lt_irrefl _ hxlo

def FlowConstruction.regularLevelHomeomorphOfFlow {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (hab : a ≤ b) (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t) :
    { x : M // f x = a } ≃ₜ { x : M // f x = b } := by
  have hup (x : { x : M // f x = a }) : f (F (b - a) x) = b := by
    have hs : f x ∈ Set.Icc a b := by rw [x.property]; exact ⟨le_rfl, hab⟩
    have ht : f x + (b - a) ∈ Set.Icc a b := by
      rw [x.property, add_sub_cancel]
      exact ⟨hab, le_rfl⟩
    simpa only [x.property, add_sub_cancel] using hF x (b - a) hs ht
  have hdown (y : { x : M // f x = b }) : f (F (a - b) y) = a := by
    have hs : f y ∈ Set.Icc a b := by rw [y.property]; exact ⟨hab, le_rfl⟩
    have ht : f y + (a - b) ∈ Set.Icc a b := by
      rw [y.property, add_sub_cancel]
      exact ⟨le_rfl, hab⟩
    simpa only [y.property, add_sub_cancel] using hF y (a - b) hs ht
  refine
    { toFun := fun x => ⟨F (b - a) x, hup x⟩
      invFun := fun y => ⟨F (a - b) y, hdown y⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := (F.continuous continuous_const continuous_subtype_val).subtype_mk _
      continuous_invFun := (F.continuous continuous_const continuous_subtype_val).subtype_mk _ }
  · intro x
    apply Subtype.ext
    change F (a - b) (F (b - a) x) = x
    rw [← F.map_add, show a - b + (b - a) = 0 by ring, F.map_zero_apply]
  · intro y
    apply Subtype.ext
    change F (b - a) (F (a - b) y) = y
    rw [← F.map_add, show b - a + (a - b) = 0 by ring, F.map_zero_apply]

theorem FlowConstruction.nonempty_regularLevelHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    Nonempty ({ x : M // f x = a } ≃ₜ { x : M // f x = b }) := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  exact ⟨regularLevelHomeomorphOfFlow hab F hF⟩

theorem FlowConstruction.circle_nullhomotopies_regular_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ ManifoldMorse.criticalPoints E f)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = a }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = b }),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  obtain ⟨e⟩ := nonempty_regularLevelHomeomorph hf hab hband
  let forward : C({ x : M // f x = a }, { x : M // f x = b }) := ⟨e, e.continuous⟩
  let backward : C({ x : M // f x = b }, { x : M // f x = a }) := ⟨e.symm, e.symm.continuous⟩
  intro g
  obtain ⟨q, hq⟩ := hnull (backward.comp g)
  have heq : forward.comp (backward.comp g) = g := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (g x)
  have hh : (forward.comp (backward.comp g)).Homotopic (ContinuousMap.const _ (e q)) :=
    (ContinuousMap.Homotopic.refl forward).comp hq
  exact ⟨e q, heq ▸ hh⟩

theorem FiniteSignedCancellation.opposite_signs_distinct {a b : SignType} (h : a * b = -1) :
    a ≠ b := by cases a <;> cases b <;> simp_all

theorem FiniteSignedCancellation.cast_add_eq_zero_of_opposite {a b : SignType}
    (h : a * b = -1) : (a : ℤ) + (b : ℤ) = 0 := by cases a <;> cases b <;> simp_all

theorem FiniteSignedCancellation.sum_sdiff_pair {X : Type*} [DecidableEq X] (s : Finset X)
    (σ : X → SignType) {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1) :
    ∑ z ∈ s \ { x, y }, (σ z : ℤ) = ∑ z ∈ s, (σ z : ℤ) := by
  classical
  have hne : x ≠ y := fun h => opposite_signs_distinct hxy (congrArg σ h)
  have hsub : ({ x, y } : Finset X) ⊆ s := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · exact Finset.mem_singleton.mp hz ▸ hy
  have hsum : ∑ z ∈ ({ x, y } : Finset X), (σ z : ℤ) = 0 := by
    rw [Finset.sum_pair hne]
    exact cast_add_eq_zero_of_opposite hxy
  have h := Finset.sum_sdiff (f := fun z => (σ z : ℤ)) hsub
  simpa only [hsum, add_zero] using h

theorem FiniteSignedCancellation.sum_sdiff_pair_of_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (σ τ : X → SignType) {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1)
    (heq : ∀ z ∈ s \ { x, y }, τ z = σ z) : ∑ z ∈ s \ { x, y }, (τ z : ℤ) = ∑ z ∈ s, (σ z : ℤ) := by
  calc
    _ = ∑ z ∈ s \ { x, y }, (σ z : ℤ) :=
      Finset.sum_congr rfl (fun z hz => congrArg (fun a : SignType => (a : ℤ)) (heq z hz))
    _ = _ := sum_sdiff_pair s σ hx hy hxy

theorem FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite {X : Type*}
    (s : Finset X) (σ : X → SignType) (hunit : ∀ x ∈ s, σ x = 1 ∨ σ x = -1)
    (hno : ∀ x ∈ s, ∀ y ∈ s, σ x * σ y ≠ -1) : s.card = (∑ x ∈ s, (σ x : ℤ)).natAbs := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  have heq (y : X) (hy : y ∈ s) : σ y = σ x := by
    rcases hunit x hx with hxp | hxn <;> rcases hunit y hy with hyp | hyn
    · exact hyp.trans hxp.symm
    · exact (hno x hx y hy (by rw [hxp, hyn]; simp)).elim
    · exact (hno x hx y hy (by rw [hxn, hyp]; simp)).elim
    · exact hyn.trans hxn.symm
  have hsum : (∑ y ∈ s, (σ y : ℤ)) = ∑ _ ∈ s, (σ x : ℤ) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [heq y hy]
  rw [hsum]
  rcases hunit x hx with hp | hn
  · simp [hp]
  · simp [hn]

def RadialFilling.direction {n : ℕ} (b : Hemisphere.Sphere n)
    (v : Hemisphere.Ambient (n + 1)) : Hemisphere.Sphere n := by
  classical
    exact
    if hv : v = 0 then b
    else
      ⟨NormedSpace.normalize v, by
        simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hv⟩

theorem RadialFilling.direction_coe {n : ℕ} (b : Hemisphere.Sphere n)
    {v : Hemisphere.Ambient (n + 1)} (hv : v ≠ 0) :
    (direction b v : Hemisphere.Ambient (n + 1)) = NormedSpace.normalize v := by
  classical simp only [direction, dif_neg hv]

theorem RadialFilling.direction_of_mem_sphere {n : ℕ} (b v : Hemisphere.Sphere n) :
    direction b v.1 = v := by
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hv : v.1 ≠ 0 := by intro h; simp [h] at hn
  apply Subtype.ext
  rw [direction_coe b hv, NormedSpace.normalize_eq_self_of_norm_eq_one hn]

def RadialFilling.radialTime {n : ℕ} (v : Hemisphere.Ambient (n + 1)) :
    unitInterval :=
  Set.projIcc 0 1 zero_le_one (1 - ‖v‖)

theorem RadialFilling.coe_radialTime {n : ℕ} (v : Hemisphere.Ambient (n + 1)) :
    (radialTime v : ℝ) = Max.max 0 (Min.min 1 (1 - ‖v‖)) :=
  rfl

theorem RadialFilling.radialTime_le_quarter {n : ℕ} {v : Hemisphere.Ambient (n + 1)}
    (hv : 3 / 4 ≤ ‖v‖) : (radialTime v : ℝ) ≤ 1 / 4 := by
  rw [coe_radialTime]
  exact max_le (by norm_num) ((min_le_right _ _).trans (by linarith))

theorem RadialFilling.three_quarters_le_radialTime {n : ℕ}
    {v : Hemisphere.Ambient (n + 1)} (hv : ‖v‖ ≤ 1 / 4) : 3 / 4 ≤ (radialTime v : ℝ) := by
  rw [coe_radialTime]
  exact le_max_of_le_right (le_min (by norm_num) (by linarith))

theorem RadialFilling.contMDiffAt_radialTime {n : ℕ} {v : Hemisphere.Ambient (n + 1)}
    (hv : 0 < ‖v‖) (hunit : ‖v‖ < 1) :
    ContMDiffAt 𝓘(ℝ, Hemisphere.Ambient (n + 1)) (𝓡∂ 1) ∞ radialTime v := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc (0 : ℝ) 1 zero_le_one) (Set.Icc 0 1) :=
    contMDiffOn_projIcc
  have hm : 1 - ‖v‖ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hn : Set.Icc (0 : ℝ) 1 ∈ 𝓝 (1 - ‖v‖) := Icc_mem_nhds (by linarith) (by linarith)
  have hproj := (hp _ hm).contMDiffAt hn
  have hnorm : ContDiffAt ℝ ∞ (Norm.norm : Hemisphere.Ambient (n + 1) → ℝ) v :=
    contDiffAt_norm ℝ (norm_pos_iff.mp hv)
  exact hproj.comp v (contDiffAt_const.sub hnorm).contMDiffAt

def RadialFilling.filling {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Hemisphere.Sphere n) (v : Hemisphere.Ambient (n + 1)) : M :=
  H (radialTime v, direction b v)

theorem RadialFilling.filling_eq_center {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Hemisphere.Sphere n)
    (htop : ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c)
    {v : Hemisphere.Ambient (n + 1)} (hv : ‖v‖ ≤ 1 / 4) : filling H b v = c :=
  htop _ _ (three_quarters_le_radialTime hv)

theorem RadialFilling.filling_eq_boundary {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Hemisphere.Sphere n)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    {v : Hemisphere.Ambient (n + 1)} (hv : 3 / 4 ≤ ‖v‖) :
    filling H b v = f (direction b v) :=
  hbottom _ _ (radialTime_le_quarter hv)

theorem RadialFilling.filling_on_sphere {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Hemisphere.Sphere n)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    (v : Hemisphere.Sphere n) : filling H b v.1 = f v := by
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  rw [filling_eq_boundary H b hbottom (by rw [hn]; norm_num), direction_of_mem_sphere]

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.beltFaceCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    PuncturedHandle.UnitBall d.chart.NegativeCoordinates ≃ₜ
      PuncturedHandle.UnitBall d.chart.NegativeCoordinates :=
  (MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates).trans
    (MorseHandle.beltFaceDiskHomeomorph.trans
      (MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates).symm)

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.beltClosedDiskPoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (z :
      PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.chart.beltSource d.radius d.radius_pos :=
  ⟨(z.2, z.1.val),
    d.chart.enlarged_closed_belt_subset_source d.radius d.radius_pos d.block
      ⟨Set.mem_univ _, mem_closedBall_zero_iff.mpr (z.1.property.trans (by norm_num))⟩⟩

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.beltClosedDiskMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        PuncturedHandle.UnitSphere d.chart.PositiveCoordinates,
      d.UpperLevel)
    where
  toFun
    z := (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (d.beltClosedDiskPoint z)).val
  continuous_toFun := by
    have hc : Continuous d.beltClosedDiskPoint :=
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)).subtype_mk _
    exact
      continuous_subtype_val.comp
        ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous.comp hc)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.newPiece_beltFaceCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (u : PuncturedHandle.UnitBall d.chart.NegativeCoordinates)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.surgery.newPiece (d.beltFaceCoordinates u, v) = d.beltClosedDiskMap (u, v) := by
  let ud := MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates u
  let vd : MorseHandle.UnitDisk d.chart.PositiveCoordinates :=
    ⟨v.val, mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp v.property).le⟩
  have hv : ‖vd.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  let z := (MorseHandle.beltFaceDiskMap ud, vd)
  let x :
    ↥({x : M | f x ≤ f p - d.radius ^ 2} ∪
        Set.range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) :=
    ⟨d.chart.attachingHandleMap d.radius d.radius_pos d.block z, Or.inr ⟨z, rfl⟩⟩
  have hnew :
    (d.surgery.newPiece (d.beltFaceCoordinates u, v) : M) = (d.attachmentHomeomorph x).val :=
    d.newPiece_eq _
  have hfront :
    x.val ∈
      frontier
        ({y | f y ≤ f p - d.radius ^ 2} ∪
          Set.range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) := by
    apply (d.attachment_frontier x).mp
    rw [← hnew]
    exact (d.surgery.newPiece (d.beltFaceCoordinates u, v)).property
  have htgt := d.block (MorseHandle.modelMap_mem_product d.radius_pos z)
  have hsource : x.val ∈ d.chart.splitChart.source := d.chart.splitChart.map_target' htgt
  have hcoords : d.chart.splitChart x.val = MorseHandle.modelMap d.radius z :=
    d.chart.splitChart.right_inv' htgt
  have hend :
    MorseHandle.descentFlow (-MorseHandle.beltFaceTime ‖ud.val‖)
        (d.chart.splitChart x.val) =
      MorseHandle.beltLevelModel d.radius ud.val vd.val := by
    rw [hcoords]
    exact MorseHandle.descentFlow_neg_beltFaceTime d.radius ud vd hv
  have hpath :
    ∀ s ∈ Set.uIcc 0 (-MorseHandle.beltFaceTime ‖ud.val‖),
      MorseHandle.descentFlow s (d.chart.splitChart x.val) ∈
        Metric.closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
          Metric.closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) := by
    intro s hs
    rw [hcoords]
    exact MorseHandle.descentFlow_positiveFace_mem_block d.radius_pos ud vd hv hs
  have hlevel :
    f
        (d.chart.splitChart.symm
          (MorseHandle.descentFlow (-MorseHandle.beltFaceTime ‖ud.val‖)
            (d.chart.splitChart x.val))) =
      f p + d.radius ^ 2 := by
    rw [d.chart.splitChart_inverse_equation (d.block (hpath _ Set.right_mem_uIcc)), hend]
    have hh := MorseHandle.beltLevelModel_height d.radius_pos ud.val hv
    change
      -‖(MorseHandle.beltLevelModel d.radius ud.val vd.val).1‖ ^ 2 +
          ‖(MorseHandle.beltLevelModel d.radius ud.val vd.val).2‖ ^ 2 =
        d.radius ^ 2 at hh
    linarith
  have horbit :=
    d.attachment_model_orbits x hfront hsource (-MorseHandle.beltFaceTime ‖ud.val‖)
      (neg_nonpos.mpr (MorseHandle.beltFaceTime_nonneg _)) hpath hlevel
  apply Subtype.ext
  rw [hnew, horbit, hend]
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.range_newPiece_eq_range_beltClosedDiskMap
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) :
    Set.range d.surgery.newPiece = Set.range d.beltClosedDiskMap := by
  ext y
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    refine ⟨(d.beltFaceCoordinates.symm u, v), ?_⟩
    rw [← d.newPiece_beltFaceCoordinates, d.beltFaceCoordinates.apply_symm_apply]
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact ⟨(d.beltFaceCoordinates u, v), d.newPiece_beltFaceCoordinates u v⟩

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.beltClosedDiskMap_mem_newInterior_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (z :
      PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltClosedDiskMap z ∈ d.surgery.NewInterior ↔ ‖z.1.val‖ < 1 := by
  rw [← d.newPiece_beltFaceCoordinates z.1 z.2, d.surgery.newPiece_mem_newInterior_iff]
  exact MorseHandle.norm_beltFaceMap_lt_one_iff z.1.val

theorem MorseHandle.contDiff_beltFaceMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] : ContDiff ℝ ∞ (beltFaceMap (N := N)) := by
  have hs : ContDiff ℝ ∞ (fun u : N => Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun u => by positivity)).div_const _
  exact hs.smul contDiff_id

theorem MorseHandle.hasFDerivAt_beltFaceMap_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] :
    HasFDerivAt (beltFaceMap (N := N)) ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N) 0 := by
  have hs : ContDiff ℝ ∞ (fun u : N => Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun u => by positivity)).div_const _
  have hd := (hs.differentiable (by simp) (0 : N)).hasFDerivAt.smul (hasFDerivAt_id (0 : N))
  change HasFDerivAt (fun u : N => (Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) • u) _ 0
  simpa [Pi.smul_def'] using hd

theorem MorseHandle.hasFDerivAt_univUnitBall_symm_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] :
    HasFDerivAt (OpenPartialHomeomorph.univUnitBall.symm : N → N) (ContinuousLinearMap.id ℝ N)
      0 := by
  have hs : ContDiffAt ℝ ∞ (fun u : N => (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹) 0 := by
    apply ContDiffAt.inv
    · exact ((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffAt.sqrt (by simp))
    · simp
  have hd := (hs.differentiableAt (by simp)).hasFDerivAt.smul (hasFDerivAt_id (0 : N))
  change HasFDerivAt (fun u : N => (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹ • u) (ContinuousLinearMap.id ℝ N) 0
  simpa [Pi.smul_def'] using hd

def MorseHandle.beltCollapseCoordinate {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] (u : N) : N :=
  OpenPartialHomeomorph.univUnitBall.symm (beltFaceMap u)

theorem MorseHandle.beltCollapseCoordinate_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] : beltCollapseCoordinate (0 : N) = 0 := by
  rw [beltCollapseCoordinate, beltFaceMap_zero,
    OpenPartialHomeomorph.univUnitBall_symm_apply_zero]

theorem MorseHandle.contDiffOn_beltCollapseCoordinate {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] :
    ContDiffOn ℝ ∞ (beltCollapseCoordinate (N := N)) (Metric.ball 0 1) := by
  apply OpenPartialHomeomorph.contDiffOn_univUnitBall_symm.comp contDiff_beltFaceMap.contDiffOn
  intro u hu
  exact mem_ball_zero_iff.mpr ((norm_beltFaceMap_lt_one_iff u).mpr (mem_ball_zero_iff.mp hu))

theorem MorseHandle.hasFDerivAt_beltCollapseCoordinate_zero {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] :
    HasFDerivAt (beltCollapseCoordinate (N := N)) ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N)
      0 := by
  have hout :
    HasFDerivAt (OpenPartialHomeomorph.univUnitBall.symm : N → N) (ContinuousLinearMap.id ℝ N)
      (beltFaceMap 0) := by
    rw [beltFaceMap_zero]
    exact hasFDerivAt_univUnitBall_symm_zero
  change HasFDerivAt ((OpenPartialHomeomorph.univUnitBall.symm : N → N) ∘ beltFaceMap) _ 0
  simpa only [ContinuousLinearMap.id_comp] using hout.comp 0 hasFDerivAt_beltFaceMap_zero

theorem MorseHandle.hasFDerivAt_scaled_beltCollapseCoordinate_zero {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] (ρ : ℝ) :
    HasFDerivAt (fun u : N => beltCollapseCoordinate (ρ⁻¹ • u))
      (((Real.sqrt 2)⁻¹ * ρ⁻¹) • ContinuousLinearMap.id ℝ N) 0 := by
  have hout :
    HasFDerivAt (beltCollapseCoordinate (N := N)) ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N)
      (ρ⁻¹ • (0 : N)) := by
    simpa only [smul_zero] using hasFDerivAt_beltCollapseCoordinate_zero (N := N)
  simpa only [Function.comp_def, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp, smul_smul, mul_comm] using
    hout.comp 0 ((hasFDerivAt_id (0 : N)).const_smul ρ⁻¹)

theorem MorseHandle.scaled_beltCollapseCoordinate_factor_pos (ρ : ℝ) (hρ : 0 < ρ) :
    0 < (Real.sqrt 2)⁻¹ * ρ⁻¹ := by positivity

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.beltNormal_beltClosedDiskMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (z :
      PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltNormal (d.beltClosedDiskMap z) = d.radius • z.1.val :=
  d.chart.beltNeighborhoodHomeomorph_normal d.radius d.radius_pos (d.beltClosedDiskPoint z)

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.collapseNormal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (x : d.UpperLevel) :
    d.chart.NegativeCoordinates :=
  MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • d.beltNormal x)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.collapseNormal_belt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.collapseNormal (d.surgery.beltSphere v) = 0 := by
  rw [collapseNormal, d.beltNormal_belt, smul_zero, MorseHandle.beltCollapseCoordinate_zero]

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.mfderiv_collapseNormal_comp {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m)
    (hg : MDifferentiableAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x)
    (hx : g x ∈ Set.range d.surgery.beltSphere) :
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x =
      ((Real.sqrt 2)⁻¹ * d.radius⁻¹) •
        mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x := by
  obtain ⟨v, hv⟩ := hx
  have hzero : (d.beltNormal ∘ g) x = 0 := by
    change d.beltNormal (g x) = 0
    rw [← hv, d.beltNormal_belt]
  have hout :
    HasFDerivAt
      (fun u : d.chart.NegativeCoordinates =>
        MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • u))
      (((Real.sqrt 2)⁻¹ * d.radius⁻¹) • ContinuousLinearMap.id ℝ _) ((d.beltNormal ∘ g) x) := by
    rw [hzero]
    exact MorseHandle.hasFDerivAt_scaled_beltCollapseCoordinate_zero d.radius
  have h := (hout.hasMFDerivAt.comp x hg.hasMFDerivAt).mfderiv
  change mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x = _ at h
  apply h.trans
  apply ContinuousLinearMap.ext
  intro u
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.contMDiffAt_collapseNormal_comp {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (x : Hemisphere.Sphere m),
      g x ∈ Set.range d.surgery.beltSphere →
        ContMDiffAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ (d.collapseNormal ∘ g) x := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg x hx
  obtain ⟨v, hv⟩ := hx
  have hn : ContMDiffAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ (d.beltNormal ∘ g) x := by
    have hnormal :=
      (d.contMDiffOn_beltNormal hf).contMDiffAt
        (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
    rw [hv] at hnormal
    exact hnormal.comp x hg.contMDiffAt
  have hzero : (d.beltNormal ∘ g) x = 0 := by
    change d.beltNormal (g x) = 0
    rw [← hv, d.beltNormal_belt]
  have hq :
    ContDiffAt ℝ ∞ (MorseHandle.beltCollapseCoordinate (N := d.chart.NegativeCoordinates))
      (d.radius⁻¹ • (d.beltNormal ∘ g) x) := by
    rw [hzero, smul_zero]
    exact
      MorseHandle.contDiffOn_beltCollapseCoordinate.contDiffAt
        (Metric.isOpen_ball.mem_nhds (by simp))
  have hs :
    ContDiffAt ℝ ∞
      (fun u : d.chart.NegativeCoordinates =>
        MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • u))
      ((d.beltNormal ∘ g) x) :=
    hq.comp _ (contDiff_id.const_smul d.radius⁻¹).contDiffAt
  exact hs.contMDiffAt.comp x hn

def ManifoldMorse.MorseSurgeryData.upperLevelInclusion {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(d.UpperLevel, { y : M // f y ≤ f p + d.radius ^ 2 }) :=
  ⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩

def ManifoldMorse.MorseSurgeryData.bandSublevelHomeomorph {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) (T : M ≃ₜ M)
    (hT : T '' {y : M | f y ≤ f p + d.radius ^ 2} = {y : M | f y ≤ f q - d'.radius ^ 2}) :
    { y : M // f y ≤ f p + d.radius ^ 2 } ≃ₜ { y : M // f y ≤ f q - d'.radius ^ 2 } :=
  (T.image {y : M | f y ≤ f p + d.radius ^ 2}).trans (Homeomorph.setCongr hT)

structure ManifoldMorse.SurgeryWindows.BandData {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) where
  ambient : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞
  level : (S.data (S.point i)).UpperLevel ≃ₜ (S.data (S.point j)).LowerLevel
  sublevel_image :
    ambient '' {x : M | f x ≤ S.upper (S.point i)} = {x : M | f x ≤ S.lower (S.point j)}
  level_coe : ∀ x : (S.data (S.point i)).UpperLevel, (level x : M) = ambient x

theorem ManifoldMorse.SurgeryWindows.nonempty_consecutiveBandData {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin S.count) (hij : i.val + 1 = j.val) : Nonempty (S.BandData i j) := by
  let _ := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
  obtain ⟨D, b, hD, hb⟩ := S.exists_consecutiveBandBridge hf i j hij
  exact ⟨⟨D, b.toHomeomorph, hD, hb⟩⟩

def ManifoldMorse.SurgeryWindows.consecutiveBandData {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin S.count) (hij : i.val + 1 = j.val) : S.BandData i j :=
  Classical.choice (S.nonempty_consecutiveBandData hf i j hij)

def ManifoldMorse.SurgeryWindows.BandData.sublevelHomeomorph {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {S : ManifoldMorse.SurgeryWindows E f} {i j : Fin S.count} (D : S.BandData i j) :
    { x : M // f x ≤ S.upper (S.point i) } ≃ₜ { x : M // f x ≤ S.lower (S.point j) } :=
  (S.data (S.point i)).bandSublevelHomeomorph (S.data (S.point j)) D.ambient.toHomeomorph
    D.sublevel_image

theorem ManifoldMorse.MorseSurgeryData.attachingHomology_subsingleton_of_index {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) (hk : k ≠ 0)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (hne : Module.finrank ℝ d.chart.NegativeCoordinates ≠ k + 1) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k) := by
  let n := Module.finrank ℝ d.chart.NegativeCoordinates - 2
  have hn : Module.finrank ℝ d.chart.NegativeCoordinates = (n + 1) + 1 := by
    dsimp [n]
    omega
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = (n + 1) + 1) := ⟨hn⟩
  let :
    Subsingleton (SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :=
    SphereHomology.unitSphere_homology_subsingleton n k hk (by omega)
  exact
    (SingularHomology.homeomorphHomologyEquiv
        (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
            (n + 1)).symm.toHomeomorph
        k).injective.subsingleton

def ManifoldMorse.MorseSurgeryData.indexTwoNormalModel {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] d.chart.NegativeCoordinates :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [hindex])

def ManifoldMorse.SurgeryWindows.HasIndexTwoPrefix {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (n : ℕ) : Prop :=
  ∀ i : Fin S.count,
    0 < i.val → i.val ≤ n → Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2

theorem ManifoldMorse.SurgeryWindows.indexTwoPrefix_mono {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) {n m : ℕ} (hnm : n ≤ m)
    (h : S.HasIndexTwoPrefix m) : S.HasIndexTwoPrefix n := fun i hi hin => h i hi (hin.trans hnm)

def ManifoldMorse.MorseSurgeryData.indexThreeBoundaryEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2 ≃ₗ[ℤ]
      ℤ := by
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1) := ⟨hindex⟩
  let H :=
    SingularHomology.homeomorphHomologyEquiv
      (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 2).toHomeomorph
      2
  exact H.symm.trans (SphereHomology.unitSphereHomologyTopEquiv 1)

theorem ManifoldMorse.MorseSurgeryData.indexThreeBoundary_scalar {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :
    a = (d.indexThreeBoundaryEquiv hindex a) • (d.indexThreeBoundaryEquiv hindex).symm 1 := by
  apply (d.indexThreeBoundaryEquiv hindex).injective
  rw [map_zsmul, LinearEquiv.apply_symm_apply, zsmul_eq_mul, mul_one]
  simp

def ManifoldMorse.SurgeryWindows.HasIndexThreeBlock {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (r c : ℕ) : Prop :=
  ∀ i : Fin S.count,
    r < i.val →
      i.val ≤ r + c → Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3

theorem ManifoldMorse.SurgeryWindows.indexThreeBlock_mono {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) {r c b : ℕ} (hcb : c ≤ b)
    (h : S.HasIndexThreeBlock r b) : S.HasIndexThreeBlock r c := fun i hri hic =>
  h i hri (hic.trans (Nat.add_le_add_left hcb r))

theorem ManifoldMorse.SurgeryWindows.indexThreeBlock_last {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (r c : ℕ) (hc : r + (c + 1) < S.count)
    (h : S.HasIndexThreeBlock r (c + 1)) :
    Module.finrank ℝ (S.data (S.point ⟨r + (c + 1), hc⟩)).chart.NegativeCoordinates = 3 :=
  h ⟨r + (c + 1), hc⟩ (by change r < r + (c + 1); omega) le_rfl

def ManifoldMorse.SurgeryWindows.lastUpperHomeomorph {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    { x : M // f x ≤ S.upper (S.last h) } ≃ₜ M :=
  (Homeomorph.setCongr (S.last_upper_univ hf h)).trans (Homeomorph.Set.univ M)

end
