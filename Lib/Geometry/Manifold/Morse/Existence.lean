/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Flow.Compact
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.Morse.HandleAttachment
public import Lib.Geometry.Manifold.Flow.HeightTranslating

/-!
# Existence of Morse functions and smoothing

Every compact smooth manifold admits a Morse function (Milnor, h-cobordism Thm 2.5), built
by chart-wise perturbation (`ChartMapPerturbation.*`), smoothing
(`ManifoldSmoothing.*`), and relative homotopies (`HomotopicRelWithin.*`).

## Main definitions and results

* `ChartMapPerturbation.*`, `ManifoldSmoothing.*`, `HomotopicRelWithin.*`.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], Theorem 2.5

## Tags

Morse function existence, perturbation, smoothing
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Attaching unions of a signed Morse chart -/

attribute [local instance 100] Classical.propDecidable in
/-- The attaching union is homeomorphic to the model with level and orbit control. -/
theorem ManifoldMorse.SignedMorseChart.exists_attachingUnionHomeomorph_with_level_and_orbits
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hband :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) :
    ∃ e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 },
      (∀ x,
          f (e x) = f p + ρ ^ 2 ↔
            x.val ∈
              frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock))) ∧
        (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) ∧
          (∀ x,
            x.val ∈
                frontier
                  ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) →
              ∀ t : ℝ, t ≤ 0 → f (F t x.val) = f p + ρ ^ 2 → (e x).val = F t x.val) := by
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hboundary (b : ℝ) (hb : b ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p) (x : M)
    (hx : f x = b) (t : ℝ) (ht : 0 < t) : f (F t x) < f x := by
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxp := hband x hcrit (hx ▸ hb)
      exact hne (hx.symm.trans (congrArg f hxp))
    simpa only [F.map_zero_apply] using
      FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hreg ht
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x :=
    hboundary _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have htop : ∀ x, f x = f p + ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f p + ρ ^ 2 := by
    intro x hx t ht
    rw [← hx]
    exact
      hboundary _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ]) x hx t ht
  have hhome :=
    FlowConstruction.exists_absorbingSublevelHomeomorph_with_boundary_orbits hf hV hdesc F
      hcurve hmono
      ((isClosed_le hf.continuous continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
      Set.subset_union_left (c.attachingHandleUnion_subset_upper ρ hρ hblock) (a := f p - ρ ^ 2)
      (fun x hcrit hx => by
        have hxp := hband x hcrit hx
        subst x
        exact
          interior_mono Set.subset_union_right
            (c.mem_interior_range_attachingHandleMap ρ hρ hblock))
      (c.forwardInvariant_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement)
      (c.interior_entry_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement
        hbottom)
      htop
  obtain ⟨e, hfront, hfixed, horbit⟩ := hhome
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · intro x
    have hx := hfront (e.symm x)
    rw [e.apply_symm_apply,
      FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop] at hx
    exact hx.symm
  · intro x hx
    let y : { x : M // f x ≤ f p + ρ ^ 2 } := ⟨x.val, hx.le⟩
    have hy : y.val ∈ frontier {z : M | f z ≤ f p + ρ ^ 2} := by
      rw [FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop]
      exact hx
    have heq : e y = x := Subtype.ext (hfixed y x.property hy)
    have hh := congrArg e.symm heq
    rw [e.symm_apply_apply] at hh
    exact congrArg (fun z : { z : M // f z ≤ f p + ρ ^ 2 } => z.val) hh.symm
  · intro x hx t ht hlevel
    apply horbit x hx t ht
    rw [FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop]
    exact hlevel

attribute [local instance 100] Classical.propDecidable in
/-- A homotopy follows the model boundary orbits of the chart. -/
def ManifoldMorse.SignedMorseChart.FollowsModelBoundaryOrbits {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 }) :
    Prop :=
  ∀ x,
    x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) →
      x.val ∈ c.splitChart.source →
        ∀ t : ℝ,
          t ≤ 0 →
            (∀ s ∈ Set.uIcc 0 t,
                MorseHandle.descentFlow s (c.splitChart x.val) ∈
                  Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                    Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ)) →
              f (c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x.val))) =
                  f p + ρ ^ 2 →
                (e x).val =
                  c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x.val))

attribute [local instance 100] Classical.propDecidable in
/-- The flow follows the model boundary orbits. -/
theorem ManifoldMorse.SignedMorseChart.followsModelBoundaryOrbits_of_flow {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (horbit :
      ∀ x,
        x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) →
          ∀ t : ℝ, t ≤ 0 → f (F t x.val) = f p + ρ ^ 2 → (e x).val = F t x.val) :
    c.FollowsModelBoundaryOrbits ρ hρ hblock e := by
  intro x hx hsource t ht hpath hlevel
  have hmodel :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hcurve hsource (fun s hs => hblock (hpath s hs))
      (fun s hs => heq _ (hpath s hs))
  exact (horbit x hx t ht (hmodel ▸ hlevel)).trans hmodel

attribute [local instance 100] Classical.propDecidable in
/-- A closed product block inside a prescribed set exists. -/
theorem ManifoldMorse.SignedMorseChart.exists_closed_productBlock_in {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) {W : Set M} (hW : IsOpen W)
    (hpW : p ∈ W) :
    ∃ r > (0 : ℝ),
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target := by
    rw [← c.splitChart_center]
    exact e.map_source c.splitChart_mem_source
  have hinv : e.symm 0 = p := by
    rw [← c.splitChart_center]
    exact e.left_inv c.splitChart_mem_source
  have hmem : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target ∩ e.symm ⁻¹' W :=
    ⟨hzero, by simpa only [Set.mem_preimage, hinv] using hpW⟩
  obtain ⟨r, hr, hsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp ((e.isOpen_inter_preimage_symm hW).mem_nhds hmem)
  refine ⟨r, hr, ?_⟩
  rw [closedBall_prod_same]
  exact hsub

attribute [local instance 100] Classical.propDecidable in
/-- A field-compatible block of the signed chart exists. -/
theorem ManifoldMorse.SignedMorseChart.exists_fieldCompatibleBlock {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) :
    ∃ ρ > (0 : ℝ),
      ∃ W : Set M,
        IsOpen W ∧
          p ∈ W ∧
            (∀ x ∈ W, V x = c.descentField x) ∧
              Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                  Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
                c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
  obtain ⟨W, hWeq, hW, hpW⟩ := mem_nhds_iff.mp heq
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hW hpW
  refine ⟨r / 2, half_pos hr, W, hW, hpW, hWeq, ?_⟩
  rw [show 2 * (r / 2) = r by ring]
  exact hblock

/-- Critical points can be isolated: a radius exists so that the ball around a critical point contains no other critical point (discreteness made quantitative; Milnor, Morse Theory, Section 2). -/
theorem ManifoldMorse.exists_isolating_radius {X : Type*} {f : X → ℝ} {K : Set X}
    (hK : K.Finite) (p : X) (hunique : ∀ x ∈ K, f x = f p → x = p) {R : ℝ} (hR : 0 < R) :
    ∃ ρ > (0 : ℝ), ρ < R ∧ ∀ x ∈ K, f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  have hfin : (f '' (K \ { p })).Finite := (hK.subset Set.sdiff_subset).image f
  have hnot : f p ∉ f '' (K \ { p }) := by
    rintro ⟨x, hx, heq⟩
    exact hx.2 (Set.mem_singleton_iff.mpr (hunique x hx.1 heq))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl (f p) hnot
  let ρ := Min.min (R / 2) (Min.min 1 (δ / 2))
  have hρ : 0 < ρ := lt_min (half_pos hR) (lt_min zero_lt_one (half_pos hδ))
  have hρR : ρ < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hρone : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < δ := by nlinarith
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro x hx hval
  by_contra hxp
  have hd : Dist.dist (f x) (f p) < δ := by
    rw [Real.dist_eq]
    have ha : |f x - f p| ≤ ρ ^ 2 := abs_le.mpr ⟨by linarith [hval.1], by linarith [hval.2]⟩
    exact ha.trans_lt hρsq
  exact hball hd ⟨x, ⟨hx, by simpa only [Set.mem_singleton_iff] using hxp⟩, rfl⟩

attribute [local instance 100] Classical.propDecidable in
/-- An isolated field-compatible block below a level exists. -/
theorem ManifoldMorse.SignedMorseChart.exists_isolated_fieldCompatibleBlock_lt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hunique : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x = f p → x = p)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ > (0 : ℝ),
      ρ < ε ∧
        ∃ W : Set M,
          IsOpen W ∧
            p ∈ W ∧
              (∀ x ∈ W, V x = c.descentField x) ∧
                (Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                      Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
                    c.splitChart.target ∩ c.splitChart.symm ⁻¹' W) ∧
                  ∀ x ∈ ManifoldMorse.criticalPoints E f,
                    f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  obtain ⟨R, hR, W, hW, hpW, heqW, hblock⟩ := c.exists_fieldCompatibleBlock V heq
  obtain ⟨ρ, hρ, hρbound, hband⟩ :=
    ManifoldMorse.exists_isolating_radius hfinite p hunique (lt_min hR hε)
  have hρR : ρ < R := hρbound.trans_le (min_le_left _ _)
  have hρε : ρ < ε := hρbound.trans_le (min_le_right _ _)
  refine ⟨ρ, hρ, hρε, W, hW, hpW, heqW, ?_, hband⟩
  intro z hz
  apply hblock
  have hr : 2 * ρ ≤ 2 * R := mul_le_mul_of_nonneg_left hρR.le (by norm_num)
  exact ⟨Metric.closedBall_subset_closedBall hr hz.1, Metric.closedBall_subset_closedBall hr hz.2⟩

/-! ### Regular loci -/

/-- The regular-in-chart locus is open. -/
theorem ManifoldMorse.isOpen_regularInChart {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    IsOpen {q : P × M | q.2 ∈ e.source ∧ fderiv ℝ (f q.1 ∘ e.symm) (e q.2) ≠ 0} := by
  have hU : IsOpen {q : P × E | q.2 ∈ e.target} := e.open_target.preimage continuous_snd
  have hd :=
    MorsePerturbation.contDiffOn_spatialDerivative (f := fun a y => f a (e.symm y)) hU
      (contDiffOn_inChart hf he)
  have hg :=
    hd.continuousOn.isOpen_inter_preimage hU
      (isClosed_singleton (x := (0 : E →L[ℝ] ℝ))).isOpen_compl
  let S : Set (P × M) := {q | q.2 ∈ e.source}
  have hS : IsOpen S := e.open_source.preimage continuous_snd
  have hm : ContinuousOn (fun q : P × M => (q.1, e q.2)) S :=
    continuous_fst.continuousOn.prodMk
      (e.continuousOn.comp continuous_snd.continuousOn (fun _ hq => hq))
  convert hm.isOpen_inter_preimage hS hg using 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
    Set.mem_singleton_iff, S]
  constructor
  · rintro ⟨hq, hn⟩
    exact ⟨hq, e.map_source hq, hn⟩
  · rintro ⟨hq, -, hn⟩
    exact ⟨hq, hn⟩

/-- Regular points are open: the set where the differential of a family of functions is nonzero is open (transversality openness; Hatcher, Algebraic Topology, Section 0). -/
theorem ManifoldMorse.isOpen_regularPoint {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) :
    IsOpen {q : P × M | q.2 ∉ criticalPoints E (f q.1)} := by
  have hslice (a : P) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f a) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  rw [isOpen_iff_mem_nhds]
  intro q hq
  let e := chartAt E q.2
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas q.2
  have hx : q.2 ∈ e.source := mem_chart_source E q.2
  have hmem : q ∈ {r : P × M | r.2 ∈ e.source ∧ fderiv ℝ (f r.1 ∘ e.symm) (e r.2) ≠ 0} :=
    ⟨hx, fun hz => hq ((mem_criticalPoints_iff (hslice q.1) he hx).mpr hz)⟩
  apply Filter.mem_of_superset ((isOpen_regularInChart hf he).mem_nhds hmem)
  intro r hr hcrit
  exact hr.2 ((mem_criticalPoints_iff (hslice r.1) he hr.1).mp hcrit)

/-- The regular locus is open. -/
theorem ManifoldMorse.isOpen_regularOn {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) {K : Set M}
    (hK : IsCompact K) : IsOpen {a : P | ∀ x ∈ K, x ∉ criticalPoints E (f a)} :=
  MorsePerturbation.isOpen_forall_mem_compact hK (isOpen_regularPoint hf)

/-- Perturbation stability of critical points: for small enough parameters the critical-point set stabilizes (Milnor, h-cobordism Theorem 2.5 machinery). -/
theorem ManifoldMorse.eventually_criticalPoints_eq {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) (a₀ : P) {U : Set M}
    (hU : IsOpen U) (hcover : criticalPoints E (f a₀) ⊆ U)
    (hfixed : ∀ a x, x ∈ U → (x ∈ criticalPoints E (f a) ↔ x ∈ criticalPoints E (f a₀))) :
    ∀ᶠ a in 𝓝 a₀, criticalPoints E (f a) = criticalPoints E (f a₀) := by
  have hreg : ∀ x ∈ Uᶜ, x ∉ criticalPoints E (f a₀) := fun x hx hc => hx (hcover hc)
  have hn := (isOpen_regularOn hf hU.isClosed_compl.isCompact).mem_nhds hreg
  filter_upwards [hn] with a ha
  ext x
  by_cases hx : x ∈ U
  · exact hfixed a x hx
  · exact iff_of_false (ha x hx) (hreg x hx)

/-! ### Constant perturbations -/

/-- The perturbation of a function by a constant shift. -/
def ManifoldMorse.constantPerturb {M : Type*} (f ψ : M → ℝ) (a : ℝ) (x : M) : ℝ :=
  f x + a * ψ x

/-- The constant perturbation is smooth. -/
theorem ManifoldMorse.contMDiff_constantPerturb {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ψ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry (constantPerturb f ψ)) :=
  (hf.comp contMDiff_snd).add (contMDiff_fst.smul (hψ.comp contMDiff_snd))

/-- A locally constant perturbation does not change the derivative. -/
theorem ManifoldMorse.mfderiv_constantPerturb_of_locally_constant {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} {b : ℝ} (hψ : ψ =ᶠ[𝓝 x] fun _ => b) (a : ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (constantPerturb f ψ a) x = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x := by
  have heq : constantPerturb f ψ a =ᶠ[𝓝 x] (fun y => f y + a * b) := by
    filter_upwards [hψ] with y hy
    simp only [constantPerturb, hy]
  rw [heq.mfderiv_eq]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f + fun _ => a * b) x = _
  rw [mfderiv_add (hf.mdifferentiableAt (by simp)) mdifferentiableAt_const, mfderiv_const]
  exact add_zero _

/-- Small constant perturbations preserve the Morse critical points. -/
theorem ManifoldMorse.eventually_constantPerturb_morse_criticalPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ψ)
    (hconstant : ∀ p ∈ criticalPoints E f, ∃ b : ℝ, ψ =ᶠ[𝓝 p] fun _ => b) :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      IsMorse E (constantPerturb f ψ a) ∧
        criticalPoints E (constantPerturb f ψ a) = criticalPoints E f := by
  have hfamily := contMDiff_constantPerturb hf hψ
  have hzero : constantPerturb f ψ 0 = f := by funext x; simp [constantPerturb]
  have hm₀ : IsMorseOn E (constantPerturb f ψ 0) Set.univ := by
    rw [hzero]
    exact fun x _ => hm x
  have hmor := (isOpen_isMorseOn hfamily isCompact_univ).mem_nhds hm₀
  let U := ⋃ b : ℝ, interior {x : M | ψ x = b}
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_interior)
  have hcover : criticalPoints E (constantPerturb f ψ 0) ⊆ U := by
    rw [hzero]
    intro p hp
    obtain ⟨b, hb⟩ := hconstant p hp
    exact Set.mem_iUnion.mpr ⟨b, mem_interior_iff_mem_nhds.mpr hb⟩
  have hfixed :
    ∀ a x,
      x ∈ U →
        (x ∈ criticalPoints E (constantPerturb f ψ a) ↔
          x ∈ criticalPoints E (constantPerturb f ψ 0)) := by
    intro a x hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    have hlocal : ψ =ᶠ[𝓝 x] fun _ => b := mem_interior_iff_mem_nhds.mp hb
    rw [hzero]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (constantPerturb f ψ a) x = 0 ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
    rw [mfderiv_constantPerturb_of_locally_constant hf hlocal a]
    rfl
  have hcrit := eventually_criticalPoints_eq hfamily 0 hU hcover hfixed
  rw [hzero] at hcrit
  filter_upwards [hmor, hcrit] with a ha hc
  exact ⟨fun x => ha x (Set.mem_univ x), hc⟩

/-- Critical values can be separated: between any two critical levels there is a regular level, the running hypothesis of the Morse-handle induction (Milnor, Morse Theory, Section 3). -/
theorem ManifoldMorse.exists_separating_critical_value {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) (p : M) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        IsMorse E g ∧
          criticalPoints E g = criticalPoints E f ∧
            (∀ x ∈ criticalPoints E f, x ≠ p → g x = f x) ∧
              ∀ x ∈ criticalPoints E f, g x = g p → x = p := by
  classical
  let K := criticalPoints E f
  have hK : K.Finite := finite_criticalPoints hf hm
  have hclosed : IsClosed (K \ { p }) := (hK.subset Set.sdiff_subset).isClosed
  have hp : p ∈ (K \ { p })ᶜ := by simp
  obtain ⟨ψ, _, hψsub⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p).mem_iff.mp
      (hclosed.isOpen_compl.mem_nhds hp)
  have hψone : (ψ : M → ℝ) =ᶠ[𝓝 p] fun _ => 1 := ψ.eventuallyEq_one
  have hψzero (x : M) (hx : x ∈ K) (hxp : x ≠ p) : (ψ : M → ℝ) =ᶠ[𝓝 x] fun _ => 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h
    exact hψsub h ⟨hx, by simpa only [Set.mem_singleton_iff] using hxp⟩
  have hconstant : ∀ x ∈ criticalPoints E f, ∃ b : ℝ, (ψ : M → ℝ) =ᶠ[𝓝 x] fun _ => b := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      exact ⟨1, hψone⟩
    · exact ⟨0, hψzero x hx hxp⟩
  have hstable := eventually_constantPerturb_morse_criticalPoints hf hm ψ.contMDiff hconstant
  let T : Set ℝ := (fun x => f x - f p) '' (K \ { p })
  have hT : T.Finite := (hK.subset Set.sdiff_subset).image _
  have hdense : Dense Tᶜ := by
    have heq : (Set.univ : Set ℝ) \ T = Tᶜ := by
      ext a
      exact and_iff_right (Set.mem_univ a)
    rw [← heq]
    exact dense_univ.sdiff_finite hT
  obtain ⟨U, hUstable, hU, hzeroU⟩ := _root_.mem_nhds_iff.mp hstable
  obtain ⟨a, haT, haU⟩ := hdense.exists_mem_open hU ⟨0, hzeroU⟩
  let g := constantPerturb f ψ a
  have hvalues (x : M) (hx : x ∈ K) (hxp : x ≠ p) : g x = f x := by
    have hxzero : ψ x = 0 := (hψzero x hx hxp).eq_of_nhds
    simp only [g, constantPerturb, hxzero, MulZeroClass.mul_zero, add_zero]
  have hpvalue : g p = f p + a := by
    have hpone : ψ p = 1 := hψone.eq_of_nhds
    simp only [g, constantPerturb, hpone, mul_one]
  refine
    ⟨g, (contMDiff_constantPerturb hf ψ.contMDiff).comp (contMDiff_const.prodMk contMDiff_id),
      (hUstable haU).1, (hUstable haU).2, hvalues, ?_⟩
  intro x hx heq
  by_contra hxp
  have hax : f x - f p = a := by rw [hvalues x hx hxp, hpvalue] at heq; linarith
  exact haT ⟨x, ⟨hx, by simpa only [Set.mem_singleton_iff] using hxp⟩, hax⟩

/-- Critical values can be made pairwise distinct by an arbitrarily small perturbation (Milnor, h-cobordism Theorem 2.5). -/
theorem ManifoldMorse.exists_distinct_critical_values {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        IsMorse E g ∧
          criticalPoints E g = criticalPoints E f ∧ Set.InjOn g (criticalPoints E g) := by
  classical
  let K := criticalPoints E f
  have hK : K.Finite := finite_criticalPoints hf hm
  have hfinite :
    ∀ s : Finset M,
      (s : Set M) ⊆ K →
        ∃ g : M → ℝ,
          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
            IsMorse E g ∧ criticalPoints E g = K ∧ Set.InjOn g (s : Set M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨f, hf, hm, rfl, by simp⟩
    | @insert p s hps ih =>
      intro hsK
      have hsK' : (s : Set M) ⊆ K := fun x hx => hsK (Finset.mem_insert_of_mem hx)
      obtain ⟨g, hg, hmg, hcrit, hinj⟩ := ih hsK'
      obtain ⟨g', hg', hmg', hcrit', hfixed, hunique⟩ := exists_separating_critical_value hg hmg p
      have hK' : criticalPoints E g' = K := hcrit'.trans hcrit
      refine ⟨g', hg', hmg', hK', ?_⟩
      intro x hx y hy heq
      have hxcrit : x ∈ criticalPoints E g := hcrit ▸ hsK hx
      have hycrit : y ∈ criticalPoints E g := hcrit ▸ hsK hy
      by_cases hxp : x = p
      · subst x
        exact (hunique y hycrit heq.symm).symm
      by_cases hyp : y = p
      · subst y
        exact hunique x hxcrit heq
      have hxs : x ∈ (s : Set M) := (Finset.mem_insert.mp hx).resolve_left hxp
      have hys : y ∈ (s : Set M) := (Finset.mem_insert.mp hy).resolve_left hyp
      apply hinj hxs hys
      rw [← hfixed x hxcrit hxp, ← hfixed y hycrit hyp]
      exact heq
  obtain ⟨g, hg, hmg, hcrit, hinj⟩ := hfinite hK.toFinset (by simp)
  refine ⟨g, hg, hmg, hcrit, ?_⟩
  rw [hcrit]
  simpa only [hK.coe_toFinset] using hinj

/-- A Morse function with all critical values distinct exists on every compact smooth manifold - the form used throughout the handle induction (Milnor, h-cobordism Theorem 2.5; Hatcher, Algebraic Topology, Section 0). -/
theorem ManifoldMorse.exists_morse_function_with_distinct_critical_values (E : Type*)
    (M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        IsMorse E f ∧ (criticalPoints E f).Finite ∧ Set.InjOn f (criticalPoints E f) := by
  obtain ⟨f, hf, hm⟩ := exists_morse_function E M
  obtain ⟨g, hg, hmg, _, hinj⟩ := exists_distinct_critical_values hf hm
  exact ⟨g, hg, hmg, finite_criticalPoints hg hmg, hinj⟩

attribute [local instance 100] Classical.propDecidable in
/-- A Morse boundary attachment with model orbits exists below a level. -/
theorem ManifoldMorse.exists_morse_boundary_attachment_with_model_orbits_lt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ),
      ρ < ε ∧
        ∃ c : SignedMorseChart (E := E) f p,
          ∃ hblock :
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
              c.splitChart.target,
            ∃ e :
              ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
                { x : M // f x ≤ f p + ρ ^ 2 },
              (∀ x,
                  f (e x) = f p + ρ ^ 2 ↔
                    x.val ∈
                      frontier
                        ({y | f y ≤ f p - ρ ^ 2} ∪
                          Set.range (c.attachingHandleMap ρ hρ hblock))) ∧
                (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) ∧
                  (frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) ∧
                    (∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) ∧
                      (∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) ∧
                        c.FollowsModelBoundaryOrbits ρ hρ hblock e ∧
                          ∀ x ∈ criticalPoints E f,
                            f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  obtain ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, _, _, _⟩ :=
    FlowConstruction.exists_adaptedDescentFlow hf hm
  obtain ⟨c, heq⟩ := hcharts p hp
  obtain ⟨ρ, hρ, hρε, W, hW, _, heqW, hblockW, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock_lt (finite_criticalPoints hf hm) hunique V heq hε
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hagreement :
    ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    have hxW : c.attachingHandleMap ρ hρ hblock z ∈ W :=
      (hblockW (MorseHandle.modelMap_mem_product hρ z)).2
    filter_upwards [hW.mem_nhds hxW] with y hy
    exact heqW y hy
  obtain ⟨e, hfront, hfixed, horbit⟩ :=
    c.exists_attachingUnionHomeomorph_with_level_and_orbits hf hV hzero hdesc F hcurve ρ hρ hblock
      hagreement hband
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hregular (b : ℝ) (hb : b ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p) (x : M)
    (hx : f x = b) : x ∉ criticalPoints E f := by
    intro hcrit
    have hxp := hband x hcrit (hx ▸ hb)
    exact hne (hx.symm.trans (congrArg f hxp))
  have hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f p - ρ ^ 2 := by
    intro x hx t ht
    have hstrict :=
      FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp)) F hcurve hzero hdesc
        (hlower x hx) ht
    simpa only [F.map_zero_apply, hx] using hstrict
  refine
    ⟨ρ, hρ, hρε, c, hblock, e, hfront, hfixed,
      FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono hbottom,
      hlower, hupper, ?_, hband⟩
  apply
    c.followsModelBoundaryOrbits_of_flow (hV.of_le (by simp)) F hcurve ρ hρ hblock (e := e)
      (horbit := horbit)
  intro z hz
  filter_upwards [hW.mem_nhds (hblockW hz).2] with y hy
  exact heqW y hy

/-! ### Surgery boundary pairs -/

/-- The boundary pair with the new boundary exchanged. -/
def SurgeryBoundaryPair.changeNewBoundary {N P R X Y Z : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (d : SurgeryBoundaryPair N P R X Y) (e : Y ≃ₜ Z) :
    SurgeryBoundaryPair N P R X Z
    where
  oldExterior := d.oldExterior
  newExterior := e ∘ d.newExterior
  oldPiece := d.oldPiece
  newPiece := e ∘ d.newPiece
  oldExterior_closed := d.oldExterior_closed
  newExterior_closed := e.isClosedEmbedding.comp d.newExterior_closed
  oldPiece_closed := d.oldPiece_closed
  newPiece_closed := e.isClosedEmbedding.comp d.newPiece_closed
  old_cover := d.old_cover
  new_cover := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : e.symm z ∈ Set.range d.newExterior ∪ Set.range d.newPiece := by
      rw [d.new_cover]
      trivial
    rcases hz with ⟨r, hr⟩ | ⟨p, hp⟩
    · exact Or.inl ⟨r, (congrArg e hr).trans (e.apply_symm_apply z)⟩
    · exact Or.inr ⟨p, (congrArg e hp).trans (e.apply_symm_apply z)⟩
  boundary := d.boundary
  old_overlap := d.old_overlap
  new_overlap := fun r p => e.injective.eq_iff.trans (d.new_overlap r p)

/-- The frontier of a closed cover piece is level-homeomorphic. -/
def ClosedCover.frontierLevelHomeomorph {M : Type*} [TopologicalSpace M] {f : M → ℝ} {b : ℝ}
    {A : Set M} (hA : IsClosed A) (e : A ≃ₜ { x : M // f x ≤ b })
    (he : ∀ x, f (e x) = b ↔ (x : M) ∈ frontier A) : frontier A ≃ₜ { x : M // f x = b } := by
  have hsub : frontier A ⊆ A := by
    intro x hx
    have hc := frontier_subset_closure hx
    rwa [hA.closure_eq] at hc
  let toA : frontier A → A := Set.inclusion hsub
  let toB : { x : M // f x = b } → { x : M // f x ≤ b } := fun x => ⟨x, x.property.le⟩
  refine
    { toFun := fun x => ⟨e (toA x), (he (toA x)).mpr x.property⟩
      invFun := fun y => ⟨e.symm (toB y), ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply (he (e.symm (toB y))).mp
    rw [e.apply_symm_apply]
    exact y.property
  · intro x
    apply Subtype.ext
    exact congrArg (fun z : A => (z : M)) (e.symm_apply_apply (toA x))
  · intro y
    apply Subtype.ext
    exact congrArg (fun z : { x : M // f x ≤ b } => (z : M)) (e.apply_symm_apply (toB y))
  · exact
      (continuous_subtype_val.comp
            (e.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk
        _
  · exact
      (continuous_subtype_val.comp
            (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk
        _

/-- The boundary exchange preserves incidence. -/
theorem SurgeryBoundaryPair.exchange_preserves_incidence {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair E F R X Y) (r : R)
    (p : PuncturedHandle.UnitSphere E × PuncturedHandle.PuncturedBall F) :
    d.oldExteriorMap r = d.oldPuncturedMap p ↔
      d.newExteriorMap r = d.newPuncturedMap (PuncturedHandle.exchange E F p) := by
  rw [d.oldPunctured_overlap, d.newPunctured_overlap]
  constructor
  · rintro ⟨q, hr, rfl⟩
    exact ⟨q, hr, PuncturedHandle.exchange_boundary q.1 q.2⟩
  · rintro ⟨q, hr, hq⟩
    refine ⟨q, hr, (PuncturedHandle.exchange E F).injective ?_⟩
    exact hq.trans (PuncturedHandle.exchange_boundary q.1 q.2).symm

/-- The boundary-pair complements are homeomorphic. -/
def SurgeryBoundaryPair.complementHomeomorph {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace R]
    [TopologicalSpace X] [TopologicalSpace Y] (d : SurgeryBoundaryPair E F R X Y) :
    d.OldComplement ≃ₜ d.NewComplement :=
  ClosedCover.homeomorphOfClosedPieces d.oldExteriorMap d.newExteriorMap d.oldPuncturedMap
    d.newPuncturedMap d.isClosedEmbedding_oldExteriorMap d.isClosedEmbedding_newExteriorMap
    d.isClosedEmbedding_oldPuncturedMap d.isClosedEmbedding_newPuncturedMap d.oldComplement_cover
    d.newComplement_cover (PuncturedHandle.exchange E F) d.exchange_preserves_incidence

attribute [local instance 100] Classical.propDecidable in
/-- The chart's boundary levels are homeomorphic. -/
def ManifoldMorse.SignedMorseChart.boundaryLevelHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (he :
      ∀ x,
        f (e x) = f p + ρ ^ 2 ↔
          x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock))) :
    frontier ({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.normHandleMap ρ hρ hblock)) ≃ₜ
      { x : M // f x = f p + ρ ^ 2 } :=
  (Homeomorph.setCongr (by rw [c.range_normHandleMap ρ hρ hblock])).trans
    (ClosedCover.frontierLevelHomeomorph
      ((isClosed_le hf continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
      e he)

attribute [local instance 100] Classical.propDecidable in
/-- The surgery boundary pair of a signed chart level. -/
def ManifoldMorse.SignedMorseChart.levelSurgeryBoundaryPair {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2})
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (he :
      ∀ x,
        f (e x) = f p + ρ ^ 2 ↔
          x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock))) :
    SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates
      { x : M //
        f x = f p - ρ ^ 2 ∧
          x ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.normHandleMap ρ hρ hblock)) }
      { x : M // f x = f p - ρ ^ 2 } { x : M // f x = f p + ρ ^ 2 } :=
  (c.attachmentBoundaryData hf ρ hρ hblock hlevel).surgeryBoundaryPair.changeNewBoundary
    (c.boundaryLevelHomeomorph hf ρ hρ hblock e he)

attribute [local instance 100] Classical.propDecidable in
/-- The belt sphere's height in the handle map. -/
theorem ManifoldMorse.SignedMorseChart.normHandleMap_belt_height {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    f
        (c.normHandleMap ρ hρ hblock
          (PuncturedHandle.ballZero, PuncturedHandle.sphereToBall v)) =
      f p + ρ ^ 2 := by
  change
    f
        (c.attachingHandleMap ρ hρ hblock
          (⟨0, by simp⟩,
            ⟨(v : c.PositiveCoordinates), Metric.sphere_subset_closedBall v.property⟩)) =
      _
  rw [c.attachingHandleMap_quadratic]
  have hv : ‖(v : c.PositiveCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  simp [MorseHandle.modelMap, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hv]

/-! ### The belt core map -/

attribute [local instance 100] Classical.propDecidable in
/-- The belt core map into the handle. -/
def ManifoldMorse.SignedMorseChart.beltCoreMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(PuncturedHandle.UnitSphere c.PositiveCoordinates, { y : M // f y = f p + ρ ^ 2 })
    where
  toFun
    v :=
    ⟨c.normHandleMap ρ hρ hblock
        (PuncturedHandle.ballZero, PuncturedHandle.sphereToBall v),
      c.normHandleMap_belt_height ρ hρ hblock v⟩
  continuous_toFun :=
    ((c.normHandleMap ρ hρ hblock).continuous.comp
          (continuous_const.prodMk (continuous_subtype_val.subtype_mk _))).subtype_mk
      _

attribute [local instance 100] Classical.propDecidable in
/-- The belt core map computes the belt point. -/
theorem ManifoldMorse.SignedMorseChart.beltCoreMap_coe {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    (c.beltCoreMap ρ hρ hblock v : M) = c.splitChart.symm (0, ρ • (v : c.PositiveCoordinates)) := by
  change
    c.splitChart.symm
        ((ρ * Real.sqrt (1 + ‖(v : c.PositiveCoordinates)‖ ^ 2)) • (0 : c.NegativeCoordinates),
          ρ • (v : c.PositiveCoordinates)) =
      _
  simp only [smul_zero]

attribute [local instance 100] Classical.propDecidable in
/-- The belt core map is smooth into the ambient manifold. -/
theorem ManifoldMorse.SignedMorseChart.contMDiff_beltCoreMap_ambient {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val ∘ c.beltCoreMap ρ hρ hblock) := by
  have heq :
    Subtype.val ∘ c.beltCoreMap ρ hρ hblock =
      fun v : PuncturedHandle.UnitSphere c.PositiveCoordinates =>
      c.splitChart.symm (0, ρ • (v : c.PositiveCoordinates)) :=
    funext (c.beltCoreMap_coe ρ hρ hblock)
  rw [heq]
  have hcoe :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.PositiveCoordinates) ∞
      (Subtype.val :
        PuncturedHandle.UnitSphere c.PositiveCoordinates → c.PositiveCoordinates) :=
    contMDiff_coe_sphere (E := c.PositiveCoordinates) (n := n)
  have hscalar :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun _ : PuncturedHandle.UnitSphere c.PositiveCoordinates => ρ) :=
    contMDiff_const
  have hpositive :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.PositiveCoordinates) ∞
      (fun v : PuncturedHandle.UnitSphere c.PositiveCoordinates =>
        ρ • (v : c.PositiveCoordinates)) :=
    hscalar.smul hcoe
  have hcoords :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun v : PuncturedHandle.UnitSphere c.PositiveCoordinates =>
        ((0 : c.NegativeCoordinates), ρ • (v : c.PositiveCoordinates))) :=
    contMDiff_const.prodMk_space hpositive
  apply c.splitChart.contMDiffOn_invFun.comp_contMDiff hcoords
  intro v
  have hh :=
    hblock
      (MorseHandle.modelMap_mem_product hρ
        ((⟨0, by simp⟩ : MorseHandle.UnitDisk c.NegativeCoordinates),
          ⟨(v : c.PositiveCoordinates), Metric.sphere_subset_closedBall v.property⟩))
  simpa [MorseHandle.modelMap] using hh

attribute [local instance 100] Classical.propDecidable in
/-- The belt sphere is the image of the belt core map. -/
theorem ManifoldMorse.SignedMorseChart.beltSphere_eq_beltCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2})
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (he :
      ∀ x,
        f (e x) = f p + ρ ^ 2 ↔
          x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)))
    (hfixed : ∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) :
    (c.levelSurgeryBoundaryPair hf ρ hρ hblock hlevel e he).beltSphere =
      c.beltCoreMap ρ hρ hblock := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  exact hfixed _ (c.normHandleMap_belt_height ρ hρ hblock v)

attribute [local instance 100] Classical.propDecidable in
/-- The belt core map is smooth. -/
theorem ManifoldMorse.SignedMorseChart.contMDiff_beltCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ (c.beltCoreMap ρ hρ hblock) := by
  let _ := RegularLevel.chartedSpace hf hreg
  exact
    (RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 n) (c.beltCoreMap ρ hρ hblock)).mpr
      (c.contMDiff_beltCoreMap_ambient n ρ hρ hblock)

/-! ### Restricted partial charts -/

/-- A partial chart restricted in source. -/
def PartialChart.restrictSource {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {U : Set M} (hU : IsOpen U) : PartialDiffeomorph I J M N ∞
    where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen U hU).toPartialEquiv
  open_source := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_source
  open_target := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono Set.inter_subset_left
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono Set.inter_subset_left

/-- A partial chart restricted in target. -/
def PartialChart.restrictTarget {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {V : Set N} (hV : IsOpen V) :
    PartialDiffeomorph I J M N ∞ :=
  (restrictSource Φ.symm hV).symm

/-- A partial chart has bijective derivative. -/
theorem PartialChart.bijective_mfderiv {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {x : M} (hx : x ∈ Φ.source) :
    Function.Bijective (mfderiv I J Φ x) := by
  have hdiff : Φ.toOpenPartialHomeomorph.MDifferentiable I J :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  exact hdiff.mfderiv_bijective hx

/-- The linearized sphere map has injective derivative. -/
theorem PartialChart.injective_mfderiv_linear_sphere {N F E H M : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {n : ℕ} [Fact (Module.finrank ℝ N = n + 1)]
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M ∞) (L : N →L[ℝ] F) (hL : Function.Injective L)
    (u : Metric.sphere (0 : N) 1) (hu : L (u : N) ∈ Φ.source) :
    Function.Injective (mfderiv (𝓡 n) I (fun v : Metric.sphere (0 : N) 1 => Φ (L (v : N))) u) := by
  have hcoesm : ContMDiff (𝓡 n) 𝓘(ℝ, N) ∞ (Subtype.val : Metric.sphere (0 : N) 1 → N) :=
    contMDiff_coe_sphere (E := N) (n := n)
  have hcoe := hcoesm.mdifferentiableAt (x := u) (by simp)
  have hlinear : MDifferentiableAt 𝓘(ℝ, N) 𝓘(ℝ, F) L (u : N) :=
    L.differentiableAt.mdifferentiableAt
  have hinner := hlinear.comp u hcoe
  have hsphere :
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, N) (Subtype.val : Metric.sphere (0 : N) 1 → N) u) := by
    convert! injective_mvfderiv_subtypeVal_sphere u
  change Function.Injective (mfderiv (𝓡 n) I (Φ ∘ (L ∘ Subtype.val)) u)
  rw [mfderiv_comp u (Φ.mdifferentiableAt (by simp) hu) hinner, mfderiv_comp u hlinear hcoe,
    mfderiv_eq_fderiv, L.fderiv]
  exact (bijective_mfderiv Φ hu).injective.comp (hL.comp hsphere)

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map is injective. -/
theorem ManifoldMorse.SignedMorseChart.injective_attachingCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Function.Injective (c.attachingCoreMap ρ hρ hblock) := by
  intro u v huv
  have hh :=
    c.attachingHandleMap_injective ρ hρ hblock
      (congrArg (fun y : { y : M // f y = f p - ρ ^ 2 } => (y : M)) huv)
  exact Subtype.ext (congrArg (fun z => (z.1 : c.NegativeCoordinates)) hh)

attribute [local instance 100] Classical.propDecidable in
/-- The belt core map is injective. -/
theorem ManifoldMorse.SignedMorseChart.injective_beltCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Function.Injective (c.beltCoreMap ρ hρ hblock) := by
  intro u v huv
  have hh :=
    c.attachingHandleMap_injective ρ hρ hblock
      (congrArg (fun y : { y : M // f y = f p + ρ ^ 2 } => (y : M)) huv)
  exact Subtype.ext (congrArg (fun z => (z.2 : c.PositiveCoordinates)) hh)

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map is a closed embedding. -/
theorem ManifoldMorse.SignedMorseChart.attachingCoreMap_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M] (ρ : ℝ)
    (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Topology.IsClosedEmbedding (c.attachingCoreMap ρ hρ hblock) :=
  (c.attachingCoreMap ρ hρ hblock).continuous.isClosedEmbedding
    (c.injective_attachingCoreMap ρ hρ hblock)

attribute [local instance 100] Classical.propDecidable in
/-- The belt core map is a closed embedding. -/
theorem ManifoldMorse.SignedMorseChart.beltCoreMap_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M] (ρ : ℝ)
    (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Topology.IsClosedEmbedding (c.beltCoreMap ρ hρ hblock) :=
  (c.beltCoreMap ρ hρ hblock).continuous.isClosedEmbedding (c.injective_beltCoreMap ρ hρ hblock)

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map's ambient derivative is injective. -/
theorem ManifoldMorse.SignedMorseChart.injective_mfderiv_attachingCoreMap_ambient
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val ∘ c.attachingCoreMap ρ hρ hblock) u) :=
  by
  let L : c.NegativeCoordinates →L[ℝ] c.NegativeCoordinates × c.PositiveCoordinates :=
    ρ • ContinuousLinearMap.inl ℝ c.NegativeCoordinates c.PositiveCoordinates
  have hL : Function.Injective L := by
    intro x y hxy
    apply smul_right_injective c.NegativeCoordinates hρ.ne'
    exact congrArg Prod.fst hxy
  have hu : L (u : c.NegativeCoordinates) ∈ c.splitChart.target := by
    have hh :=
      hblock
        (MorseHandle.modelMap_mem_product hρ
          (⟨(u : c.NegativeCoordinates), Metric.sphere_subset_closedBall u.property⟩,
            (⟨0, by simp⟩ : MorseHandle.UnitDisk c.PositiveCoordinates)))
    simpa [L, MorseHandle.modelMap] using hh
  have heq :
    Subtype.val ∘ c.attachingCoreMap ρ hρ hblock =
      fun v : PuncturedHandle.UnitSphere c.NegativeCoordinates => c.splitChart.symm (L v) :=
    by
    funext v
    rw [Function.comp_apply, c.attachingCoreMap_coe]
    congr 1
    simp [L]
  rw [heq]
  exact PartialChart.injective_mfderiv_linear_sphere c.splitChart.symm L hL u hu

attribute [local instance 100] Classical.propDecidable in
/-- The belt core map's ambient derivative is injective. -/
theorem ManifoldMorse.SignedMorseChart.injective_mfderiv_beltCoreMap_ambient {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val ∘ c.beltCoreMap ρ hρ hblock) v) := by
  let L : c.PositiveCoordinates →L[ℝ] c.NegativeCoordinates × c.PositiveCoordinates :=
    ρ • ContinuousLinearMap.inr ℝ c.NegativeCoordinates c.PositiveCoordinates
  have hL : Function.Injective L := by
    intro x y hxy
    apply smul_right_injective c.PositiveCoordinates hρ.ne'
    exact congrArg Prod.snd hxy
  have hv : L (v : c.PositiveCoordinates) ∈ c.splitChart.target := by
    have hh :=
      hblock
        (MorseHandle.modelMap_mem_product hρ
          ((⟨0, by simp⟩ : MorseHandle.UnitDisk c.NegativeCoordinates),
            ⟨(v : c.PositiveCoordinates), Metric.sphere_subset_closedBall v.property⟩))
    simpa [L, MorseHandle.modelMap] using hh
  have heq :
    Subtype.val ∘ c.beltCoreMap ρ hρ hblock =
      fun u : PuncturedHandle.UnitSphere c.PositiveCoordinates => c.splitChart.symm (L u) :=
    by
    funext u
    rw [Function.comp_apply, c.beltCoreMap_coe]
    congr 1
    simp [L]
  rw [heq]
  exact PartialChart.injective_mfderiv_linear_sphere c.splitChart.symm L hL v hv

attribute [local instance 100] Classical.propDecidable in
/-- The attaching core map's derivative is injective. -/
theorem ManifoldMorse.SignedMorseChart.injective_mfderiv_attachingCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    letI := RegularLevel.chartedSpace hf hreg
    Function.Injective
      (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (c.attachingCoreMap ρ hρ hblock) u) := by
  exact
    RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 n)
      (c.attachingCoreMap ρ hρ hblock) u (c.contMDiff_attachingCoreMap_ambient n ρ hρ hblock u)
      (c.injective_mfderiv_attachingCoreMap_ambient n ρ hρ hblock u)

attribute [local instance 100] Classical.propDecidable in
/-- The belt core map's derivative is injective. -/
theorem ManifoldMorse.SignedMorseChart.injective_mfderiv_beltCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf hreg
    Function.Injective
      (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (c.beltCoreMap ρ hρ hblock) v) := by
  exact
    RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 n) (c.beltCoreMap ρ hρ hblock) v
      (c.contMDiff_beltCoreMap_ambient n ρ hρ hblock v)
      (c.injective_mfderiv_beltCoreMap_ambient n ρ hρ hblock v)

/-! ### Smoothing homotopies -/

/-- The flattening time function of a homotopy. -/
def ManifoldSmoothing.flattenTime (t : unitInterval) : unitInterval :=
  ⟨Max.max 0 (Min.min 1 (3 * (t : ℝ) - 1)), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- The flattening time is continuous. -/
theorem ManifoldSmoothing.continuous_flattenTime : Continuous flattenTime :=
  (continuous_const.max
      (continuous_const.min
        ((continuous_const.mul continuous_subtype_val).sub continuous_const))) |>.subtype_mk
    _

/-- The flattening time is zero on the lower collar. -/
theorem ManifoldSmoothing.flattenTime_eq_zero (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 3) :
    flattenTime t = 0 := by
  apply Subtype.ext
  change Max.max 0 (Min.min 1 (3 * (t : ℝ) - 1)) = 0
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

/-- The flattening time is one on the upper collar. -/
theorem ManifoldSmoothing.flattenTime_eq_one (t : unitInterval) (ht : 2 / 3 ≤ (t : ℝ)) :
    flattenTime t = 1 := by
  apply Subtype.ext
  change Max.max 0 (Min.min 1 (3 * (t : ℝ) - 1)) = 1
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

/-- The homotopy flattened to be stationary on the collars. -/
def ManifoldSmoothing.flattenedHomotopyMap {X N : Type*} [TopologicalSpace X]
    [TopologicalSpace N] {f g : C(X, N)} (H : f.Homotopy g) : C(unitInterval × X, N)
    where
  toFun q := H (flattenTime q.1, q.2)
  continuous_toFun :=
    H.continuous.comp ((continuous_flattenTime.comp continuous_fst).prodMk continuous_snd)

/-- The flattened homotopy on the lower collar. -/
theorem ManifoldSmoothing.flattenedHomotopyMap_lower {X N : Type*} [TopologicalSpace X]
    [TopologicalSpace N] {f g : C(X, N)} (H : f.Homotopy g) (t : unitInterval) (x : X)
    (ht : (t : ℝ) ≤ 1 / 3) : flattenedHomotopyMap H (t, x) = f x := by
  change H (flattenTime t, x) = f x
  rw [flattenTime_eq_zero t ht, H.apply_zero]

/-- The flattened homotopy on the upper collar. -/
theorem ManifoldSmoothing.flattenedHomotopyMap_upper {X N : Type*} [TopologicalSpace X]
    [TopologicalSpace N] {f g : C(X, N)} (H : f.Homotopy g) (t : unitInterval) (x : X)
    (ht : 2 / 3 ≤ (t : ℝ)) : flattenedHomotopyMap H (t, x) = g x := by
  change H (flattenTime t, x) = g x
  rw [flattenTime_eq_one t ht, H.apply_one]

/-! ### Homotopy collars -/

/-- The collar regions where the homotopy is flattened. -/
def ManifoldSmoothing.homotopyCollars (X : Type*) : Set (unitInterval × X) :=
  {q | (q.1 : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (q.1 : ℝ)}

/-- A neighborhood of the homotopy collars. -/
def ManifoldSmoothing.homotopyCollarNeighborhood (X : Type*) : Set (unitInterval × X) :=
  {q | (q.1 : ℝ) < 1 / 3 ∨ 2 / 3 < (q.1 : ℝ)}

/-- The homotopy collars are closed. -/
theorem ManifoldSmoothing.isClosed_homotopyCollars {X : Type*} [TopologicalSpace X] :
    IsClosed (homotopyCollars X) :=
  (isClosed_le (continuous_subtype_val.comp continuous_fst) continuous_const).union
    (isClosed_le continuous_const (continuous_subtype_val.comp continuous_fst))

/-- The collar neighborhood is open. -/
theorem ManifoldSmoothing.isOpen_homotopyCollarNeighborhood {X : Type*}
    [TopologicalSpace X] : IsOpen (homotopyCollarNeighborhood X) :=
  (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).union
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst))

/-- The collars lie in the collar neighborhood. -/
theorem ManifoldSmoothing.homotopyCollars_subset {X : Type*} :
    homotopyCollars X ⊆ homotopyCollarNeighborhood X := by
  rintro q (hl | hu)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-! ### Chart perturbations of maps -/

/-- A family of coordinate perturbations of a map. -/
def ChartMapPerturbation.coordinateFamily {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (q : F × X) : F :=
  c (f q.2) + β q.2 • q.1

/-- A coordinate perturbation is valid on a chart domain. -/
def ChartMapPerturbation.Valid {G F K X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : F) : Prop :=
  ∀ x ∈ tsupport β, coordinateFamily c f β (a, x) ∈ c.target

/-- The perturbed map in the chart. -/
def ChartMapPerturbation.perturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : F) (x : X) : N := by
  classical exact if f x ∈ c.source then c.symm (coordinateFamily c f β (a, x)) else f x

/-- A zero perturbation leaves the map unchanged. -/
theorem ChartMapPerturbation.perturb_eq_of_zero {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : F) {x : X}
    (hx : β x = 0) : perturb c f β a x = f x := by
  classical
  by_cases hs : f x ∈ c.source
  · simp only [perturb, hs, if_pos, coordinateFamily, hx, zero_smul, add_zero]
    exact c.left_inv' hs
  · simp only [perturb, hs, if_false]

/-- The zero perturbation is the original map. -/
theorem ChartMapPerturbation.perturb_zero {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (x : X) :
    perturb c f β 0 x = f x := by
  classical
  by_cases hs : f x ∈ c.source
  · simp only [perturb, hs, if_pos, coordinateFamily, smul_zero, add_zero]
    exact c.left_inv' hs
  · simp only [perturb, hs, if_false]

/-- The zero perturbation is valid. -/
theorem ChartMapPerturbation.valid_zero {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : Valid c f β (0 : F) := by
  intro x hx
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

/-- The coordinate perturbation lands in the target chart. -/
theorem ChartMapPerturbation.coordinate_mem_target {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F}
    (ha : Valid c f β a) {x : X} (hx : f x ∈ c.source) :
    coordinateFamily c f β (a, x) ∈ c.target := by
  by_cases hβx : β x = 0
  · simpa only [coordinateFamily, hβx, zero_smul, add_zero] using c.map_source' hx
  · exact ha x (subset_tsupport β hβx)

/-- The perturbed map lands in the source. -/
theorem ChartMapPerturbation.perturb_mem_source {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F} (ha : Valid c f β a)
    {x : X} (hx : f x ∈ c.source) : perturb c f β a x ∈ c.source := by
  classical
  simp only [perturb, hx, if_pos]
  exact c.map_target' (coordinate_mem_target c f β ha hx)

/-- The perturbation computes in the chart. -/
theorem ChartMapPerturbation.chart_perturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F} (ha : Valid c f β a)
    {x : X} (hx : f x ∈ c.source) : c (perturb c f β a x) = coordinateFamily c f β (a, x) := by
  classical
  simp only [perturb, hx, if_pos]
  exact c.right_inv' (coordinate_mem_target c f β ha hx)

/-- The coordinate family is smooth. -/
theorem ChartMapPerturbation.contMDiffAt_coordinateFamily {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (q : F × X) (hq : f q.2 ∈ c.source) :
    ContMDiffAt (𝓘(ℝ, F).prod I) 𝓘(ℝ, F) ∞ (coordinateFamily c f β) q :=
  ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq)).comp q
        (hf.comp contMDiff_snd).contMDiffAt).add
    (((hβ.comp contMDiff_snd).contMDiffAt).smul contMDiffAt_fst)

/-- Small perturbations are valid. -/
theorem ChartMapPerturbation.eventually_valid {E G F H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∀ᶠ a in 𝓝 (0 : F), Valid c f β a := by
  apply hcompact.isCompact.eventually_forall_of_forall_eventually
  intro x hx
  have hh := (contMDiffAt_coordinateFamily c hf hβ (0, x) (hsupport hx)).continuousAt
  apply hh.preimage_mem_nhds
  apply c.open_target.mem_nhds
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

/-- The perturbation radius lemma: with positive radius one can choose a perturbation parameter making the perturbed chart map avoid a finite set of target points while staying smooth - the avoidance engine of the existence proof (Milnor, h-cobordism, proof of Theorem 2.5). -/
theorem ChartMapPerturbation.exists_radius_valid {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∃ ε > (0 : ℝ), ∀ a : F, ‖a‖ < ε → Valid c f β a := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (eventually_valid c hf hβ hcompact hsupport)
  exact ⟨ε, hε, fun a ha => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ha)⟩

/-- The perturbation is smooth. -/
theorem ChartMapPerturbation.contMDiffAt_perturb {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X)
    (ha : Valid c f β q.1) :
    ContMDiffAt (𝓘(ℝ, F).prod I) J ∞ (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord := contMDiffAt_coordinateFamily c hf hβ q hx
    have htarget := coordinate_mem_target c f β ha hx
    have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp q hcoord
    apply hh.congr_of_eventuallyEq
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.continuous.comp continuous_snd).continuousAt.preimage_mem_nhds
        (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, if_pos, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact perturb_eq_of_zero c f β r.1 hr

/-- The perturbation is jointly smooth. -/
theorem ChartMapPerturbation.contMDiff_perturb {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : F}
    (ha : Valid c f β a) : ContMDiff I J ∞ (perturb c f β a) := by
  intro x
  exact
    (contMDiffAt_perturb c hf hβ hsupport (a, x) ha).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)

/-- The coordinate family is continuous. -/
theorem ChartMapPerturbation.continuousAt_coordinateFamily {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (q : F × X) (hq : f q.2 ∈ c.source) :
    ContinuousAt (coordinateFamily c f β) q :=
  ((c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hq)).comp (f :=
        fun r : F × X => f r.2) (hf.comp continuous_snd).continuousAt).add
    ((hβ.comp continuous_snd).continuousAt.smul continuousAt_fst)

/-- A continuous small perturbation is eventually valid. -/
theorem ChartMapPerturbation.eventually_valid_of_continuous {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∀ᶠ a in 𝓝 (0 : F), Valid c f β a := by
  apply hcompact.isCompact.eventually_forall_of_forall_eventually
  intro x hx
  apply (continuousAt_coordinateFamily c hf hβ (0, x) (hsupport hx)).preimage_mem_nhds
  apply c.open_target.mem_nhds
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

/-- A radius on which a continuous perturbation is valid exists. -/
theorem ChartMapPerturbation.exists_radius_valid_of_continuous {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∃ ε > (0 : ℝ), ∀ a : F, ‖a‖ < ε → Valid c f β a := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (eventually_valid_of_continuous c hf hβ hcompact hsupport)
  exact ⟨ε, hε, fun a ha => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ha)⟩

/-- The perturbation is continuous. -/
theorem ChartMapPerturbation.continuousAt_perturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : Continuous f)
    (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X)
    (ha : Valid c f β q.1) : ContinuousAt (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord := continuousAt_coordinateFamily c hf hβ q hx
    have htarget := coordinate_mem_target c f β ha hx
    have hh :=
      (c.contMDiffOn_invFun.continuousOn.continuousAt (c.open_target.mem_nhds htarget)).comp
        hcoord
    apply hh.congr
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.comp continuous_snd).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, if_pos, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp continuous_snd).continuousAt.congr
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact (perturb_eq_of_zero c f β r.1 hr).symm

/-- A continuous family eventually maps a compact set into an open set. -/
theorem ChartMapPerturbation.eventually_maps_compact_into_open_of_continuous
    {G F K X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [TopologicalSpace N] [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N}
    {β : X → ℝ} (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {L : Set X} (hL : IsCompact L) {U : Set N} (hU : IsOpen U) (hfL : Set.MapsTo f L U) :
    ∀ᶠ a in 𝓝 (0 : F), Set.MapsTo (perturb c f β a) L U := by
  apply hL.eventually_forall_of_forall_eventually
  intro x hx
  apply
    (continuousAt_perturb c hf hβ hsupport (0, x) (valid_zero c f β hsupport)).preimage_mem_nhds
  apply hU.mem_nhds
  simpa only [perturb_zero] using hfL hx

/-- The perturbation of a smooth map is smooth. -/
theorem ChartMapPerturbation.contMDiffAt_perturb_of_contMDiffAt {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X) (hf : ContMDiffAt I J ∞ f q.2)
    (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β q.2) (ha : Valid c f β q.1) :
    ContMDiffAt (𝓘(ℝ, F).prod I) J ∞ (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord : ContMDiffAt (𝓘(ℝ, F).prod I) 𝓘(ℝ, F) ∞ (coordinateFamily c f β) q :=
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).comp q
            (hf.comp q contMDiffAt_snd)).add
        ((hβ.comp q contMDiffAt_snd).smul contMDiffAt_fst)
    have htarget := coordinate_mem_target c f β ha hx
    have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp q hcoord
    apply hh.congr_of_eventuallyEq
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.continuousAt.comp continuousAt_snd).preimage_mem_nhds (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, if_pos, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp q contMDiffAt_snd).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact perturb_eq_of_zero c f β r.1 hr

/-- A family eventually maps a compact set into an open set. -/
theorem ChartMapPerturbation.eventually_maps_compact_into_open {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {L : Set X}
    (hL : IsCompact L) {U : Set N} (hU : IsOpen U) (hfL : Set.MapsTo f L U) :
    ∀ᶠ a in 𝓝 (0 : F), Set.MapsTo (perturb c f β a) L U := by
  apply hL.eventually_forall_of_forall_eventually
  intro x hx
  have hc :=
    (contMDiffAt_perturb c hf hβ hsupport (0, x) (valid_zero c f β hsupport)).continuousAt
  apply hc.preimage_mem_nhds
  apply hU.mem_nhds
  simpa only [perturb_zero] using hfL hx

/-- A small interval scaling stays within the bound. -/
theorem ChartMapPerturbation.norm_interval_smul_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ε : ℝ} {a : F} (ha : ‖a‖ < ε) (t : unitInterval) : ‖(t : ℝ) • a‖ < ε := by
  calc
    ‖(t : ℝ) • a‖ = (t : ℝ) * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
    _ ≤ ‖a‖ := by nlinarith [t.2.2, norm_nonneg a]
    _ < ε := ha

/-- The perturbation is a homotopy relative to the fixed set. -/
def ChartMapPerturbation.homotopyRel {E G F H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {ε : ℝ} (hvalid : ∀ a : F, ‖a‖ < ε → Valid c f β a)
    {a : F} (ha : ‖a‖ < ε) :
    (⟨f, hf.continuous⟩ : C(X, N)).HomotopyRel
      ⟨perturb c f β a, (contMDiff_perturb c hf hβ hsupport (hvalid a ha)).continuous⟩
      {x | β x = 0}
    where
  toFun q := perturb c f β ((q.1 : ℝ) • a) q.2
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hv := hvalid _ (norm_interval_smul_lt ha q.1)
    have hp : Continuous (fun r : unitInterval × X => ((r.1 : ℝ) • a, r.2)) :=
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const).prodMk continuous_snd
    exact
      ContinuousAt.comp (f := fun r : unitInterval × X => ((r.1 : ℝ) • a, r.2))
        (contMDiffAt_perturb c hf hβ hsupport (((q.1 : ℝ) • a), q.2) hv).continuousAt
        hp.continuousAt
  map_zero_left
    x := by
    change perturb c f β ((0 : ℝ) • a) x = f x
    rw [zero_smul, perturb_zero]
  map_one_left
    x := by
    change perturb c f β ((1 : ℝ) • a) x = perturb c f β a x
    rw [one_smul]
  prop' _ x hx := perturb_eq_of_zero c f β _ hx

/-- The time-variable perturbation of a homotopy. -/
def ChartMapPerturbation.variablePerturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : X → F) (x : X) : N :=
  perturb c f β (a x) x

/-- The variable perturbation is continuous. -/
theorem ChartMapPerturbation.continuous_variablePerturb {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    {a : X → F} (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (ha : Continuous a) (hvalid : ∀ x, Valid c f β (a x)) :
    Continuous (variablePerturb c f β a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact
    (continuousAt_perturb c hf hβ hsupport (a x, x) (hvalid x)).comp (f := fun y : X => (a y, y))
      (ha.prodMk continuous_id).continuousAt

/-- The variable perturbation is smooth. -/
theorem ChartMapPerturbation.contMDiffAt_variablePerturb {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {a : X → F}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {x : X} (hf : ContMDiffAt I J ∞ f x)
    (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β x) (ha : ContMDiffAt I 𝓘(ℝ, F) ∞ a x)
    (hvalid : Valid c f β (a x)) : ContMDiffAt I J ∞ (variablePerturb c f β a) x :=
  (contMDiffAt_perturb_of_contMDiffAt c hsupport (a x, x) hf hβ hvalid).comp x (f := fun y : X =>
    (a y, y)) (ha.prodMk contMDiffAt_id)

/-- The variable perturbation is a relative homotopy. -/
def ChartMapPerturbation.variableHomotopyRel {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {a : X → F}
    (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (ha : Continuous a) {ε : ℝ} (hvalid : ∀ v : F, ‖v‖ < ε → Valid c f β v)
    (hbound : ∀ x, ‖a x‖ < ε) {C : Set X} (hfixed : ∀ x ∈ C, β x = 0 ∨ a x = 0) :
    (⟨f, hf⟩ : C(X, N)).HomotopyRel
      ⟨variablePerturb c f β a,
        continuous_variablePerturb c hf hβ hsupport ha (fun x => hvalid _ (hbound x))⟩
      C
    where
  toFun q := perturb c f β ((q.1 : ℝ) • a q.2) q.2
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hv := hvalid _ (norm_interval_smul_lt (hbound q.2) q.1)
    have hp : Continuous (fun r : unitInterval × X => ((r.1 : ℝ) • a r.2, r.2)) :=
      ((continuous_subtype_val.comp continuous_fst).smul (ha.comp continuous_snd)).prodMk
        continuous_snd
    exact
      (continuousAt_perturb c hf hβ hsupport (((q.1 : ℝ) • a q.2), q.2) hv).comp (f :=
        fun r : unitInterval × X => ((r.1 : ℝ) • a r.2, r.2)) hp.continuousAt
  map_zero_left
    x := by
    change perturb c f β ((0 : ℝ) • a x) x = f x
    rw [zero_smul, perturb_zero]
  map_one_left
    x := by
    change perturb c f β ((1 : ℝ) • a x) x = perturb c f β (a x) x
    rw [one_smul]
  prop' t x
    hx := by
    rcases hfixed x hx with hb | ha₀
    · exact perturb_eq_of_zero c f β _ hb
    · change perturb c f β ((t : ℝ) • a x) x = f x
      rw [ha₀, smul_zero, perturb_zero]

/-- The perturbation cut off outside a plateau. -/
def ChartMapPerturbation.cutoffCoordinates {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (χ : X → ℝ) (x : X) : F :=
  χ x • c (f x)

/-- The cutoff coordinates on the plateau. -/
theorem ChartMapPerturbation.cutoffCoordinates_eq_of_one {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (χ : X → ℝ) {x : X} (hx : χ x = 1) :
    cutoffCoordinates c f χ x = c (f x) := by simp only [cutoffCoordinates, hx, one_smul]

/-- The cutoff coordinates are continuous. -/
theorem ChartMapPerturbation.continuous_cutoffCoordinates {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {χ : X → ℝ}
    (hf : Continuous f) (hχ : Continuous χ) (hsupport : tsupport χ ⊆ f ⁻¹' c.source) :
    Continuous (cutoffCoordinates c f χ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact
      hχ.continuousAt.smul
        ((c.contMDiffOn_toFun.continuousOn.continuousAt
              (c.open_source.mem_nhds (hsupport hx))).comp
          hf.continuousAt)
  · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (continuousAt_const (y := (0 : F))).congr
    filter_upwards [hz] with y hy
    simp only [cutoffCoordinates, hy, zero_smul, Pi.zero_apply]

/-- The cutoff coordinates are smooth. -/
theorem ChartMapPerturbation.contMDiffAt_cutoffCoordinates {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {χ : X → ℝ}
    (hsupport : tsupport χ ⊆ f ⁻¹' c.source) {x : X} (hf : ContMDiffAt I J ∞ f x)
    (hχ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ x) : ContMDiffAt I 𝓘(ℝ, F) ∞ (cutoffCoordinates c f χ) x := by
  by_cases hx : x ∈ tsupport χ
  · exact
      hχ.smul ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds (hsupport hx))).comp x hf)
  · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contMDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [cutoffCoordinates, hy, zero_smul, Pi.zero_apply]

/-- Smooth approximation within a chart: coordinate functions can be smoothly approximated while avoiding prescribed finite sets (Whitney approximation, chart form; Lee, Introduction to Smooth Manifolds, Thm 6.21-adjacent). -/
theorem ChartMapPerturbation.exists_smooth_coordinate_approximation {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {χ : X → ℝ} [FiniteDimensional ℝ E]
    [IsManifold I ∞ X] [SigmaCompactSpace X] [T2Space X] (hf : Continuous f)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hsupport : tsupport χ ⊆ f ⁻¹' c.source) {C U : Set X}
    (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : X → F,
      ContMDiff I 𝓘(ℝ, F) ∞ g ∧
        (∀ x, Dist.dist (g x) (cutoffCoordinates c f χ x) < ε) ∧
          Set.EqOn g (cutoffCoordinates c f χ) C := by
  have hk := continuous_cutoffCoordinates c hf hχ.continuous hsupport
  have hkU : ContMDiffOn I 𝓘(ℝ, F) ∞ (cutoffCoordinates c f χ) U := by
    intro x hx
    exact
      (contMDiffAt_cutoffCoordinates c hsupport ((hfU x hx).contMDiffAt (hU.mem_nhds hx))
          hχ.contMDiffAt).contMDiffWithinAt
  have hUn : U ∈ 𝓝ˢ C := mem_nhdsSet_iff_forall.mpr (fun x hx => hU.mem_nhds (hCU hx))
  obtain ⟨g, hg, hgeq, _⟩ :=
    hk.exists_contMDiff_approx_and_eqOn I ⊤ (continuous_const (y := ε)) (fun _ => hε) hC hUn hkU
  exact ⟨g, g.contMDiff, hg, hgeq⟩

/-- The smoothed map built from the cutoff perturbation. -/
def ChartMapPerturbation.smoothedMap {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β χ : X → ℝ) (g : X → F) : X → N :=
  variablePerturb c f β (fun x => g x - cutoffCoordinates c f χ x)

/-- The coordinate family on the plateau. -/
theorem ChartMapPerturbation.coordinateFamily_eq_on_plateau {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β χ : X → ℝ) (g : X → F) {x : X}
    (hβx : β x = 1) (hχx : χ x = 1) :
    coordinateFamily c f β (g x - cutoffCoordinates c f χ x, x) = g x := by
  simp only [coordinateFamily, cutoffCoordinates, hβx, hχx, one_smul]
  abel

/-- The smoothed map on the plateau. -/
theorem ChartMapPerturbation.smoothedMap_eq_on_plateau {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β χ : X → ℝ)
    (g : X → F) (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hnested : ∀ x ∈ tsupport β, χ x = 1)
    {x : X} (hβx : β x = 1) : smoothedMap c f β χ g x = c.symm (g x) := by
  classical
  have hs : x ∈ tsupport β :=
    subset_tsupport β
      (by
        change β x ≠ 0
        rw [hβx]
        exact one_ne_zero)
  change perturb c f β (g x - cutoffCoordinates c f χ x) x = _
  have hsource : f x ∈ c.source := hsupport hs
  simp only [perturb, hsource, if_pos]
  rw [coordinateFamily_eq_on_plateau c f β χ g hβx (hnested x hs)]

/-- The smoothed map is smooth on the plateau. -/
theorem ChartMapPerturbation.contMDiffAt_smoothedMap_on_plateau {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {χ : X → ℝ} {g : X → F}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hnested : ∀ x ∈ tsupport β, χ x = 1) {x : X}
    (hplateau : β =ᶠ[𝓝 x] (fun _ => 1)) (hg : ContMDiffAt I 𝓘(ℝ, F) ∞ g x)
    (hvalid : Valid c f β (g x - cutoffCoordinates c f χ x)) :
    ContMDiffAt I J ∞ (smoothedMap c f β χ g) x := by
  have hβx : β x = 1 := hplateau.eq_of_nhds
  have hs : x ∈ tsupport β :=
    subset_tsupport β
      (by
        change β x ≠ 0
        rw [hβx]
        exact one_ne_zero)
  have htarget := coordinate_mem_target c f β hvalid (hsupport hs)
  rw [coordinateFamily_eq_on_plateau c f β χ g hβx (hnested x hs)] at htarget
  have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp x hg
  apply hh.congr_of_eventuallyEq
  filter_upwards [hplateau] with y hy
  exact smoothedMap_eq_on_plateau c f β χ g hsupport hnested hy

/-- The smoothed map is smooth where the old map was. -/
theorem ChartMapPerturbation.contMDiffAt_smoothedMap_of_old {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {χ : X → ℝ} {g : X → F}
    (hβsupport : tsupport β ⊆ f ⁻¹' c.source) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) {x : X}
    (hf : ContMDiffAt I J ∞ f x) (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β x)
    (hχ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ x) (hg : ContMDiffAt I 𝓘(ℝ, F) ∞ g x)
    (hvalid : Valid c f β (g x - cutoffCoordinates c f χ x)) :
    ContMDiffAt I J ∞ (smoothedMap c f β χ g) x :=
  contMDiffAt_variablePerturb c hβsupport hf hβ
    (hg.sub (contMDiffAt_cutoffCoordinates c hχsupport hf hχ)) hvalid

/-! ### Homotopy relative to a subset -/

/-- Two maps are homotopic relative to a subset within a target. -/
def HomotopicRelWithin {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (C K : Set X) (O : Set Y) : Prop :=
  ∃ F : f.HomotopyRel g C, ∀ t : unitInterval, Set.MapsTo (fun x => F (t, x)) K O

/-- Relative homotopy is reflexive. -/
theorem HomotopicRelWithin.refl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} {O : Set Y} (f : C(X, Y)) (C : Set X) (hmaps : Set.MapsTo f K O) :
    HomotopicRelWithin f f C K O :=
  ⟨ContinuousMap.HomotopyRel.refl f C, fun _ => hmaps⟩

/-- A relative homotopy within the target is a relative homotopy. -/
theorem HomotopicRelWithin.homotopicRel {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} {C K : Set X} {O : Set Y}
    (H : HomotopicRelWithin f g C K O) : f.HomotopicRel g C := by
  obtain ⟨F, _⟩ := H
  exact ⟨F⟩

/-- The right map lands in the target. -/
theorem HomotopicRelWithin.mapsTo_right {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} {C K : Set X} {O : Set Y}
    (H : HomotopicRelWithin f g C K O) : Set.MapsTo g K O := by
  obtain ⟨F, hF⟩ := H
  intro x hx
  exact (congrArg (fun y => y ∈ O) (F.map_one_left x)).mp (hF 1 hx)

/-- Relative homotopy is transitive. -/
theorem HomotopicRelWithin.trans {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g h : C(X, Y)} {C K : Set X} {O : Set Y} (H : HomotopicRelWithin f g C K O)
    (G : HomotopicRelWithin g h C K O) : HomotopicRelWithin f h C K O := by
  obtain ⟨F, hF⟩ := H
  obtain ⟨G, hG⟩ := G
  refine ⟨ContinuousMap.HomotopyRel.trans F G, ?_⟩
  intro t x hx
  change (F.toHomotopy.trans G.toHomotopy) (t, x) ∈ O
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hF _ hx
  · exact hG _ hx

/-- Relative homotopy is monotone in the fixed set. -/
theorem HomotopicRelWithin.mono {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} {C K : Set X} {O : Set Y} (H : HomotopicRelWithin f g C K O)
    {D L : Set X} {P : Set Y} (hDC : D ⊆ C) (hLK : L ⊆ K) (hOP : O ⊆ P) :
    HomotopicRelWithin f g D L P := by
  obtain ⟨F, hF⟩ := H
  exact
    ⟨{ toHomotopy := F.toHomotopy, prop' := fun t x hx => F.eq_fst t (hDC hx) }, fun t x hx =>
      hOP (hF t (hLK hx))⟩

/-- The perturbation lands in the target given a source subset. -/
theorem ChartMapPerturbation.perturb_mem_of_source_subset {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F}
    (ha : Valid c f β a) {O : Set N} (hsource : c.source ⊆ O) {x : X} (hx : f x ∈ O) :
    perturb c f β a x ∈ O := by
  by_cases hxc : f x ∈ c.source
  · exact hsource (perturb_mem_source c f β ha hxc)
  · simpa only [perturb, if_neg hxc] using hx

/-- The perturbation is homotopic relative to the fixed set within the target. -/
theorem ChartMapPerturbation.homotopicRelWithin_of_source_subset {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {ε : ℝ}
    (hvalid : ∀ a : F, ‖a‖ < ε → Valid c f β a) {a : F} (ha : ‖a‖ < ε) {D : Set X} {O : Set N}
    (hsource : c.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    HomotopicRelWithin (⟨f, hf.continuous⟩ : C(X, N))
      ⟨perturb c f β a, (contMDiff_perturb c hf hβ hsupport (hvalid a ha)).continuous⟩
      {x | β x = 0} D O := by
  refine ⟨homotopyRel c hf hβ hsupport hvalid ha, ?_⟩
  intro t x hx
  exact
    perturb_mem_of_source_subset c f β (hvalid _ (norm_interval_smul_lt ha t)) hsource (hmaps hx)

/-- The variable perturbation is relatively homotopic within the target. -/
theorem ChartMapPerturbation.variableHomotopicRelWithin_of_source_subset {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : X → F}
    (ha : Continuous a) {ε : ℝ} (hvalid : ∀ v : F, ‖v‖ < ε → Valid c f β v)
    (hbound : ∀ x, ‖a x‖ < ε) {C D : Set X} {O : Set N} (hfixed : ∀ x ∈ C, β x = 0 ∨ a x = 0)
    (hsource : c.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    HomotopicRelWithin (⟨f, hf⟩ : C(X, N))
      ⟨variablePerturb c f β a,
        continuous_variablePerturb c hf hβ hsupport ha (fun x => hvalid _ (hbound x))⟩
      C D O := by
  refine ⟨variableHomotopyRel c hf hβ hsupport ha hvalid hbound hfixed, ?_⟩
  intro t x hx
  exact
    perturb_mem_of_source_subset c f β (hvalid _ (norm_interval_smul_lt (hbound x) t)) hsource
      (hmaps hx)

/-! ### Smoothing patches -/

/-- A patch on which a map can be smoothed relative to a boundary. -/
structure ManifoldSmoothing.MapSmoothingPatch {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ G K)
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N] where
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  cutoff : X → ℝ
  outer : X → ℝ
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cutoff
  outer_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ outer
  compact : HasCompactSupport cutoff
  outer_compact : HasCompactSupport outer
  nested : ∀ x ∈ tsupport cutoff, outer x = 1

/-- Two smoothing patches are compatible on their overlap. -/
def ManifoldSmoothing.MapSmoothingPatch.Compatible {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N))
    (f : X → N) : Prop :=
  Set.MapsTo f (tsupport p.outer) p.chart.source

/-- The plateau where the patch smoothing is exact. -/
def ManifoldSmoothing.MapSmoothingPatch.plateau {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (p : ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N)) : Set X :=
  interior {x | p.cutoff x = 1}

/-- The inner support lies in the outer patch. -/
theorem ManifoldSmoothing.MapSmoothingPatch.inner_support_subset_outer {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N)) :
    tsupport p.cutoff ⊆ tsupport p.outer := by
  intro x hx
  apply subset_tsupport p.outer
  change p.outer x ≠ 0
  rw [p.nested x hx]
  exact one_ne_zero

/-- The inner patch is compatible with the outer. -/
theorem ManifoldSmoothing.MapSmoothingPatch.inner_compatible {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N))
    {f : X → N} (hf : p.Compatible f) : tsupport p.cutoff ⊆ f ⁻¹' p.chart.source := fun _ hx =>
  hf (p.inner_support_subset_outer hx)

/-- The plateau cutoff is eventually one. -/
theorem ManifoldSmoothing.MapSmoothingPatch.plateau_eventually_one {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N))
    {x : X} (hx : x ∈ p.plateau) : p.cutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact interior_subset (s := {y : X | p.cutoff y = 1}) hy

/-- One patch smoothing step exists within the target. -/
theorem ManifoldSmoothing.exists_smoothing_patch_step_within_target {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] [FiniteDimensional ℝ E] [IsManifold I ∞ X] [SigmaCompactSpace X]
    [T2Space X] {ι : Type*} [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (i : ι)
    (f : C(X, N)) (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C)
    (hU : IsOpen U) (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) {D : Set X} {O : Set N}
    (hsource : (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ f' : C(X, N),
      (∀ j, (p j).Compatible f') ∧
        HomotopicRelWithin f f' C D O ∧
          ∀ x, ContMDiffAt I J ∞ f x ∨ x ∈ (p i).plateau → ContMDiffAt I J ∞ f' x := by
  have hinner := (p i).inner_compatible (hcompatible i)
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      ChartMapPerturbation.eventually_maps_compact_into_open_of_continuous (p i).chart
        f.continuous (p i).smooth.continuous hinner (p j).outer_compact.isCompact
        (p j).chart.open_source (hcompatible j)
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hkeep
  obtain ⟨r, hr, hvalid⟩ :=
    ChartMapPerturbation.exists_radius_valid_of_continuous (p i).chart f.continuous
      (p i).smooth.continuous (p i).compact hinner
  obtain ⟨g, hg, happrox, heq⟩ :=
    ChartMapPerturbation.exists_smooth_coordinate_approximation (p i).chart f.continuous
      (p i).outer_smooth (hcompatible i) hC hU hCU hfU (lt_min hδ hr)
  let a : X → G := fun x =>
    g x - ChartMapPerturbation.cutoffCoordinates (p i).chart f (p i).outer x
  have ha : Continuous a :=
    hg.continuous.sub
      (ChartMapPerturbation.continuous_cutoffCoordinates (p i).chart f.continuous
        (p i).outer_smooth.continuous (hcompatible i))
  have hbound (x : X) : ‖a x‖ < Min.min δ r := by simpa only [a, dist_eq_norm] using happrox x
  have haδ (x : X) : ‖a x‖ < δ := (lt_min_iff.mp (hbound x)).1
  have har (x : X) : ‖a x‖ < r := (lt_min_iff.mp (hbound x)).2
  let f' : C(X, N) :=
    ⟨ChartMapPerturbation.variablePerturb (p i).chart f (p i).cutoff a,
      ChartMapPerturbation.continuous_variablePerturb (p i).chart f.continuous
        (p i).smooth.continuous hinner ha (fun x => hvalid _ (har x))⟩
  refine ⟨f', ?_, ?_, ?_⟩
  · intro j x hx
    have hh :=
      hδkeep
        (show a x ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ x)
    exact hh j hx
  · exact
      ChartMapPerturbation.variableHomotopicRelWithin_of_source_subset (p i).chart
        f.continuous (p i).smooth.continuous hinner ha hvalid har
        (fun x hx => Or.inr (sub_eq_zero.mpr (heq hx))) hsource hmaps
  · intro x hx
    rcases hx with hold | hplateau
    · exact
        ChartMapPerturbation.contMDiffAt_smoothedMap_of_old (p i).chart hinner
          (hcompatible i) hold (p i).smooth.contMDiffAt (p i).outer_smooth.contMDiffAt
          hg.contMDiffAt (hvalid _ (har x))
    · exact
        ChartMapPerturbation.contMDiffAt_smoothedMap_on_plateau (p i).chart hinner
          (p i).nested ((p i).plateau_eventually_one hplateau) hg.contMDiffAt (hvalid _ (har x))

/-- Finite-patch smoothing: finitely many smoothing patches suffice to make a piecewise-defined function smooth on the whole compact manifold (Milnor, h-cobordism, Theorem 2.5 proof). -/
theorem ManifoldSmoothing.exists_finite_patch_smoothing_within_target {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [T2Space X] [SigmaCompactSpace X] [TopologicalSpace N] [ChartedSpace K N] {ι : Type*}
    [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (f : C(X, N))
    (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U)
    (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) {D : Set X} {O : Set N}
    (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) (s : Finset ι) :
    ∃ f' : C(X, N),
      (∀ j, (p j).Compatible f') ∧
        HomotopicRelWithin f f' C D O ∧
          ∀ x, (ContMDiffAt I J ∞ f x ∨ ∃ i ∈ s, x ∈ (p i).plateau) → ContMDiffAt I J ∞ f' x := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hcompatible, HomotopicRelWithin.refl f C hmaps, ?_⟩
    intro x hx
    simpa using hx
  | @insert i s _ ih =>
    obtain ⟨f₁, hc₁, hhom₁, hsm₁⟩ := ih
    have hf₁U : ContMDiffOn I J ∞ f₁ U := by
      intro x hx
      exact (hsm₁ x (Or.inl ((hfU x hx).contMDiffAt (hU.mem_nhds hx)))).contMDiffWithinAt
    obtain ⟨f₂, hc₂, hhom₂, hsm₂⟩ :=
      exists_smoothing_patch_step_within_target p i f₁ hc₁ hC hU hCU hf₁U (hsource i)
        hhom₁.mapsTo_right
    refine ⟨f₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply hsm₂ x
    rcases hx with hold | ⟨j, hj, hplateau⟩
    · exact Or.inl (hsm₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hplateau
      · exact Or.inl (hsm₁ x (Or.inr ⟨j, hjs, hplateau⟩))

/-- Finitely many patches give a global smoothing. -/
theorem ManifoldSmoothing.exists_finite_patch_smoothing {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [T2Space X] [SigmaCompactSpace X] [TopologicalSpace N] [ChartedSpace K N] {ι : Type*}
    [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (f : C(X, N))
    (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U)
    (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) (s : Finset ι) :
    ∃ f' : C(X, N),
      (∀ j, (p j).Compatible f') ∧
        f.HomotopicRel f' C ∧
          ∀ x, (ContMDiffAt I J ∞ f x ∨ ∃ i ∈ s, x ∈ (p i).plateau) → ContMDiffAt I J ∞ f' x := by
  obtain ⟨f', hc, hrel, hsm⟩ :=
    exists_finite_patch_smoothing_within_target p f hcompatible hC hU hCU hfU
      (fun _ => Set.subset_univ _) (Set.mapsTo_univ f Set.univ) s
  exact ⟨f', hc, hrel.homotopicRel, hsm⟩

/-- A smoothing exists from a finite patch cover. -/
theorem ManifoldSmoothing.exists_smoothing_of_finite_patches {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [T2Space X] [SigmaCompactSpace X] [TopologicalSpace N] [ChartedSpace K N] {ι : Type*}
    [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (f : C(X, N))
    (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U)
    (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) (hcover : ∀ x, ∃ i, x ∈ (p i).plateau) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨f', _, hhom, hsm⟩ :=
    exists_finite_patch_smoothing p f hcompatible hC hU hCU hfU Finset.univ
  refine ⟨f', ?_, hhom⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact hsm x (Or.inr ⟨i, Finset.mem_univ i, hi⟩)

/-! ### Existence of smoothings -/

/-- A smoothing patch exists at a point inside an open set. -/
theorem ManifoldSmoothing.exists_smoothing_patch_at_in_open {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    (f : C(X, N)) (x : X) {O : Set N} (hO : IsOpen O) (hxO : f x ∈ O) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N),
      p.Compatible f ∧ x ∈ p.plateau ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := modelChartPartialDiffeomorph (I := J) (f x)
  let c := PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∈ 𝓝 x := (c.open_source.preimage f.continuous).mem_nhds hsource
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU
  have hχone : {y : X | χ y = 1} ∈ 𝓝 x := χ.eventuallyEq_one
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hχone
  let p : MapSmoothingPatch I J (X := X) (N := N) :=
    { chart := c
      cutoff := β
      outer := χ
      smooth := β.contMDiff
      outer_smooth := χ.contMDiff
      compact := β.hasCompactSupport
      outer_compact := χ.hasCompactSupport
      nested := fun y hy => hβ hy }
  refine ⟨p, hχ, ?_, fun _ hx => hx.2⟩
  change x ∈ interior {y : X | β y = 1}
  exact mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one

/-- A smoothing patch exists at every point. -/
theorem ManifoldSmoothing.exists_smoothing_patch_at {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    (f : C(X, N)) (x : X) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N), p.Compatible f ∧ x ∈ p.plateau := by
  obtain ⟨p, hc, hp, _⟩ :=
    exists_smoothing_patch_at_in_open (I := I) (J := J) f x isOpen_univ (Set.mem_univ _)
  exact ⟨p, hc, hp⟩

/-- A smooth map homotopic relative to a closed set exists. -/
theorem ManifoldSmoothing.exists_smooth_map_homotopicRel {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    [CompactSpace X] (f : C(X, N)) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) : ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  classical
  have hp (x : X) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N), p.Compatible f ∧ x ∈ p.plateau :=
    exists_smoothing_patch_at f x
  choose p hpcompatible hpplateau using hp
  have hopen (x : X) : IsOpen (p x).plateau := isOpen_interior
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, (p x).plateau := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hpplateau x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (p x).plateau) hopen hcover
  apply
    exists_smoothing_of_finite_patches (fun i : s => p i.1) f (fun i => hpcompatible i.1) hC hU
      hCU hfU
  intro x
  obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, hix⟩

/-- A smooth map homotopic to a continuous map exists. -/
theorem ManifoldSmoothing.exists_smooth_map_homotopic {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    [CompactSpace X] (f : C(X, N)) : ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.Homotopic f' := by
  obtain ⟨f', hf', ⟨H⟩⟩ :=
    exists_smooth_map_homotopicRel (I := I) (J := J) f isClosed_empty isOpen_empty
      (Set.Subset.refl ∅) contMDiffOn_empty
  exact ⟨f', hf', ⟨H.toHomotopy⟩⟩

/-- The flattened homotopy is smooth on the collar complement. -/
theorem ManifoldSmoothing.contMDiffOn_flattenedHomotopyMap {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] {f g : C(X, N)} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (H : f.Homotopy g) :
    ContMDiffOn ((𝓡∂ 1).prod I) J ∞ (flattenedHomotopyMap H) (homotopyCollarNeighborhood X) := by
  rintro q (hl | hu)
  · have hs : ContMDiff ((𝓡∂ 1).prod I) J ∞ (fun r : unitInterval × X => f r.2) :=
      hf.comp contMDiff_snd
    have heq : flattenedHomotopyMap H =ᶠ[𝓝 q] (fun r => f r.2) := by
      have hn : {r : unitInterval × X | (r.1 : ℝ) < 1 / 3} ∈ 𝓝 q :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).mem_nhds hl
      filter_upwards [hn] with r hr
      exact flattenedHomotopyMap_lower H r.1 r.2 (le_of_lt hr)
    exact (hs.contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt
  · have hs : ContMDiff ((𝓡∂ 1).prod I) J ∞ (fun r : unitInterval × X => g r.2) :=
      hg.comp contMDiff_snd
    have heq : flattenedHomotopyMap H =ᶠ[𝓝 q] (fun r => g r.2) := by
      have hn : {r : unitInterval × X | 2 / 3 < (r.1 : ℝ)} ∈ 𝓝 q :=
        (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).mem_nhds hu
      filter_upwards [hn] with r hr
      exact flattenedHomotopyMap_upper H r.1 r.2 (le_of_lt hr)
    exact (hs.contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt

/-- A smooth homotopy with collar control exists. -/
theorem ManifoldSmoothing.exists_smooth_homotopy_with_collars {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [CompactSpace X] [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N] {f g : C(X, N)} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (H : f.Homotopy g) :
    ∃ H' : f.Homotopy g,
      ContMDiff ((𝓡∂ 1).prod I) J ∞ H' ∧
        (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H' (t, x) = f x) ∧
          (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H' (t, x) = g x) := by
  obtain ⟨F, hF, ⟨K⟩⟩ :=
    exists_smooth_map_homotopicRel (flattenedHomotopyMap H) isClosed_homotopyCollars
      isOpen_homotopyCollarNeighborhood homotopyCollars_subset
      (contMDiffOn_flattenedHomotopyMap hf hg H)
  have hlo (t : unitInterval) (x : X) (ht : (t : ℝ) ≤ 1 / 4) : F (t, x) = f x := by
    have heq := K.fst_eq_snd (show (t, x) ∈ homotopyCollars X from Or.inl ht)
    rw [← heq]
    exact flattenedHomotopyMap_lower H t x (by linarith)
  have hhi (t : unitInterval) (x : X) (ht : 3 / 4 ≤ (t : ℝ)) : F (t, x) = g x := by
    have heq := K.fst_eq_snd (show (t, x) ∈ homotopyCollars X from Or.inr ht)
    rw [← heq]
    exact flattenedHomotopyMap_upper H t x (by linarith)
  let H' : f.Homotopy g :=
    { toContinuousMap := F
      map_zero_left := fun x => hlo 0 x (by norm_num)
      map_one_left := fun x => hhi 1 x (by norm_num) }
  exact ⟨H', hF, hlo, hhi⟩
end Mathoverflow1973
