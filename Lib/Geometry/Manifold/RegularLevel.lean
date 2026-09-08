/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Geometry.Manifold.Flow.Compact


set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

theorem Smale.RegularLevel.surjective_of_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {L : E →L[ℝ] ℝ} (hL : L ≠ 0) : Function.Surjective L := by
  have hex : ∃ v, L v ≠ 0 := by
    by_contra! h
    exact hL (ContinuousLinearMap.ext h)
  obtain ⟨v, hv⟩ := hex
  intro r
  refine ⟨(r / L v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]

theorem Smale.RegularLevel.finrank_kernel_add_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    Module.finrank ℝ L.ker + 1 = Module.finrank ℝ E := by
  have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr (surjective_of_ne_zero hL)
  have hdim := L.toLinearMap.finrank_range_add_finrank_ker
  change Module.finrank ℝ L.range + Module.finrank ℝ L.ker = Module.finrank ℝ E at hdim
  rw [hr, finrank_top, Module.finrank_self] at hdim
  omega

theorem Smale.RegularLevel.exists_height_partialDiffeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E} {x : E} (hU : IsOpen U)
    (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U) (hreg : fderiv ℝ f x ≠ 0) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × (fderiv ℝ f x).ker) E (ℝ × (fderiv ℝ f x).ker) ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ (∀ y, (Φ y).1 = f y) ∧ Φ x = (f x, 0) := by
  let L := fderiv ℝ f x
  have hs : HasStrictFDerivAt f L x :=
    (hf.contDiffAt (hU.mem_nhds hx)).hasStrictFDerivAt (by simp)
  have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr (surjective_of_ne_zero hreg)
  have hk : L.ker.ClosedComplemented := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := hs.implicitFunctionDataOfComplemented f L hr hk
  have hg : ContDiffOn ℝ ∞ φ.prodFun U := by
    apply hf.prodMk
    change ContDiffOn ℝ ∞ (fun y => Classical.choose hk (y - x)) U
    exact (Classical.choose hk).contDiff.comp_contDiffOn (contDiffOn_id.sub contDiffOn_const)
  obtain ⟨Φ, hΦ, hΦU, hΦf⟩ :=
    NoExotic.exists_partialDiffeomorph_of_contDiffOn hU hx hg φ.isInvertible_fderiv_prodFun
  refine ⟨Φ, hΦ, hΦU, ?_, ?_⟩
  · intro y
    rw [hΦf]
    rfl
  · rw [hΦf]
    change (f x, Classical.choose hk (x - x)) = (f x, 0)
    simp

abbrev Smale.RegularLevel.Model (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))

theorem Smale.RegularLevel.exists_native_height_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) M (ℝ × Model E) ∞,
      x ∈ Φ.source ∧ (∀ y ∈ Φ.source, (Φ y).1 = f y) ∧ Φ x = (f x, 0) := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hxe : x ∈ e.source := mem_chart_source E x
  let c : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞ :=
    { e.toPartialEquiv with
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  have hreg : fderiv ℝ (f ∘ e.symm) (e x) ≠ 0 := fun h =>
    hx ((Smale.ManifoldMorse.mem_criticalPoints_iff hf he hxe).mpr h)
  obtain ⟨d, hd, -, hfirst, hcenter⟩ :=
    exists_height_partialDiffeomorph e.open_target (e.map_source hxe)
      (Smale.ManifoldMorse.contDiffOn_chartExpression hf he) hreg
  let L := fderiv ℝ (f ∘ e.symm) (e x)
  have hdim : Module.finrank ℝ L.ker = Module.finrank ℝ (Model E) := by
    have hh := finrank_kernel_add_one hreg
    change Module.finrank ℝ L.ker + 1 = Module.finrank ℝ E at hh
    rw [finrank_euclideanSpace_fin]
    omega
  let j : L.ker ≃L[ℝ] Model E := ContinuousLinearEquiv.ofFinrankEq hdim
  let J : (ℝ × L.ker) ≃L[ℝ] (ℝ × Model E) := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr j
  let τ := J.toDiffeomorph.toPartialDiffeomorph
  refine ⟨(c.trans d).trans τ, ⟨⟨hxe, hd⟩, Set.mem_univ _⟩, ?_, ?_⟩
  · intro y hy
    change (d (e y)).1 = f y
    rw [hfirst]
    exact congrArg f (e.left_inv hy.1.1)
  · change J (d (e x)) = (f x, 0)
    rw [hcenter]
    change (f (e.symm (e x)), j 0) = (f x, 0)
    rw [e.left_inv hxe, map_zero]

theorem Smale.RegularLevel.inverse_height {M D : Type*} [TopologicalSpace M] [TopologicalSpace D]
    {f : M → ℝ} {b : ℝ} (e : OpenPartialHomeomorph M (ℝ × D)) (he : ∀ y ∈ e.source, (e y).1 = f y)
    {v : D} (hv : (b, v) ∈ e.target) : f (e.symm (b, v)) = b := by
  have h := he (e.symm (b, v)) (e.map_target hv)
  rw [e.right_inv hv] at h
  exact h.symm

attribute [local instance 100] Classical.propDecidable in
def Smale.RegularLevel.sliceInverse {M D : Type*} [TopologicalSpace M] [TopologicalSpace D]
    {f : M → ℝ} {b : ℝ} (e : OpenPartialHomeomorph M (ℝ × D)) (he : ∀ y ∈ e.source, (e y).1 = f y)
    (base : { x : M // f x = b }) (v : D) : { x : M // f x = b } :=
  if hv : (b, v) ∈ e.target then ⟨e.symm (b, v), inverse_height e he hv⟩ else base

attribute [local instance 100] Classical.propDecidable in
def Smale.RegularLevel.sliceChart {M D : Type*} [TopologicalSpace M] [TopologicalSpace D]
    {f : M → ℝ} {b : ℝ} (e : OpenPartialHomeomorph M (ℝ × D)) (he : ∀ y ∈ e.source, (e y).1 = f y)
    (base : { x : M // f x = b }) : OpenPartialHomeomorph { x : M // f x = b } D
    where
  toFun x := (e x).2
  invFun := sliceInverse e he base
  source := {x | (x : M) ∈ e.source}
  target := {v | (b, v) ∈ e.target}
  map_source' := by
    intro x hx
    have hp : (b, (e x).2) = e x := Prod.ext ((he x hx).trans x.property).symm rfl
    change (b, (e x).2) ∈ e.target
    rw [hp]
    exact e.map_source hx
  map_target' := by
    intro v hv
    change (b, v) ∈ e.target at hv
    change (sliceInverse e he base v : M) ∈ e.source
    simp only [sliceInverse, dif_pos hv]
    exact e.map_target hv
  left_inv' := by
    intro x hx
    have hp : (b, (e x).2) = e x := Prod.ext ((he x hx).trans x.property).symm rfl
    have ht : (b, (e x).2) ∈ e.target := hp ▸ e.map_source hx
    simp only [sliceInverse, dif_pos ht]
    apply Subtype.ext
    change e.symm (b, (e x).2) = x
    rw [hp]
    exact e.left_inv hx
  right_inv' := by
    intro v hv
    change (b, v) ∈ e.target at hv
    simp only [sliceInverse, dif_pos hv]
    rw [e.right_inv hv]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun :=
    continuous_snd.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx))
  continuousOn_invFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply
      (e.symm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun _ hv => hv)).congr
    intro v hv
    change (b, v) ∈ e.target at hv
    simp only [Function.comp_apply, sliceInverse, dif_pos hv]
    rfl

attribute [local instance 100] Classical.propDecidable in
theorem Smale.RegularLevel.sliceChart_symm_coe {M D : Type*} [TopologicalSpace M]
    [TopologicalSpace D] {f : M → ℝ} {b : ℝ} (e : OpenPartialHomeomorph M (ℝ × D))
    (he : ∀ y ∈ e.source, (e y).1 = f y) (base : { x : M // f x = b }) {v : D}
    (hv : v ∈ (sliceChart e he base).target) :
    ((sliceChart e he base).symm v : M) = e.symm (b, v) := by
  change (b, v) ∈ e.target at hv
  change (sliceInverse e he base v : M) = _
  simp only [sliceInverse, dif_pos hv]

theorem Smale.RegularLevel.contDiffOn_slice_transition {E D M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace M]
    [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × D) M (ℝ × D) ∞)
    (hΦ : ∀ y ∈ Φ.source, (Φ y).1 = f y) (hΨ : ∀ y ∈ Ψ.source, (Ψ y).1 = f y)
    (x y : { z : M // f z = b }) :
    let c := sliceChart Φ.toOpenPartialHomeomorph hΦ x
    let d := sliceChart Ψ.toOpenPartialHomeomorph hΨ y
    ContDiffOn ℝ ∞ (c.symm.trans d) (c.symm.trans d).source := by
  let c := sliceChart Φ.toOpenPartialHomeomorph hΦ x
  let d := sliceChart Ψ.toOpenPartialHomeomorph hΨ y
  let S := (c.symm.trans d).source
  have hS (v : D) (hv : v ∈ S) : (b, v) ∈ Φ.target ∧ Φ.symm (b, v) ∈ Ψ.source := by
    refine ⟨hv.1, ?_⟩
    have hh : (c.symm v : M) ∈ Ψ.source := hv.2
    rwa [sliceChart_symm_coe Φ.toOpenPartialHomeomorph hΦ x hv.1] at hh
  have hfirst : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (fun v => Φ.symm (b, v)) S :=
    Φ.contMDiffOn_invFun.comp ((contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn)
      (fun v hv => (hS v hv).1)
  have hsecond := Ψ.contMDiffOn_toFun.comp hfirst (fun v hv => (hS v hv).2)
  have hfull : ContDiffOn ℝ ∞ (fun v => (Ψ (Φ.symm (b, v))).2) S :=
    (contDiff_snd.contMDiff.comp_contMDiffOn hsecond).contDiffOn
  apply hfull.congr
  intro v hv
  change (Ψ (c.symm v : M)).2 = (Ψ (Φ.symm (b, v))).2
  rw [sliceChart_symm_coe Φ.toOpenPartialHomeomorph hΦ x hv.1]
  rfl

def Smale.RegularLevel.heightChart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) M (ℝ × Model E) ∞ :=
  Classical.choose (exists_native_height_chart hf (hreg x x.property))

theorem Smale.RegularLevel.heightChart_mem_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) : (x : M) ∈ (heightChart hf hreg x).source :=
  (Classical.choose_spec (exists_native_height_chart hf (hreg x x.property))).1

theorem Smale.RegularLevel.heightChart_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) :
    ∀ y ∈ (heightChart hf hreg x).source, (heightChart hf hreg x y).1 = f y :=
  (Classical.choose_spec (exists_native_height_chart hf (hreg x x.property))).2.1

def Smale.RegularLevel.levelChart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) : OpenPartialHomeomorph { x : M // f x = b } (Model E) :=
  sliceChart (heightChart hf hreg x).toOpenPartialHomeomorph (heightChart_height hf hreg x) x

@[instance_reducible]
def Smale.RegularLevel.chartedSpace {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ChartedSpace (Model E) { x : M // f x = b }
    where
  atlas := Set.range (levelChart hf hreg)
  chartAt := levelChart hf hreg
  mem_chart_source := heightChart_mem_source hf hreg
  chart_mem_atlas := fun x => ⟨x, rfl⟩

theorem Smale.RegularLevel.isManifold {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    letI := chartedSpace hf hreg
    IsManifold 𝓘(ℝ, Model E) ∞ { x : M // f x = b } := by
  let _ := chartedSpace hf hreg
  apply isManifold_of_contDiffOn
  intro c d hc hd
  obtain ⟨x, rfl⟩ := hc
  obtain ⟨y, rfl⟩ := hd
  simpa only [mfld_simps, levelChart] using
    contDiffOn_slice_transition (heightChart hf hreg x) (heightChart hf hreg y)
      (heightChart_height hf hreg x) (heightChart_height hf hreg y) x y

theorem Smale.RegularLevel.contMDiff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    letI := chartedSpace hf hreg
    ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, E) ∞ (Subtype.val : { x : M // f x = b } → M) := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  intro x
  let Φ := heightChart hf hreg x
  let c := levelChart hf hreg x
  have hx : x ∈ c.source := heightChart_mem_source hf hreg x
  have hc : ContMDiffAt 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ c x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hx
  have ht : (b, c x) ∈ Φ.target := c.map_source hx
  have hslice : ContMDiffAt 𝓘(ℝ, Model E) 𝓘(ℝ, E) ∞ (fun v => Φ.symm (b, v)) (c x) :=
    (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds ht)).comp (c x)
      (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
  have hcomp := hslice.comp x hc
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  change (y : M) = Φ.symm (b, c y)
  have heq : (b, c y) = Φ y :=
    Prod.ext ((heightChart_height hf hreg x y hy).trans y.property).symm rfl
  rw [heq]
  exact (Φ.left_inv' hy).symm

theorem Smale.RegularLevel.contMDiffAt_iff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) (x : X) :
    letI := chartedSpace hf hreg
    ContMDiffAt I 𝓘(ℝ, Model E) ∞ g x ↔ ContMDiffAt I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) x := by
  let _ := chartedSpace hf hreg
  constructor
  · intro hg
    exact (Smale.RegularLevel.contMDiff_inclusion hf hreg).contMDiffAt.comp x hg
  · intro hg
    apply contMDiffAt_iff_target.mpr
    refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hg.continuousAt, ?_⟩
    let Φ := heightChart hf hreg (g x)
    have hΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) ∞ Φ (g x) :=
      Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (heightChart_mem_source hf hreg (g x)))
    have hcomp := hΦ.comp x hg
    change ContMDiffAt I 𝓘(ℝ, Model E) ∞ (fun y => (Φ (g y)).2) x
    exact contDiff_snd.contMDiff.contMDiffAt.comp x hcomp

theorem Smale.RegularLevel.contMDiff_iff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    ContMDiff I 𝓘(ℝ, Model E) ∞ g ↔ ContMDiff I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) := by
  let _ := chartedSpace hf hreg
  exact forall_congr' (contMDiffAt_iff_inclusion hf hreg I g)

theorem Smale.RegularLevel.injective_mfderiv_of_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) (x : X)
    (hg : ContMDiffAt I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) x)
    (hi : Function.Injective (mfderiv I 𝓘(ℝ, E) (Subtype.val ∘ g) x)) :
    letI := chartedSpace hf hreg
    Function.Injective (mfderiv I 𝓘(ℝ, Model E) g x) := by
  let _ := chartedSpace hf hreg
  have hgl := (contMDiffAt_iff_inclusion hf hreg I g x).mpr hg
  have hv := (Smale.RegularLevel.contMDiff_inclusion hf hreg).contMDiffAt (x := g x)
  rw [mfderiv_comp x (hv.mdifferentiableAt (by simp)) (hgl.mdifferentiableAt (by simp))] at hi
  exact fun v w hvw =>
    hi
      (congrArg (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) (g x))
        hvw)
end Mathoverflow1973
