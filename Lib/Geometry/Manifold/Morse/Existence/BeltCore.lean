/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.Morse.HandleAttachment
public import Lib.Geometry.Manifold.Flow.HeightTranslating
public import Lib.Geometry.Manifold.Morse.Existence.LevelSurgery
public import Lib.Geometry.Manifold.Morse.Existence.PartialChart

/-!
# The attaching and belt spheres of a handle

For a signed Morse chart `c` at `p` and a block radius `ρ`, the core of the handle meets the
upper level `{f = f p + ρ²}` in the belt sphere, the image of the unit sphere of the positive
coordinates under the `beltCoreMap`, and the lower level in the attaching sphere, the image of
the `attachingCoreMap`. Both maps are smooth closed embeddings with injective differential
(Milnor, *Lectures on the h-cobordism theorem*, §3, attaching and belt spheres).

## Main definitions and results

* `ManifoldMorse.SignedMorseChart.beltCoreMap` and `beltSphere_eq_beltCoreMap`.
* `ManifoldMorse.SignedMorseChart.attachingCoreMap_isClosedEmbedding`,
  `beltCoreMap_isClosedEmbedding`.
* `ManifoldMorse.SignedMorseChart.injective_mfderiv_attachingCoreMap`,
  `injective_mfderiv_beltCoreMap`.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65]

## Tags

handle, attaching sphere, belt sphere, embedding
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Surgery boundary pairs -/

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
