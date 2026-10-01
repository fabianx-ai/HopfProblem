/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.BeltComplement
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Collar

/-!
# Surgery data of a Morse critical point

`ManifoldMorse.MorseSurgeryData E f p` packages, for a critical point `p` of a smooth `f`, a
signed Morse chart and radius `ρ`, the homeomorphism of `{f ≤ f p - ρ²} ∪ handle` with
`{f ≤ f p + ρ²}`, and the resulting surgery boundary pair from the level `f p - ρ²` to the
level `f p + ρ²` with its attaching and belt spheres (Milnor, *Morse Theory*, Thm 3.2;
Milnor, *Lectures on the h-cobordism theorem*, §3). The attaching and belt sphere maps are
smooth closed embeddings with injective differentials, such data exist for every isolated
critical value with arbitrarily small radius (`ManifoldMorse.exists_morseSurgeryData_lt`),
and between two windows without critical values in between the levels are related by an
ambient diffeomorphism (`ManifoldMorse.MorseSurgeryData.exists_smoothBandBridge`; Milnor,
*Morse Theory*, Thm 3.1).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- The surgery data of a signed Morse chart: attaching and belt spheres with levels. -/
structure ManifoldMorse.MorseSurgeryData (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ)
    (p : M) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : SignedMorseChart (E := E) f p
  block :
    Metric.closedBall (0 : chart.NegativeCoordinates) (2 * radius) ×ˢ
        Metric.closedBall (0 : chart.PositiveCoordinates) (2 * radius) ⊆
      chart.splitChart.target
  attachmentHomeomorph :
    ↥({x : M | f x ≤ f p - radius ^ 2} ∪
          Set.range (chart.attachingHandleMap radius radius_pos block)) ≃ₜ
      { x : M // f x ≤ f p + radius ^ 2 }
  attachment_frontier :
    ∀ x,
      f (attachmentHomeomorph x) = f p + radius ^ 2 ↔
        x.val ∈
          frontier
            ({y : M | f y ≤ f p - radius ^ 2} ∪
              Set.range (chart.attachingHandleMap radius radius_pos block))
  attachment_fixed : ∀ x, f x.val = f p + radius ^ 2 → (attachmentHomeomorph x).val = x.val
  attachment_model_orbits :
    chart.FollowsModelBoundaryOrbits radius radius_pos block attachmentHomeomorph
  surgery :
    SurgeryBoundaryPair chart.NegativeCoordinates chart.PositiveCoordinates
      { x : M //
        f x = f p - radius ^ 2 ∧
          x ∈
            frontier
              ({y | f y ≤ f p - radius ^ 2} ∪
                Set.range (chart.normHandleMap radius radius_pos block)) }
      { x : M // f x = f p - radius ^ 2 } { x : M // f x = f p + radius ^ 2 }
  oldExterior_eq : ∀ r, (surgery.oldExterior r : M) = r.val
  newExterior_eq :
    ∀ r, (surgery.newExterior r : M) = (attachmentHomeomorph ⟨r.val, Or.inl r.property.1.le⟩).val
  oldPiece_eq :
    ∀ z,
      (surgery.oldPiece z : M) =
        chart.normHandleMap radius radius_pos block (PuncturedHandle.sphereToBall z.1, z.2)
  newPiece_eq :
    ∀ z,
      (surgery.newPiece z : M) =
        (attachmentHomeomorph
            ⟨chart.normHandleMap radius radius_pos block
                (z.1, PuncturedHandle.sphereToBall z.2),
              Or.inr
                ⟨chart.handleBallCoordinates (z.1, PuncturedHandle.sphereToBall z.2),
                  rfl⟩⟩).val
  belt_eq : surgery.beltSphere = chart.beltCoreMap radius radius_pos block
  lower_regular : ∀ x, f x = f p - radius ^ 2 → x ∉ criticalPoints E f
  upper_regular : ∀ x, f x = f p + radius ^ 2 → x ∉ criticalPoints E f

/-- The lower level of the surgery data. -/
abbrev ManifoldMorse.MorseSurgeryData.LowerLevel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :=
  { x : M // f x = f p - d.radius ^ 2 }

/-- The upper level of the surgery data. -/
abbrev ManifoldMorse.MorseSurgeryData.UpperLevel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :=
  { x : M // f x = f p + d.radius ^ 2 }

attribute [local instance 100] Classical.propDecidable in
/-- The attaching map computes the sphere inclusion. -/
theorem ManifoldMorse.MorseSurgeryData.attaching_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    d.surgery.attachingSphere = d.chart.attachingCoreMap d.radius d.radius_pos d.block :=
  d.chart.attachingSphere_eq_attachingCoreMap d.radius d.radius_pos d.block d.surgery
    d.oldPiece_eq

attribute [local instance 100] Classical.propDecidable in
/-- The attaching sphere map is a closed embedding. -/
theorem ManifoldMorse.MorseSurgeryData.attaching_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] :
    Topology.IsClosedEmbedding d.surgery.attachingSphere := by
  rw [d.attaching_eq]
  exact d.chart.attachingCoreMap_isClosedEmbedding d.radius d.radius_pos d.block

attribute [local instance 100] Classical.propDecidable in
/-- The belt sphere map is a closed embedding. -/
theorem ManifoldMorse.MorseSurgeryData.belt_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] :
    Topology.IsClosedEmbedding d.surgery.beltSphere := by
  rw [d.belt_eq]
  exact d.chart.beltCoreMap_isClosedEmbedding d.radius d.radius_pos d.block

attribute [local instance 100] Classical.propDecidable in
/-- The attaching map is smooth. -/
theorem ManifoldMorse.MorseSurgeryData.attaching_smooth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.surgery.attachingSphere := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  rw [d.attaching_eq]
  exact d.chart.contMDiff_attachingCoreMap n hf d.radius d.radius_pos d.block d.lower_regular

attribute [local instance 100] Classical.propDecidable in
/-- The belt map is smooth. -/
theorem ManifoldMorse.MorseSurgeryData.belt_smooth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.surgery.beltSphere := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  rw [d.belt_eq]
  exact d.chart.contMDiff_beltCoreMap n hf d.radius d.radius_pos d.block d.upper_regular

attribute [local instance 100] Classical.propDecidable in
/-- The attaching map's derivative is injective. -/
theorem ManifoldMorse.MorseSurgeryData.attaching_derivative_injective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)]
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    Function.Injective
      (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.attachingSphere u) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  rw [d.attaching_eq]
  exact
    d.chart.injective_mfderiv_attachingCoreMap n hf d.radius d.radius_pos d.block d.lower_regular
      u

attribute [local instance 100] Classical.propDecidable in
/-- The belt map's derivative is injective. -/
theorem ManifoldMorse.MorseSurgeryData.belt_derivative_injective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  rw [d.belt_eq]
  exact d.chart.injective_mfderiv_beltCoreMap n hf d.radius d.radius_pos d.block d.upper_regular v

attribute [local instance 100] Classical.propDecidable in
/-- Loops in the upper level are nullhomotopic. -/
theorem ManifoldMorse.MorseSurgeryData.upper_circle_nullhomotopies {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [T2Space M] (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)] (hn : 0 < n)
    (hdim : 3 + n < Module.finrank ℝ E)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = f p - d.radius ^ 2 }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = f p + d.radius ^ 2 }),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) :=
  d.chart.surgery_newBoundary_circle_nullhomotopies n hn hf d.radius d.radius_pos d.block
    d.lower_regular d.surgery d.oldPiece_eq hdim hnull

attribute [local instance 100] Classical.propDecidable in
/-- Morse surgery data exists below a level. -/
theorem ManifoldMorse.exists_morseSurgeryData_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : MorseSurgeryData E f p,
      d.radius < ε ∧
        ∀ x ∈ criticalPoints E f,
          f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p := by
  obtain ⟨ρ, hρ, hρε, c, hblock, e, he, hfixed, hlevel, hlower, hupper, horbits, hband⟩ :=
    exists_morse_boundary_attachment_with_model_orbits_lt hf hm hp hunique hε
  exact
    ⟨{  radius := ρ
        radius_pos := hρ
        chart := c
        block := hblock
        attachmentHomeomorph := e
        attachment_frontier := he
        attachment_fixed := hfixed
        attachment_model_orbits := horbits
        surgery := c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e he
        oldExterior_eq := fun _ => rfl
        newExterior_eq := fun _ => rfl
        oldPiece_eq := fun _ => rfl
        newPiece_eq := fun _ => rfl
        belt_eq := c.beltSphere_eq_beltCoreMap hf.continuous ρ hρ hblock hlevel e he hfixed
        lower_regular := hlower
        upper_regular := hupper }, hρε, hband⟩

/-- The standard sphere parametrization by hemisphere coordinates. -/
def SphereCoordinates.standardParametrization (N : Type*) [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)] [FiniteDimensional ℝ N] :
    Diffeomorph (𝓡 n) (𝓡 n) (Hemisphere.Sphere n) (Metric.sphere (0 : N) 1) ∞ := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let b := (stdOrthonormalBasis ℝ N).reindex (finCongr (Fact.out : Module.finrank ℝ N = n + 1))
  exact SphereCoordinates.ofLinearIsometry b.repr.symm

attribute [local instance 100] Classical.propDecidable in
/-- The attaching sphere transported by the flow. -/
def ManifoldMorse.MorseSurgeryData.transportedAttachingSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) : C(Hemisphere.Sphere n, d.UpperLevel) :=
  ⟨fun x =>
    e.symm
      (d'.surgery.attachingSphere
        (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n x)),
    e.symm.continuous.comp
      (d'.surgery.attachingSphere.continuous.comp
        (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates
            n).continuous)⟩

attribute [local instance 100] Classical.propDecidable in
/-- The transported attaching sphere computes the flow. -/
theorem ManifoldMorse.MorseSurgeryData.transportedAttachingSphere_apply {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) (x : Hemisphere.Sphere n) :
    e (d.transportedAttachingSphere d' n e x) =
      d'.surgery.attachingSphere
        (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n x) :=
  e.apply_symm_apply _

attribute [local instance 100] Classical.propDecidable in
/-- The range of the transported attaching sphere. -/
theorem ManifoldMorse.MorseSurgeryData.range_transportedAttachingSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) :
    Set.range (d.transportedAttachingSphere d' n e) =
      e ⁻¹' Set.range d'.surgery.attachingSphere := by
  let s := SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨s x, (d.transportedAttachingSphere_apply d' n e x).symm⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := s.surjective z
    refine ⟨x, e.injective ?_⟩
    rw [d.transportedAttachingSphere_apply d' n e]
    exact (congrArg d'.surgery.attachingSphere hx).trans hz

attribute [local instance 100] Classical.propDecidable in
/-- The transported attaching sphere is smooth. -/
theorem ManifoldMorse.MorseSurgeryData.transportedAttachingSphere_smooth {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := RegularLevel.chartedSpace hf d'.lower_regular
    ∀ e :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) d.UpperLevel
        d'.LowerLevel ∞,
      ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞
        (d.transportedAttachingSphere d' n e.toHomeomorph) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.chartedSpace hf d'.lower_regular
  intro e
  exact
    e.symm.contMDiff.comp
      ((d'.attaching_smooth hf n).comp
        (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates
            n).contMDiff)

/-- A smooth band bridge of the surgery data exists. -/
theorem ManifoldMorse.MorseSurgeryData.exists_smoothBandBridge {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [T2Space M] [CompactSpace M]
    (hgap : f p + d.radius ^ 2 ≤ f q - d'.radius ^ 2)
    (hband :
      ∀ x,
        f x ∈ Set.Icc (f p + d.radius ^ 2) (f q - d'.radius ^ 2) →
          x ∉ ManifoldMorse.criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := RegularLevel.chartedSpace hf d'.lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ e :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) d.UpperLevel
          d'.LowerLevel ∞,
        D '' {x : M | f x ≤ f p + d.radius ^ 2} = {x : M | f x ≤ f q - d'.radius ^ 2} ∧
          ∀ x : d.UpperLevel, (e x : M) = D x := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.chartedSpace hf d'.lower_regular
  obtain ⟨D, hlevel, hsublevel⟩ :=
    RegularLevel.exists_ambient_regularBand_transport hf hgap hband
  obtain ⟨e, he⟩ :=
    RegularLevel.exists_levelDiffeomorph_of_ambient hf d.upper_regular d'.lower_regular D
      hlevel
  exact ⟨D, e, hsublevel, he⟩
