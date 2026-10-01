/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Collar.Tubular
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.Flow.HeightTranslating

/-!
# Collars of a regular level

Let `f : M → ℝ` be smooth on a compact manifold and `b` a regular value. A vector field `V` with
`df V = 1` on the level `f⁻¹(b)` gives transverse coordinates `(x, t) ↦ r (e x + t • de V)`
(`RegularLevel.transverseCoordinates`, with `e` a Euclidean embedding and `r` a smooth retraction
onto `M`), a diffeomorphism from a neighbourhood of `f⁻¹(b) × {0}` in `f⁻¹(b) × ℝ` onto a
neighbourhood of the level (`RegularLevel.exists_transverseCollar`). After a change of the `ℝ`
coordinate the collar is adapted to the height: `f (Ψ (x, t)) = b + t`
(`RegularLevel.exists_heightCollar`), and its image contains a band `f⁻¹ (ball b ε)`
(`RegularLevel.exists_heightCollar_with_band`). This is the collar neighbourhood theorem in its
two-sided, regular-level form (cf. Lee, *Introduction to Smooth Manifolds*, Thm 9.25; Milnor,
*Lectures on the h-cobordism theorem*, §3).

## References

* [John M. Lee, *Introduction to Smooth Manifolds*][lee13], Thm 9.25
* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, §3

## Tags

collar, regular level, regular value
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

@[expose] public noncomputable section

/-! ### Transverse level coordinates -/

/-- The displacement of a regular level set along the flow. -/
def RegularLevel.levelDisplacement {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (z : { x : M // f x = b } × ℝ) : EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.toFun z.1 + z.2 • mvfderiv 𝓘(ℝ, E) e.toFun z.1 (V z.1)

/-- The domain of transverse level coordinates. -/
def RegularLevel.transverseCoordinateDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) : Set ({ x : M // f x = b } × ℝ) :=
  levelDisplacement V ⁻¹' r.domain

/-- The transverse coordinates of a regular level set. -/
def RegularLevel.transverseCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) : ({ x : M // f x = b } × ℝ) → M :=
  r.toFun ∘ levelDisplacement V

/-- The transverse coordinates at time zero. -/
theorem RegularLevel.transverseCoordinates_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : { x : M // f x = b }) :
    transverseCoordinates r V (x, 0) = x := by
  simp only [transverseCoordinates, Function.comp_apply, levelDisplacement, zero_smul, add_zero]
  exact r.retract x

/-- Zero lies in the transverse coordinate domain. -/
theorem RegularLevel.zero_mem_transverseCoordinateDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {b : ℝ} {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : { x : M // f x = b }) :
    (x, 0) ∈ transverseCoordinateDomain r V := by
  change e.toFun x + (0 : ℝ) • _ ∈ r.domain
  simp only [zero_smul, add_zero]
  exact r.contains ⟨x, rfl⟩

/-- The level displacement is smooth. -/
theorem RegularLevel.contMDiff_levelDisplacement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : NativeEuclideanEmbedding E M}
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    letI := chartedSpace hf hreg
    ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) (𝓡 e.ambientDimension) ∞
      (levelDisplacement (e := e) (f := f) (b := b) V) := by
  let _ := chartedSpace hf hreg
  have hi :
    ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun z : { x : M // f x = b } × ℝ => (z.1 : M)) :=
    (RegularLevel.contMDiff_inclusion hf hreg).comp contMDiff_fst
  have hfirst := e.smooth.comp hi
  have hfield := (e.contMDiff_embeddedField hV).comp hi
  have htime :
    ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (Prod.snd : { x : M // f x = b } × ℝ → ℝ) :=
    contMDiff_snd
  exact hfirst.add (htime.smul hfield)

/-- The transverse coordinate domain is open. -/
theorem RegularLevel.isOpen_transverseCoordinateDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    IsOpen (transverseCoordinateDomain (f := f) (b := b) r V) := by
  let _ := chartedSpace hf hreg
  exact r.open_domain.preimage (contMDiff_levelDisplacement (e := e) V hf hreg hV).continuous

/-- The transverse coordinates are smooth on their domain. -/
theorem RegularLevel.contMDiffOn_transverseCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    letI := chartedSpace hf hreg
    ContMDiffOn (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (transverseCoordinates r V)
      (transverseCoordinateDomain (f := f) (b := b) r V) := by
  let _ := chartedSpace hf hreg
  exact
    r.smooth.comp (contMDiff_levelDisplacement (e := e) V hf hreg hV).contMDiffOn (fun _ hz => hz)

/-- The transverse coordinates' derivative in time at zero. -/
theorem RegularLevel.mfderiv_transverseCoordinates_time_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {b : ℝ} {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : { x : M // f x = b }) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0 =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (V x) := by
  let A := mvfderiv 𝓘(ℝ, E) e.toFun (x : M) (V x)
  let line : ℝ → EuclideanSpace ℝ (Fin e.ambientDimension) := fun t => e.toFun x + t • A
  have hline : HasFDerivAt line ((ContinuousLinearMap.id ℝ ℝ).smulRight A) 0 :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight A).hasFDerivAt.const_add (e.toFun x)
  have hzero : line 0 = e.toFun x := by simp [line]
  have hr : MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (line 0) := by
    rw [hzero]
    exact
      (r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨x, rfl⟩))).mdifferentiableAt
        (by simp)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (r.toFun ∘ line) 0 = _
  rw [mfderiv_comp 0 hr hline.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv, hline.fderiv,
    hzero]
  apply ContinuousLinearMap.ext
  intro t
  change ℝ at t
  let R : EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] E :=
    mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)
  change R (t • A) = t • (V x : E)
  rw [map_smul]
  congr 1
  exact congrArg (fun L => L (V x)) (r.mfderiv_retract_comp (x : M))

/-- The transverse coordinates' derivative at zero. -/
theorem RegularLevel.mfderiv_transverseCoordinates_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    mfderiv (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (transverseCoordinates r V) (x, 0) =
      transverseTangentMap hf hreg x (V x) := by
  let _ := chartedSpace hf hreg
  have hs :=
    (contMDiffOn_transverseCoordinates r V hf hreg hV).contMDiffAt
      ((isOpen_transverseCoordinateDomain r V hf hreg hV).mem_nhds
        (zero_mem_transverseCoordinateDomain r V x))
  have hbase : (fun y : { x : M // f x = b } => transverseCoordinates r V (y, 0)) = Subtype.val :=
    funext (transverseCoordinates_zero r V)
  apply ContinuousLinearMap.ext
  intro w
  rw [mfderiv_prod_eq_add_apply (hs.mdifferentiableAt (by simp)), hbase,
    mfderiv_transverseCoordinates_time_zero r V x]
  rfl

/-- The transverse coordinates are a local diffeomorphism at zero. -/
theorem RegularLevel.isLocalDiffeomorphAt_transverseCoordinates_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : { x : M // f x = b }) (hunit : mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1) :
    letI := chartedSpace hf hreg
    IsLocalDiffeomorphAt (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (transverseCoordinates r V)
      (x, 0) := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  have hs := contMDiffOn_transverseCoordinates r V hf hreg hV
  have hi :
    (mfderiv (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (transverseCoordinates r V)
        (x, 0)).IsInvertible := by
    rw [mfderiv_transverseCoordinates_zero r V hf hreg hV x]
    let A := transverseTangentMap hf hreg x (V x)
    exact
      ⟨(LinearEquiv.ofBijective A.toLinearMap
            (bijective_transverseTangentMap hf hreg x (V x) hunit)).toContinuousLinearEquiv,
        rfl⟩
  exact
    isLocalDiffeomorphAt_between_manifolds
      (isOpen_transverseCoordinateDomain r V hf hreg hV)
      (zero_mem_transverseCoordinateDomain r V x) hs hi

/-- The height along the transverse coordinates differentiates to one. -/
theorem RegularLevel.hasDerivAt_height_transverseCoordinates_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : { x : M // f x = b }) (hunit : mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1) :
    HasDerivAt (fun t : ℝ => f (transverseCoordinates r V (x, t))) 1 0 := by
  let _ := chartedSpace hf hreg
  have hs :=
    (contMDiffOn_transverseCoordinates r V hf hreg hV).contMDiffAt
      ((isOpen_transverseCoordinateDomain r V hf hreg hV).mem_nhds
        (zero_mem_transverseCoordinateDomain r V x))
  have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (x, t)) 0 :=
    contMDiffAt_const.prodMk contMDiffAt_id
  have hcurve := ((hs.comp 0 hpair).mdifferentiableAt (by simp)).hasMFDerivAt
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0) at hcurve
  rw [mfderiv_transverseCoordinates_time_zero r V x] at hcurve
  have hc := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp 0 hcurve
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro t
  change ℝ at t
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  have hd : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (transverseCoordinates r V (x, 0)) : E →L[ℝ] ℝ) = L := by
    rw [transverseCoordinates_zero r V x]
    rfl
  change
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (transverseCoordinates r V (x, 0)) : E →L[ℝ] ℝ) (t • (V x : E)) =
      t • (1 : ℝ)
  exact
    (congrArg (fun T : E →L[ℝ] ℝ => T (t • (V x : E))) hd).trans
      ((L.map_smul t (V x)).trans (congrArg (fun a : ℝ => t • a) hunit))

/-! ### The height collar -/

/-- A unit-height field exists near a regular level. -/
theorem RegularLevel.exists_unitHeightField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        ∀ x : { x : M // f x = b }, mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1 := by
  have hband : ∀ x, f x ∈ Set.Icc b b → x ∉ ManifoldMorse.criticalPoints E f := fun x hx =>
    hreg x (le_antisymm hx.2 hx.1)
  obtain ⟨φ, W, -, -, hW, hφ, V, hV, hheight⟩ :=
    FlowConstruction.exists_regularBandField hf hband
  refine ⟨V, hV, ?_⟩
  intro x
  exact (hheight x).trans (hφ (hW (by rw [x.property]; exact ⟨le_rfl, le_rfl⟩)))

/-- A transverse collar of a regular level exists. -/
theorem RegularLevel.exists_transverseCollar {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
          (Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Φ.source ∧
            (∀ x : { x : M // f x = b }, Φ (x, 0) = x) ∧
              ∀ x : { x : M // f x = b }, HasDerivAt (fun t : ℝ => f (Φ (x, t))) 1 0 := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let _ : CompactSpace { x : M // f x = b } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Nonempty M := Nonempty.map (fun x : { x : M // f x = b } => (x : M)) inferInstance
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hunit⟩ := exists_unitHeightField hf hreg
  let K : Set ({ x : M // f x = b } × ℝ) := Set.univ ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hinj : Set.InjOn (transverseCoordinates r V) K := by
    rintro ⟨x, s⟩ ⟨-, hs⟩ ⟨y, t⟩ ⟨-, ht⟩ hxy
    have hs0 : s = 0 := hs
    have ht0 : t = 0 := ht
    subst s
    subst t
    rw [transverseCoordinates_zero r V x, transverseCoordinates_zero r V y] at hxy
    exact Prod.ext (Subtype.ext hxy) rfl
  have hloc :
    ∀ z ∈ K,
      IsLocalDiffeomorphAt (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (transverseCoordinates r V) z :=
    by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact isLocalDiffeomorphAt_transverseCoordinates_zero r V hf hreg hV x (hunit x)
  have hKD : K ⊆ transverseCoordinateDomain r V := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact zero_mem_transverseCoordinateDomain r V x
  obtain ⟨Φ, hKΦ, -, heq⟩ :=
    exists_partialDiffeomorph_near_compact hK hinj hloc
      (isOpen_transverseCoordinateDomain r V hf hreg hV) hKD
  obtain ⟨ε, hε, hsource⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset isCompact_univ Φ.open_source hKΦ
  refine ⟨ε, hε, Φ, hsource, ?_, ?_⟩
  · intro x
    exact (congrFun heq (x, 0)).trans (transverseCoordinates_zero r V x)
  · intro x
    have hh : (fun t : ℝ => f (Φ (x, t))) = fun t : ℝ => f (transverseCoordinates r V (x, t)) :=
      funext (fun t => congrArg f (congrFun heq (x, t)))
    rw [hh]
    exact hasDerivAt_height_transverseCoordinates_zero r V hf hreg hV x (hunit x)

/-- A height band inside an open set exists. -/
theorem RegularLevel.exists_heightBand_subset_open {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {g : X → ℝ} (hg : Continuous g) {a : ℝ} {U : Set X} (hU : IsOpen U)
    (hlevel : ∀ x, g x = a → x ∈ U) : ∃ δ : ℝ, 0 < δ ∧ g ⁻¹' Metric.ball a δ ⊆ U := by
  have hclosed : IsClosed (g '' Uᶜ) := (hU.isClosed_compl.isCompact.image hg).isClosed
  have ha : a ∉ g '' Uᶜ := by
    rintro ⟨x, hx, hxa⟩
    exact hx (hlevel x hxa)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl a ha
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  by_contra hnot
  exact hball hx ⟨x, hnot, rfl⟩

/-- A height collar of a regular level exists. -/
theorem RegularLevel.exists_heightCollar {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Ψ :
          PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
          (Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Ψ.source ∧
            (∀ x : { x : M // f x = b }, Ψ (x, 0) = x) ∧ ∀ z ∈ Ψ.source, f (Ψ z) = b + z.2 := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let _ : CompactSpace { x : M // f x = b } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  obtain ⟨ε, hε, Φ, hsource, hzero, hderiv⟩ := exists_transverseCollar hf hreg
  let H : { x : M // f x = b } × ℝ → ℝ := fun z => f (Φ z) - b
  have hH : ContMDiffOn (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H Φ.source :=
    (hf.comp_contMDiffOn Φ.contMDiffOn_toFun).sub contMDiff_const.contMDiffOn
  have hH0 (x : { x : M // f x = b }) : H (x, 0) = 0 := by
    change f (Φ (x, 0)) - b = 0
    rw [hzero x, x.property, sub_self]
  have hzeroSource (x : { x : M // f x = b }) : (x, 0) ∈ Φ.source :=
    hsource ⟨Set.mem_univ x, Metric.mem_closedBall_self hε.le⟩
  have hHt (x : { x : M // f x = b }) : HasDerivAt (fun t : ℝ => H (x, t)) 1 0 :=
    (hderiv x).sub_const b
  obtain ⟨χ, hKχ, -, hχ⟩ :=
    CollarHeight.exists_heightChangeChart Φ.open_source hH hH0 hzeroSource hHt
  have hχzero (x : { x : M // f x = b }) : χ (x, 0) = (x, 0) :=
    (congrFun hχ (x, 0)).trans (CollarHeight.heightChange_zero hH0 x)
  have hχtarget (x : { x : M // f x = b }) : (x, 0) ∈ χ.target := by
    rw [← hχzero x]
    exact χ.map_source' (hKχ ⟨Set.mem_univ x, rfl⟩)
  have hχinv (x : { x : M // f x = b }) : χ.symm (x, 0) = (x, 0) := by
    have hh : χ.symm (χ (x, 0)) = (x, 0) := χ.left_inv' (hKχ ⟨Set.mem_univ x, rfl⟩)
    rwa [hχzero x] at hh
  let Ψ := χ.symm.trans Φ
  have hzeroΨ : (Set.univ : Set { x : M // f x = b }) ×ˢ {(0 : ℝ)} ⊆ Ψ.source := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨hχtarget x, ?_⟩
    change χ.symm (x, 0) ∈ Φ.source
    rw [hχinv x]
    exact hzeroSource x
  obtain ⟨δ, hδ, hproduct⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset isCompact_univ Ψ.open_source hzeroΨ
  refine ⟨δ, hδ, Ψ, hproduct, ?_, ?_⟩
  · intro x
    change Φ (χ.symm (x, 0)) = x
    rw [hχinv x, hzero x]
  · intro z hz
    have hheight : H (χ.symm z) = z.2 := by
      calc
        H (χ.symm z) = (χ (χ.symm z)).2 := (congrArg Prod.snd (congrFun hχ (χ.symm z))).symm
        _ = z.2 := congrArg Prod.snd (χ.right_inv' hz.1)
    change f (Φ (χ.symm z)) = b + z.2
    change f (Φ (χ.symm z)) - b = z.2 at hheight
    linarith

/-- A height collar with a prescribed band exists. -/
theorem RegularLevel.exists_heightCollar_with_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Ψ :
          PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
          (Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Ψ.source ∧
            (∀ x : { x : M // f x = b }, Ψ (x, 0) = x) ∧
              (∀ z ∈ Ψ.source, f (Ψ z) = b + z.2) ∧ f ⁻¹' Metric.ball b ε ⊆ Ψ.target := by
  let _ := chartedSpace hf hreg
  obtain ⟨ε, hε, Ψ, hsource, hzero, hheight⟩ := exists_heightCollar hf hreg
  have hlevel : ∀ x, f x = b → x ∈ Ψ.target := by
    intro x hx
    let y : { x : M // f x = b } := ⟨x, hx⟩
    have hmem : Ψ (y, 0) ∈ Ψ.target :=
      Ψ.map_source' (hsource ⟨Set.mem_univ y, Metric.mem_closedBall_self hε.le⟩)
    have hy : Ψ (y, 0) = x := hzero y
    exact hy ▸ hmem
  obtain ⟨δ, hδ, hband⟩ := exists_heightBand_subset_open hf.continuous Ψ.open_target hlevel
  refine ⟨Min.min ε δ, lt_min hε hδ, Ψ, ?_, hzero, hheight, ?_⟩
  · exact fun z hz => hsource ⟨hz.1, Metric.closedBall_subset_closedBall (min_le_left ε δ) hz.2⟩
  · exact fun x hx => hband (Metric.ball_subset_ball (min_le_right ε δ) hx)
