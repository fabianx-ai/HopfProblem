/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.CriticalPoints

/-!
# Descent vector fields and prescribed derivatives

For a smooth `f : M → ℝ` on a σ-compact Hausdorff manifold modelled on a finite-dimensional real
space: near a regular point there is a smooth field `V` with `df(V) = 1`; for a smooth `χ`
supported off the critical set there is a smooth `V` with `df(V) = χ`; and finitely many local
fields with `df(V) < 0` off the critical set, given on disjoint open sets, glue to a global smooth
field with `df(V) < 0` off the critical set that agrees with them on prescribed closed sets
(convex gluing by partitions of unity, Mathlib's
`exists_contMDiffSection_forall_mem_convex_of_local`; cf. the gradient-like vector fields of
Milnor, *Lectures on the h-cobordism theorem*, §3). Also: the pullback of a constant or smooth
field along a chart or partial diffeomorphism (`chartDirection`, `partialChartField`) and its
`df`-value.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- A chart coordinate direction field. -/
def FlowConstruction.chartDirection {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (e : OpenPartialHomeomorph M E) (w : E) :
    (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e (fun y => (NormedSpace.fromTangentSpace y).symm w)

/-- The chart direction field is smooth on the chart domain. -/
theorem FlowConstruction.contMDiffOn_chartDirection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (w : E) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, chartDirection e w x⟩ : TangentBundle 𝓘(ℝ, E) M)) e.source := by
  have hW :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y : E => (⟨y, (NormedSpace.fromTangentSpace y).symm w⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  intro x hx
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x).IsInvertible := ⟨he'.mfderiv hx, rfl⟩
  exact
    ((hW (e x)).mpullback_vectorField_preimage (contMDiffAt_of_mem_maximalAtlas he hx) hinv
        (by simp)).contMDiffWithinAt

/-- The chart direction differentiates the function as the derivative component. -/
theorem FlowConstruction.mvfderiv_chartDirection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (w : E) {x : M} (hx : x ∈ e.source) :
    mvfderiv 𝓘(ℝ, E) f x (chartDirection e w x) = fderiv ℝ (f ∘ e.symm) (e x) w := by
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have h₁ := he'.comp_symm_deriv (e.map_source hx)
  rw [e.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he'.symm_comp_deriv hx)
  have hc :
    fderiv ℝ (f ∘ e.symm) (e x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (e x) (hf.mdifferentiableAt (by simp))
        (he'.mdifferentiableAt_symm (e.map_source hx))]
    rw [e.left_inv hx]
  unfold chartDirection
  rw [VectorField.mpullback_apply, hi]
  exact (congrArg (fun A : E →L[ℝ] ℝ => A w) hc).symm

/-- Near a regular point there is a unit-speed field. -/
theorem FlowConstruction.exists_unitSpeedField_near_regular {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {p : M} (hp : p ∉ ManifoldMorse.criticalPoints E f) :
    ∃ U : Set M,
      IsOpen U ∧
        p ∈ U ∧
          ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
            ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) U ∧
              ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) f x (V x) = 1 := by
  classical
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hpS : p ∈ e.source := mem_chart_source E p
  have hdf : fderiv ℝ (f ∘ e.symm) (e p) ≠ 0 := fun h =>
    hp ((ManifoldMorse.mem_criticalPoints_iff hf he hpS).mpr h)
  have hw : ∃ w : E, fderiv ℝ (f ∘ e.symm) (e p) w ≠ 0 := by
    by_contra! h
    exact hdf (ContinuousLinearMap.ext h)
  obtain ⟨w, hw⟩ := hw
  let D : M → ℝ := fun x => fderiv ℝ (f ∘ e.symm) (e x) w
  have hder :=
    (ManifoldMorse.contDiffOn_chartExpression hf he).fderiv_of_isOpen e.open_target (m := ∞)
      (by simp)
  have hD : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D e.source :=
    (hder.clm_apply contDiffOn_const).contMDiffOn.comp (contMDiffOn_of_mem_maximalAtlas he)
      (fun _ hx => e.map_source hx)
  let U : Set M := e.source ∩ D ⁻¹' {0}ᶜ
  have hU : IsOpen U :=
    hD.continuousOn.isOpen_inter_preimage e.open_source
      (isClosed_singleton (x := (0 : ℝ))).isOpen_compl
  let V : (x : M) → TangentSpace 𝓘(ℝ, E) x := fun x => (D x)⁻¹ • chartDirection e w x
  refine ⟨U, hU, ⟨hpS, hw⟩, V, ?_, ?_⟩
  · exact
      ((hD.mono Set.inter_subset_left).inv₀ (fun _ hx => hx.2)).smul_section
        ((contMDiffOn_chartDirection he w).mono Set.inter_subset_left)
  · intro x hx
    change mvfderiv 𝓘(ℝ, E) f x ((D x)⁻¹ • chartDirection e w x) = 1
    rw [map_smul, smul_eq_mul, mvfderiv_chartDirection hf he w hx.1]
    exact inv_mul_cancel₀ hx.2

/-- Near a regular point a prescribed nonzero derivative field exists. -/
theorem FlowConstruction.exists_prescribedDerivativeField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] {f χ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ (ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        ∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) = χ x := by
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x => {w | mvfderiv 𝓘(ℝ, E) f x w = χ x}
  have hC (x : M) : Convex ℝ (C x) :=
    (convex_singleton (χ x)).linear_preimage (mvfderiv 𝓘(ℝ, E) f x).toLinearMap
  have hlocal :
    ∀ p : M,
      ∃ U ∈ 𝓝 p,
        ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))
              U ∧
            ∀ x ∈ U, V x ∈ C x := by
    intro p
    by_cases hp : p ∉ ManifoldMorse.criticalPoints E f
    · obtain ⟨U, hU, hpU, V, hV, hVunit⟩ := exists_unitSpeedField_near_regular hf hp
      refine ⟨U, hU.mem_nhds hpU, (fun x => χ x • V x), hχ.contMDiffOn.smul_section hV, ?_⟩
      intro x hx
      change mvfderiv 𝓘(ℝ, E) f x (χ x • V x) = χ x
      rw [map_smul, hVunit x hx, smul_eq_mul, mul_one]
    · have hps : p ∉ tsupport χ := fun h => hp (hsupp h)
      refine
        ⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl.mem_nhds hps, (fun _ => 0),
          (Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, E))).contMDiffOn, ?_⟩
      intro x hx
      change mvfderiv 𝓘(ℝ, E) f x 0 = χ x
      rw [map_zero, image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨V, hV⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
      (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, hV⟩

/-- Local descent fields glue to a descent field near a regular set. -/
theorem FlowConstruction.exists_gluedDescentField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {ι : Type*} [Finite ι] (U K : ι → Set M)
    (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsClosed (K i)) (hKU : ∀ i, K i ⊆ U i)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : ManifoldMorse.criticalPoints E f ⊆ ⋃ i, K i)
    (Vloc : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hVloc :
      ∀ i,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, Vloc i x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U i))
    (hdesc :
      ∀ i x,
        x ∈ U i →
          x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (Vloc i x) < 0) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
          ∀ i x, x ∈ K i → V x = Vloc i x := by
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x =>
    {w |
      (x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x w < 0) ∧
        ∀ i, x ∈ K i → w = Vloc i x}
  have hC (x : M) : Convex ℝ (C x) := by
    intro u hu v hv a b ha hb hab
    refine ⟨?_, ?_⟩
    · intro hreg
      have h := (convex_Iio (0 : ℝ)) (hu.1 hreg) (hv.1 hreg) ha hb hab
      simpa only [map_add, map_smul, smul_eq_mul, Set.mem_Iio] using h
    · intro i hxi
      rw [hu.2 i hxi, hv.2 i hxi, ← add_smul, hab, one_smul]
  have hclosed : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hK
  have hlocal :
    ∀ p : M,
      ∃ W ∈ 𝓝 p,
        ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))
              W ∧
            ∀ x ∈ W, V x ∈ C x := by
    intro p
    by_cases hp : p ∈ ⋃ i, K i
    · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
      refine ⟨U i, (hU i).mem_nhds (hKU i hpi), Vloc i, hVloc i, ?_⟩
      intro x hx
      refine ⟨hdesc i x hx, ?_⟩
      intro j hxj
      by_cases hij : i = j
      · subst j
        rfl
      · exact False.elim (Set.disjoint_left.mp (hdisj hij) hx (hKU j hxj))
    · have hpreg : p ∉ ManifoldMorse.criticalPoints E f := fun h => hp (hcover h)
      obtain ⟨W, hW, hpW, V, hV, hVf⟩ := exists_unitSpeedField_near_regular hf hpreg
      refine
        ⟨W ∩ (⋃ i, K i)ᶜ, (hW.inter hclosed.isOpen_compl).mem_nhds ⟨hpW, hp⟩, (fun x => -(V x)),
          hV.neg_section.mono Set.inter_subset_left, ?_⟩
      intro x hx
      refine ⟨?_, ?_⟩
      · intro _
        change mvfderiv 𝓘(ℝ, E) f x (-V x) < 0
        rw [map_neg, hVf x hx.1]
        norm_num
      · intro i hxi
        exact False.elim (hx.2 (Set.mem_iUnion.mpr ⟨i, hxi⟩))
  obtain ⟨V, hV⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
      (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, fun x => (hV x).1, fun i x hx => (hV x).2 i hx⟩

/-- A descent field exists on a closed patch of regular points. -/
theorem MorseCancellation.exists_closed_patch_descent_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] {f : M → ℝ}
    (V₀ : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV₀ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V₀ x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero₀ : ∀ x ∈ ManifoldMorse.criticalPoints E f, V₀ x = 0)
    (hdesc₀ : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V₀ x) < 0)
    {ι : Type*} [Finite ι] (K U : ι → Set M) (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (Vloc : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hVloc :
      ∀ i,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, Vloc i x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U i))
    (hzero : ∀ i x, x ∈ U i → x ∈ ManifoldMorse.criticalPoints E f → Vloc i x = 0)
    (hdesc :
      ∀ i x,
        x ∈ U i →
          x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (Vloc i x) < 0) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
          (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
            ∀ i x, x ∈ K i → V x = Vloc i x := by
  classical
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x =>
    {w |
      (x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x w < 0) ∧
        (x ∈ ManifoldMorse.criticalPoints E f → w = 0) ∧ ∀ i, x ∈ K i → w = Vloc i x}
  have hC (x : M) : Convex ℝ (C x) := by
    intro u hu v hv a b ha hb hab
    refine ⟨?_, ?_, ?_⟩
    · intro hreg
      have h := (convex_Iio (0 : ℝ)) (hu.1 hreg) (hv.1 hreg) ha hb hab
      simpa only [map_add, map_smul, smul_eq_mul, Set.mem_Iio] using h
    · intro hcrit
      rw [hu.2.1 hcrit, hv.2.1 hcrit, smul_zero, smul_zero, add_zero]
    · intro i hxi
      rw [hu.2.2 i hxi, hv.2.2 i hxi, ← add_smul, hab, one_smul]
  have hclosed : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hK
  have hlocal :
    ∀ p : M,
      ∃ O ∈ 𝓝 p,
        ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))
              O ∧
            ∀ x ∈ O, V x ∈ C x := by
    intro p
    by_cases hp : p ∈ ⋃ i, K i
    · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
      let R := ⋃ j : { j : ι // j ≠ i }, K j
      have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hK j)
      have hpR : p ∉ R := by
        intro hpR
        obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hpR
        exact Set.disjoint_left.mp (hdisj (fun h => j.property h.symm)) hpi hpj
      refine
        ⟨U i ∩ Rᶜ, ((hU i).inter hR.isOpen_compl).mem_nhds ⟨hKU i hpi, hpR⟩, Vloc i,
          (hVloc i).mono Set.inter_subset_left, ?_⟩
      intro x hx
      refine ⟨hdesc i x hx.1, hzero i x hx.1, ?_⟩
      intro j hxj
      by_cases hij : i = j
      · subst j
        rfl
      · exact False.elim (hx.2 (Set.mem_iUnion.mpr ⟨⟨j, fun h => hij h.symm⟩, hxj⟩))
    · refine ⟨(⋃ i, K i)ᶜ, hclosed.isOpen_compl.mem_nhds hp, V₀, hV₀.contMDiffOn, ?_⟩
      intro x hx
      refine ⟨hdesc₀ x, hzero₀ x, ?_⟩
      intro i hxi
      exact False.elim (hx (Set.mem_iUnion.mpr ⟨i, hxi⟩))
  obtain ⟨V, hV⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
      (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, fun x => (hV x).2.1, fun x => (hV x).1, fun i x hx => (hV x).2.2 i hx⟩

/-- A field on a partial chart. -/
def FlowConstruction.partialChartField {E F M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) (W : F → F) :
    (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) e (fun y => (NormedSpace.fromTangentSpace y).symm (W y))

/-- The partial chart field is smooth on its domain. -/
theorem FlowConstruction.contMDiffOn_partialChartField {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) {W : F → F} (hW : ContDiff ℝ ∞ W) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, partialChartField e W x⟩ : TangentBundle 𝓘(ℝ, E) M)) e.source := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hW' :
    ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, F).tangent) ∞
      (fun y : F =>
        (⟨y, (NormedSpace.fromTangentSpace y).symm (W y)⟩ : TangentBundle 𝓘(ℝ, F) F)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hW
  intro x hx
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x).IsInvertible := ⟨he.mfderiv hx, rfl⟩
  exact
    ((hW' (e x)).mpullback_vectorField_preimage
        ((e.contMDiffOn x hx).contMDiffAt (e.open_source.mem_nhds hx)) hinv
        (by simp)).contMDiffWithinAt

/-- The partial chart field's derivative of the function. -/
theorem FlowConstruction.mvfderiv_partialChartField {E F M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) (W : F → F) {x : M} (hx : x ∈ e.source) :
    mvfderiv 𝓘(ℝ, E) f x (partialChartField e W x) = fderiv ℝ (f ∘ e.symm) (e x) (W (e x)) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₁ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he.symm_comp_deriv hx)
  have hc :
    fderiv ℝ (f ∘ e'.symm) (e' x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e'.symm (e' x)) := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (e' x) (hf.mdifferentiableAt (by simp))
        (he.mdifferentiableAt_symm (e'.map_source hx))]
    rw [e'.left_inv hx]
  unfold partialChartField
  rw [VectorField.mpullback_apply]
  change
    mvfderiv 𝓘(ℝ, E) f x
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e' x).inverse
          ((NormedSpace.fromTangentSpace (e' x)).symm (W (e' x)))) =
      _
  rw [hi]
  exact (congrArg (fun A : F →L[ℝ] ℝ => A (W (e' x))) hc).symm
