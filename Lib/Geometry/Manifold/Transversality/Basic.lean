/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
/-!
# Transversality: submersions, regular values, and supported perturbations

The elementary transversality toolkit: the surjectivity of a derivative read in a chart, regular
values and the null set of critical values, the transversality relation for two maps into a common
manifold, perturbation of a map by a translation in a chart, diffeomorphisms supported in a compact
set and the germs they realise, smooth radial deformations, and the shrinking of an embedded disc.

## Main definitions and results

* `NativeSubmersion.surjective_fderiv_sourceChart_iff`,
  `NativeSubmersion.isOpen_surjective_nativeDerivative` : being a submersion is a chart-independent
  and open condition.
* `RegularValues.exists_null_exceptional_values_manifold` : the set of critical values of a smooth
  map between manifolds of equal dimension is null (Sard's theorem in the equidimensional case).
* `NativeTransversality.At` : the transversality relation `f ⋔ g` at a pair of points, i.e. the
  surjectivity of `d f_x ⊕ d g_y` whenever `g y = f x` (Guillemin–Pollack, §2.3), together with its
  chart description, its openness in a smooth family, and its invariance under a diffeomorphism of
  the target.
* `TransverseCoordinates.dense_native_translations` : the translations making two maps into a
  finite-dimensional vector space transverse are dense — the parametric transversality theorem
  (Hirsch, Ch. 3).
* `SupportedGerms.Realizes` and `SupportedGerms.realizes_local_germ` : a germ of a diffeomorphism
  at the origin with derivative of determinant one is the germ of a diffeomorphism isotopic to the
  identity through diffeomorphisms supported in a prescribed neighbourhood. The ambient space is
  assumed of dimension at least two (the basis is indexed by a `Finite`, `Nontrivial` type).
* `SmoothRadial.radialMap`, `SmoothRadial.diffeomorph`, `DiskShrinking.family` : the radial maps
  `x ↦ φ(‖x‖²) • x`, when they are diffeomorphisms, and the isotopy shrinking the unit disc by a
  factor `a` while fixing the complement of a larger ball.
* `DiskShrinking.exists_embedded_disk_isotopy_of_same_center` : the disc theorem — two embedded
  discs of positive codimension with the same centre in a manifold of dimension at least two are
  carried onto one another by a diffeomorphism isotopic to the identity (Hirsch, Thm 8.3.1; Palais).

## References

* [M. Hirsch, *Differential Topology*][hirsch76], Ch. 2–3 and Thm 8.3.1.
* [V. Guillemin, A. Pollack, *Differential Topology*][gp74], Ch. 2.

## Tags

transversality, general position, perturbation, isotopy, disc theorem
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section

/-- Transparent variant of `Diffeomorph.toPartialDiffeomorph`: Mathlib's version is not
`@[expose]`d, so under the module system its fields do not unfold for importers. This
version keeps `source = target = univ` and `⇑_ = h`/`⇑_.symm = h.symm` definitional. -/
def Diffeomorph.toPartialDiffeomorph' {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J ∞ N] (h : Diffeomorph I J M N ∞) :
    PartialDiffeomorph I J M N ∞ where
  toPartialEquiv :=
    { toFun := h
      invFun := h.symm
      source := Set.univ
      target := Set.univ
      map_source' := fun _ _ => Set.mem_univ _
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := fun _ _ => h.symm_apply_apply _
      right_inv' := fun _ _ => h.apply_symm_apply _ }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := fun x _ => h.contMDiff_toFun x
  contMDiffOn_invFun := fun x _ => h.symm.contMDiff_toFun x

/-- Transparent variant of `IsLocalDiffeomorph.diffeomorphOfBijective`: Mathlib's version is
not `@[expose]`d, so its function values do not unfold for module-mode importers. Built on
`Equiv.ofBijective`, hence `⇑(hf.diffeomorph' hf') = f` is definitional. The inverse is
smooth because near each `y` it agrees with the local inverse at `g y`. -/
def IsLocalDiffeomorph.diffeomorph' {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] {f : M → N}
    (hf : IsLocalDiffeomorph I J ∞ f) (hf' : Function.Bijective f) :
    Diffeomorph I J M N ∞ where
  toEquiv := Equiv.ofBijective f hf'
  contMDiff_toFun := hf.contMDiff
  contMDiff_invFun := by
    intro y
    have hfgy : f ((Equiv.ofBijective f hf').symm y) = y :=
      (Equiv.ofBijective f hf').right_inv y
    have hmem : y ∈ (hf ((Equiv.ofBijective f hf').symm y)).localInverse.source := by
      have h := (hf ((Equiv.ofBijective f hf').symm y)).localInverse_mem_source
      rwa [hfgy] at h
    have heq :
      EqOn (Equiv.ofBijective f hf').symm
        (hf ((Equiv.ofBijective f hf').symm y)).localInverse
        (hf ((Equiv.ofBijective f hf').symm y)).localInverse.source := by
      intro y' hy'
      apply hf'.1
      trans y'
      · exact (Equiv.ofBijective f hf').right_inv y'
      · exact ((hf ((Equiv.ofBijective f hf').symm y)).localInverse_right_inv hy').symm
    exact ((hf ((Equiv.ofBijective f hf').symm y)).localInverse_contMDiffOn.congr
        heq).contMDiffAt
      ((hf ((Equiv.ofBijective f hf').symm y)).localInverse_open_source.mem_nhds hmem)

/-- Being a submersion is a chart-independent condition: the derivative of `f` read in a chart `c`
is surjective at `z` exactly when the manifold derivative of `f` is surjective at `c.symm z`.
-/
theorem NativeSubmersion.surjective_fderiv_sourceChart_iff {E F H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    (c : PartialDiffeomorph I 𝓘(ℝ, E) X E ∞) {f : X → F} {z : E} (hz : z ∈ c.target)
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f (c.symm z)) :
    Function.Surjective (fderiv ℝ (f ∘ c.symm) z) ↔
      Function.Surjective (mfderiv I 𝓘(ℝ, F) f (c.symm z)) := by
  let A : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f (c.symm z)
  let B : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I c.symm z
  have hd : fderiv ℝ (f ∘ c.symm) z = A.comp B := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp z hf (c.symm.mdifferentiableAt (by simp) hz)
  have hB : Function.Surjective B := (PartialChart.bijective_mfderiv c.symm hz).surjective
  rw [hd]
  change Function.Surjective (A.comp B) ↔ Function.Surjective A
  constructor
  · intro h w
    obtain ⟨v, hv⟩ := h w
    exact ⟨B v, hv⟩
  · intro h
    exact h.comp hB

/-- In a smooth family of maps between manifolds of equal dimension, the set of parameters and
points at which the derivative is surjective is open.
-/
theorem NativeSubmersion.isOpen_surjective_nativeDerivative {E F H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [I.Boundaryless] [IsManifold I ∞ X] {f : P → X → F} {W : Set (P × X)}
    (hW : IsOpen W) (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ (Function.uncurry f) W)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsOpen {q : P × X | q ∈ W ∧ Function.Surjective (mfderiv I 𝓘(ℝ, F) (f q.1) q.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqsurj⟩
  let c := modelChartPartialDiffeomorph (I := I) q.2
  have hqc : q.2 ∈ c.source := mem_extChartAt_source q.2
  let Q : Set (P × E) := Set.univ ×ˢ c.target
  let C : P × E → P × X := fun r => (r.1, c.symm r.2)
  have hQ : IsOpen Q := isOpen_univ.prod c.open_target
  have hC : ContMDiffOn 𝓘(ℝ, P × E) (𝓘(ℝ, P).prod I) ∞ C Q :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (c.contMDiffOn_invFun.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hr => hr.2))
  let U : Set (P × E) := Q ∩ C ⁻¹' W
  have hU : IsOpen U := hC.continuousOn.isOpen_inter_preimage hQ hW
  have hcoord : ContDiffOn ℝ ∞ (fun r : P × E => f r.1 (c.symm r.2)) U :=
    (hf.comp (hC.mono Set.inter_subset_left) (fun _ hr => hr.2)).contDiffOn
  have hspatial :=
    MorsePerturbation.contDiffOn_spatialDerivative (f := fun a z => f a (c.symm z)) hU
      hcoord
  have hopen : IsOpen {A : E →L[ℝ] F | Function.Surjective A} := by
    have heq : {A : E →L[ℝ] F | Function.Surjective A} = {A : E →L[ℝ] F | Function.Injective A} :=
      by
      ext A
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).symm
    rw [heq]
    exact ContinuousLinearMap.isOpen_injective
  let V : Set (P × E) :=
    U ∩
      (fun r => fderiv ℝ (fun z => f r.1 (c.symm z)) r.2) ⁻¹'
        {A : E →L[ℝ] F | Function.Surjective A}
  have hV : IsOpen V := hspatial.continuousOn.isOpen_inter_preimage hU hopen
  have hiff (r : P × E) (hr : r ∈ U) :
    Function.Surjective (fderiv ℝ (fun z => f r.1 (c.symm z)) r.2) ↔
      Function.Surjective (mfderiv I 𝓘(ℝ, F) (f r.1) (c.symm r.2)) := by
    have hfr : ContMDiffAt I 𝓘(ℝ, F) ∞ (f r.1) (c.symm r.2) :=
      (hf.contMDiffAt (hW.mem_nhds hr.2)).comp (c.symm r.2)
        (contMDiffAt_const.prodMk contMDiffAt_id)
    exact surjective_fderiv_sourceChart_iff c hr.1.2 (hfr.mdifferentiableAt (by simp))
  have hleft : c.symm (c q.2) = q.2 := c.left_inv' hqc
  have hqU : (q.1, c q.2) ∈ U := by
    refine ⟨⟨Set.mem_univ _, c.map_source' hqc⟩, ?_⟩
    change (q.1, c.symm (c q.2)) ∈ W
    rw [hleft]
    exact hq
  have hqV : (q.1, c q.2) ∈ V := by
    refine ⟨hqU, (hiff _ hqU).mpr ?_⟩
    exact hleft.symm ▸ hqsurj
  have hforward : ContinuousAt (fun r : P × X => (r.1, c r.2)) q :=
    continuousAt_fst.prodMk
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hqc)).continuousAt.comp
        continuousAt_snd)
  have hn := hforward.preimage_mem_nhds (hV.mem_nhds hqV)
  have hnc : ∀ᶠ r : P × X in 𝓝 q, r.2 ∈ c.source :=
    continuous_snd.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hqc)
  apply Filter.mem_of_superset (Filter.inter_mem hn hnc)
  intro r hr
  have hleft' : c.symm (c r.2) = r.2 := c.left_inv' hr.2
  have hmem : (r.1, c.symm (c r.2)) ∈ W := hr.1.1.2
  have hsurj := (hiff (r.1, c r.2) hr.1.1).mp hr.1.2
  refine ⟨?_, hleft' ▸ hsurj⟩
  rwa [hleft'] at hmem

/-- Sard's theorem for a differentiable self-map of a finite-dimensional space in the
equidimensional case: outside a null set of values the derivative at every preimage in `s` is
bijective.
-/
theorem RegularValues.exists_null_exceptional_values_on {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → E}
    {s : Set E} (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    ∃ T : Set E, μ T = 0 ∧ ∀ x ∈ s, f x ∉ T → Function.Bijective (fderiv ℝ f x) := by
  let B : Set E := {x | x ∈ s ∧ (fderiv ℝ f x).det = 0}
  have hzero : μ (f '' B) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hf x hx.1).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx.2)
  refine ⟨f '' B, hzero, ?_⟩
  intro x hx hfx
  apply (bijective_iff_det_ne_zero _).mpr
  intro hdet
  exact hfx ⟨x, ⟨hx, hdet⟩, rfl⟩

/-- The critical values of a smooth map on the source of one chart, between manifolds of equal
dimension, form a null set.
-/
theorem RegularValues.exists_null_exceptional_values_in_chart {E F H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace X] [ChartedSpace H X] [MeasurableSpace F] [BorelSpace F]
    (μ : MeasureTheory.Measure F) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (c : PartialDiffeomorph I 𝓘(ℝ, E) X E ∞) {f : X → F} {s : Set X} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ T : Set F,
      μ T = 0 ∧ ∀ x ∈ c.source ∩ s, f x ∉ T → Function.Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  let L : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hdim
  let W : Set F := L '' (c.target ∩ c.symm ⁻¹' s)
  let G : F → F := fun z => f (c.symm (L.symm z))
  have hcoord (z : F) (hz : z ∈ W) : L.symm z ∈ c.target ∧ c.symm (L.symm z) ∈ s := by
    obtain ⟨w, hw, rfl⟩ := hz
    rw [L.symm_apply_apply]
    exact hw
  have hsmooth (z : F) (hz : z ∈ W) : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ G z := by
    have hh := hcoord z hz
    exact
      (hf.contMDiffAt (hs.mem_nhds hh.2)).comp z
        ((c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds hh.1)).comp z
          L.symm.contDiff.contMDiff.contMDiffAt)
  obtain ⟨T, hT, hgood⟩ :=
    exists_null_exceptional_values_on μ
      (fun z hz => (hsmooth z hz).mdifferentiableAt (by simp) |>.differentiableAt)
  refine ⟨T, hT, ?_⟩
  intro x hx hfx
  let z := L (c x)
  have hz : z ∈ W := by
    refine ⟨c x, ⟨c.map_source' hx.1, ?_⟩, rfl⟩
    change c.symm (c x) ∈ s
    have heq : c.symm (c x) = x := c.left_inv' hx.1
    rw [heq]
    exact hx.2
  have hpoint : c.symm (L.symm z) = x := by
    change c.symm (L.symm (L (c x))) = x
    rw [L.symm_apply_apply]
    exact c.left_inv' hx.1
  have hvalue : G z = f x := congrArg f hpoint
  have hbij := hgood z hz (by rwa [hvalue])
  have hfx' : MDifferentiableAt I 𝓘(ℝ, F) f (c.symm (L.symm z)) :=
    (hf.contMDiffAt (hs.mem_nhds (hcoord z hz).2)).mdifferentiableAt (by simp)
  have hinner : MDifferentiableAt 𝓘(ℝ, F) I (c.symm ∘ L.symm) z :=
    (c.symm.mdifferentiableAt (by simp) (hcoord z hz).1).comp z
      L.symm.toContinuousLinearMap.differentiableAt.mdifferentiableAt
  rw [← mfderiv_eq_fderiv] at hbij
  change Function.Bijective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (f ∘ (c.symm ∘ L.symm)) z) at hbij
  rw [mfderiv_comp z hfx' hinner] at hbij
  have hsurj : Function.Surjective (mfderiv I 𝓘(ℝ, F) f (c.symm (L.symm z))) := by
    intro w
    obtain ⟨v, hv⟩ := hbij.surjective w
    exact ⟨mfderiv 𝓘(ℝ, F) I (c.symm ∘ L.symm) z v, hv⟩
  exact hpoint ▸ hsurj

/-- Sard's theorem, equidimensional case: for a smooth map from a Lindelöf manifold to a manifold of
the same dimension, the set of critical values is null, so almost every value is regular.
-/
theorem RegularValues.exists_null_exceptional_values_manifold {E F H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [MeasurableSpace F] [BorelSpace F] (μ : MeasureTheory.Measure F)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] [LindelofSpace X] {f : X → F} {s : Set X}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ T : Set F, μ T = 0 ∧ ∀ x ∈ s, f x ∉ T → Function.Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  classical
  let c (x : X) := modelChartPartialDiffeomorph (I := I) x
  let U : X → Set X := fun x => (c x).source
  have hU : ∀ x, IsOpen (U x) := fun x => (c x).open_source
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨t, htcount, ht⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let _ := htcount.to_subtype
  choose T hT hgood using fun i : t => exists_null_exceptional_values_in_chart μ (c i) hs hf hdim
  refine ⟨⋃ i : t, T i, MeasureTheory.measure_iUnion_null hT, ?_⟩
  intro x hx hfx
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  apply hgood ⟨i, hit⟩ x ⟨hxi, hx⟩
  intro hi
  exact hfx (Set.mem_iUnion.mpr ⟨⟨i, hit⟩, hi⟩)

/-- The derivative of the difference map `(x, y) ↦ g y - f x` is the coproduct of `-d f_x` and
`d g_y`.
-/
theorem TransverseCoordinates.mfderiv_sheetDifference {D Z F H K X Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {J : ModelWithCorners ℝ Z K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace K Y] {f : X → F} {g : Y → F} {x : X}
    {y : Y} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hg : MDifferentiableAt J 𝓘(ℝ, F) g y) :
    (mfderiv (I.prod J) 𝓘(ℝ, F) (fun z : X × Y => g z.2 - f z.1) (x, y) : D × Z →L[ℝ] F) =
      (-(mfderiv I 𝓘(ℝ, F) f x : D →L[ℝ] F)).coprod (mfderiv J 𝓘(ℝ, F) g y : Z →L[ℝ] F) := by
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x
  let B : Z →L[ℝ] F := mfderiv J 𝓘(ℝ, F) g y
  change
    (mfderiv (I.prod J) 𝓘(ℝ, F) (g ∘ Prod.snd - f ∘ Prod.fst) (x, y) : D × Z →L[ℝ] F) =
      (-A).coprod B
  have hf' : MDifferentiableAt (I.prod J) 𝓘(ℝ, F) (f ∘ Prod.fst) (x, y) :=
    hf.comp (x, y) mdifferentiableAt_fst
  have hg' : MDifferentiableAt (I.prod J) 𝓘(ℝ, F) (g ∘ Prod.snd) (x, y) :=
    hg.comp (x, y) mdifferentiableAt_snd
  rw [mfderiv_sub hg' hf', mfderiv_comp (x, y) hg mdifferentiableAt_snd,
    mfderiv_comp (x, y) hf mdifferentiableAt_fst, mfderiv_fst, mfderiv_snd]
  apply ContinuousLinearMap.ext
  intro v
  change B v.2 - A v.1 = -(A v.1) + B v.2
  abel

/-- The difference map `(x, y) ↦ g y - f x` is a submersion at `(x, y)` exactly when `f` and `g` are
transverse there, that is when `d f_x ⊕ d g_y` is surjective.
-/
theorem TransverseCoordinates.surjective_sheetDifference_iff {D Z F H K X Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {J : ModelWithCorners ℝ Z K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace K Y] {f : X → F} {g : Y → F} {x : X}
    {y : Y} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hg : MDifferentiableAt J 𝓘(ℝ, F) g y) :
    Function.Surjective (mfderiv (I.prod J) 𝓘(ℝ, F) (fun z : X × Y => g z.2 - f z.1) (x, y)) ↔
      Function.Surjective
        ((mfderiv I 𝓘(ℝ, F) f x : D →L[ℝ] F).coprod (mfderiv J 𝓘(ℝ, F) g y : Z →L[ℝ] F)) := by
  rw [mfderiv_sheetDifference hf hg]
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x
  let B : Z →L[ℝ] F := mfderiv J 𝓘(ℝ, F) g y
  change Function.Surjective ((-A).coprod B) ↔ Function.Surjective (A.coprod B)
  constructor
  · intro h w
    obtain ⟨v, hv⟩ := h w
    refine ⟨(-v.1, v.2), ?_⟩
    change A (-v.1) + B v.2 = w
    change -(A v.1) + B v.2 = w at hv
    simpa only [map_neg] using hv
  · intro h w
    obtain ⟨v, hv⟩ := h w
    refine ⟨(-v.1, v.2), ?_⟩
    change -(A (-v.1)) + B v.2 = w
    change A v.1 + B v.2 = w at hv
    simpa only [map_neg, neg_neg] using hv

/-- For maps into a finite-dimensional space, the translations `a` for which `f` and `g + a` fail to
be transverse form a null set; this is the measure-theoretic form of the parametric
transversality theorem (Hirsch, Differential Topology, Ch. 3).
-/
theorem TransverseCoordinates.exists_null_exceptional_native_translations
    {D Z F H K X Y : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {J : ModelWithCorners ℝ Z K} [I.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace K Y] [IsManifold J ∞ Y] [LindelofSpace (X × Y)] [MeasurableSpace F]
    [BorelSpace F] (μ : MeasureTheory.Measure F) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {f : X → F} {g : Y → F} {U : Set X} {V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U) (hg : ContMDiffOn J 𝓘(ℝ, F) ∞ g V)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F) :
    ∃ T : Set F,
      μ T = 0 ∧
        ∀ a ∉ T,
          ∀ x ∈ U,
            ∀ y ∈ V,
              g y = f x + a →
                Function.Surjective ((mfderiv I 𝓘(ℝ, F) f x).coprod (mfderiv J 𝓘(ℝ, F) g y)) := by
  let B : X × Y → F := fun z => g z.2 - f z.1
  have hB : ContMDiffOn (I.prod J) 𝓘(ℝ, F) ∞ B (U ×ˢ V) := by
    intro z hz
    have hfx : ContMDiffAt (I.prod J) 𝓘(ℝ, F) ∞ (fun w : X × Y => f w.1) z :=
      (hf.contMDiffAt (hU.mem_nhds hz.1)).comp z contMDiffAt_fst
    have hgy : ContMDiffAt (I.prod J) 𝓘(ℝ, F) ∞ (fun w : X × Y => g w.2) z :=
      (hg.contMDiffAt (hV.mem_nhds hz.2)).comp z contMDiffAt_snd
    exact (hgy.sub hfx).contMDiffWithinAt
  obtain ⟨T, hT, hgood⟩ :=
    RegularValues.exists_null_exceptional_values_manifold μ (hU.prod hV) hB
      (by simpa only [Module.finrank_prod] using hdim)
  refine ⟨T, hT, ?_⟩
  intro a ha x hx y hy hxy
  have hvalue : B (x, y) = a := by
    change g y - f x = a
    rw [hxy, add_sub_cancel_left]
  have hs := hgood (x, y) ⟨hx, hy⟩ (by rwa [hvalue])
  change
    Function.Surjective (mfderiv (I.prod J) 𝓘(ℝ, F) (fun z : X × Y => g z.2 - f z.1) (x, y)) at hs
  rw [mfderiv_sheetDifference ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hg.contMDiffAt (hV.mem_nhds hy)).mdifferentiableAt (by simp))] at hs
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x
  let B' : Z →L[ℝ] F := mfderiv J 𝓘(ℝ, F) g y
  change Function.Surjective ((-A).coprod B') at hs
  change Function.Surjective (A.coprod B')
  intro w
  obtain ⟨v, hv⟩ := hs w
  refine ⟨(-v.1, v.2), ?_⟩
  change A (-v.1) + B' v.2 = w
  change -(A v.1) + B' v.2 = w at hv
  simpa only [map_neg] using hv

/-- The translations making two maps into a finite-dimensional space transverse form a dense set: a
generic translate of one map is transverse to the other.
-/
theorem TransverseCoordinates.dense_native_translations {D Z F H K X Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ D H}
    {J : ModelWithCorners ℝ Z K} [I.Boundaryless] [J.Boundaryless] [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace K Y]
    [IsManifold J ∞ Y] [LindelofSpace (X × Y)] {f : X → F} {g : Y → F} {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U)
    (hg : ContMDiffOn J 𝓘(ℝ, F) ∞ g V)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F) :
    Dense
      {a : F |
        ∀ x ∈ U,
          ∀ y ∈ V,
            g y = f x + a →
              Function.Surjective ((mfderiv I 𝓘(ℝ, F) f x).coprod (mfderiv J 𝓘(ℝ, F) g y))} := by
  let _ : MeasurableSpace F := borel F
  let _ : BorelSpace F := ⟨rfl⟩
  let μ : MeasureTheory.Measure F := MeasureTheory.Measure.addHaar
  obtain ⟨T, hT, hgood⟩ := exists_null_exceptional_native_translations μ hU hV hf hg hdim
  have hdense : Dense Tᶜ := by
    apply μ.dense_of_ae
    rw [MeasureTheory.ae_iff]
    simpa only [Set.mem_compl_iff, Classical.not_not, Set.ofPred_mem_eq] using hT
  exact hdense.mono hgood

/-- Translating a map by a constant near a point does not change its derivative there. -/
theorem ChartMapPerturbation.mfderiv_eq_of_translation_germ {D F H X : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    {u v : X → F} {a : F} {x : X} (hu : MDifferentiableAt I 𝓘(ℝ, F) u x)
    (hevent : v =ᶠ[𝓝 x] fun z => u z + a) :
    (mfderiv I 𝓘(ℝ, F) v x : D →L[ℝ] F) = mfderiv I 𝓘(ℝ, F) u x := by
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) u x
  let C : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) (fun _ : X => a) x
  have hC : C = 0 := mfderiv_const
  have hh :=
    mfderiv_add hu
      (show MDifferentiableAt I 𝓘(ℝ, F) (fun _ : X => a) x from mdifferentiableAt_const)
  change (mfderiv I 𝓘(ℝ, F) (fun z => u z + a) x : D →L[ℝ] F) = A + C at hh
  rw [hC] at hh
  exact hevent.mfderiv_eq.trans (hh.trans (add_zero A))

/-- Transversality can be tested in a chart of the target: if the two maps composed with a chart are
transverse at a pair of points, so are the maps themselves.
-/
theorem ChartMapPerturbation.transverse_of_chart {D Z G F H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ D H}
    {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X}
    {y : Y} (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y) (hxy : g y = f x)
    (hx : f x ∈ c.source)
    (ht :
      Function.Surjective
        ((mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F).coprod
          (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F))) :
    Function.Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G)) := by
  let A : D →L[ℝ] G := mfderiv I J f x
  let B : Z →L[ℝ] G := mfderiv I' J g y
  let C : G →L[ℝ] F := mfderiv J 𝓘(ℝ, F) c (f x)
  have hy : g y ∈ c.source := hxy ▸ hx
  have hA : (mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F) = C.comp A :=
    mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf
  have hB : (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F) = C.comp B := by
    rw [mfderiv_comp y (c.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  have heq : (C.comp A).coprod (C.comp B) = C.comp (A.coprod B) := by
    apply ContinuousLinearMap.ext
    intro v
    change C (A v.1) + C (B v.2) = C (A v.1 + B v.2)
    exact (C.map_add _ _).symm
  rw [hA, hB] at ht
  change Function.Surjective ((C.comp A).coprod (C.comp B)) at ht
  rw [heq] at ht
  have hC : Function.Injective C := (PartialChart.bijective_mfderiv c hx).injective
  change Function.Surjective (A.coprod B)
  intro w
  obtain ⟨v, hv⟩ := ht (C w)
  exact ⟨v, hC hv⟩

/-- The converse: transversality of the two maps implies transversality of their compositions with a
chart of the target.
-/
theorem ChartMapPerturbation.transverse_in_chart {D Z G F H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ D H}
    {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X}
    {y : Y} (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y) (hxy : g y = f x)
    (hx : f x ∈ c.source)
    (ht :
      Function.Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G))) :
    Function.Surjective
      ((mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F).coprod
        (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F)) := by
  let A : D →L[ℝ] G := mfderiv I J f x
  let B : Z →L[ℝ] G := mfderiv I' J g y
  let C : G →L[ℝ] F := mfderiv J 𝓘(ℝ, F) c (f x)
  have hy : g y ∈ c.source := hxy ▸ hx
  have hA : (mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F) = C.comp A :=
    mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf
  have hB : (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F) = C.comp B := by
    rw [mfderiv_comp y (c.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  rw [hA, hB]
  change Function.Surjective ((C.comp A).coprod (C.comp B))
  have hC : Function.Surjective C := (PartialChart.bijective_mfderiv c hx).surjective
  change Function.Surjective (A.coprod B) at ht
  intro w
  obtain ⟨z, hz⟩ := hC w
  obtain ⟨v, hv⟩ := ht z
  refine ⟨v, ?_⟩
  change C (A v.1) + C (B v.2) = w
  rw [← C.map_add]
  exact (congrArg C hv).trans hz

/-- The transversality relation `f ⋔ g` at a pair of points: whenever `g y = f x`, the coproduct
`d f_x ⊕ d g_y` of the two derivatives is surjective (Guillemin–Pollack, Differential Topology,
§2.3).
-/
def NativeTransversality.At {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    (I : ModelWithCorners ℝ D H) (I' : ModelWithCorners ℝ Z H') (J : ModelWithCorners ℝ G K)
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [TopologicalSpace N] [ChartedSpace K N] (f : X → N) (g : Y → N) (x : X) (y : Y) : Prop :=
  g y = f x →
    Function.Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G))

/-- In a chart of the target, transversality at `(x, y)` is the surjectivity of the derivative of
the difference `(x, y) ↦ c (g y) - c (f x)`.
-/
theorem NativeTransversality.at_iff_chart_difference {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X}
    {y : Y} (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y) (hxy : g y = f x)
    (hx : f x ∈ c.source) :
    At I I' J f g x y ↔
      Function.Surjective
        (mfderiv (I.prod I') 𝓘(ℝ, F) (fun z : X × Y => c (g z.2) - c (f z.1)) (x, y)) := by
  have hy : g y ∈ c.source := hxy ▸ hx
  have hcf := (c.mdifferentiableAt (by simp) hx).comp x hf
  have hcg := (c.mdifferentiableAt (by simp) hy).comp y hg
  have hdiff := TransverseCoordinates.surjective_sheetDifference_iff hcf hcg
  constructor
  · intro ht
    apply hdiff.mpr
    exact ChartMapPerturbation.transverse_in_chart c hf hg hxy hx (ht hxy)
  · intro h _
    exact ChartMapPerturbation.transverse_of_chart c hf hg hxy hx (hdiff.mp h)

/-- Transversality is an open condition in a smooth family: the set of parameters and pairs of
points at which `f b` is transverse to `g` is open.
-/
theorem NativeTransversality.isOpen_at_family {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ G]
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [IsManifold I ∞ X] [IsManifold I' ∞ Y]
    [IsManifold J ∞ N] [T2Space N] {f : P → X → N} {g : Y → N} {U : Set P} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) J ∞ (Function.uncurry f) (U ×ˢ Set.univ))
    (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) :
    IsOpen {r : P × (X × Y) | r.1 ∈ U ∧ At I I' J (f r.1) g r.2.1 r.2.2} := by
  let W₀ : Set (P × (X × Y)) := U ×ˢ Set.univ
  have hW₀ : IsOpen W₀ := hU.prod isOpen_univ
  let F : P × (X × Y) → N := fun r => f r.1 r.2.1
  let G' : P × (X × Y) → N := fun r => g r.2.2
  have hF : ContMDiffOn (𝓘(ℝ, P).prod (I.prod I')) J ∞ F W₀ :=
    hf.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).contMDiffOn
      (fun _ hr => ⟨hr.1, Set.mem_univ _⟩)
  have hG : ContMDiff (𝓘(ℝ, P).prod (I.prod I')) J ∞ G' :=
    hg.comp (contMDiff_snd.comp contMDiff_snd)
  have hslice (a : P) (x : X) (ha : a ∈ U) : ContMDiffAt I J ∞ (f a) x :=
    (hf.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ha, Set.mem_univ x⟩)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqt⟩
  have hq₀ : q ∈ W₀ := ⟨hq, Set.mem_univ _⟩
  by_cases hcross : g q.2.2 = f q.1 q.2.1
  · let c := modelChartPartialDiffeomorph (I := J) (f q.1 q.2.1)
    have hqc : f q.1 q.2.1 ∈ c.source := mem_extChartAt_source _
    have hqgc : g q.2.2 ∈ c.source := hcross ▸ hqc
    let W : Set (P × (X × Y)) := (W₀ ∩ F ⁻¹' c.source) ∩ G' ⁻¹' c.source
    have hW : IsOpen W :=
      (hF.continuousOn.isOpen_inter_preimage hW₀ c.open_source).inter
        (c.open_source.preimage hG.continuous)
    let B : P → X × Y → G := fun a z => c (g z.2) - c (f a z.1)
    have hB : ContMDiffOn (𝓘(ℝ, P).prod (I.prod I')) 𝓘(ℝ, G) ∞ (Function.uncurry B) W := by
      intro r hr
      have hfirst :
        ContMDiffAt (𝓘(ℝ, P).prod (I.prod I')) 𝓘(ℝ, G) ∞ (fun s : P × (X × Y) => c (f s.1 s.2.1))
          r :=
        (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hr.1.2)).comp r
          (hF.contMDiffAt (hW₀.mem_nhds hr.1.1))
      have hsecond :
        ContMDiffAt (𝓘(ℝ, P).prod (I.prod I')) 𝓘(ℝ, G) ∞ (fun s : P × (X × Y) => c (g s.2.2)) r :=
        (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hr.2)).comp r hG.contMDiffAt
      exact (hsecond.sub hfirst).contMDiffWithinAt
    have hopen :=
      NativeSubmersion.isOpen_surjective_nativeDerivative hW hB
        (by simpa only [Module.finrank_prod] using hdim)
    have hqB : Function.Surjective (mfderiv (I.prod I') 𝓘(ℝ, G) (B q.1) q.2) :=
      (at_iff_chart_difference c ((hslice q.1 q.2.1 hq).mdifferentiableAt (by simp))
            (hg.mdifferentiableAt (by simp)) hcross hqc).mp
        hqt
    have hn :=
      hopen.mem_nhds
        (show q ∈ {r | r ∈ W ∧ Function.Surjective (mfderiv (I.prod I') 𝓘(ℝ, G) (B r.1) r.2)} from
          ⟨⟨⟨hq₀, hqc⟩, hqgc⟩, hqB⟩)
    apply Filter.mem_of_superset hn
    intro r hr
    refine ⟨hr.1.1.1.1, ?_⟩
    intro hxy
    have ht :=
      (at_iff_chart_difference c ((hslice r.1 r.2.1 hr.1.1.1.1).mdifferentiableAt (by simp))
            (hg.mdifferentiableAt (by simp)) hxy hr.1.1.2).mpr
        hr.2
    exact ht hxy
  · have hpair : ContinuousAt (fun r : P × (X × Y) => (G' r, F r)) q :=
      hG.continuous.continuousAt.prodMk (hF.contMDiffAt (hW₀.mem_nhds hq₀)).continuousAt
    have hne : IsOpen {z : N × N | z.1 ≠ z.2} := isOpen_ne_fun continuous_fst continuous_snd
    have hn := hpair.preimage_mem_nhds (hne.mem_nhds hcross)
    have hparam : ∀ᶠ r : P × (X × Y) in 𝓝 q, r.1 ∈ U :=
      continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hq)
    apply Filter.mem_of_superset (Filter.inter_mem hparam hn)
    intro r hr
    refine ⟨hr.1, ?_⟩
    intro hxy
    exact False.elim (hr.2 hxy)

/-- Transversality along a compact set persists under small changes of the parameter: if `f a` is
transverse to `g` on a compact set, so is `f b` for all `b` near `a`.
-/
theorem NativeTransversality.eventually_on_compact {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ G]
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [IsManifold I ∞ X] [IsManifold I' ∞ Y]
    [IsManifold J ∞ N] [T2Space N] {f : P → X → N} {g : Y → N} {U : Set P} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) J ∞ (Function.uncurry f) (U ×ˢ Set.univ))
    (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {C : Set (X × Y)}
    (hC : IsCompact C) {a : P} (ha : a ∈ U) (htrans : ∀ z ∈ C, At I I' J (f a) g z.1 z.2) :
    ∀ᶠ b in 𝓝 a, ∀ z ∈ C, At I I' J (f b) g z.1 z.2 := by
  have hopen :=
    MorsePerturbation.isOpen_forall_mem_compact hC (isOpen_at_family hU hf hg hdim)
  have hn := hopen.mem_nhds (fun z hz => ⟨ha, htrans z hz⟩)
  filter_upwards [hn] with b hb z hz
  exact (hb z hz).2

/-- Transversality is invariant under a diffeomorphism of the target: `f ⋔ g` at `(x, y)` exactly
when `P ∘ f ⋔ P ∘ g` there.
-/
theorem TransverseGerms.native_transversality_partial_diffeomorph_iff
    {A B Z E HA HB HZ HE X Y N M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HA] [TopologicalSpace HB]
    [TopologicalSpace HZ] [TopologicalSpace HE] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} {J : ModelWithCorners ℝ Z HZ} {J' : ModelWithCorners ℝ E HE}
    [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
    [TopologicalSpace N] [ChartedSpace HZ N] [TopologicalSpace M] [ChartedSpace HE M]
    (P : PartialDiffeomorph J J' N M ∞) {f : X → N} {g : Y → N} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y) (hxy : g y = f x)
    (hx : f x ∈ P.source) :
    NativeTransversality.At I I' J f g x y ↔
      NativeTransversality.At I I' J' (P ∘ f) (P ∘ g) x y := by
  let L : A →L[ℝ] Z := mfderiv I J f x
  let R : B →L[ℝ] Z := mfderiv I' J g y
  let C : Z →L[ℝ] E := mfderiv J J' P (f x)
  have hy : g y ∈ P.source := hxy ▸ hx
  have hL : (mfderiv I J' (P ∘ f) x : A →L[ℝ] E) = C.comp L :=
    mfderiv_comp x (P.mdifferentiableAt (by simp) hx) hf
  have hR : (mfderiv I' J' (P ∘ g) y : B →L[ℝ] E) = C.comp R := by
    rw [mfderiv_comp y (P.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  have hC : Function.Bijective C := PartialChart.bijective_mfderiv P hx
  constructor
  · intro ht _
    have hsum : Function.Surjective (L.coprod R) := ht hxy
    rw [hL, hR]
    intro w
    obtain ⟨z, hz⟩ := hC.surjective w
    obtain ⟨v, hv⟩ := hsum z
    refine ⟨v, ?_⟩
    change C (L v.1) + C (R v.2) = w
    rw [← C.map_add]
    exact (congrArg C hv).trans hz
  · intro ht _
    have hsum := ht (show (P ∘ g) y = (P ∘ f) x from congrArg P hxy)
    rw [hL, hR] at hsum
    intro w
    obtain ⟨v, hv⟩ := hsum (C w)
    refine ⟨v, hC.injective ?_⟩
    change C (L v.1 + R v.2) = C w
    rw [C.map_add]
    exact hv

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

/-- Translation by a vector, as a diffeomorphism of a normed space. -/
def NativeParametrization.translation {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : D) : Diffeomorph 𝓘(ℝ, D) 𝓘(ℝ, D) D D ∞
    where
  toEquiv :=
    { toFun := fun x => x + a
      invFun := fun x => x - a
      left_inv := fun _ => add_sub_cancel_right _ _
      right_inv := fun _ => sub_add_cancel _ _ }
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

/-- The chart of a manifold at a point `x`, translated so that `0` is sent to `x`; a parametrisation
of a neighbourhood of `x` centred at the origin.
-/
def NativeParametrization.centered {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] (x : N) :
    PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, D) D N ∞ :=
  let c := modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  (translation (c x)).toPartialDiffeomorph'.trans c.symm

/-- The origin lies in the source of the centred parametrisation. -/
theorem NativeParametrization.zero_mem_centered_source {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : (0 : D) ∈ (centered (D := D) x).source := by
  let c := modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  refine ⟨Set.mem_univ _, ?_⟩
  change 0 + c x ∈ c.target
  rw [zero_add]
  exact c.map_source' (mem_extChartAt_source x)

/-- The centred parametrisation sends the origin to the given point. -/
theorem NativeParametrization.centered_zero {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : centered (D := D) x (0 : D) = x := by
  let c := modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  change c.symm (0 + c x) = x
  rw [zero_add]
  exact c.left_inv' (mem_extChartAt_source x)

/-- The given point lies in the target of its centred parametrisation. -/
theorem NativeParametrization.mem_centered_target {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : x ∈ (centered (D := D) x).target := by
  have hx := (centered (D := D) x).map_source' (zero_mem_centered_source (D := D) x)
  rwa [centered_zero] at hx

/-- An isotopy supported in `K` preserves every set containing `K`. -/
theorem SupportedDiffeomorph.SupportedRelativeIsotopy.mapsTo_superset {E H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace X] [ChartedSpace H X] {e : Diffeomorph I I X X ∞} {K S : Set X}
    (A : SupportedDiffeomorph.SupportedRelativeIsotopy e K S) {U : Set X} (hKU : K ⊆ U)
    (t : ℝ) : Set.MapsTo (fun x => A.family (t, x)) U U := by
  obtain ⟨d, hd⟩ := A.slices t
  have hfix : ∀ x ∉ U, d x = x := by
    intro x hx
    exact (hd x).trans (A.fixedOutside t x (fun h => hx (hKU h)))
  intro x hx
  change A.family (t, x) ∈ U
  rw [← hd]
  exact SupportedDiffeomorph.mapsTo_of_fixed_outside d.toEquiv hfix hx

/-- The transport of a compactly supported relative isotopy through a partial diffeomorphism:
extending by the identity outside the image of the support gives a relative isotopy of the
target.
-/
def SupportedDiffeomorph.SupportedRelativeIsotopy.extension {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    {e : Diffeomorph I I X X ∞} {K S : Set X}
    (A : SupportedDiffeomorph.SupportedRelativeIsotopy e K S)
    (Φ : PartialDiffeomorph I J X Y ∞) (hK : IsCompact K) (hKsource : K ⊆ Φ.source) {T : Set Y}
    (hfixed : ∀ x ∈ Φ.source, Φ x ∈ T → x ∈ S) :
    SupportedDiffeomorph.SupportedRelativeIsotopy
      (SupportedDiffeomorph.extension Φ e hK hKsource A.endpoint_fixed_outside) (Φ '' K) T
    where
  family := fun p => SupportedDiffeomorph.extendMap Φ (fun x => A.family (p.1, x)) p.2
  smooth :=
    SupportedDiffeomorph.contMDiff_extendFamily Φ A.smooth hK hKsource A.fixedOutside
      (A.mapsTo_superset hKsource)
  zero := by
    intro y
    have heq : (fun x => A.family (0, x)) = id := funext A.zero
    rw [heq]
    exact SupportedDiffeomorph.extendMap_id Φ y
  one := by
    intro y
    exact congrArg (fun f : X → X => SupportedDiffeomorph.extendMap Φ f y) (funext A.one)
  slices := by
    intro t
    obtain ⟨d, hd⟩ := A.slices t
    have hfix : ∀ x ∉ K, d x = x := fun x hx => (hd x).trans (A.fixedOutside t x hx)
    exact
      ⟨SupportedDiffeomorph.extension Φ d hK hKsource hfix, fun y =>
        congrArg (fun f : X → X => SupportedDiffeomorph.extendMap Φ f y) (funext hd)⟩
  fixedOutside := fun t y hy =>
    SupportedDiffeomorph.extendMap_eq_of_notMem_image Φ (A.fixedOutside t) hy
  fixedOn := by
    intro t y hy
    by_cases hyt : y ∈ Φ.target
    · rw [SupportedDiffeomorph.extendMap_of_mem Φ _ hyt]
      have hsource : Φ.symm y ∈ Φ.source := Φ.map_target' hyt
      have hi : Φ (Φ.symm y) = y := Φ.right_inv' hyt
      have hs : Φ.symm y ∈ S := hfixed (Φ.symm y) hsource (hi.symm ▸ hy)
      rw [A.fixedOn t (Φ.symm y) hs]
      exact hi
    · exact SupportedDiffeomorph.extendMap_of_notMem Φ _ hyt

/-- The isotopy of `M × P` which, in the chart `Φ`, translates the `M` coordinate by `-β(x) • b(u)`
at time `smoothTransition t` and leaves the `P` coordinate fixed; a fibrewise bump translation
of a chart.
-/
def SupportedDiffeomorph.normalBumpFamily {E F H M P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (p : ℝ × (M × P)) : M × P :=
  (bumpFamily Φ β (-(Real.smoothTransition p.1 • b p.2.2), p.2.1), p.2.2)

/-- The bump translation leaves the second factor fixed. -/
theorem SupportedDiffeomorph.normalBumpFamily_normal {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (t : ℝ) (z : M × P) :
    (normalBumpFamily Φ β b (t, z)).2 = z.2 :=
  rfl

/-- The bump translation is the identity at time zero. -/
theorem SupportedDiffeomorph.normalBumpFamily_zero {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (z : M × P) :
    normalBumpFamily Φ β b (0, z) = z := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition 0 • b z.2), z.1) = z.1
    rw [Real.smoothTransition.zero, zero_smul, neg_zero, bumpFamily_zero]
  · rfl

/-- The bump translation fixes every fibre over a parameter where the translating field vanishes. -/
theorem SupportedDiffeomorph.normalBumpFamily_fixed_fiber {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) {u : P} (hu : b u = 0)
    (t : ℝ) (x : M) : normalBumpFamily Φ β b (t, (x, u)) = (x, u) := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition t • b u), x) = x
    rw [hu, smul_zero, neg_zero, bumpFamily_zero]
  · rfl

/-- The bump translation is the identity outside the product of the two supports; it is compactly
supported.
-/
theorem SupportedDiffeomorph.normalBumpFamily_fixed_outside {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup P] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E)
    (t : ℝ) (z : M × P) (hz : z ∉ (Φ '' tsupport β) ×ˢ tsupport b) :
    normalBumpFamily Φ β b (t, z) = z := by
  by_cases hu : z.2 ∈ tsupport b
  · have hx : z.1 ∉ Φ '' tsupport β := fun hx => hz ⟨hx, hu⟩
    exact Prod.ext (bumpFamily_fixed_outside Φ β _ hx) rfl
  · have hb : b z.2 = 0 := by
      by_contra hb
      exact hu (subset_tsupport b hb)
    exact normalBumpFamily_fixed_fiber Φ β b hb t z.1

/-- At time one the bump translation reads in the chart as the translation `x ↦ x - β x • b u`. -/
theorem SupportedDiffeomorph.normalBumpFamily_chart {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) {x : E} (hx : x ∈ Φ.source)
    (u : P) : normalBumpFamily Φ β b (1, (Φ x, u)) = (Φ (x - β x • b u), u) := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition 1 • b u), Φ x) = _
    rw [Real.smoothTransition.one, one_smul, bumpFamily_chart Φ β _ hx, smul_neg, ←
      sub_eq_add_neg]
  · rfl

/-- For a compactly supported bump function in a chart there is a radius `ε` such that every
translating field of norm less than `ε` yields a bump translation which is smooth, a
diffeomorphism at each time, and compactly supported.
-/
theorem SupportedDiffeomorph.exists_radius_normalBumpFamily {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ P] [J.Boundaryless]
    [IsManifold J ∞ M] [T2Space M] {β : E → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ b : P → E,
          ContDiff ℝ ∞ b →
            HasCompactSupport b →
              (∀ u, ‖b u‖ < ε) →
                ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) (J.prod 𝓘(ℝ, P)) ∞
                    (normalBumpFamily Φ β b) ∧
                  (∀ t,
                      ∃ D : Diffeomorph (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) (M × P) (M × P) ∞,
                        ∀ z, D z = normalBumpFamily Φ β b (t, z)) ∧
                    IsCompact ((Φ '' tsupport β) ×ˢ tsupport b) := by
  obtain ⟨ε, hε, hdiff, hsmooth, -⟩ := exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro b hb hbcompact hbound
  have hsmall (t : ℝ) (u : P) : ‖-(Real.smoothTransition t • b u)‖ < ε := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact
      (mul_le_of_le_one_left (norm_nonneg (b u)) (Real.smoothTransition.le_one t)).trans_lt
        (hbound u)
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hvec :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) 𝓘(ℝ, E) ∞
      (fun p : ℝ × (M × P) => Real.smoothTransition p.1 • b p.2.2) :=
    (hθ.comp contMDiff_fst).smul (hb.contMDiff.comp (contMDiff_snd.comp contMDiff_snd))
  have hneg :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) 𝓘(ℝ, E) ∞
      (fun p : ℝ × (M × P) => -(Real.smoothTransition p.1 • b p.2.2)) :=
    (show ContDiff ℝ ∞ (fun x : E => -x) from contDiff_neg).contMDiff.comp hvec
  have hparam :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) (𝓘(ℝ, E).prod J) ∞
      (fun p : ℝ × (M × P) => (-(Real.smoothTransition p.1 • b p.2.2), p.2.1)) :=
    hneg.prodMk (contMDiff_fst.comp contMDiff_snd)
  have hfirst :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) J ∞
      (fun p : ℝ × (M × P) => bumpFamily Φ β (-(Real.smoothTransition p.1 • b p.2.2), p.2.1)) := by
    intro p
    exact (hsmooth _ (hsmall p.1 p.2.2)).comp p hparam.contMDiffAt
  refine ⟨hfirst.prodMk (contMDiff_snd.comp contMDiff_snd), ?_, ?_⟩
  · intro t
    have ht :
      ContMDiff (J.prod 𝓘(ℝ, P)) J ∞
        (fun z : M × P => bumpFamily Φ β (-(Real.smoothTransition t • b z.2), z.1)) :=
      hfirst.comp (contMDiff_const.prodMk contMDiff_id)
    have hslices :
      ∀ u : P,
        ∃ D : Diffeomorph J J M M ∞,
          ∀ x, D x = bumpFamily Φ β (-(Real.smoothTransition t • b u), x) :=
      fun u => hdiff _ (hsmall t u)
    have hlocal :
      IsLocalDiffeomorph (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) ∞
        (FiberwiseDiffeomorph.retainParameter fun z : M × P =>
          bumpFamily Φ β (-(Real.smoothTransition t • b z.2), z.1)) := by
      intro p
      exact
        isLocalDiffeomorphAt_boundaryless isOpen_univ (Set.mem_univ p)
          (FiberwiseDiffeomorph.contMDiff_retainParameter ht).contMDiffOn
          (FiberwiseDiffeomorph.isInvertible_mfderiv_retainParameter ht hslices p)
    refine ⟨IsLocalDiffeomorph.diffeomorph' hlocal ?_, fun _ => rfl⟩
    apply FiberwiseDiffeomorph.bijective_retainParameter
    intro s
    obtain ⟨d, hd⟩ := hslices s
    rw [show (fun x => bumpFamily Φ β (-(Real.smoothTransition t • b s), x)) = d from
      funext fun x => (hd x).symm]
    exact d.bijective
  · exact
      (hcompact.isCompact.image_of_continuousOn
            (Φ.contMDiffOn_toFun.continuousOn.mono hsupport)).prod
        hbcompact.isCompact

/-- A smooth map vanishing at the origin agrees near the origin with a compactly supported smooth
map of arbitrarily small norm, supported in a prescribed neighbourhood.
-/
theorem exists_small_supported_germ {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] {L : P → E} {U : Set P}
    (hU : IsOpen U) (hzero : (0 : P) ∈ U) (hL : ContDiffOn ℝ ∞ L U) (hLzero : L 0 = 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ b : P → E,
      ContDiff ℝ ∞ b ∧
        HasCompactSupport b ∧ tsupport b ⊆ U ∧ (∀ u, ‖b u‖ < ε) ∧ b =ᶠ[𝓝 (0 : P)] L ∧ b 0 = 0 := by
  let V : Set P := U ∩ L ⁻¹' Metric.ball (0 : E) ε
  have hV : IsOpen V := hL.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hzeroV : (0 : P) ∈ V := ⟨hzero, by simpa [hLzero] using hε⟩
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, hβrange⟩ :=
    exists_compact_smooth_cutoff isCompact_singleton hV (Set.singleton_subset_iff.mpr hzeroV)
  let b : P → E := fun u => β u • L u
  have hfix (u : P) (hu : u ∉ tsupport β) : β u = 0 := by
    by_contra hne
    exact hu (subset_tsupport β hne)
  have hsmooth : ContDiff ℝ ∞ b := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    by_cases hu : u ∈ U
    · exact hβ.contDiffAt.smul (hL.contDiffAt (hU.mem_nhds hu))
    · have hnot : u ∉ tsupport β := fun h => hu (hβsupport h).1
      have hc : ContDiffAt ℝ ∞ (fun _ : P => (0 : E)) u := contDiffAt_const
      apply hc.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hnot] with v hv
      change β v • L v = 0
      rw [hfix v hv, zero_smul]
  have hsupport : tsupport b ⊆ tsupport β := by
    apply closure_mono
    intro u hu hβu
    apply hu
    change β u • L u = 0
    rw [hβu, zero_smul]
  have hcompact : HasCompactSupport b :=
    HasCompactSupport.intro hβcompact.isCompact
      (fun u hu => by change β u • L u = 0; rw [hfix u hu, zero_smul])
  have hsmall (u : P) : ‖b u‖ < ε := by
    by_cases hu : u ∈ tsupport β
    · have hLu : ‖L u‖ < ε := mem_ball_zero_iff.mp (hβsupport hu).2
      change ‖β u • L u‖ < ε
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβrange u).1]
      exact (mul_le_of_le_one_left (norm_nonneg (L u)) (hβrange u).2).trans_lt hLu
    · change ‖β u • L u‖ < ε
      rw [hfix u hu, zero_smul, norm_zero]
      exact hε
  have hgerm : b =ᶠ[𝓝 (0 : P)] L := by
    filter_upwards [hβone.filter_mono (nhds_le_nhdsSet (Set.mem_singleton (0 : P)))] with u hu
    change β u • L u = L u
    rw [hu, one_smul]
  exact
    ⟨b, hsmooth, hcompact, hsupport.trans (hβsupport.trans Set.inter_subset_left), hsmall, hgerm,
      hgerm.eq_of_nhds.trans hLzero⟩

/-- Every linear shear `(x, y) ↦ (x + L y, y)` is, near the origin, the time-one map of a compactly
supported isotopy which preserves the second coordinate and fixes the subspace `y = 0`.
-/
theorem SupportedDiffeomorph.exists_supported_shear_isotopy {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : F →L[ℝ] E) {U : Set (E × F)} (hU : IsOpen U)
    (hzero : (0 : E × F) ∈ U) :
    ∃ (A : ℝ × (E × F) → E × F) (K : Set (E × F)),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞ A ∧
            (∀ p, A (0, p) = p) ∧
              (∀ t,
                  ∃ D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) ∞,
                    ∀ p, D p = A (t, p)) ∧
                (∀ t p, p ∉ K → A (t, p) = p) ∧
                  (∀ t p, (A (t, p)).2 = p.2) ∧
                    (∀ t x, A (t, (x, (0 : F))) = (x, 0)) ∧
                      (fun p => A (1, p)) =ᶠ[𝓝 (0 : E × F)] (fun p => (p.1 + L p.2, p.2)) := by
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzero)
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, -⟩ :=
    exists_compact_smooth_cutoff (K := {(0 : E)}) isCompact_singleton Metric.isOpen_ball
      (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hρ))
  let Φ := (Diffeomorph.refl 𝓘(ℝ, E) E ∞).toPartialDiffeomorph'
  obtain ⟨ε, hε, hfamily⟩ :=
    exists_radius_normalBumpFamily (P := F) Φ hβ hβcompact
      (show tsupport β ⊆ Φ.source from Set.subset_univ _)
  obtain ⟨b, hb, hbcompact, hbsupport, hbsmall, hbeq, hbzero⟩ :=
    exists_small_supported_germ Metric.isOpen_ball (Metric.mem_ball_self hρ)
      (show ContDiffOn ℝ ∞ (fun y : F => -(L y)) (Metric.ball 0 ρ) from L.contDiff.neg.contDiffOn)
      (show -(L (0 : F)) = 0 by simp) hε
  obtain ⟨hAprod, hdiffprod, hK⟩ := hfamily b hb hbcompact hbsmall
  let A := normalBumpFamily Φ β b
  let K : Set (E × F) := (Φ '' tsupport β) ×ˢ tsupport b
  let V := PartialChart.vectorProduct E F
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞ A :=
    V.symm.contMDiff.comp (hAprod.comp (contMDiff_fst.prodMk (V.contMDiff.comp contMDiff_snd)))
  have hdiff (t : ℝ) :
    ∃ D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) ∞, ∀ p, D p = A (t, p) := by
    obtain ⟨D, hD⟩ := hdiffprod t
    exact ⟨(V.trans D).trans V.symm, hD⟩
  have hKU : K ⊆ U := by
    rintro ⟨x, y⟩ ⟨⟨w, hw, rfl⟩, hy⟩
    apply hρU
    change (w, y) ∈ Metric.ball (0 : E × F) ρ
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    exact ⟨mem_ball_zero_iff.mp (hβsupport hw), mem_ball_zero_iff.mp (hbsupport hy)⟩
  have hplateau : ∀ᶠ x in 𝓝 (0 : E), β x = 1 :=
    hβone.filter_mono (nhds_le_nhdsSet (Set.mem_singleton (0 : E)))
  have hfirst : ∀ᶠ p in 𝓝 (0 : E × F), β p.1 = 1 := (continuous_fst.tendsto (0 : E × F)) hplateau
  have hsecond : ∀ᶠ p in 𝓝 (0 : E × F), b p.2 = -(L p.2) :=
    (continuous_snd.tendsto (0 : E × F)) hbeq
  refine
    ⟨A, K, hK, hKU, hA, normalBumpFamily_zero Φ β b, hdiff, normalBumpFamily_fixed_outside Φ β b,
      normalBumpFamily_normal Φ β b, fun t x => normalBumpFamily_fixed_fiber Φ β b hbzero t x, ?_⟩
  filter_upwards [hfirst, hsecond] with p hp₁ hp₂
  have hh := normalBumpFamily_chart Φ β b (show p.1 ∈ Φ.source from Set.mem_univ _) p.2
  change A (1, p) = (p.1 - β p.1 • b p.2, p.2) at hh
  rwa [hp₁, one_smul, hp₂, sub_neg_eq_add] at hh

/-- The germ at the origin of a map `f` is realised by a diffeomorphism supported in `U`: there is a
diffeomorphism agreeing with `f` near the origin which is isotopic to the identity through
diffeomorphisms supported in a compact subset of `U` and fixing the origin.
-/
def SupportedGerms.Realizes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (f : E → E) : Prop :=
  ∃ (d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E),
    IsCompact K ∧
      K ⊆ U ∧
        Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy d K {0}) ∧
          (d : E → E) =ᶠ[𝓝 (0 : E)] f

/-- Germs realised by supported diffeomorphisms are closed under composition. -/
theorem SupportedGerms.Realizes.comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {f g : E → E} (hf : SupportedGerms.Realizes U f)
    (hg : SupportedGerms.Realizes U g) : SupportedGerms.Realizes U (f ∘ g) := by
  obtain ⟨d, K, hK, hKU, ⟨A⟩, hd⟩ := hf
  obtain ⟨e, L, hL, hLU, ⟨B⟩, he⟩ := hg
  have he0 : e (0 : E) = 0 := B.endpoint_fixed_on 0 rfl
  have het : Filter.Tendsto e (𝓝 (0 : E)) (𝓝 0) := by
    simpa only [he0] using e.continuous.tendsto (0 : E)
  have C : SupportedDiffeomorph.SupportedRelativeIsotopy (e.trans d) (K ∪ L) {0} := by
    refine
      ⟨(fun p => A.family (p.1, B.family p)), A.smooth.comp (contMDiff_fst.prodMk B.smooth), ?_,
        ?_, ?_, ?_, ?_⟩
    · intro x
      rw [B.zero, A.zero]
    · intro x
      change A.family (1, B.family (1, x)) = d (e x)
      rw [B.one, A.one]
    · intro t
      obtain ⟨dₜ, hdₜ⟩ := A.slices t
      obtain ⟨eₜ, heₜ⟩ := B.slices t
      refine ⟨eₜ.trans dₜ, ?_⟩
      intro x
      change dₜ (eₜ x) = A.family (t, B.family (t, x))
      rw [heₜ, hdₜ]
    · intro t x hx
      rw [B.fixedOutside t x (fun h => hx (Or.inr h)),
        A.fixedOutside t x (fun h => hx (Or.inl h))]
    · intro t x hx
      rw [B.fixedOn t x hx, A.fixedOn t x hx]
  refine ⟨e.trans d, K ∪ L, hK.union hL, Set.union_subset hKU hLU, ⟨C⟩, ?_⟩
  filter_upwards [hd.comp_tendsto het, he] with x hx hy
  change d (e x) = f (g x)
  exact hx.trans (congrArg f hy)

/-- Realisability is invariant under conjugation by a linear isomorphism, the neighbourhood being
transported along.
-/
theorem SupportedGerms.Realizes.conj {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : E ≃L[ℝ] F) {U : Set E} {f : E → E}
    (hf : SupportedGerms.Realizes U f) :
    SupportedGerms.Realizes (c '' U) (fun y => c (f (c.symm y))) := by
  obtain ⟨d, K, hK, hKU, ⟨A⟩, hd⟩ := hf
  let D := (c.symm.toDiffeomorph.trans d).trans c.toDiffeomorph
  have B : SupportedDiffeomorph.SupportedRelativeIsotopy D (c '' K) {0} := by
    refine
      ⟨(fun p => c (A.family (p.1, c.symm p.2))),
        c.toDiffeomorph.contMDiff.comp
          (A.smooth.comp
            (contMDiff_fst.prodMk (c.symm.toDiffeomorph.contMDiff.comp contMDiff_snd))),
        ?_, ?_, ?_, ?_, ?_⟩
    · intro y
      rw [A.zero, c.apply_symm_apply]
    · intro y
      change c (A.family (1, c.symm y)) = c (d (c.symm y))
      rw [A.one]
    · intro t
      obtain ⟨e, he⟩ := A.slices t
      refine ⟨(c.symm.toDiffeomorph.trans e).trans c.toDiffeomorph, ?_⟩
      intro y
      change c (e (c.symm y)) = c (A.family (t, c.symm y))
      rw [he]
    · intro t y hy
      have hnot : c.symm y ∉ K := fun h => hy ⟨c.symm y, h, c.apply_symm_apply y⟩
      rw [A.fixedOutside t (c.symm y) hnot, c.apply_symm_apply]
    · intro t y hy
      have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      subst y
      rw [map_zero, A.fixedOn t 0 rfl, map_zero]
  refine ⟨D, c '' K, hK.image c.continuous, Set.image_mono hKU, ⟨B⟩, ?_⟩
  have ht : Filter.Tendsto c.symm (𝓝 (0 : F)) (𝓝 0) := by
    simpa only [map_zero] using c.symm.continuous.tendsto (0 : F)
  filter_upwards [hd.comp_tendsto ht] with y hy
  exact congrArg c hy

/-- The germ of a linear shear is realised by a supported diffeomorphism. -/
theorem SupportedGerms.realizes_shear {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (L : F →L[ℝ] E) {U : Set (E × F)} (hU : IsOpen U)
    (h0 : (0 : E × F) ∈ U) : Realizes U (fun p => (p.1 + L p.2, p.2)) := by
  obtain ⟨A, K, hK, hKU, hA, hA0, hdiff, hfix, -, hcore, hgerm⟩ :=
    SupportedDiffeomorph.exists_supported_shear_isotopy L hU h0
  obtain ⟨d, hd⟩ := hdiff 1
  have H : SupportedDiffeomorph.SupportedRelativeIsotopy d K {0} := by
    refine ⟨A, hA, hA0, fun x => (hd x).symm, hdiff, hfix, ?_⟩
    intro t x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact hcore t 0
  refine ⟨d, K, hK, hKU, ⟨H⟩, ?_⟩
  filter_upwards [hgerm] with x hx
  exact (hd x).trans hx

/-- The elementary diagonal matrix `diag(a, a⁻¹)` in the coordinates `i, j` is a product of six
transvections.
-/
theorem LinearFramePaths.diag2n_decompose {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (a : ℝ) (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij a ha =
      Matrix.SpecialLinearGroup.transvection hij a *
                Matrix.SpecialLinearGroup.transvection hij.symm (-a⁻¹) *
              Matrix.SpecialLinearGroup.transvection hij a *
            Matrix.SpecialLinearGroup.transvection hij (-1) *
          Matrix.SpecialLinearGroup.transvection hij.symm 1 *
        Matrix.SpecialLinearGroup.transvection hij (-1) := by
  apply Subtype.ext
  change
    Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1) =
      (1 + Matrix.single i j a) * (1 + Matrix.single j i (-a⁻¹)) * (1 + Matrix.single i j a) *
            (1 + Matrix.single i j (-1)) *
          (1 + Matrix.single j i 1) *
        (1 + Matrix.single i j (-1))
  simp only [mul_add, add_mul, one_mul, mul_one, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;> by_cases hli : l = i <;>
      by_cases hlj : l = j <;>
    simp_all [Matrix.diagonal_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- Every transvection is joined to the identity by a path in `SL(n, ℝ)`. -/
theorem LinearFramePaths.joined_one_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (a : ℝ) :
    Joined (1 : Matrix.SpecialLinearGroup ι ℝ) (Matrix.SpecialLinearGroup.transvection hij a) := by
  refine
    ⟨{  toFun := fun t => Matrix.SpecialLinearGroup.transvection hij ((t : ℝ) * a)
        continuous_toFun := ?_
        source' := by simp
        target' := by simp }⟩
  apply Continuous.subtype_mk
  change Continuous (fun t : unitInterval => (1 : Matrix ι ι ℝ) + Matrix.single i j ((t : ℝ) * a))
  apply continuous_pi
  intro k
  apply continuous_pi
  intro l
  simp only [Matrix.add_apply, Matrix.single_apply]
  by_cases h : i = k ∧ j = l
  · simp only [h, and_self, ite_true]
    fun_prop
  · simp only [h, ite_false]
    fun_prop

/-- `SL(n, ℝ)` is path connected for `n ≥ 2`: every matrix of determinant one is joined to the
identity.
-/
theorem LinearFramePaths.joined_one_specialLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] (A : Matrix.SpecialLinearGroup ι ℝ) :
    Joined (1 : Matrix.SpecialLinearGroup ι ℝ) A := by
  apply
    Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun A => Joined (1 : Matrix.SpecialLinearGroup ι ℝ) A) A
  · intro i j hij a ha
    rw [diag2n_decompose hij a ha]
    have hmul {A B : Matrix.SpecialLinearGroup ι ℝ} (hA : Joined 1 A) (hB : Joined 1 B) :
      Joined 1 (A * B) := by simpa only [one_mul] using hA.mul hB
    exact
      hmul
        (hmul
          (hmul
            (hmul (hmul (joined_one_transvection hij a) (joined_one_transvection hij.symm (-a⁻¹)))
              (joined_one_transvection hij a))
            (joined_one_transvection hij (-1)))
          (joined_one_transvection hij.symm 1))
        (joined_one_transvection hij (-1))
  · exact fun i j hij a => joined_one_transvection hij a
  · intro A B hA hB
    simpa only [one_mul] using hA.mul hB

/-- The linear isomorphism splitting `ι → ℝ` into the `i`-th coordinate and the remaining ones. -/
def SupportedGerms.coordinateSplit {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    (ι → ℝ) ≃L[ℝ] ℝ × ({ j : ι // j ≠ i } → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (x i, fun j => x j)
      invFun := fun p j => if h : j = i then p.1 else p.2 ⟨j, h⟩
      left_inv := by
        intro x
        funext j
        by_cases h : j = i <;> simp [h]
      right_inv := by
        rintro ⟨a, x⟩
        apply Prod.ext
        · simp
        · funext j
          simp [j.property]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The germ of a transvection is realised by a supported diffeomorphism, a transvection being a
shear in suitable coordinates.
-/
theorem SupportedGerms.realizes_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) (h0 : (0 : ι → ℝ) ∈ U) {i j : ι} (hij : i ≠ j) (a : ℝ) :
    Realizes U
      (Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.transvection hij a)) := by
  let c := coordinateSplit i
  let L : ({ k : ι // k ≠ i } → ℝ) →L[ℝ] ℝ := a • ContinuousLinearMap.proj ⟨j, Ne.symm hij⟩
  have h :=
    (realizes_shear L (c.toHomeomorph.isOpenMap _ hU)
          (show (0 : ℝ × ({ k : ι // k ≠ i } → ℝ)) ∈ c '' U from ⟨0, h0, map_zero c⟩)).conj
      c.symm
  have hset : c.symm '' (c '' U) = U := by
    rw [← Set.image_comp]
    simp only [ContinuousLinearEquiv.symm_comp_self, Set.image_id]
  change Realizes (c.symm '' (c '' U)) (fun y => c.symm ((c y).1 + L (c y).2, (c y).2)) at h
  rw [hset] at h
  convert h using 1
  funext x k
  change
    ((Matrix.SpecialLinearGroup.transvection hij a : Matrix ι ι ℝ) *ᵥ x) k =
      (c.symm ((c x).1 + L (c x).2, (c x).2)) k
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  by_cases hk : k = i
  · subst k
    simp [c, coordinateSplit, L]
  · simp [c, coordinateSplit, L, hk]

/-- The germ of any matrix of determinant one is realised by a supported diffeomorphism. -/
theorem SupportedGerms.realizes_specialLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] {U : Set (ι → ℝ)} (hU : IsOpen U) (h0 : (0 : ι → ℝ) ∈ U)
    (A : Matrix.SpecialLinearGroup ι ℝ) : Realizes U (Matrix.SpecialLinearGroup.toLin' A) := by
  have hmul (A B : Matrix.SpecialLinearGroup ι ℝ)
    (hA : Realizes U (Matrix.SpecialLinearGroup.toLin' A))
    (hB : Realizes U (Matrix.SpecialLinearGroup.toLin' B)) :
    Realizes U (Matrix.SpecialLinearGroup.toLin' (A * B)) := by
    convert hA.comp hB using 1
    funext x
    rw [map_mul]
    rfl
  apply
    Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun A => Realizes U (Matrix.SpecialLinearGroup.toLin' A)) A
  · intro i j hij a ha
    rw [LinearFramePaths.diag2n_decompose hij a ha]
    exact
      hmul _ _
        (hmul _ _
          (hmul _ _
            (hmul _ _
              (hmul _ _ (realizes_transvection hU h0 hij a)
                (realizes_transvection hU h0 hij.symm (-a⁻¹)))
              (realizes_transvection hU h0 hij a))
            (realizes_transvection hU h0 hij (-1)))
          (realizes_transvection hU h0 hij.symm 1))
        (realizes_transvection hU h0 hij (-1))
  · exact fun i j hij a => realizes_transvection hU h0 hij a
  · exact hmul

/-- The germ of a linear automorphism of determinant one of a finite-dimensional space of dimension
at least two (the basis `b` is indexed by a `Finite`, `Nontrivial` type) is realised by a
supported diffeomorphism.
-/
theorem SupportedGerms.realizes_det_one {ι : Type*} [Finite ι] [Nontrivial ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (b : Module.Basis ι ℝ E)
    (C : E ≃L[ℝ] E) (hdet : C.toLinearMap.det = 1) {U : Set E} (hU : IsOpen U)
    (h0 : (0 : E) ∈ U) : Realizes U C := by
  classical
  let := Fintype.ofFinite ι
  let A : Matrix.SpecialLinearGroup ι ℝ :=
    ⟨LinearMap.toMatrix b b C.toLinearMap, (LinearMap.det_toMatrix b C.toLinearMap).trans hdet⟩
  let c : (ι → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv
  have h :=
    (realizes_specialLinear (c.symm.toHomeomorph.isOpenMap _ hU)
          (show (0 : ι → ℝ) ∈ c.symm '' U from ⟨0, h0, map_zero c.symm⟩) A).conj
      c
  change Realizes (c '' (c.symm '' U)) (fun y => c (A.toLin' (c.symm y))) at h
  have hset : c '' (c.symm '' U) = U := by
    rw [← Set.image_comp]
    simp only [ContinuousLinearEquiv.self_comp_symm, Set.image_id]
  rw [hset] at h
  convert h using 1
  funext x
  apply c.symm.injective
  rw [c.symm_apply_apply]
  exact (LinearMap.toMatrix_mulVec_repr b b C.toLinearMap x).symm

/-- A cut-off of a bounded Lipschitz map is Lipschitz, with constant `a + b R` in terms of the
Lipschitz constants and the bound.
-/
theorem SmallPerturbation.lipschitzWith_cutoff_smul {P E : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : P → E} {β : P → ℝ} {S : Set P} {a b R : ℝ≥0}
    (hu : LipschitzOnWith a u S) (hbound : ∀ x ∈ S, ‖u x‖ ≤ R) (hβ : LipschitzWith b β)
    (hβbound : ∀ x, |β x| ≤ 1) (hzero : ∀ x ∉ S, β x = 0) :
    LipschitzWith (a + b * R) (fun x => β x • u x) := by
  have hcross (x y : P) (hx : x ∈ S) (hy : y ∉ S) :
    Dist.dist (β x • u x) (β y • u y) ≤ ((a + b * R : ℝ≥0) : ℝ) * Dist.dist x y := by
    have hβx : |β x| ≤ (b : ℝ) * Dist.dist x y := by
      have h := hβ.dist_le_mul x y
      simpa only [hzero y hy, Real.dist_eq, sub_zero] using h
    rw [hzero y hy, zero_smul, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc
      |β x| * ‖u x‖ ≤ ((b : ℝ) * Dist.dist x y) * R :=
        mul_le_mul hβx (hbound x hx) (norm_nonneg _) (by positivity)
      _ ≤ ((a + b * R : ℝ≥0) : ℝ) * Dist.dist x y := by
        simp only [NNReal.coe_add, NNReal.coe_mul]
        nlinarith [mul_nonneg a.coe_nonneg (dist_nonneg (x := x) (y := y))]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · have hu' : ‖u x - u y‖ ≤ (a : ℝ) * Dist.dist x y := by
        simpa only [dist_eq_norm] using hu.dist_le_mul x hx y hy
      have hβ' : |β x - β y| ≤ (b : ℝ) * Dist.dist x y := by
        simpa only [Real.dist_eq] using hβ.dist_le_mul x y
      have hsplit : β x • u x - β y • u y = β x • (u x - u y) + (β x - β y) • u y := by
        rw [smul_sub, sub_smul]
        abel
      rw [dist_eq_norm, hsplit]
      calc
        ‖β x • (u x - u y) + (β x - β y) • u y‖ ≤ ‖β x • (u x - u y)‖ + ‖(β x - β y) • u y‖ :=
          norm_add_le _ _
        _ = |β x| * ‖u x - u y‖ + |β x - β y| * ‖u y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ((a : ℝ) * Dist.dist x y) + ((b : ℝ) * Dist.dist x y) * R := by
          exact
            add_le_add (mul_le_mul (hβbound x) hu' (norm_nonneg _) (by norm_num))
              (mul_le_mul hβ' (hbound y hy) (norm_nonneg _) (by positivity))
        _ = ((a + b * R : ℝ≥0) : ℝ) * Dist.dist x y := by
          simp only [NNReal.coe_add, NNReal.coe_mul]
          ring
    · exact hcross x y hx hy
  · by_cases hy : y ∈ S
    · simpa only [dist_comm] using hcross y x hy hx
    · rw [hzero x hx, hzero y hy, zero_smul, zero_smul, dist_self]
      positivity

/-- A smooth map whose derivative vanishes at the origin is Lipschitz with arbitrarily small
constant on some closed ball around the origin.
-/
theorem SmallPerturbation.exists_closedBall_small_lipschitz_of_fderiv_zero {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] {u : P → E}
    {U : Set P} (hU : IsOpen U) (hzero : (0 : P) ∈ U) (hu : ContDiffOn ℝ ∞ u U)
    (hdu : fderiv ℝ u 0 = 0) {a : ℝ≥0} (ha : 0 < a) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        Metric.closedBall (0 : P) ρ ⊆ U ∧ LipschitzOnWith a u (Metric.closedBall (0 : P) ρ) := by
  have hd : ContinuousAt (fderiv ℝ u) 0 :=
    (hu.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hzero)
  have hsmall : ∀ᶠ x in 𝓝 (0 : P), ‖fderiv ℝ u x‖ < (a : ℝ) := by
    have h : ∀ᶠ x in 𝓝 (0 : P), fderiv ℝ u x ∈ Metric.ball (fderiv ℝ u 0) (a : ℝ) :=
      hd.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ u 0) (show (0 : ℝ) < a from ha))
    simpa only [hdu, mem_ball_zero_iff] using h
  have hnear : ∀ᶠ x in 𝓝 (0 : P), x ∈ U := hU.mem_nhds hzero
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hnear.and hsmall)
  refine ⟨ρ, hρ, fun x hx => (hball hx).1, ?_⟩
  apply (convex_closedBall (0 : P) ρ).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (hu.contDiffAt (hU.mem_nhds (hball hx).1)).differentiableAt (by simp)
  · intro x hx
    exact (hball hx).2.le

/-- A smooth map vanishing to first order at the origin agrees near the origin with a compactly
supported map that is globally Lipschitz with arbitrarily small constant and is pointwise a
scalar multiple of it between `0` and `1`.
-/
theorem SmallPerturbation.exists_lipschitz_supported_germ {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : P → E} {U : Set P} (hU : IsOpen U) (hzero : (0 : P) ∈ U)
    (hu : ContDiffOn ℝ ∞ u U) (hu₀ : u 0 = 0) (hdu : fderiv ℝ u 0 = 0) {κ : ℝ≥0} (hκ : 0 < κ) :
    ∃ w : P → E,
      ContDiff ℝ ∞ w ∧
        HasCompactSupport w ∧
          tsupport w ⊆ U ∧
            LipschitzWith κ w ∧ w =ᶠ[𝓝 (0 : P)] u ∧ ∀ x, ∃ c ∈ Set.Icc (0 : ℝ) 1, w x = c • u x :=
  by
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, hβrange⟩ :=
    exists_compact_smooth_cutoff (K := {(0 : P)}) (U := Metric.ball (0 : P) 1)
      isCompact_singleton Metric.isOpen_ball (by simp)
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hβcompact hβ (by simp)
  let a : ℝ≥0 := κ / (1 + k)
  have hden : (0 : ℝ≥0) < 1 + k := by positivity
  have ha : 0 < a := div_pos hκ hden
  obtain ⟨ρ, hρ, hρU, hlocal⟩ :=
    exists_closedBall_small_lipschitz_of_fderiv_zero hU hzero hu hdu ha
  let r : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hr : 0 < r := hρ
  let βρ : P → ℝ := fun x => β (ρ⁻¹ • x)
  have hβρ : ContDiff ℝ ∞ βρ := hβ.comp (ρ⁻¹ • ContinuousLinearMap.id ℝ P).contDiff
  have hβρlip : LipschitzWith (k * ‖ρ⁻¹‖₊) βρ := hk.comp (lipschitzWith_smul ρ⁻¹)
  have hβρbound (x : P) : |βρ x| ≤ 1 := by
    change |β (ρ⁻¹ • x)| ≤ 1
    rw [abs_of_nonneg (hβrange _).1]
    exact (hβrange _).2
  have hβρzero (x : P) (hx : x ∉ Metric.closedBall (0 : P) ρ) : βρ x = 0 := by
    by_contra hne
    have hm : ρ⁻¹ • x ∈ Metric.ball (0 : P) 1 := hβsupport (subset_tsupport β hne)
    have hn : ‖ρ⁻¹ • x‖ < 1 := mem_ball_zero_iff.mp hm
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), inv_mul_lt_one₀ hρ] at hn
    exact hx (mem_closedBall_zero_iff.mpr hn.le)
  have hbound : ∀ x ∈ Metric.closedBall (0 : P) ρ, ‖u x‖ ≤ (a * r : ℝ≥0) := by
    intro x hx
    have h0 : (0 : P) ∈ Metric.closedBall (0 : P) ρ := by simpa using hρ.le
    have hn := hlocal.dist_le_mul x hx 0 h0
    rw [hu₀, dist_zero_right, dist_zero_right] at hn
    change ‖u x‖ ≤ (a : ℝ) * ρ
    exact hn.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) a.coe_nonneg)
  let w : P → E := fun x => βρ x • u x
  have hwzero (x : P) (hx : x ∉ Metric.closedBall (0 : P) ρ) : w x = 0 := by
    change βρ x • u x = 0
    rw [hβρzero x hx, zero_smul]
  have hsmooth : ContDiff ℝ ∞ w := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hβρ.contDiffAt.smul (hu.contDiffAt (hU.mem_nhds hx))
    · have hnot : x ∉ Metric.closedBall (0 : P) ρ := fun h => hx (hρU h)
      have hc : ContDiffAt ℝ ∞ (fun _ : P => (0 : E)) x := contDiffAt_const
      apply hc.congr_of_eventuallyEq
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hnot] with y hy
      exact hwzero y hy
  have hcompact : HasCompactSupport w :=
    HasCompactSupport.intro (ProperSpace.isCompact_closedBall (0 : P) ρ) hwzero
  have hsupport : tsupport w ⊆ Metric.closedBall (0 : P) ρ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra hnot
    exact hx (hwzero x hnot)
  have hwlip : LipschitzWith (a + (k * ‖ρ⁻¹‖₊) * (a * r)) w :=
    lipschitzWith_cutoff_smul hlocal hbound hβρlip hβρbound hβρzero
  have hnn : ‖ρ‖₊ = r := Real.nnnorm_of_nonneg hρ.le
  have hcoeff : a + (k * ‖ρ⁻¹‖₊) * (a * r) = κ := by
    rw [nnnorm_inv, hnn]
    calc
      a + (k * r⁻¹) * (a * r) = a + (k * a) * (r⁻¹ * r) := by ring
      _ = a + k * a := by rw [inv_mul_cancel₀ hr.ne', mul_one]
      _ = (1 + k) * a := by ring
      _ = κ := by
        dsimp [a]
        rw [div_eq_mul_inv, ← mul_assoc, mul_comm (1 + k) κ, mul_assoc, mul_inv_cancel₀ hden.ne',
          mul_one]
  rw [hcoeff] at hwlip
  have hβ₀ : ∀ᶠ x in 𝓝 (0 : P), β x = 1 :=
    hβone.filter_mono (nhds_le_nhdsSet (Set.mem_singleton (0 : P)))
  have hscale : Filter.Tendsto (fun x : P => ρ⁻¹ • x) (𝓝 0) (𝓝 0) := by
    have hs : Continuous (fun x : P => ρ⁻¹ • x) := (ρ⁻¹ • ContinuousLinearMap.id ℝ P).continuous
    simpa only [smul_zero] using (hs.continuousAt (x := (0 : P))).tendsto
  have hgerm : w =ᶠ[𝓝 (0 : P)] u := by
    have hscaled : ∀ᶠ x in 𝓝 (0 : P), β (ρ⁻¹ • x) = 1 := hscale hβ₀
    filter_upwards [hscaled] with x hx
    change β (ρ⁻¹ • x) • u x = u x
    rw [hx, one_smul]
  refine ⟨w, hsmooth, hcompact, hsupport.trans hρU, hwlip, hgerm, ?_⟩
  intro x
  exact ⟨βρ x, hβrange _, rfl⟩

/-- A smooth map fixing the origin whose derivative there is the identity agrees near the origin
with the time-one map of a compactly supported isotopy of diffeomorphisms.
-/
theorem SmallPerturbation.exists_supported_tangent_identity_isotopy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U) (hf₀ : f 0 = 0)
    (hdf : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E) :
    ∃ (A : ℝ × E → E) (K : Set E),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
            (∀ x, A (0, x) = x) ∧
              (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
                (∀ t x, x ∉ K → A (t, x) = x) ∧
                  (∀ t x, ∃ c ∈ Set.Icc (0 : ℝ) 1, A (t, x) = x + c • (f x - x)) ∧
                    (fun x => A (1, x)) =ᶠ[𝓝 (0 : E)] f := by
  let u : E → E := fun x => f x - x
  have hu : ContDiffOn ℝ ∞ u U := hf.sub contDiffOn_id
  have hu₀ : u 0 = 0 := by simp [u, hf₀]
  have hdu : fderiv ℝ u 0 = 0 := by
    have hdiff : DifferentiableAt ℝ f 0 :=
      (hf.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)
    change fderiv ℝ (f - id) 0 = 0
    rw [fderiv_sub hdiff differentiableAt_id, hdf, fderiv_id, sub_self]
  obtain ⟨w, hw, hwcompact, hwsupport, hwlip, hweq, hwscalar⟩ :=
    exists_lipschitz_supported_germ hU hzero hu hu₀ hdu (show (0 : ℝ≥0) < 1 / 2 by norm_num)
  let A : ℝ × E → E := fun p => p.2 + Real.smoothTransition p.1 • w p.2
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A :=
    contMDiff_snd.add ((hθ.comp contMDiff_fst).smul (hw.contMDiff.comp contMDiff_snd))
  refine ⟨A, tsupport w, hwcompact.isCompact, hwsupport, hA, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [A, Real.smoothTransition.zero]
  · intro t
    have hs : ContDiff ℝ ∞ (fun x => Real.smoothTransition t • w x) := contDiff_const.smul hw
    have hlip :
      LipschitzWith (‖Real.smoothTransition t‖₊ * (1 / 2))
        (fun x => Real.smoothTransition t • w x) :=
      (lipschitzWith_smul (Real.smoothTransition t)).comp hwlip
    have hθnorm : ‖Real.smoothTransition t‖₊ ≤ 1 := by
      change ‖Real.smoothTransition t‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
      exact Real.smoothTransition.le_one t
    have hsmall : ‖Real.smoothTransition t‖₊ * (1 / 2 : ℝ≥0) < 1 := by
      calc
        _ ≤ 1 * (1 / 2 : ℝ≥0) := mul_le_mul_of_nonneg_right hθnorm (by positivity)
        _ < 1 := by norm_num
    have hloc :
      IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun x => x + Real.smoothTransition t • w x) := by
      intro x
      apply
        isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ x)
          ((contDiff_id.add hs).contMDiff.contMDiffOn)
      rw [mfderiv_eq_fderiv]
      exact isInvertible_fderiv_id_add hs hlip hsmall x
    exact
      ⟨IsLocalDiffeomorph.diffeomorph' hloc (bijective_id_add hlip hsmall), fun _ => rfl⟩
  · intro t x hx
    have hz : w x = 0 := by
      by_contra hne
      exact hx (subset_tsupport w hne)
    simp only [A, hz, smul_zero, add_zero]
  · intro t x
    obtain ⟨c, hc, hwc⟩ := hwscalar x
    refine
      ⟨Real.smoothTransition t * c,
        ⟨mul_nonneg (Real.smoothTransition.nonneg t) hc.1,
          (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one t) hc.1).trans
            (by simpa only [one_mul] using hc.2)⟩,
        ?_⟩
    change x + Real.smoothTransition t • w x = x + _
    rw [hwc, smul_smul]
  · filter_upwards [hweq] with x hx
    change x + Real.smoothTransition 1 • w x = f x
    rw [Real.smoothTransition.one, one_smul, hx]
    change x + (f x - x) = f x
    abel

/-- The relative form of the previous statement: the isotopy can be taken to preserve a linear
functional `Q` that the map preserves and to fix a set `S` that the map fixes.
-/
theorem SmallPerturbation.exists_relative_tangent_identity_isotopy {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → E} {U S : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf₀ : f 0 = 0) (hdf : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E)
    (Q : E →L[ℝ] F) (hQ : ∀ x ∈ U, Q (f x) = Q x) (hS : ∀ x ∈ U ∩ S, f x = x) :
    ∃ (A : ℝ × E → E) (K : Set E),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
            (∀ x, A (0, x) = x) ∧
              (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
                (∀ t x, x ∉ K → A (t, x) = x) ∧
                  (∀ t x, Q (A (t, x)) = Q x) ∧
                    (∀ t x, x ∈ S → A (t, x) = x) ∧ (fun x => A (1, x)) =ᶠ[𝓝 (0 : E)] f := by
  obtain ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, hscalar, hgerm⟩ :=
    exists_supported_tangent_identity_isotopy hU hzero hf hf₀ hdf
  refine ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, ?_, ?_, hgerm⟩
  · intro t x
    by_cases hx : x ∈ U
    · obtain ⟨c, _, heq⟩ := hscalar t x
      rw [heq, map_add, map_smul, map_sub, hQ x hx, sub_self, smul_zero, add_zero]
    · rw [hfix t x (fun h => hx (hKU h))]
  · intro t x hxS
    by_cases hx : x ∈ U
    · obtain ⟨c, _, heq⟩ := hscalar t x
      rw [heq, hS x ⟨hx, hxS⟩, sub_self, smul_zero, add_zero]
    · exact hfix t x (fun h => hx (hKU h))

/-- A map preserving a linear projection `Q` near the origin has derivative preserving `Q`. -/
theorem SmallPerturbation.fderiv_preserves_projection {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : DifferentiableAt ℝ f 0) (Q : E →L[ℝ] F)
    (hQ : ∀ x ∈ U, Q (f x) = Q x) : Q.comp (fderiv ℝ f 0) = Q := by
  have heq : Q ∘ f =ᶠ[𝓝 (0 : E)] Q := by
    filter_upwards [hU.mem_nhds hzero] with x hx
    exact hQ x hx
  have hc : fderiv ℝ (Q ∘ f) 0 = Q.comp (fderiv ℝ f 0) :=
    (Q.hasFDerivAt.comp 0 hf.hasFDerivAt).fderiv
  exact hc.symm.trans (heq.fderiv_eq.trans Q.fderiv)

/-- A map fixing a subspace near the origin has derivative fixing that subspace. -/
theorem SmallPerturbation.fderiv_fixes_subspace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → E} {U : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : DifferentiableAt ℝ f 0) (S : Submodule ℝ E) (hS : ∀ x ∈ U ∩ (S : Set E), f x = x) :
    ∀ x ∈ S, fderiv ℝ f 0 x = x := by
  have heq : f ∘ (S.subtypeL : S → E) =ᶠ[𝓝 (0 : S)] (S.subtypeL : S → E) := by
    have hn : ∀ᶠ x : S in 𝓝 (0 : S), (x : E) ∈ U :=
      S.subtypeL.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hzero)
    filter_upwards [hn] with x hx
    exact hS x ⟨hx, x.property⟩
  have hc : fderiv ℝ (f ∘ (S.subtypeL : S → E)) (0 : S) = (fderiv ℝ f 0).comp S.subtypeL :=
    (hf.hasFDerivAt.comp (0 : S) S.subtypeL.hasFDerivAt).fderiv
  have hlinear : (fderiv ℝ f 0).comp S.subtypeL = S.subtypeL :=
    hc.symm.trans (heq.fderiv_eq.trans S.subtypeL.fderiv)
  intro x hx
  exact congrArg (fun A : S →L[ℝ] E => A ⟨x, hx⟩) hlinear

/-- Germ linearisation: a smooth map fixing the origin with bijective derivative there factors near
the origin as its derivative composed with the time-one map of a compactly supported isotopy;
the linear part and the isotopy inherit the map's preservation of a functional `Q` and of a
subspace `S`.
-/
theorem SmallPerturbation.exists_relative_germ_linearization_isotopy {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → E} {U : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf₀ : f 0 = 0) (hdf : Function.Bijective (fderiv ℝ f 0))
    (Q : E →L[ℝ] F) (hQ : ∀ x ∈ U, Q (f x) = Q x) (S : Submodule ℝ E)
    (hS : ∀ x ∈ U ∩ (S : Set E), f x = x) :
    ∃ (C : E ≃L[ℝ] E) (A : ℝ × E → E) (K : Set E),
      C.toContinuousLinearMap = fderiv ℝ f 0 ∧
        (∀ x, Q (C x) = Q x) ∧
          (∀ x ∈ S, C x = x) ∧
            IsCompact K ∧
              K ⊆ U ∧
                ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                  (∀ x, A (0, x) = x) ∧
                    (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
                      (∀ t x, x ∉ K → A (t, x) = x) ∧
                        (∀ t x, Q (A (t, x)) = Q x) ∧
                          (∀ t x, x ∈ S → A (t, x) = x) ∧
                            f =ᶠ[𝓝 (0 : E)] (fun x => C (A (1, x))) := by
  have hfd : DifferentiableAt ℝ f 0 :=
    (hf.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)
  let C := (LinearEquiv.ofBijective (fderiv ℝ f 0).toLinearMap hdf).toContinuousLinearEquiv
  have hC : C.toContinuousLinearMap = fderiv ℝ f 0 := rfl
  have hQC : ∀ x, Q (C x) = Q x := by
    intro x
    exact congrArg (fun A : E →L[ℝ] F => A x) (fderiv_preserves_projection hU hzero hfd Q hQ)
  have hCS : ∀ x ∈ S, C x = x := fderiv_fixes_subspace hU hzero hfd S hS
  have hQCinv (y : E) : Q (C.symm y) = Q y := by
    have h := (hQC (C.symm y)).symm
    simpa only [C.apply_symm_apply] using h
  have hCSinv (x : E) (hx : x ∈ S) : C.symm x = x := by
    have h := C.symm_apply_apply x
    rwa [hCS x hx] at h
  let G : E → E := C.symm ∘ f
  have hG : ContDiffOn ℝ ∞ G U := C.symm.contDiff.comp_contDiffOn hf
  have hG₀ : G 0 = 0 := by simp [G, hf₀]
  have hGder : fderiv ℝ G 0 = C.symm.toContinuousLinearMap.comp (fderiv ℝ f 0) :=
    (C.symm.toContinuousLinearMap.hasFDerivAt.comp 0 hfd.hasFDerivAt).fderiv
  have hdG : fderiv ℝ G 0 = ContinuousLinearMap.id ℝ E := by
    rw [hGder, ← hC]
    ext x
    exact C.symm_apply_apply x
  have hQG : ∀ x ∈ U, Q (G x) = Q x := by
    intro x hx
    change Q (C.symm (f x)) = Q x
    rw [hQCinv, hQ x hx]
  have hSG : ∀ x ∈ U ∩ (S : Set E), G x = x := by
    intro x hx
    change C.symm (f x) = x
    rw [hS x hx, hCSinv x hx.2]
  obtain ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, hprojection, hfixed, hgerm⟩ :=
    exists_relative_tangent_identity_isotopy hU hzero hG hG₀ hdG Q hQG hSG
  refine ⟨C, A, K, hC, hQC, hCS, hK, hKU, hA, hA₀, hdiff, hfix, hprojection, hfixed, ?_⟩
  filter_upwards [hgerm] with x hx
  change A (1, x) = C.symm (f x) at hx
  rw [hx, C.apply_symm_apply]

/-- A germ at the origin of a smooth map fixing the origin whose derivative is bijective of
determinant one is realised by a diffeomorphism supported in any prescribed neighbourhood. The
space is assumed of dimension at least two (the basis `b` is indexed by a `Finite`, `Nontrivial`
type).
-/
theorem SupportedGerms.realizes_local_germ {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite ι] [Nontrivial ι] (b : Module.Basis ι ℝ E)
    {f : E → E} {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf0 : f 0 = 0) (hbij : Function.Bijective (fderiv ℝ f 0))
    (hdet : (fderiv ℝ f 0).toLinearMap.det = 1) : Realizes U f := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨C, A, K, hC, -, -, hK, hKU, hA, hA0, hdiff, hfix, -, hfixed, hgerm⟩ :=
    SmallPerturbation.exists_relative_germ_linearization_isotopy hU h0 hf hf0 hbij
      (0 : E →L[ℝ] ℝ) (fun _ _ => rfl) (⊥ : Submodule ℝ E)
      (by
        intro x hx
        have hx0 : x = 0 := hx.2
        subst x
        exact hf0)
  have hCdet : C.toLinearMap.det = 1 := by
    change C.toContinuousLinearMap.toLinearMap.det = 1
    rw [hC]
    exact hdet
  obtain ⟨d, hd⟩ := hdiff 1
  have H : SupportedDiffeomorph.SupportedRelativeIsotopy d K {0} := by
    refine ⟨A, hA, hA0, fun x => (hd x).symm, hdiff, hfix, ?_⟩
    intro t x hx
    exact hfixed t x (Set.mem_singleton_iff.mp hx)
  have hdreal : Realizes U (fun x => A (1, x)) :=
    ⟨d, K, hK, hKU, ⟨H⟩, Filter.Eventually.of_forall hd⟩
  obtain ⟨D, L, hL, hLU, hH, hDgerm⟩ := (realizes_det_one b C hCdet hU h0).comp hdreal
  exact ⟨D, L, hL, hLU, hH, hDgerm.trans hgerm.symm⟩

/-- The diagonal matrix with entry `a` in position `i` and `1` elsewhere. -/
def LinearFramePaths.scalarDiagonal {ι : Type*} [DecidableEq ι] (i : ι) (a : ℝ) :
    Matrix ι ι ℝ :=
  Matrix.diagonal (fun k => if k = i then a else 1)

/-- The determinant of the elementary scalar diagonal matrix is its entry. -/
theorem LinearFramePaths.det_scalarDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (a : ℝ) : Matrix.det (scalarDiagonal i a) = a := by simp [scalarDiagonal, Matrix.det_diagonal]

/-- Elementary scalar diagonal matrices multiply by multiplying their entries. -/
theorem LinearFramePaths.scalarDiagonal_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (a b : ℝ) : scalarDiagonal i a * scalarDiagonal i b = scalarDiagonal i (a * b) := by
  rw [scalarDiagonal, scalarDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i <;> simp [h]

/-- The elementary scalar diagonal matrix with entry one is the identity. -/
theorem LinearFramePaths.scalarDiagonal_one {ι : Type*} [DecidableEq ι] (i : ι) :
    scalarDiagonal i 1 = 1 := by simp [scalarDiagonal]

/-- The elementary scalar diagonal matrix depends continuously on its entry. -/
theorem LinearFramePaths.continuous_scalarDiagonal {ι : Type*} [DecidableEq ι] (i : ι) :
    Continuous (scalarDiagonal i) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro l
  simp only [scalarDiagonal, Matrix.diagonal_apply]
  by_cases hkl : k = l
  · simp only [hkl, ite_true]
    by_cases hli : l = i
    · simp only [hli, ite_true]
      fun_prop
    · simp only [hli, ite_false]
      fun_prop
  · simp only [hkl, ite_false]
    fun_prop

/-- The open set of matrices whose determinant has a prescribed sign, one of the two components of
`GL(n, ℝ)` when `σ = ±1`.
-/
def LinearFramePaths.determinantComponent {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ℝ) :
    TopologicalSpace.Opens (Matrix ι ι ℝ) :=
  ⟨{A | 0 < σ * Matrix.det A},
    isOpen_lt continuous_const (continuous_const.mul continuous_id.matrix_det)⟩

/-- The elementary scalar diagonal matrix with the same determinant as the given matrix, a normal
form in its determinant component.
-/
def LinearFramePaths.diagonalPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) {σ : ℝ}
    (A : determinantComponent (ι := ι) σ) : determinantComponent (ι := ι) σ :=
  ⟨scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)),
    by
    change 0 < σ * Matrix.det (scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)))
    rw [det_scalarDiagonal]
    exact A.property⟩

/-- For `n ≥ 2` a matrix is joined inside its determinant component to the elementary scalar
diagonal matrix of the same determinant.
-/
theorem LinearFramePaths.joined_diagonal_to_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] (i : ι) {σ : ℝ} (A : determinantComponent (ι := ι) σ) :
    Joined (diagonalPoint i A) A := by
  have ha : Matrix.det (A : Matrix ι ι ℝ) ≠ 0 := by
    intro hz
    have hh : 0 < σ * Matrix.det (A : Matrix ι ι ℝ) := A.property
    rw [hz, MulZeroClass.mul_zero] at hh
    exact lt_irrefl _ hh
  let N : Matrix.SpecialLinearGroup ι ℝ :=
    ⟨scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ))⁻¹ * (A : Matrix ι ι ℝ), by
      rw [Matrix.det_mul, det_scalarDiagonal, inv_mul_cancel₀ ha]⟩
  let ψ : Matrix.SpecialLinearGroup ι ℝ → determinantComponent (ι := ι) σ := fun L =>
    ⟨scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) * (L : Matrix ι ι ℝ),
      by
      change 0 < σ * Matrix.det (scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) * L.val)
      rw [Matrix.det_mul, det_scalarDiagonal, L.property, mul_one]
      exact A.property⟩
  have hψ : Continuous ψ := (continuous_const.mul continuous_subtype_val).subtype_mk _
  have h0 : ψ 1 = diagonalPoint i A := by
    apply Subtype.ext
    change scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) * 1 = _
    rw [mul_one]
    rfl
  have h1 : ψ N = A := by
    apply Subtype.ext
    change
      scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) *
          (scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ))⁻¹ * (A : Matrix ι ι ℝ)) =
        _
    rw [← mul_assoc, scalarDiagonal_mul, mul_inv_cancel₀ ha, scalarDiagonal_one, one_mul]
  have h := (joined_one_specialLinear N).map hψ
  rwa [h0, h1] at h

/-- Two elementary scalar diagonal matrices in the same determinant component are joined by a path
in it.
-/
theorem LinearFramePaths.joined_diagonal_points {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) {σ : ℝ} (A B : determinantComponent (ι := ι) σ) :
    Joined (diagonalPoint i A) (diagonalPoint i B) := by
  let g := fun t : unitInterval =>
    (1 - (t : ℝ)) * Matrix.det (A : Matrix ι ι ℝ) + (t : ℝ) * Matrix.det (B : Matrix ι ι ℝ)
  have hg : Continuous g := by fun_prop
  have hpos (t : unitInterval) : 0 < σ * g t := by
    have hh :=
      (convex_Ioi (0 : ℝ)) A.property B.property (sub_nonneg.mpr t.property.2) t.property.1
        (show 1 - (t : ℝ) + (t : ℝ) = 1 by ring)
    change
      0 <
        (1 - (t : ℝ)) * (σ * Matrix.det (A : Matrix ι ι ℝ)) +
          (t : ℝ) * (σ * Matrix.det (B : Matrix ι ι ℝ)) at hh
    convert hh using 1
    dsimp only [g]
    ring
  refine
    ⟨{  toFun := fun t =>
          ⟨scalarDiagonal i (g t),
            by
            change 0 < σ * Matrix.det (scalarDiagonal i (g t))
            rw [det_scalarDiagonal]
            exact hpos t⟩
        continuous_toFun :=
          ((continuous_scalarDiagonal i).comp hg).subtype_mk
            (fun t => by
              change 0 < σ * Matrix.det (scalarDiagonal i (g t))
              rw [det_scalarDiagonal]
              exact hpos t)
        source' := ?_
        target' := ?_ }⟩
  · apply Subtype.ext
    simp [g, diagonalPoint]
  · apply Subtype.ext
    simp [g, diagonalPoint]

/-- For `n ≥ 2` the set of matrices of a given determinant sign is path connected; so `GL(n, ℝ)` has
exactly the two components cut out by the sign of the determinant.
-/
theorem LinearFramePaths.joined_determinantComponent {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nontrivial ι] {σ : ℝ} (A B : determinantComponent (ι := ι) σ) : Joined A B :=
  by
  let i := Classical.choice (inferInstance : Nonempty ι)
  exact
    (joined_diagonal_to_matrix i A).symm.trans
      ((joined_diagonal_points i A B).trans (joined_diagonal_to_matrix i B))

/-- Every nonzero real number is the determinant of a linear automorphism of a finite-dimensional
space.
-/
theorem SupportedGerms.exists_linearEquiv_with_det {B ι : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [Finite ι] (b : Module.Basis ι ℝ B) (i : ι) {r : ℝ}
    (hr : r ≠ 0) : ∃ R : B ≃L[ℝ] B, R.toLinearMap.det = r := by
  classical
  let := Fintype.ofFinite ι
  let L : B →ₗ[ℝ] B := Matrix.toLin b b (LinearFramePaths.scalarDiagonal i r)
  have hdet : L.det = r := by
    rw [← LinearMap.det_toMatrix b L]
    change
      Matrix.det
          (LinearMap.toMatrix b b
            (Matrix.toLin b b (LinearFramePaths.scalarDiagonal i r))) =
        r
    rw [LinearMap.toMatrix_toLin]
    exact LinearFramePaths.det_scalarDiagonal i r
  have hker : L.ker = ⊥ := by
    by_contra hk
    exact hr (hdet.symm.trans (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk))
  have hi : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  have hbij : Function.Bijective L :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩
  exact ⟨(LinearEquiv.ofBijective L hbij).toContinuousLinearEquiv, hdet⟩

/-- An automorphism of `A × B` can be corrected to determinant one by an automorphism of the second
factor alone.
-/
theorem SupportedGerms.exists_normal_det_correction {A B ι : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [Finite ι] (b : Module.Basis ι ℝ B) (i : ι)
    (C : (A × B) ≃L[ℝ] (A × B)) :
    ∃ R : B ≃L[ℝ] B,
      (((ContinuousLinearEquiv.refl ℝ A).prodCongr R).toContinuousLinearMap.comp
            C.toContinuousLinearMap).toLinearMap.det =
        1 := by
  classical
  let := Fintype.ofFinite ι
  have hne : C.toLinearMap.det ≠ 0 := C.toLinearEquiv.isUnit_det'.ne_zero
  obtain ⟨R, hR⟩ := exists_linearEquiv_with_det b i (inv_ne_zero hne)
  refine ⟨R, ?_⟩
  change LinearMap.det ((LinearMap.id.prodMap R.toLinearMap).comp C.toLinearMap) = 1
  rw [LinearMap.det_comp, LinearMap.det_prodMap, LinearMap.det_id, one_mul, hR,
    inv_mul_cancel₀ hne]

/-- A chart of `A × B` fixing the origin can be straightened along the first factor: there is a
diffeomorphism supported near the origin and isotopic to the identity carrying the germ of
`x ↦ Φ (x, 0)` to the germ of the inclusion `x ↦ (x, 0)`.
-/
theorem SupportedGerms.exists_supported_disk_germ_alignment {A B ι κ : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [Finite ι] [Finite κ] [Nontrivial κ]
    (b : Module.Basis ι ℝ B) (i : ι) (basis : Module.Basis κ ℝ (A × B))
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ Φ.source) (hΦ0 : Φ 0 = 0) {U : Set (A × B)} (hU : IsOpen U)
    (h0U : (0 : A × B) ∈ U) :
    ∃ (d : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞) (K : Set (A × B)),
      IsCompact K ∧
        K ⊆ U ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy d K {0}) ∧
            (fun x : A => d (Φ (x, 0))) =ᶠ[𝓝 (0 : A)] (fun x => (x, (0 : B))) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  have ht0 : (0 : A × B) ∈ Φ.target := hΦ0 ▸ Φ.map_source' h0
  have hi0 : Φ.symm 0 = 0 := by
    have hh := Φ.left_inv' h0
    rwa [hΦ0] at hh
  have hi : ContDiffOn ℝ ∞ (Φ.symm : (A × B) → A × B) Φ.target := Φ.contMDiffOn_invFun.contDiffOn
  have hib : Function.Bijective (fderiv ℝ Φ.symm 0) := by
    have hh := PartialChart.bijective_mfderiv Φ.symm ht0
    change
      Function.Bijective (mfderiv 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) Φ.symm 0 : (A × B) →L[ℝ] (A × B)) at hh
    rwa [mfderiv_eq_fderiv] at hh
  let C := (LinearEquiv.ofBijective (fderiv ℝ Φ.symm 0).toLinearMap hib).toContinuousLinearEquiv
  obtain ⟨R, hR⟩ := exists_normal_det_correction b i C
  let T := (ContinuousLinearEquiv.refl ℝ A).prodCongr R
  let f : (A × B) → A × B := T ∘ Φ.symm
  have hf : ContDiffOn ℝ ∞ f (U ∩ Φ.target) :=
    T.contDiff.comp_contDiffOn (hi.mono Set.inter_subset_right)
  have hf0 : f 0 = 0 := by simp only [f, Function.comp_apply, hi0, map_zero]
  have hfi :=
    ((hi.contDiffAt (Φ.open_target.mem_nhds ht0)).differentiableAt (by simp)).hasFDerivAt
  have hdf : fderiv ℝ f 0 = T.toContinuousLinearMap.comp C.toContinuousLinearMap :=
    (T.toContinuousLinearMap.hasFDerivAt.comp 0 hfi).fderiv
  have hfb : Function.Bijective (fderiv ℝ f 0) := by
    rw [hdf]
    exact T.bijective.comp C.bijective
  have hdet : (fderiv ℝ f 0).toLinearMap.det = 1 := by
    rw [hdf]
    exact hR
  obtain ⟨d, K, hK, hKU, hH, hgerm⟩ :=
    realizes_local_germ basis (hU.inter Φ.open_target) ⟨h0U, ht0⟩ hf hf0 hfb hdet
  refine ⟨d, K, hK, hKU.trans Set.inter_subset_left, hH, ?_⟩
  have hΦt : Filter.Tendsto Φ (𝓝 (0 : A × B)) (𝓝 0) := by
    have hh := Φ.toOpenPartialHomeomorph.continuousAt h0
    change Filter.Tendsto Φ (𝓝 (0 : A × B)) (𝓝 (Φ 0)) at hh
    rwa [hΦ0] at hh
  have hcore : Filter.Tendsto (fun x : A => (x, (0 : B))) (𝓝 0) (𝓝 (0 : A × B)) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  filter_upwards [(hgerm.comp_tendsto hΦt).comp_tendsto hcore,
    hcore (Φ.open_source.mem_nhds h0)] with x hx hxsource
  change d (Φ (x, 0)) = f (Φ (x, 0)) at hx
  rw [hx]
  change T (Φ.symm (Φ (x, 0))) = (x, 0)
  have hinv : Φ.symm (Φ (x, 0)) = (x, 0) := Φ.left_inv' hxsource
  rw [hinv]
  simp [T]

/-- Two charts of a manifold with the same centre agree along the first factor after a supported
diffeomorphism: there is a diffeomorphism of `M`, isotopic to the identity through
diffeomorphisms supported in a compact subset of the target of `Ψ`, carrying the germ of
`x ↦ Φ (x, 0)` to the germ of `x ↦ Ψ (x, 0)`.
-/
theorem SupportedGerms.exists_native_disk_germ_alignment {A B E H M ι κ : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [Finite ι] [Finite κ] [Nontrivial κ] (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B)) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, A × B) J (A × B) M ∞)
    (hΦ0 : (0 : A × B) ∈ Φ.source) (hΨ0 : (0 : A × B) ∈ Ψ.source) (hcenter : Φ 0 = Ψ 0) :
    ∃ (D : Diffeomorph J J M M ∞) (K : Set M),
      IsCompact K ∧
        K ⊆ Ψ.target ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy D K {Ψ 0}) ∧
            (fun x : A => D (Φ (x, 0))) =ᶠ[𝓝 (0 : A)] (fun x => Ψ (x, (0 : B))) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  let Θ := Φ.trans Ψ.symm
  have hΘ0 : (0 : A × B) ∈ Θ.source := by
    refine ⟨hΦ0, ?_⟩
    change Φ 0 ∈ Ψ.target
    rw [hcenter]
    exact Ψ.map_source' hΨ0
  have hΘzero : Θ 0 = 0 := by
    change Ψ.symm (Φ 0) = 0
    rw [hcenter]
    exact Ψ.left_inv' hΨ0
  obtain ⟨d, L, hL, hLsource, ⟨Hiso⟩, hgerm⟩ :=
    exists_supported_disk_germ_alignment b i basis Θ hΘ0 hΘzero Ψ.open_source hΨ0
  let D := SupportedDiffeomorph.extension Ψ d hL hLsource Hiso.endpoint_fixed_outside
  have hfixed : ∀ x ∈ Ψ.source, Ψ x ∈ ({Ψ 0} : Set M) → x ∈ ({0} : Set (A × B)) := by
    intro x hx hh
    exact
      Set.mem_singleton_iff.mpr
        (Ψ.toOpenPartialHomeomorph.injOn hx hΨ0 (Set.mem_singleton_iff.mp hh))
  have HD := Hiso.extension Ψ hL hLsource hfixed
  refine
    ⟨D, Ψ '' L, hL.image_of_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono hLsource), ?_,
      ⟨HD⟩, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact Ψ.map_source' (hLsource hx)
  · have hcore : Filter.Tendsto (fun x : A => (x, (0 : B))) (𝓝 0) (𝓝 (0 : A × B)) :=
      (continuous_id.prodMk continuous_const).tendsto 0
    filter_upwards [hgerm, hcore (Θ.open_source.mem_nhds hΘ0)] with x hx hxsource
    have ht : Φ (x, 0) ∈ Ψ.target := hxsource.2
    have hback : Ψ (Θ (x, 0)) = Φ (x, 0) := Ψ.right_inv' ht
    calc
      D (Φ (x, 0)) = D (Ψ (Θ (x, 0))) := congrArg D hback.symm
      _ = Ψ (d (Θ (x, 0))) :=
        (SupportedDiffeomorph.extension_chart Ψ d hL hLsource Hiso.endpoint_fixed_outside
          (Ψ.map_target' ht))
      _ = Ψ (x, 0) := congrArg Ψ hx

/-- The radial map `x ↦ φ(‖x‖²) • x` determined by a real function `φ`. -/
def SmoothRadial.radialMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (φ : ℝ → ℝ)
    (x : N) : N :=
  φ (‖x‖ ^ 2) • x

/-- For a positive `φ` the radial map multiplies norms by `φ(‖x‖²)`. -/
theorem SmoothRadial.norm_radialMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (x : N) : ‖radialMap φ x‖ = φ (‖x‖ ^ 2) * ‖x‖ := by
  rw [radialMap, norm_smul, Real.norm_eq_abs, abs_of_pos (hpos _)]

/-- For a positive monotone `φ` the radius function `r ↦ φ(r²) r` is strictly increasing on
`[0, ∞)`.
-/
theorem SmoothRadial.radius_strictMono {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) : StrictMonoOn (fun r => φ (r ^ 2) * r) (Set.Ici 0) := by
  intro r hr s hs hrs
  have hsq : r ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hr hs).mpr hrs.le
  exact (mul_lt_mul_of_pos_left hrs (hpos _)).trans_le (mul_le_mul_of_nonneg_right (hmono hsq) hs)

/-- For a positive monotone `φ` the radial map is injective. -/
theorem SmoothRadial.radialMap_injective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) :
    Function.Injective (radialMap (N := N) φ) := by
  intro x y hxy
  have hn : ‖x‖ = ‖y‖ := by
    apply (radius_strictMono hpos hmono).injOn (norm_nonneg x) (norm_nonneg y)
    simpa only [norm_radialMap hpos] using congrArg Norm.norm hxy
  change φ (‖x‖ ^ 2) • x = φ (‖y‖ ^ 2) • y at hxy
  rw [hn] at hxy
  exact smul_right_injective N (hpos _).ne' hxy

/-- A continuous `φ` equal to `1` beyond radius `R` gives a surjective radial map. -/
theorem SmoothRadial.radialMap_surjective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hR : 0 < R)
    (hout : ∀ s, R ^ 2 ≤ s → φ s = 1) : Function.Surjective (radialMap (N := N) φ) := by
  intro y
  by_cases hy : R ≤ ‖y‖
  · refine ⟨y, ?_⟩
    rw [radialMap, hout _ ((sq_le_sq₀ hR.le (norm_nonneg y)).mpr hy), one_smul]
  by_cases hyzero : y = 0
  · subst y
    exact ⟨0, by simp only [radialMap, smul_zero]⟩
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hyzero
  have htarget : ‖y‖ ∈ Set.Icc (φ (0 ^ 2) * 0) (φ (R ^ 2) * R) := by
    simpa only [MulZeroClass.mul_zero, hout _ le_rfl, one_mul, Set.mem_Icc] using
      And.intro hypos.le (le_of_not_ge hy)
  have hcont : Continuous (fun r : ℝ => φ (r ^ 2) * r) :=
    (hc.comp (continuous_id.pow 2)).mul continuous_id
  obtain ⟨r, hr, hradius⟩ := intermediate_value_Icc hR.le hcont.continuousOn htarget
  change φ (r ^ 2) * r = ‖y‖ at hradius
  let x : N := (r / ‖y‖) • y
  have hnorm : ‖x‖ = r := by
    change ‖(r / ‖y‖) • y‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.1 hypos.le),
      div_mul_cancel₀ _ hypos.ne']
  refine ⟨x, ?_⟩
  change φ (‖x‖ ^ 2) • ((r / ‖y‖) • y) = y
  rw [hnorm, smul_smul, ← mul_div_assoc, hradius, div_self hypos.ne', one_smul]

/-- The radial map of a smooth `φ` is smooth on an inner product space. -/
theorem SmoothRadial.contDiff_radialMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (radialMap (N := N) φ) :=
  (hφ.comp (contDiff_id.norm_sq ℝ)).smul contDiff_id

/-- The derivative of the radial map: `v ↦ φ(‖x‖²) • v + 2 φ'(‖x‖²) ⟪x, v⟫ • x`. -/
theorem SmoothRadial.fderiv_radialMap_apply {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : N) :
    fderiv ℝ (radialMap φ) x v =
      φ (‖x‖ ^ 2) • v + (2 * deriv φ (‖x‖ ^ 2) * Inner.inner ℝ x v) • x := by
  have hscale :=
    ((hφ.differentiable (by simp) (‖x‖ ^ 2)).hasDerivAt).comp_hasFDerivAt x
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hd := hscale.smul (hasFDerivAt_id x)
  rw [show fderiv ℝ (radialMap φ) x = _ from hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_apply,
    id_eq]
  congr 1
  ring_nf

/-- For a positive monotone smooth `φ` the radial map has injective derivative everywhere. -/
theorem SmoothRadial.fderiv_radialMap_injective {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) (x : N) : Function.Injective (fderiv ℝ (radialMap φ) x) := by
  have hzero : ∀ v : N, fderiv ℝ (radialMap φ) x v = 0 → v = 0 := by
    intro v hv
    have heq := congrArg (fun w : N => Inner.inner ℝ v w) hv
    rw [fderiv_radialMap_apply hφ, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm v x, inner_zero_right] at heq
    have hd : 0 ≤ deriv φ (‖x‖ ^ 2) := hmono.deriv_nonneg
    have hnonneg : 0 ≤ 2 * deriv φ (‖x‖ ^ 2) * (Inner.inner ℝ v x) ^ 2 := by positivity
    have hterm : φ (‖x‖ ^ 2) * ‖v‖ ^ 2 ≤ 0 := by nlinarith
    have hsq : ‖v‖ ^ 2 ≤ 0 := by
      by_contra hn
      exact (not_lt_of_ge hterm) (mul_pos (hpos _) (lt_of_not_ge hn))
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  intro v w hvw
  have hsub : fderiv ℝ (radialMap φ) x (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hzero (v - w) hsub)

/-- In finite dimension the derivative of such a radial map is invertible everywhere. -/
theorem SmoothRadial.isInvertible_fderiv_radialMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) (x : N) :
    (fderiv ℝ (radialMap (N := N) φ) x).IsInvertible := by
  let L :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (radialMap φ) x).toLinearMap
        (fderiv_radialMap_injective hφ hpos hmono x)).toContinuousLinearEquiv
  exact ⟨L, by ext v; rfl⟩

/-- A positive monotone smooth `φ` equal to `1` beyond radius `R` makes the radial map a
diffeomorphism of the whole space, the identity outside the ball of radius `R`.
-/
def SmoothRadial.diffeomorph {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    [FiniteDimensional ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) {R : ℝ} (hR : 0 < R) (hout : ∀ s, R ^ 2 ≤ s → φ s = 1) :
    Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞ := by
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) ∞ (radialMap (N := N) φ) := by
    intro x
    apply
      isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ x)
        (contDiff_radialMap hφ).contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv]
    exact isInvertible_fderiv_radialMap hφ hpos hmono x
  exact
    IsLocalDiffeomorph.diffeomorph' hlocal
      ⟨radialMap_injective hpos hmono, radialMap_surjective hφ.continuous hR hout⟩

/-- The time profile `t ↦ 1 + (a - 1) smoothTransition t` of the disc shrinking, running smoothly
from `1` at time `0` to `a` at time `1`.
-/
def SmoothRadial.shrinkTimeFactor (a t : ℝ) : ℝ :=
  1 + (a - 1) * Real.smoothTransition t

/-- For `a ≤ 1` the time profile stays between `a` and `1`. -/
theorem SmoothRadial.shrinkTimeFactor_bounds {a : ℝ} (ha₁ : a ≤ 1) (t : ℝ) :
    a ≤ shrinkTimeFactor a t ∧ shrinkTimeFactor a t ≤ 1 := by
  have ht₀ := Real.smoothTransition.nonneg t
  have ht₁ := Real.smoothTransition.le_one t
  unfold shrinkTimeFactor
  constructor <;> nlinarith

/-- The time profile is `1` at time zero. -/
theorem SmoothRadial.shrinkTimeFactor_zero (a : ℝ) : shrinkTimeFactor a 0 = 1 := by
  simp only [shrinkTimeFactor, Real.smoothTransition.zero, MulZeroClass.mul_zero, add_zero]

/-- The time profile is `a` at time one. -/
theorem SmoothRadial.shrinkTimeFactor_one (a : ℝ) : shrinkTimeFactor a 1 = a := by
  simp only [shrinkTimeFactor, Real.smoothTransition.one, mul_one]
  ring

/-- The time profile is smooth. -/
theorem SmoothRadial.contDiff_shrinkTimeFactor (a : ℝ) :
    ContDiff ℝ ∞ (shrinkTimeFactor a) :=
  contDiff_const.add (contDiff_const.mul (Real.smoothTransition.contDiff (n := ⊤)))

/-- The radial profile of the disc shrinking: equal to `a` on the unit ball and to `1` beyond radius
`R`, interpolating smoothly in between.
-/
def DiskShrinking.scale (R a s : ℝ) : ℝ :=
  a + (1 - a) * Real.smoothTransition ((s - 1) / (R ^ 2 - 1))

/-- The radial profile is smooth. -/
theorem DiskShrinking.contDiff_scale (R a : ℝ) : ContDiff ℝ ∞ (scale R a) :=
  contDiff_const.add
    (contDiff_const.mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp
        ((contDiff_id.sub contDiff_const).div_const _)))

/-- The radial profile is positive. -/
theorem DiskShrinking.scale_pos {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (R s : ℝ) :
    0 < scale R a s :=
  add_pos_of_pos_of_nonneg ha (mul_nonneg (sub_nonneg.mpr ha₁) (Real.smoothTransition.nonneg _))

/-- For `1 < R` and `a ≤ 1` the radial profile is monotone. -/
theorem DiskShrinking.scale_monotone {R a : ℝ} (hR : 1 < R) (ha₁ : a ≤ 1) :
    Monotone (scale R a) := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  intro s t hst
  exact
    add_le_add_right
      (mul_le_mul_of_nonneg_left
        (Real.smoothTransition.monotone
          (div_le_div_of_nonneg_right (sub_le_sub_right hst 1) hden.le))
        (sub_nonneg.mpr ha₁))
      a

/-- On the unit ball the radial profile equals `a`. -/
theorem DiskShrinking.scale_inner {R : ℝ} (hR : 1 < R) (a : ℝ) {s : ℝ} (hs : s ≤ 1) :
    scale R a s = a := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  rw [scale,
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hden.le)]
  simp only [MulZeroClass.mul_zero, add_zero]

/-- Beyond radius `R` the radial profile equals `1`. -/
theorem DiskShrinking.scale_outer {R : ℝ} (hR : 1 < R) (a : ℝ) {s : ℝ} (hs : R ^ 2 ≤ s) :
    scale R a s = 1 := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  rw [scale, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hden).mpr (by linarith))]
  ring

/-- The radial profile for `a = 1` is constant `1`. -/
theorem DiskShrinking.scale_one (R s : ℝ) : scale R 1 s = 1 := by
  simp only [scale, sub_self, MulZeroClass.zero_mul, add_zero]

/-- The disc-shrinking isotopy: the radial map with profile `scale R (shrinkTimeFactor a t)`, which
at time one contracts the unit ball by the factor `a` and is the identity outside the ball of
radius `R`.
-/
def DiskShrinking.family {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (R a : ℝ) (p : ℝ × N) : N :=
  SmoothRadial.radialMap (scale R (SmoothRadial.shrinkTimeFactor a p.1)) p.2

/-- The disc-shrinking isotopy is smooth in time and space. -/
theorem DiskShrinking.contMDiff_family {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (R a : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, N) ∞ (family (N := N) R a) := by
  have ht :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => SmoothRadial.shrinkTimeFactor a p.1) :=
    (SmoothRadial.contDiff_shrinkTimeFactor a).contMDiff.comp contMDiff_fst
  have hn : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × N => ‖p.2‖ ^ 2) :=
    (show ContDiff ℝ ∞ (fun x : N => ‖x‖ ^ 2) from contDiff_id.norm_sq ℝ).contMDiff.comp
      contMDiff_snd
  have hz :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × N => (‖p.2‖ ^ 2 - 1) / (R ^ 2 - 1)) :=
    by
    simpa only [div_eq_mul_inv, Pi.mul_def, Pi.sub_def] using
      (hn.sub contMDiff_const).mul (contMDiff_const (c := (R ^ 2 - 1)⁻¹))
  exact
    (ht.add
          ((contMDiff_const.sub ht).mul
            ((Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp hz))).smul
      contMDiff_snd

/-- The disc-shrinking isotopy is the identity at time zero. -/
theorem DiskShrinking.family_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (R a : ℝ) (x : N) : family R a (0, x) = x := by
  simp only [family, SmoothRadial.shrinkTimeFactor_zero, SmoothRadial.radialMap,
    scale_one, one_smul]

/-- Each time slice of the disc-shrinking isotopy is a diffeomorphism. -/
theorem DiskShrinking.family_slices {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {R a : ℝ} (hR : 1 < R) (ha : 0 < a)
    (ha₁ : a ≤ 1) (t : ℝ) :
    ∃ D : Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞, ∀ x, D x = family R a (t, x) := by
  have ht := SmoothRadial.shrinkTimeFactor_bounds ha₁ t
  exact
    ⟨SmoothRadial.diffeomorph (contDiff_scale R _) (scale_pos (ha.trans_le ht.1) ht.2 R)
        (scale_monotone hR ht.2) (zero_lt_one.trans hR) (fun _ hs => scale_outer hR _ hs),
      fun _ => rfl⟩

/-- The disc-shrinking isotopy is the identity outside the ball of radius `R`, hence compactly
supported.
-/
theorem DiskShrinking.family_outer {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {R : ℝ} (hR : 1 < R) (a t : ℝ) {x : N}
    (hx : R ≤ ‖x‖) : family R a (t, x) = x := by
  rw [family, SmoothRadial.radialMap,
    scale_outer hR _ ((sq_le_sq₀ (zero_lt_one.trans hR).le (norm_nonneg x)).mpr hx), one_smul]

/-- At time one the disc-shrinking isotopy is the scaling by `a` on the unit ball. -/
theorem DiskShrinking.family_one_inner {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {R : ℝ} (hR : 1 < R) (a : ℝ) {x : N}
    (hx : ‖x‖ ≤ 1) : family R a (1, x) = a • x := by
  rw [family, SmoothRadial.radialMap, SmoothRadial.shrinkTimeFactor_one,
    scale_inner hR a (by nlinarith [norm_nonneg x])]

/-- The disc-shrinking isotopy fixes the origin. -/
theorem DiskShrinking.family_origin {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (R a t : ℝ) : family R a (t, (0 : N)) = 0 := by
  simp only [family, SmoothRadial.radialMap, smul_zero]

/-- An open set containing the closed unit ball contains a closed ball of radius strictly bigger
than one.
-/
theorem DiskShrinking.exists_larger_closedBall_subset {D : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {U : Set D} (hU : IsOpen U)
    (hunit : Metric.closedBall (0 : D) 1 ⊆ U) :
    ∃ R : ℝ, 1 < R ∧ Metric.closedBall (0 : D) R ⊆ U := by
  let T : Set ℝ := {r | ∀ x ∈ Metric.closedBall (0 : D) 1, r • x ∈ U}
  have hT : IsOpen T :=
    MorsePerturbation.isOpen_forall_mem_compact (ProperSpace.isCompact_closedBall (0 : D) 1)
      (hU.preimage (continuous_fst.smul continuous_snd))
  have h1 : (1 : ℝ) ∈ T := by
    intro x hx
    simpa only [one_smul] using hunit hx
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h1)
  let R : ℝ := 1 + δ / 2
  have hR : 1 < R := by dsimp [R]; linarith
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hRT : R ∈ T :=
    hδT
      (by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by dsimp [R]; linarith)]
        dsimp [R]
        linarith)
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hnorm : ‖R⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    exact
      (inv_mul_le_iff₀ hRpos).mpr (by simpa only [mul_one] using mem_closedBall_zero_iff.mp hx)
  have hh := hRT (R⁻¹ • x) (mem_closedBall_zero_iff.mpr hnorm)
  simpa only [smul_inv_smul₀ hRpos.ne'] using hh

/-- An open set of `D × Z` containing the unit disc of the first factor contains the image of a ball
of radius `R > 1` under a linear isomorphism restricting to the inclusion of that disc.
-/
theorem DiskShrinking.exists_disk_ellipsoid_in_open {D Z : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ Z] {U : Set (D × Z)} (hU : IsOpen U)
    (hzero : Metric.closedBall (0 : D) 1 ×ˢ {(0 : Z)} ⊆ U) :
    ∃ R : ℝ,
      1 < R ∧
        ∃ L : WithLp 2 (D × Z) ≃L[ℝ] D × Z,
          (∀ x : D, L (WithLp.toLp 2 (x, (0 : Z))) = (x, 0)) ∧
            Set.MapsTo L (Metric.closedBall 0 R) U := by
  obtain ⟨A, B, hA, hB, hKA, h0B, hAB⟩ :=
    generalized_tube_lemma (ProperSpace.isCompact_closedBall (0 : D) 1)
      (isCompact_singleton (x := (0 : Z))) hU hzero
  obtain ⟨R, hR, hRA⟩ := exists_larger_closedBall_subset hA hKA
  obtain ⟨ε, hε, hεB⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hB.mem_nhds (h0B (Set.mem_singleton (0 : Z))))
  have hRpos : 0 < R := zero_lt_one.trans hR
  let δ : ℝ := ε / R
  have hδ : 0 < δ := div_pos hε hRpos
  let T : Z ≃L[ℝ] Z := (LinearEquiv.smulOfNeZero ℝ Z δ hδ.ne').toContinuousLinearEquiv
  let L : WithLp 2 (D × Z) ≃L[ℝ] D × Z :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ D Z).trans
      ((ContinuousLinearEquiv.refl ℝ D).prodCongr T)
  have hL (p : WithLp 2 (D × Z)) : L p = (p.fst, δ • p.snd) := rfl
  refine ⟨R, hR, L, ?_, ?_⟩
  · intro x
    rw [hL]
    change (x, δ • (0 : Z)) = (x, 0)
    rw [smul_zero]
  · intro p hp
    rw [hL]
    apply hAB
    refine
      ⟨hRA
          (mem_closedBall_zero_iff.mpr
            ((WithLp.norm_fst_le D p).trans (mem_closedBall_zero_iff.mp hp))),
        hεB ?_⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    calc
      δ * ‖p.snd‖ ≤ δ * R :=
        mul_le_mul_of_nonneg_left ((WithLp.norm_snd_le D p).trans (mem_closedBall_zero_iff.mp hp))
          hδ.le
      _ = ε := div_mul_cancel₀ ε hRpos.ne'

/-- Isotopy extension through a chart: a compactly supported isotopy on the source of a partial
diffeomorphism extends to a compactly supported isotopy of the target intertwined with it by the
chart.
-/
theorem SupportedDiffeomorph.exists_supported_isotopy_extension {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {A : ℝ × X → X} (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A)
    (hA₀ : ∀ x, A (0, x) = x) (hdiff : ∀ t, ∃ D : Diffeomorph I I X X ∞, ∀ x, D x = A (t, x))
    {K : Set X} (hK : IsCompact K) (hKsource : K ⊆ Φ.source)
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) :
    ∃ (B : ℝ × Y → Y) (L : Set Y),
      IsCompact L ∧
        L ⊆ Φ.target ∧
          ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ B ∧
            (∀ y, B (0, y) = y) ∧
              (∀ t, ∃ D : Diffeomorph J J Y Y ∞, ∀ y, D y = B (t, y)) ∧
                (∀ t y, y ∉ L → B (t, y) = y) ∧
                  (∀ t, Set.MapsTo (fun x => A (t, x)) Φ.source Φ.source) ∧
                    ∀ t x, x ∈ Φ.source → B (t, Φ x) = Φ (A (t, x)) := by
  have hsource : ∀ t, Set.MapsTo (fun x => A (t, x)) Φ.source Φ.source := by
    intro t
    obtain ⟨D, hD⟩ := hdiff t
    have hDfix : ∀ x ∉ K, D x = x := fun x hx => (hD x).trans (hfix t x hx)
    have heq : (fun x => A (t, x)) = D := funext (fun x => (hD x).symm)
    rw [heq]
    exact mapsTo_source Φ D.toEquiv hKsource hDfix
  let B : ℝ × Y → Y := fun q => extendMap Φ (fun x => A (q.1, x)) q.2
  refine
    ⟨B, Φ '' K, hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKsource), ?_,
      contMDiff_extendFamily Φ hA hK hKsource hfix hsource, ?_, ?_, ?_, hsource, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source' (hKsource hx)
  · intro y
    have heq : (fun x => A (0, x)) = id := funext hA₀
    change extendMap Φ (fun x => A (0, x)) y = y
    rw [heq]
    exact extendMap_id Φ y
  · intro t
    obtain ⟨D, hD⟩ := hdiff t
    have hDfix : ∀ x ∉ K, D x = x := fun x hx => (hD x).trans (hfix t x hx)
    refine ⟨extension Φ D hK hKsource hDfix, ?_⟩
    intro y
    exact congrArg (fun f : X → X => extendMap Φ f y) (funext hD)
  · intro t y hy
    exact extendMap_eq_of_notMem_image Φ (hfix t) hy
  · intro t x hx
    exact extendMap_chart Φ (fun z => A (t, z)) hx

/-- In a chart whose source contains the unit disc of the first factor there is a diffeomorphism of
the manifold, isotopic to the identity through diffeomorphisms supported in some compact subset
`K ⊆ Φ.target` of the chart and fixing its centre `Φ (0, 0)`, which contracts that disc by the
factor `a`.
-/
theorem DiskShrinking.exists_chart_disk_shrinking {D Z E H M : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) I (D × Z) M ∞)
    (hzero : Metric.closedBall (0 : D) 1 ×ˢ {(0 : Z)} ⊆ Φ.source) {a : ℝ} (ha : 0 < a)
    (ha₁ : a ≤ 1) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ P : Diffeomorph I I M M ∞,
            Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy P K {Φ (0, 0)}) ∧
              ∀ x : D, ‖x‖ ≤ 1 → P (Φ (x, 0)) = Φ (a • x, 0) := by
  obtain ⟨R, hR, L, hLzero, hLsource⟩ := exists_disk_ellipsoid_in_open Φ.open_source hzero
  let Ψ := L.toDiffeomorph.toPartialDiffeomorph'.trans Φ
  have hsource : Metric.closedBall (0 : WithLp 2 (D × Z)) R ⊆ Ψ.source := by
    intro z hz
    exact ⟨Set.mem_univ z, hLsource hz⟩
  have htarget : Ψ.target ⊆ Φ.target := fun _ hy => hy.1
  have hΨ (x : D) : Ψ (WithLp.toLp 2 (x, (0 : Z))) = Φ (x, 0) := by
    change Φ (L (WithLp.toLp 2 (x, (0 : Z)))) = _
    rw [hLzero]
  have hΨ0 : Ψ (0 : WithLp 2 (D × Z)) = Φ (0, 0) := hΨ 0
  have h0source : (0 : WithLp 2 (D × Z)) ∈ Ψ.source :=
    hsource (Metric.mem_closedBall_self (zero_le_one.trans hR.le))
  have hfix : ∀ t (z : WithLp 2 (D × Z)), z ∉ Metric.closedBall 0 R → family R a (t, z) = z := by
    intro t z hz
    exact family_outer hR a t (le_of_not_ge (fun hn => hz (mem_closedBall_zero_iff.mpr hn)))
  obtain ⟨B, K, hK, hKt, hB, hB0, hBt, hBfix, -, hchart⟩ :=
    SupportedDiffeomorph.exists_supported_isotopy_extension Ψ (contMDiff_family R a)
      (family_zero R a) (family_slices hR ha ha₁) (ProperSpace.isCompact_closedBall 0 R) hsource
      hfix
  obtain ⟨P, hP⟩ := hBt 1
  refine
    ⟨K, hK, hKt.trans htarget, P,
      ⟨{  family := B
          smooth := hB
          zero := hB0
          one := fun y => (hP y).symm
          slices := hBt
          fixedOutside := hBfix
          fixedOn := ?_ }⟩, ?_⟩
  · intro t y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    rw [← hΨ0, hchart t 0 h0source, family_origin]
  · intro x hx
    have hn : ‖WithLp.toLp 2 (x, (0 : Z))‖ ≤ 1 := by simpa only [WithLp.norm_toLp_fst] using hx
    have hs : WithLp.toLp 2 (x, (0 : Z)) ∈ Ψ.source :=
      hsource (mem_closedBall_zero_iff.mpr (hn.trans hR.le))
    have hsmul : a • WithLp.toLp 2 (x, (0 : Z)) = WithLp.toLp 2 (a • x, (0 : Z)) := by
      change WithLp.toLp 2 (a • x, a • (0 : Z)) = _
      rw [smul_zero]
    rw [← hΨ x, hP, hchart 1 _ hs, family_one_inner hR a hn, hsmul, hΨ]

/-- The inverse of a diffeomorphism isotopic to the identity is isotopic to the identity. -/
theorem SupportedDiffeomorph.IsotopicToIdentity.symm {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] {e : Diffeomorph J J M M ∞}
    (he : SupportedDiffeomorph.IsotopicToIdentity e) :
    SupportedDiffeomorph.IsotopicToIdentity e.symm := by
  obtain ⟨A, hA, hA₀, hA₁, hdiff⟩ := he
  let B : ℝ × M → M := fun p => e.symm (A (1 - p.1, p.2))
  have hrev : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => 1 - t) :=
    (contDiff_const.sub contDiff_id).contMDiff
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ B :=
    e.symm.contMDiff.comp (hA.comp ((hrev.comp contMDiff_fst).prodMk contMDiff_snd))
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · intro x
    change e.symm (A (1 - 0, x)) = x
    rw [sub_zero, hA₁, e.symm_apply_apply]
  · intro x
    change e.symm (A (1 - 1, x)) = e.symm x
    rw [sub_self, hA₀]
  · intro t
    obtain ⟨d, hd⟩ := hdiff (1 - t)
    refine ⟨d.trans e.symm, ?_⟩
    intro x
    change e.symm (A (1 - t, x)) = e.symm (d x)
    rw [hd]

/-- Two charts with the same centre carry the unit disc of the first factor to discs that agree
after a diffeomorphism isotopic to the identity.
-/
theorem SupportedGerms.exists_disk_chart_isotopy {A B E H M ι κ : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [Finite ι] [Finite κ] [Nontrivial κ] (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B)) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, A × B) J (A × B) M ∞)
    (hΦ : Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} ⊆ Φ.source)
    (hΨ : Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} ⊆ Ψ.source) (hcenter : Φ 0 = Ψ 0) :
    ∃ D : Diffeomorph J J M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity D ∧
        ∀ x ∈ Metric.closedBall (0 : A) 1, D (Φ (x, 0)) = Ψ (x, 0) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  have hz : (0 : A × B) ∈ Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} :=
    ⟨Metric.mem_closedBall_self zero_le_one, rfl⟩
  obtain ⟨D, K, -, -, ⟨HD⟩, hgerm⟩ :=
    exists_native_disk_germ_alignment b i basis Φ Ψ (hΦ hz) (hΨ hz) hcenter
  obtain ⟨ε, hε, hεeq⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgerm
  let a : ℝ := Min.min 1 ε
  have ha : 0 < a := lt_min zero_lt_one hε
  have ha1 : a ≤ 1 := min_le_left _ _
  obtain ⟨KΦ, -, -, P, ⟨HP⟩, hP⟩ := DiskShrinking.exists_chart_disk_shrinking Φ hΦ ha ha1
  obtain ⟨KΨ, -, -, Q, ⟨HQ⟩, hQ⟩ := DiskShrinking.exists_chart_disk_shrinking Ψ hΨ ha ha1
  refine
    ⟨(P.trans D).trans Q.symm,
      (HP.isotopicToIdentity.trans HD.isotopicToIdentity).trans HQ.isotopicToIdentity.symm, ?_⟩
  intro x hx
  have hn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hsmall : a • x ∈ Metric.closedBall (0 : A) ε := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_of_le_one_right ha.le hn).trans (min_le_right _ _)
  have heq : D (Φ (a • x, 0)) = Ψ (a • x, 0) := hεeq hsmall
  change Q.symm (D (P (Φ (x, 0)))) = Ψ (x, 0)
  rw [hP x hn, heq, ← hQ x hn, Q.symm_apply_apply]

/-- The disc theorem: two smooth embeddings of the closed unit disc into a compact manifold of
dimension at least two, of the same positive codimension and with the same centre, are carried
onto one another by a diffeomorphism isotopic to the identity (Hirsch, Differential Topology,
Thm 8.3.1; Palais).
-/
theorem DiskShrinking.exists_embedded_disk_isotopy_of_same_center {D E M : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hgi : Set.InjOn g (Metric.closedBall (0 : D) 1))
    (hfd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) (hcenter : f 0 = g 0) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity P ∧
        ∀ x ∈ Metric.closedBall (0 : D) 1, P (f x) = g x := by
  classical
  let B := EuclideanSpace ℝ (Fin n)
  obtain ⟨ε, hε, Φ, hΦprod, hΦzero, -⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_closedBall hf hfi hfd n hdim isOpen_univ
      (Set.mapsTo_univ _ _)
  obtain ⟨δ, hδ, Ψ, hΨprod, hΨzero, -⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_closedBall hg hgi hgd n hdim isOpen_univ
      (Set.mapsTo_univ _ _)
  have hΦ : Metric.closedBall (0 : D) 1 ×ˢ {(0 : B)} ⊆ Φ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hΦprod ⟨hx, Metric.mem_closedBall_self hε.le⟩
  have hΨ : Metric.closedBall (0 : D) 1 ×ˢ {(0 : B)} ⊆ Ψ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hΨprod ⟨hx, Metric.mem_closedBall_self hδ.le⟩
  have hcenter' : Φ 0 = Ψ 0 := by
    change Φ (0, 0) = Ψ (0, 0)
    rw [hΦzero 0 (Metric.mem_closedBall_self zero_le_one),
      hΨzero 0 (Metric.mem_closedBall_self zero_le_one), hcenter]
  have hB : 0 < Module.finrank ℝ B := by simpa only [B, finrank_euclideanSpace_fin] using hn
  have hDB : 2 ≤ Module.finrank ℝ (D × B) := by
    simpa only [Module.finrank_prod, B, finrank_euclideanSpace_fin, hdim] using hE
  let _ : Nontrivial (Fin (Module.finrank ℝ (D × B))) := Fin.nontrivial_iff_two_le.mpr hDB
  obtain ⟨P, hP, hformula⟩ :=
    SupportedGerms.exists_disk_chart_isotopy (Module.finBasis ℝ B) ⟨0, hB⟩
      (Module.finBasis ℝ (D × B)) Φ Ψ hΦ hΨ hcenter'
  refine ⟨P, hP, ?_⟩
  intro x hx
  rw [← hΦzero x hx, hformula x hx, hΨzero x hx]

/-- Homogeneity in a chart: points close enough to a given point of a chart can be moved onto its
image by a compactly supported isotopy of the manifold that is the identity outside the chart.
-/
theorem SupportedDiffeomorph.exists_supported_pointMoving {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {x : E}
    (hx : x ∈ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        Metric.ball x ε ⊆ Φ.source ∧
          ∀ y ∈ Metric.ball x ε,
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
                (∀ z, A (0, z) = z) ∧
                  (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ z, A (t, z) = d z) ∧
                    (∀ t z, z ∉ Φ.target → A (t, z) = z) ∧ A (1, Φ x) = Φ y := by
  obtain ⟨β, hβsupport, hβcompact, hβsmooth, -, hβx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (Φ.open_source.mem_nhds hx)
  obtain ⟨δ, hδ, hmove⟩ := exists_small_supported_bump_isotopy Φ hβsmooth hβcompact hβsupport
  obtain ⟨ρ, hρ, hρsource⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hx)
  refine ⟨Min.min δ ρ, lt_min hδ hρ, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_right _ _)).trans hρsource
  · intro y hy
    have hnear : ‖y - x‖ < δ := by
      simpa only [dist_eq_norm] using
        (show Dist.dist y x < Min.min δ ρ from hy).trans_le (min_le_left _ _)
    obtain ⟨A, hA, hzero, hdiff, hfix, hend⟩ := hmove (y - x) hnear
    refine ⟨A, hA, hzero, hdiff, ?_, ?_⟩
    · intro t z hz
      apply hfix t z
      rintro ⟨q, hq, rfl⟩
      exact hz (Φ.map_source' (hβsupport hq))
    · have hterminal := hend x hx
      rw [hβx, one_smul] at hterminal
      have hxy : x + (y - x) = y := by abel
      exact hterminal.trans (congrArg Φ hxy)

/-- Homogeneity of a manifold: every point of an open set has a neighbourhood in it each of whose
points is the image of that point under a diffeomorphism that is the identity outside the open
set.
-/
theorem SupportedDiffeomorph.exists_open_pointMoving {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ V : Set M,
      IsOpen V ∧
        x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  let c := modelChartPartialDiffeomorph (I := J) x
  let Φ := PartialChart.restrictTarget c.symm hU
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv' hxc
  have hxΦ : c x ∈ Φ.source := by
    refine ⟨c.map_source' hxc, ?_⟩
    change c.symm (c x) ∈ U
    rw [hcx]
    exact hx
  have hΦx : Φ (c x) = x := hcx
  obtain ⟨ε, hε, hball, hmove⟩ := exists_supported_pointMoving Φ hxΦ
  refine
    ⟨Φ '' Metric.ball (c x) ε,
      Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hball,
      ⟨c x, Metric.mem_ball_self hε, hΦx⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (Φ.map_source' (hball hv)).2
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨A, _, _, hdiff, hfix, hend⟩ := hmove v hv
    obtain ⟨d, hd⟩ := hdiff 1
    refine ⟨d, ?_, ?_⟩
    · rw [hΦx] at hend
      exact (hd x).symm.trans hend
    · intro z hz
      exact (hd z).symm.trans (hfix 1 z (fun h => hz h.2))

/-- Precomposing the left summand of a surjective `coprod` with a surjection keeps it
surjective: if `L.coprod R` and `P` are surjective then so is `(L ∘ P).coprod R`. -/
theorem ContinuousLinearMap.surjective_coprod_comp_left {A A' B G : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup A'] [NormedSpace ℝ A'] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : A →L[ℝ] G) (R : B →L[ℝ] G)
    (P : A' →L[ℝ] A) (hP : Function.Surjective P) (htrans : Function.Surjective (L.coprod R)) :
    Function.Surjective ((L.comp P).coprod R) := by
  intro y
  obtain ⟨⟨a, b⟩, hab⟩ := htrans y
  obtain ⟨a', ha⟩ := hP a
  refine ⟨(a', b), ?_⟩
  change L (P a') + R b = y
  rw [ha]
  exact hab
