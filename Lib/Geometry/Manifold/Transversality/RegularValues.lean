/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
/-!
# Submersions and regular values in equal dimension

Surjectivity of the derivative is a chart-independent condition, and in a smooth family of maps
between manifolds of equal dimension it is an open condition on parameter and point. Sard's theorem
in the equidimensional case: the critical values of a smooth map from a Lindelöf manifold to a
finite-dimensional space of the same dimension form a Haar-null set (proved from Mathlib's
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`).

## Main results

* `NativeSubmersion.surjective_fderiv_sourceChart_iff`,
  `NativeSubmersion.isOpen_surjective_nativeDerivative`
* `RegularValues.exists_null_exceptional_values_manifold`

## References

* [V. Guillemin, A. Pollack, *Differential Topology*][gp74], §1.7 (Sard's theorem).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


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
