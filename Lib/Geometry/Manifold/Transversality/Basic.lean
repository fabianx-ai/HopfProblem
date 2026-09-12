/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Geometry.Manifold.Collar
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.Cancellation

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

theorem Smale.NativeSubmersion.surjective_fderiv_sourceChart_iff {E F H X : Type*}
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
  have hB : Function.Surjective B := (Smale.PartialChart.bijective_mfderiv c.symm hz).surjective
  rw [hd]
  change Function.Surjective (A.comp B) ↔ Function.Surjective A
  constructor
  · intro h w
    obtain ⟨v, hv⟩ := h w
    exact ⟨B v, hv⟩
  · intro h
    exact h.comp hB

theorem Smale.NativeSubmersion.isOpen_surjective_nativeDerivative {E F H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [I.Boundaryless] [IsManifold I ∞ X] {f : P → X → F} {W : Set (P × X)}
    (hW : IsOpen W) (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ (Function.uncurry f) W)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsOpen {q : P × X | q ∈ W ∧ Function.Surjective (mfderiv I 𝓘(ℝ, F) (f q.1) q.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqsurj⟩
  let c := NoExotic.modelChartPartialDiffeomorph (I := I) q.2
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
    Smale.MorsePerturbation.contDiffOn_spatialDerivative (f := fun a z => f a (c.symm z)) hU
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

theorem Smale.RegularValues.exists_null_exceptional_values_on {E : Type*} [NormedAddCommGroup E]
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

theorem Smale.RegularValues.exists_null_exceptional_values_in_chart {E F H X : Type*}
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

theorem Smale.RegularValues.exists_null_exceptional_values_manifold {E F H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [MeasurableSpace F] [BorelSpace F] (μ : MeasureTheory.Measure F)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] [LindelofSpace X] {f : X → F} {s : Set X}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ T : Set F, μ T = 0 ∧ ∀ x ∈ s, f x ∉ T → Function.Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  classical
  let c (x : X) := NoExotic.modelChartPartialDiffeomorph (I := I) x
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

theorem Smale.TransverseCoordinates.mfderiv_sheetDifference {D Z F H K X Y : Type*}
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

theorem Smale.TransverseCoordinates.surjective_sheetDifference_iff {D Z F H K X Y : Type*}
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

theorem Smale.TransverseCoordinates.exists_null_exceptional_native_translations
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
    Smale.RegularValues.exists_null_exceptional_values_manifold μ (hU.prod hV) hB
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

theorem Smale.TransverseCoordinates.dense_native_translations {D Z F H K X Y : Type*}
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

theorem Smale.ChartMapPerturbation.mfderiv_eq_of_translation_germ {D F H X : Type*}
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

theorem Smale.ChartMapPerturbation.transverse_of_chart {D Z G F H H' K X Y N : Type*}
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
  have hC : Function.Injective C := (Smale.PartialChart.bijective_mfderiv c hx).injective
  change Function.Surjective (A.coprod B)
  intro w
  obtain ⟨v, hv⟩ := ht (C w)
  exact ⟨v, hC hv⟩

theorem Smale.ChartMapPerturbation.transverse_in_chart {D Z G F H H' K X Y N : Type*}
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
  have hC : Function.Surjective C := (Smale.PartialChart.bijective_mfderiv c hx).surjective
  change Function.Surjective (A.coprod B) at ht
  intro w
  obtain ⟨z, hz⟩ := hC w
  obtain ⟨v, hv⟩ := ht z
  refine ⟨v, ?_⟩
  change C (A v.1) + C (B v.2) = w
  rw [← C.map_add]
  exact (congrArg C hv).trans hz

def Smale.NativeTransversality.At {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    (I : ModelWithCorners ℝ D H) (I' : ModelWithCorners ℝ Z H') (J : ModelWithCorners ℝ G K)
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [TopologicalSpace N] [ChartedSpace K N] (f : X → N) (g : Y → N) (x : X) (y : Y) : Prop :=
  g y = f x →
    Function.Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G))

theorem Smale.NativeTransversality.at_iff_chart_difference {D Z G H H' K X Y N : Type*}
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
  have hdiff := Smale.TransverseCoordinates.surjective_sheetDifference_iff hcf hcg
  constructor
  · intro ht
    apply hdiff.mpr
    exact Smale.ChartMapPerturbation.transverse_in_chart c hf hg hxy hx (ht hxy)
  · intro h _
    exact Smale.ChartMapPerturbation.transverse_of_chart c hf hg hxy hx (hdiff.mp h)

theorem Smale.NativeTransversality.isOpen_at_family {D Z G H H' K X Y N : Type*}
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
  · let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f q.1 q.2.1)
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
      Smale.NativeSubmersion.isOpen_surjective_nativeDerivative hW hB
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

theorem Smale.NativeTransversality.eventually_on_compact {D Z G H H' K X Y N : Type*}
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
    Smale.MorsePerturbation.isOpen_forall_mem_compact hC (isOpen_at_family hU hf hg hdim)
  have hn := hopen.mem_nhds (fun z hz => ⟨ha, htrans z hz⟩)
  filter_upwards [hn] with b hb z hz
  exact (hb z hz).2

theorem Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff
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
    Smale.NativeTransversality.At I I' J f g x y ↔
      Smale.NativeTransversality.At I I' J' (P ∘ f) (P ∘ g) x y := by
  let L : A →L[ℝ] Z := mfderiv I J f x
  let R : B →L[ℝ] Z := mfderiv I' J g y
  let C : Z →L[ℝ] E := mfderiv J J' P (f x)
  have hy : g y ∈ P.source := hxy ▸ hx
  have hL : (mfderiv I J' (P ∘ f) x : A →L[ℝ] E) = C.comp L :=
    mfderiv_comp x (P.mdifferentiableAt (by simp) hx) hf
  have hR : (mfderiv I' J' (P ∘ g) y : B →L[ℝ] E) = C.comp R := by
    rw [mfderiv_comp y (P.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  have hC : Function.Bijective C := Smale.PartialChart.bijective_mfderiv P hx
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

theorem Smale.MorseHandle.ambientMap_lower_sphere {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (u : Metric.sphere (0 : N) 1) (v : P) :
    -‖(ambientMap ρ ((u : N), v)).1‖ ^ 2 + ‖(ambientMap ρ ((u : N), v)).2‖ ^ 2 = -(ρ ^ 2) := by
  have hA : 0 < ρ * Real.sqrt (1 + ‖v‖ ^ 2) := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  simp only [ambientMap, norm_smul, Real.norm_eq_abs, abs_of_pos hA, abs_of_pos hρ,
    mem_sphere_zero_iff_norm.mp u.property, mul_one, mul_pow,
    Real.sq_sqrt (show 0 ≤ 1 + ‖v‖ ^ 2 by positivity)]
  ring

theorem Smale.MorseHandle.ambientMap_sphere_mem_product {N P : Type*} [NormedAddCommGroup N]
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

theorem Smale.MorseHandle.norm_ambientInverse_fst_of_lower {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P)
    (hz : -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 = -(ρ ^ 2)) : ‖(ambientInverse ρ z).1‖ = 1 := by
  let A : ℝ := ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)
  have hA : 0 < A := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hA₂ : A ^ 2 = ρ ^ 2 + ‖z.2‖ ^ 2 := inverse_scale_sq hρ z.2
  have hn : ‖z.1‖ = A := by nlinarith [norm_nonneg z.1]
  change ‖A⁻¹ • z.1‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA), hn, inv_mul_cancel₀ hA.ne']

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.SignedMorseChart.beltRawCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ)
    (z : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates × c.NegativeCoordinates) :
    c.NegativeCoordinates × c.PositiveCoordinates :=
  (Smale.MorseHandle.ambientMap ρ ((z.1 : c.PositiveCoordinates), z.2)).swap

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.continuous_beltRawCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltRawCoordinates ρ) :=
  continuous_swap.comp
    ((Smale.MorseHandle.ambientHomeomorph ρ hρ).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.SignedMorseChart.beltSource {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    TopologicalSpace.Opens
      (Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates × c.NegativeCoordinates) :=
  ⟨c.beltRawCoordinates ρ ⁻¹' c.splitChart.target,
    c.splitChart.open_target.preimage (c.continuous_beltRawCoordinates ρ hρ)⟩

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.SignedMorseChart.beltTarget {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) :
    TopologicalSpace.Opens { y : M // f y = f p + ρ ^ 2 } :=
  ⟨Subtype.val ⁻¹' c.splitChart.source, c.splitChart.open_source.preimage continuous_subtype_val⟩

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.SignedMorseChart.beltNeighborhoodMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.beltSource ρ hρ) : c.beltTarget ρ :=
  ⟨⟨c.splitChart.symm (c.beltRawCoordinates ρ z.val),
      by
      rw [c.splitChart_inverse_equation z.property]
      have hh := Smale.MorseHandle.ambientMap_lower_sphere hρ z.val.1 z.val.2
      change
        -‖(c.beltRawCoordinates ρ z.val).2‖ ^ 2 + ‖(c.beltRawCoordinates ρ z.val).1‖ ^ 2 =
          -(ρ ^ 2) at hh
      linarith⟩,
    c.splitChart.map_target' z.property⟩

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.continuous_beltNeighborhoodMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltNeighborhoodMap ρ hρ) := by
  have hc :
    Continuous (fun z : c.beltSource ρ hρ => c.splitChart.symm (c.beltRawCoordinates ρ z.val)) :=
    c.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous
      ((c.continuous_beltRawCoordinates ρ hρ).comp continuous_subtype_val) (fun z => z.property)
  exact (hc.subtype_mk _).subtype_mk _

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.SignedMorseChart.beltInverseCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (y : M) :
    c.PositiveCoordinates × c.NegativeCoordinates :=
  Smale.MorseHandle.ambientInverse ρ (c.splitChart y).swap

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.continuousOn_beltInverseCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    ContinuousOn (c.beltInverseCoordinates ρ) c.splitChart.source :=
  (Smale.MorseHandle.ambientHomeomorph ρ hρ).symm.continuous.comp_continuousOn
    (continuous_swap.comp_continuousOn c.splitChart.contMDiffOn_toFun.continuousOn)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.beltInverseCoordinates_neighborhoodMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.beltSource ρ hρ) :
    c.beltInverseCoordinates ρ ((c.beltNeighborhoodMap ρ hρ z).val : M) =
      ((z.val.1 : c.PositiveCoordinates), z.val.2) := by
  have hr :
    c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val)) =
      c.beltRawCoordinates ρ z.val :=
    c.splitChart.right_inv' z.property
  change
    Smale.MorseHandle.ambientInverse ρ
        (c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val))).swap =
      _
  rw [hr]
  exact Smale.MorseHandle.ambientInverse_ambientMap hρ _

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.norm_beltInverseCoordinates_fst {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (y : { y : M // f y = f p + ρ ^ 2 }) (hy : (y : M) ∈ c.splitChart.source) :
    ‖(c.beltInverseCoordinates ρ y).1‖ = 1 := by
  apply Smale.MorseHandle.norm_ambientInverse_fst_of_lower hρ
  have hh := c.splitChart_equation hy
  rw [y.property] at hh
  change -‖(c.splitChart (y : M)).2‖ ^ 2 + ‖(c.splitChart (y : M)).1‖ ^ 2 = -(ρ ^ 2)
  linarith

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.SignedMorseChart.beltNeighborhoodInverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (y : c.beltTarget ρ) : c.beltSource ρ hρ := by
  let v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates :=
    ⟨(c.beltInverseCoordinates ρ (y.val : M)).1,
      mem_sphere_zero_iff_norm.mpr (c.norm_beltInverseCoordinates_fst ρ hρ y.val y.property)⟩
  refine ⟨(v, (c.beltInverseCoordinates ρ (y.val : M)).2), ?_⟩
  change
    (Smale.MorseHandle.ambientMap ρ
          (Smale.MorseHandle.ambientInverse ρ (c.splitChart (y.val : M)).swap)).swap ∈
      c.splitChart.target
  rw [Smale.MorseHandle.ambientMap_ambientInverse hρ, Prod.swap_swap]
  exact c.splitChart.map_source' y.property

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.continuous_beltNeighborhoodInverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltNeighborhoodInverse ρ hρ) := by
  have hc : Continuous (fun y : c.beltTarget ρ => c.beltInverseCoordinates ρ (y.val : M)) :=
    (c.continuousOn_beltInverseCoordinates ρ hρ).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.property)
  exact ((hc.fst.subtype_mk _).prodMk hc.snd).subtype_mk _

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.SignedMorseChart.beltNeighborhoodHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
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
          (Smale.MorseHandle.ambientMap ρ
              (Smale.MorseHandle.ambientInverse ρ (c.splitChart (y.val : M)).swap)).swap =
        (y.val : M)
    rw [Smale.MorseHandle.ambientMap_ambientInverse hρ, Prod.swap_swap]
    exact c.splitChart.left_inv' y.property
  continuous_toFun := c.continuous_beltNeighborhoodMap ρ hρ
  continuous_invFun := c.continuous_beltNeighborhoodInverse ρ hρ

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.enlarged_closed_belt_subset_source {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    (Set.univ : Set (Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates)) ×ˢ
        Metric.closedBall (0 : c.NegativeCoordinates) (3 / 2 : ℝ) ⊆
      c.beltSource ρ hρ := by
  rintro ⟨v, u⟩ ⟨_, hu⟩
  have hh :=
    Smale.MorseHandle.ambientMap_sphere_mem_product hρ v u (mem_closedBall_zero_iff.mp hu)
  exact hblock ⟨hh.2, hh.1⟩

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.beltNeighborhoodHomeomorph_normal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
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
def Smale.ManifoldMorse.MorseSurgeryData.beltNormalDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) : Set d.UpperLevel :=
  (Subtype.val : d.UpperLevel → M) ⁻¹' d.chart.splitChart.source

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.beltNormal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    d.UpperLevel → d.chart.NegativeCoordinates := fun x => (d.chart.splitChart (x : M)).1

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.isOpen_beltNormalDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) : IsOpen d.beltNormalDomain :=
  d.chart.splitChart.open_source.preimage continuous_subtype_val

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.belt_model_mem_target {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
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
theorem Smale.ManifoldMorse.MorseSurgeryData.belt_mem_normalDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.surgery.beltSphere v ∈ d.beltNormalDomain := by
  change (d.surgery.beltSphere v : M) ∈ d.chart.splitChart.source
  rw [d.belt_eq, d.chart.beltCoreMap_coe]
  exact d.chart.splitChart.map_target' (d.belt_model_mem_target v)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.belt_split_coordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.chart.splitChart (d.surgery.beltSphere v : M) =
      (0, d.radius • (v : d.chart.PositiveCoordinates)) := by
  rw [d.belt_eq, d.chart.beltCoreMap_coe]
  exact d.chart.splitChart.right_inv' (d.belt_model_mem_target v)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.beltNormal_belt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltNormal (d.surgery.beltSphere v) = 0 := by
  change (d.chart.splitChart (d.surgery.beltSphere v : M)).1 = 0
  rw [d.belt_split_coordinates]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.beltNormal_eq_zero_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) {x : d.UpperLevel}
    (hx : x ∈ d.beltNormalDomain) : d.beltNormal x = 0 ↔ x ∈ Set.range d.surgery.beltSphere := by
  constructor
  · intro hzero
    let z := d.chart.splitChart (x : M)
    have hz₁ : z.1 = 0 := hzero
    have heq := d.chart.splitChart_equation hx
    change f (x : M) = f p - ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 at heq
    rw [hz₁, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, x.property] at heq
    have hnorm : ‖z.2‖ = d.radius := by nlinarith [norm_nonneg z.2, d.radius_pos]
    let v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates :=
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
theorem Smale.ManifoldMorse.MorseSurgeryData.contMDiffOn_beltNormal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffOn 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ d.beltNormal
      d.beltNormalDomain := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  have hcoords :
    ContMDiffOn 𝓘(ℝ, Smale.RegularLevel.Model E)
      𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
      (d.chart.splitChart ∘ (Subtype.val : d.UpperLevel → M)) d.beltNormalDomain :=
    d.chart.splitChart.contMDiffOn_toFun.comp
      (Smale.RegularLevel.contMDiff_inclusion hf d.upper_regular).contMDiffOn (fun _ hx => hx)
  exact contDiff_fst.contMDiff.comp_contMDiffOn hcoords

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.beltNormal_derivative_comp_belt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    (mfderiv 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
            (d.surgery.beltSphere v)).comp
        (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) d.surgery.beltSphere v) =
      0 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
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

def Smale.NativeParametrization.translation {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : D) : Diffeomorph 𝓘(ℝ, D) 𝓘(ℝ, D) D D ∞
    where
  toEquiv :=
    { toFun := fun x => x + a
      invFun := fun x => x - a
      left_inv := fun _ => add_sub_cancel_right _ _
      right_inv := fun _ => sub_add_cancel _ _ }
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

def Smale.NativeParametrization.centered {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] (x : N) :
    PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, D) D N ∞ :=
  let c := NoExotic.modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  (translation (c x)).toPartialDiffeomorph.trans c.symm

theorem Smale.NativeParametrization.zero_mem_centered_source {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : (0 : D) ∈ (centered (D := D) x).source := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  refine ⟨Set.mem_univ _, ?_⟩
  change 0 + c x ∈ c.target
  rw [zero_add]
  exact c.map_source' (mem_extChartAt_source x)

theorem Smale.NativeParametrization.centered_zero {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : centered (D := D) x (0 : D) = x := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  change c.symm (0 + c x) = x
  rw [zero_add]
  exact c.left_inv' (mem_extChartAt_source x)

theorem Smale.NativeParametrization.mem_centered_target {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : x ∈ (centered (D := D) x).target := by
  have hx := (centered (D := D) x).map_source' (zero_mem_centered_source (D := D) x)
  rwa [centered_zero] at hx

theorem Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.mapsTo_superset {E H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace X] [ChartedSpace H X] {e : Diffeomorph I I X X ∞} {K S : Set X}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K S) {U : Set X} (hKU : K ⊆ U)
    (t : ℝ) : Set.MapsTo (fun x => A.family (t, x)) U U := by
  obtain ⟨d, hd⟩ := A.slices t
  have hfix : ∀ x ∉ U, d x = x := by
    intro x hx
    exact (hd x).trans (A.fixedOutside t x (fun h => hx (hKU h)))
  intro x hx
  change A.family (t, x) ∈ U
  rw [← hd]
  exact Smale.SupportedDiffeomorph.mapsTo_of_fixed_outside d.toEquiv hfix hx

def Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.extension {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    {e : Diffeomorph I I X X ∞} {K S : Set X}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K S)
    (Φ : PartialDiffeomorph I J X Y ∞) (hK : IsCompact K) (hKsource : K ⊆ Φ.source) {T : Set Y}
    (hfixed : ∀ x ∈ Φ.source, Φ x ∈ T → x ∈ S) :
    Smale.SupportedDiffeomorph.SupportedRelativeIsotopy
      (Smale.SupportedDiffeomorph.extension Φ e hK hKsource A.endpoint_fixed_outside) (Φ '' K) T
    where
  family := fun p => Smale.SupportedDiffeomorph.extendMap Φ (fun x => A.family (p.1, x)) p.2
  smooth :=
    Smale.SupportedDiffeomorph.contMDiff_extendFamily Φ A.smooth hK hKsource A.fixedOutside
      (A.mapsTo_superset hKsource)
  zero := by
    intro y
    have heq : (fun x => A.family (0, x)) = id := funext A.zero
    rw [heq]
    exact Smale.SupportedDiffeomorph.extendMap_id Φ y
  one := by
    intro y
    exact congrArg (fun f : X → X => Smale.SupportedDiffeomorph.extendMap Φ f y) (funext A.one)
  slices := by
    intro t
    obtain ⟨d, hd⟩ := A.slices t
    have hfix : ∀ x ∉ K, d x = x := fun x hx => (hd x).trans (A.fixedOutside t x hx)
    exact
      ⟨Smale.SupportedDiffeomorph.extension Φ d hK hKsource hfix, fun y =>
        congrArg (fun f : X → X => Smale.SupportedDiffeomorph.extendMap Φ f y) (funext hd)⟩
  fixedOutside := fun t y hy =>
    Smale.SupportedDiffeomorph.extendMap_eq_of_notMem_image Φ (A.fixedOutside t) hy
  fixedOn := by
    intro t y hy
    by_cases hyt : y ∈ Φ.target
    · rw [Smale.SupportedDiffeomorph.extendMap_of_mem Φ _ hyt]
      have hsource : Φ.symm y ∈ Φ.source := Φ.map_target' hyt
      have hi : Φ (Φ.symm y) = y := Φ.right_inv' hyt
      have hs : Φ.symm y ∈ S := hfixed (Φ.symm y) hsource (hi.symm ▸ hy)
      rw [A.fixedOn t (Φ.symm y) hs]
      exact hi
    · exact Smale.SupportedDiffeomorph.extendMap_of_notMem Φ _ hyt

def Smale.SupportedDiffeomorph.normalBumpFamily {E F H M P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (p : ℝ × (M × P)) : M × P :=
  (bumpFamily Φ β (-(Real.smoothTransition p.1 • b p.2.2), p.2.1), p.2.2)

theorem Smale.SupportedDiffeomorph.normalBumpFamily_normal {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (t : ℝ) (z : M × P) :
    (normalBumpFamily Φ β b (t, z)).2 = z.2 :=
  rfl

theorem Smale.SupportedDiffeomorph.normalBumpFamily_zero {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (z : M × P) :
    normalBumpFamily Φ β b (0, z) = z := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition 0 • b z.2), z.1) = z.1
    rw [Real.smoothTransition.zero, zero_smul, neg_zero, bumpFamily_zero]
  · rfl

theorem Smale.SupportedDiffeomorph.normalBumpFamily_fixed_fiber {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) {u : P} (hu : b u = 0)
    (t : ℝ) (x : M) : normalBumpFamily Φ β b (t, (x, u)) = (x, u) := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition t • b u), x) = x
    rw [hu, smul_zero, neg_zero, bumpFamily_zero]
  · rfl

theorem Smale.SupportedDiffeomorph.normalBumpFamily_fixed_outside {E F H M P : Type*}
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

theorem Smale.SupportedDiffeomorph.normalBumpFamily_chart {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) {x : E} (hx : x ∈ Φ.source)
    (u : P) : normalBumpFamily Φ β b (1, (Φ x, u)) = (Φ (x - β x • b u), u) := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition 1 • b u), Φ x) = _
    rw [Real.smoothTransition.one, one_smul, bumpFamily_chart Φ β _ hx, smul_neg, ←
      sub_eq_add_neg]
  · rfl

theorem Smale.SupportedDiffeomorph.exists_radius_normalBumpFamily {E F H M P : Type*}
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
    exact ⟨Smale.FiberwiseDiffeomorph.diffeomorph ht hslices, fun _ => rfl⟩
  · exact
      (hcompact.isCompact.image_of_continuousOn
            (Φ.contMDiffOn_toFun.continuousOn.mono hsupport)).prod
        hbcompact.isCompact

theorem Smale.exists_small_supported_germ {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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

theorem Smale.SupportedDiffeomorph.exists_supported_shear_isotopy {E F : Type*}
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
    Smale.exists_compact_smooth_cutoff (K := {(0 : E)}) isCompact_singleton Metric.isOpen_ball
      (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hρ))
  let Φ := (Diffeomorph.refl 𝓘(ℝ, E) E ∞).toPartialDiffeomorph
  obtain ⟨ε, hε, hfamily⟩ :=
    exists_radius_normalBumpFamily (P := F) Φ hβ hβcompact
      (show tsupport β ⊆ Φ.source from Set.subset_univ _)
  obtain ⟨b, hb, hbcompact, hbsupport, hbsmall, hbeq, hbzero⟩ :=
    Smale.exists_small_supported_germ Metric.isOpen_ball (Metric.mem_ball_self hρ)
      (show ContDiffOn ℝ ∞ (fun y : F => -(L y)) (Metric.ball 0 ρ) from L.contDiff.neg.contDiffOn)
      (show -(L (0 : F)) = 0 by simp) hε
  obtain ⟨hAprod, hdiffprod, hK⟩ := hfamily b hb hbcompact hbsmall
  let A := normalBumpFamily Φ β b
  let K : Set (E × F) := (Φ '' tsupport β) ×ˢ tsupport b
  let V := Smale.PartialChart.vectorProduct E F
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

def Degree.SupportedGerms.Realizes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (f : E → E) : Prop :=
  ∃ (d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E),
    IsCompact K ∧
      K ⊆ U ∧
        Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy d K {0}) ∧
          (d : E → E) =ᶠ[𝓝 (0 : E)] f

theorem Degree.SupportedGerms.Realizes.comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {f g : E → E} (hf : Degree.SupportedGerms.Realizes U f)
    (hg : Degree.SupportedGerms.Realizes U g) : Degree.SupportedGerms.Realizes U (f ∘ g) := by
  obtain ⟨d, K, hK, hKU, ⟨A⟩, hd⟩ := hf
  obtain ⟨e, L, hL, hLU, ⟨B⟩, he⟩ := hg
  have he0 : e (0 : E) = 0 := B.endpoint_fixed_on 0 rfl
  have het : Filter.Tendsto e (𝓝 (0 : E)) (𝓝 0) := by
    simpa only [he0] using e.continuous.tendsto (0 : E)
  have C : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy (e.trans d) (K ∪ L) {0} := by
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

theorem Degree.SupportedGerms.Realizes.conj {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : E ≃L[ℝ] F) {U : Set E} {f : E → E}
    (hf : Degree.SupportedGerms.Realizes U f) :
    Degree.SupportedGerms.Realizes (c '' U) (fun y => c (f (c.symm y))) := by
  obtain ⟨d, K, hK, hKU, ⟨A⟩, hd⟩ := hf
  let D := (c.symm.toDiffeomorph.trans d).trans c.toDiffeomorph
  have B : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D (c '' K) {0} := by
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

theorem Degree.SupportedGerms.realizes_shear {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (L : F →L[ℝ] E) {U : Set (E × F)} (hU : IsOpen U)
    (h0 : (0 : E × F) ∈ U) : Realizes U (fun p => (p.1 + L p.2, p.2)) := by
  obtain ⟨A, K, hK, hKU, hA, hA0, hdiff, hfix, -, hcore, hgerm⟩ :=
    Smale.SupportedDiffeomorph.exists_supported_shear_isotopy L hU h0
  obtain ⟨d, hd⟩ := hdiff 1
  have H : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy d K {0} := by
    refine ⟨A, hA, hA0, fun x => (hd x).symm, hdiff, hfix, ?_⟩
    intro t x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact hcore t 0
  refine ⟨d, K, hK, hKU, ⟨H⟩, ?_⟩
  filter_upwards [hgerm] with x hx
  exact (hd x).trans hx

theorem Degree.LinearFramePaths.diag2n_decompose {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}
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

theorem Degree.LinearFramePaths.joined_one_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
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

theorem Degree.LinearFramePaths.joined_one_specialLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
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

def Degree.SupportedGerms.coordinateSplit {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
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

theorem Degree.SupportedGerms.realizes_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
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

theorem Degree.SupportedGerms.realizes_specialLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
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
    rw [Degree.LinearFramePaths.diag2n_decompose hij a ha]
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

theorem Degree.SupportedGerms.realizes_det_one {ι : Type*} [Finite ι] [Nontrivial ι] {E : Type*}
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

theorem Smale.SmallPerturbation.lipschitzWith_cutoff_smul {P E : Type*} [PseudoMetricSpace P]
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

theorem Smale.SmallPerturbation.exists_closedBall_small_lipschitz_of_fderiv_zero {P E : Type*}
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

theorem Smale.SmallPerturbation.exists_lipschitz_supported_germ {P E : Type*}
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
    Smale.exists_compact_smooth_cutoff (K := {(0 : P)}) (U := Metric.ball (0 : P) 1)
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

theorem Smale.SmallPerturbation.exists_supported_tangent_identity_isotopy {E : Type*}
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
    exact ⟨diffeomorphIdAdd hs hlip hsmall, fun _ => rfl⟩
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

theorem Smale.SmallPerturbation.exists_relative_tangent_identity_isotopy {E F : Type*}
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

theorem Smale.SmallPerturbation.fderiv_preserves_projection {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : DifferentiableAt ℝ f 0) (Q : E →L[ℝ] F)
    (hQ : ∀ x ∈ U, Q (f x) = Q x) : Q.comp (fderiv ℝ f 0) = Q := by
  have heq : Q ∘ f =ᶠ[𝓝 (0 : E)] Q := by
    filter_upwards [hU.mem_nhds hzero] with x hx
    exact hQ x hx
  have hc : fderiv ℝ (Q ∘ f) 0 = Q.comp (fderiv ℝ f 0) :=
    (Q.hasFDerivAt.comp 0 hf.hasFDerivAt).fderiv
  exact hc.symm.trans (heq.fderiv_eq.trans Q.fderiv)

theorem Smale.SmallPerturbation.fderiv_fixes_subspace {E : Type*} [NormedAddCommGroup E]
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

theorem Smale.SmallPerturbation.exists_relative_germ_linearization_isotopy {E F : Type*}
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

theorem Degree.SupportedGerms.realizes_local_germ {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite ι] [Nontrivial ι] (b : Module.Basis ι ℝ E)
    {f : E → E} {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf0 : f 0 = 0) (hbij : Function.Bijective (fderiv ℝ f 0))
    (hdet : (fderiv ℝ f 0).toLinearMap.det = 1) : Realizes U f := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨C, A, K, hC, -, -, hK, hKU, hA, hA0, hdiff, hfix, -, hfixed, hgerm⟩ :=
    Smale.SmallPerturbation.exists_relative_germ_linearization_isotopy hU h0 hf hf0 hbij
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
  have H : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy d K {0} := by
    refine ⟨A, hA, hA0, fun x => (hd x).symm, hdiff, hfix, ?_⟩
    intro t x hx
    exact hfixed t x (Set.mem_singleton_iff.mp hx)
  have hdreal : Realizes U (fun x => A (1, x)) :=
    ⟨d, K, hK, hKU, ⟨H⟩, Filter.Eventually.of_forall hd⟩
  obtain ⟨D, L, hL, hLU, hH, hDgerm⟩ := (realizes_det_one b C hCdet hU h0).comp hdreal
  exact ⟨D, L, hL, hLU, hH, hDgerm.trans hgerm.symm⟩

def Degree.LinearFramePaths.scalarDiagonal {ι : Type*} [DecidableEq ι] (i : ι) (a : ℝ) :
    Matrix ι ι ℝ :=
  Matrix.diagonal (fun k => if k = i then a else 1)

theorem Degree.LinearFramePaths.det_scalarDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (a : ℝ) : Matrix.det (scalarDiagonal i a) = a := by simp [scalarDiagonal, Matrix.det_diagonal]

theorem Degree.LinearFramePaths.scalarDiagonal_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (a b : ℝ) : scalarDiagonal i a * scalarDiagonal i b = scalarDiagonal i (a * b) := by
  rw [scalarDiagonal, scalarDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i <;> simp [h]

theorem Degree.LinearFramePaths.scalarDiagonal_one {ι : Type*} [DecidableEq ι] (i : ι) :
    scalarDiagonal i 1 = 1 := by simp [scalarDiagonal]

theorem Degree.LinearFramePaths.continuous_scalarDiagonal {ι : Type*} [DecidableEq ι] (i : ι) :
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

def Degree.LinearFramePaths.determinantComponent {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ℝ) :
    TopologicalSpace.Opens (Matrix ι ι ℝ) :=
  ⟨{A | 0 < σ * Matrix.det A},
    isOpen_lt continuous_const (continuous_const.mul continuous_id.matrix_det)⟩

def Degree.LinearFramePaths.diagonalPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) {σ : ℝ}
    (A : determinantComponent (ι := ι) σ) : determinantComponent (ι := ι) σ :=
  ⟨scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)),
    by
    change 0 < σ * Matrix.det (scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)))
    rw [det_scalarDiagonal]
    exact A.property⟩

theorem Degree.LinearFramePaths.joined_diagonal_to_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
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

theorem Degree.LinearFramePaths.joined_diagonal_points {ι : Type*} [Fintype ι] [DecidableEq ι]
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

theorem Degree.LinearFramePaths.joined_determinantComponent {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nontrivial ι] {σ : ℝ} (A B : determinantComponent (ι := ι) σ) : Joined A B :=
  by
  let i := Classical.choice (inferInstance : Nonempty ι)
  exact
    (joined_diagonal_to_matrix i A).symm.trans
      ((joined_diagonal_points i A B).trans (joined_diagonal_to_matrix i B))

theorem Degree.SupportedGerms.exists_linearEquiv_with_det {B ι : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [Finite ι] (b : Module.Basis ι ℝ B) (i : ι) {r : ℝ}
    (hr : r ≠ 0) : ∃ R : B ≃L[ℝ] B, R.toLinearMap.det = r := by
  classical
  let := Fintype.ofFinite ι
  let L : B →ₗ[ℝ] B := Matrix.toLin b b (Degree.LinearFramePaths.scalarDiagonal i r)
  have hdet : L.det = r := by
    rw [← LinearMap.det_toMatrix b L]
    change
      Matrix.det
          (LinearMap.toMatrix b b
            (Matrix.toLin b b (Degree.LinearFramePaths.scalarDiagonal i r))) =
        r
    rw [LinearMap.toMatrix_toLin]
    exact Degree.LinearFramePaths.det_scalarDiagonal i r
  have hker : L.ker = ⊥ := by
    by_contra hk
    exact hr (hdet.symm.trans (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk))
  have hi : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  have hbij : Function.Bijective L :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩
  exact ⟨(LinearEquiv.ofBijective L hbij).toContinuousLinearEquiv, hdet⟩

theorem Degree.SupportedGerms.exists_normal_det_correction {A B ι : Type*} [NormedAddCommGroup A]
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

theorem Degree.SupportedGerms.exists_supported_disk_germ_alignment {A B ι κ : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [Finite ι] [Finite κ] [Nontrivial κ]
    (b : Module.Basis ι ℝ B) (i : ι) (basis : Module.Basis κ ℝ (A × B))
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ Φ.source) (hΦ0 : Φ 0 = 0) {U : Set (A × B)} (hU : IsOpen U)
    (h0U : (0 : A × B) ∈ U) :
    ∃ (d : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞) (K : Set (A × B)),
      IsCompact K ∧
        K ⊆ U ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy d K {0}) ∧
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
    have hh := Smale.PartialChart.bijective_mfderiv Φ.symm ht0
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

theorem Degree.SupportedGerms.exists_native_disk_germ_alignment {A B E H M ι κ : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [Finite ι] [Finite κ] [Nontrivial κ] (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B)) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, A × B) J (A × B) M ∞)
    (hΦ0 : (0 : A × B) ∈ Φ.source) (hΨ0 : (0 : A × B) ∈ Ψ.source) (hcenter : Φ 0 = Ψ 0) :
    ∃ (D : Diffeomorph J J M M ∞) (K : Set M),
      IsCompact K ∧
        K ⊆ Ψ.target ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K {Ψ 0}) ∧
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
  let D := Smale.SupportedDiffeomorph.extension Ψ d hL hLsource Hiso.endpoint_fixed_outside
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
        (Smale.SupportedDiffeomorph.extension_chart Ψ d hL hLsource Hiso.endpoint_fixed_outside
          (Ψ.map_target' ht))
      _ = Ψ (x, 0) := congrArg Ψ hx

def Smale.SmoothRadial.radialMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (φ : ℝ → ℝ)
    (x : N) : N :=
  φ (‖x‖ ^ 2) • x

theorem Smale.SmoothRadial.norm_radialMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (x : N) : ‖radialMap φ x‖ = φ (‖x‖ ^ 2) * ‖x‖ := by
  rw [radialMap, norm_smul, Real.norm_eq_abs, abs_of_pos (hpos _)]

theorem Smale.SmoothRadial.radius_strictMono {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) : StrictMonoOn (fun r => φ (r ^ 2) * r) (Set.Ici 0) := by
  intro r hr s hs hrs
  have hsq : r ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hr hs).mpr hrs.le
  exact (mul_lt_mul_of_pos_left hrs (hpos _)).trans_le (mul_le_mul_of_nonneg_right (hmono hsq) hs)

theorem Smale.SmoothRadial.radialMap_injective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) :
    Function.Injective (radialMap (N := N) φ) := by
  intro x y hxy
  have hn : ‖x‖ = ‖y‖ := by
    apply (radius_strictMono hpos hmono).injOn (norm_nonneg x) (norm_nonneg y)
    simpa only [norm_radialMap hpos] using congrArg Norm.norm hxy
  change φ (‖x‖ ^ 2) • x = φ (‖y‖ ^ 2) • y at hxy
  rw [hn] at hxy
  exact smul_right_injective N (hpos _).ne' hxy

theorem Smale.SmoothRadial.radialMap_surjective {N : Type*} [NormedAddCommGroup N]
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

theorem Smale.SmoothRadial.contDiff_radialMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (radialMap (N := N) φ) :=
  (hφ.comp (contDiff_id.norm_sq ℝ)).smul contDiff_id

theorem Smale.SmoothRadial.fderiv_radialMap_apply {N : Type*} [NormedAddCommGroup N]
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

theorem Smale.SmoothRadial.fderiv_radialMap_injective {N : Type*} [NormedAddCommGroup N]
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

theorem Smale.SmoothRadial.isInvertible_fderiv_radialMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) (x : N) :
    (fderiv ℝ (radialMap (N := N) φ) x).IsInvertible := by
  let L :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (radialMap φ) x).toLinearMap
        (fderiv_radialMap_injective hφ hpos hmono x)).toContinuousLinearEquiv
  exact ⟨L, by ext v; rfl⟩

def Smale.SmoothRadial.diffeomorph {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    [FiniteDimensional ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) {R : ℝ} (hR : 0 < R) (hout : ∀ s, R ^ 2 ≤ s → φ s = 1) :
    Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞ := by
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) ∞ (radialMap (N := N) φ) := by
    intro x
    apply
      Smale.isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ x)
        (contDiff_radialMap hφ).contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv]
    exact isInvertible_fderiv_radialMap hφ hpos hmono x
  exact
    hlocal.diffeomorphOfBijective
      ⟨radialMap_injective hpos hmono, radialMap_surjective hφ.continuous hR hout⟩

def Smale.SmoothRadial.shrinkTimeFactor (a t : ℝ) : ℝ :=
  1 + (a - 1) * Real.smoothTransition t

theorem Smale.SmoothRadial.shrinkTimeFactor_bounds {a : ℝ} (ha₁ : a ≤ 1) (t : ℝ) :
    a ≤ shrinkTimeFactor a t ∧ shrinkTimeFactor a t ≤ 1 := by
  have ht₀ := Real.smoothTransition.nonneg t
  have ht₁ := Real.smoothTransition.le_one t
  unfold shrinkTimeFactor
  constructor <;> nlinarith

theorem Smale.SmoothRadial.shrinkTimeFactor_zero (a : ℝ) : shrinkTimeFactor a 0 = 1 := by
  simp only [shrinkTimeFactor, Real.smoothTransition.zero, MulZeroClass.mul_zero, add_zero]

theorem Smale.SmoothRadial.shrinkTimeFactor_one (a : ℝ) : shrinkTimeFactor a 1 = a := by
  simp only [shrinkTimeFactor, Real.smoothTransition.one, mul_one]
  ring

theorem Smale.SmoothRadial.contDiff_shrinkTimeFactor (a : ℝ) :
    ContDiff ℝ ∞ (shrinkTimeFactor a) :=
  contDiff_const.add (contDiff_const.mul (Real.smoothTransition.contDiff (n := ⊤)))

def Degree.DiskShrinking.scale (R a s : ℝ) : ℝ :=
  a + (1 - a) * Real.smoothTransition ((s - 1) / (R ^ 2 - 1))

theorem Degree.DiskShrinking.contDiff_scale (R a : ℝ) : ContDiff ℝ ∞ (scale R a) :=
  contDiff_const.add
    (contDiff_const.mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp
        ((contDiff_id.sub contDiff_const).div_const _)))

theorem Degree.DiskShrinking.scale_pos {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (R s : ℝ) :
    0 < scale R a s :=
  add_pos_of_pos_of_nonneg ha (mul_nonneg (sub_nonneg.mpr ha₁) (Real.smoothTransition.nonneg _))

theorem Degree.DiskShrinking.scale_monotone {R a : ℝ} (hR : 1 < R) (ha₁ : a ≤ 1) :
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

theorem Degree.DiskShrinking.scale_inner {R : ℝ} (hR : 1 < R) (a : ℝ) {s : ℝ} (hs : s ≤ 1) :
    scale R a s = a := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  rw [scale,
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hden.le)]
  simp only [MulZeroClass.mul_zero, add_zero]

theorem Degree.DiskShrinking.scale_outer {R : ℝ} (hR : 1 < R) (a : ℝ) {s : ℝ} (hs : R ^ 2 ≤ s) :
    scale R a s = 1 := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  rw [scale, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hden).mpr (by linarith))]
  ring

theorem Degree.DiskShrinking.scale_one (R s : ℝ) : scale R 1 s = 1 := by
  simp only [scale, sub_self, MulZeroClass.zero_mul, add_zero]

def Degree.DiskShrinking.family {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (R a : ℝ) (p : ℝ × N) : N :=
  Smale.SmoothRadial.radialMap (scale R (Smale.SmoothRadial.shrinkTimeFactor a p.1)) p.2

theorem Degree.DiskShrinking.contMDiff_family {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (R a : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, N) ∞ (family (N := N) R a) := by
  have ht :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => Smale.SmoothRadial.shrinkTimeFactor a p.1) :=
    (Smale.SmoothRadial.contDiff_shrinkTimeFactor a).contMDiff.comp contMDiff_fst
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

theorem Degree.DiskShrinking.family_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (R a : ℝ) (x : N) : family R a (0, x) = x := by
  simp only [family, Smale.SmoothRadial.shrinkTimeFactor_zero, Smale.SmoothRadial.radialMap,
    scale_one, one_smul]

theorem Degree.DiskShrinking.family_slices {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {R a : ℝ} (hR : 1 < R) (ha : 0 < a)
    (ha₁ : a ≤ 1) (t : ℝ) :
    ∃ D : Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞, ∀ x, D x = family R a (t, x) := by
  have ht := Smale.SmoothRadial.shrinkTimeFactor_bounds ha₁ t
  exact
    ⟨Smale.SmoothRadial.diffeomorph (contDiff_scale R _) (scale_pos (ha.trans_le ht.1) ht.2 R)
        (scale_monotone hR ht.2) (zero_lt_one.trans hR) (fun _ hs => scale_outer hR _ hs),
      fun _ => rfl⟩

theorem Degree.DiskShrinking.family_outer {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {R : ℝ} (hR : 1 < R) (a t : ℝ) {x : N}
    (hx : R ≤ ‖x‖) : family R a (t, x) = x := by
  rw [family, Smale.SmoothRadial.radialMap,
    scale_outer hR _ ((sq_le_sq₀ (zero_lt_one.trans hR).le (norm_nonneg x)).mpr hx), one_smul]

theorem Degree.DiskShrinking.family_one_inner {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {R : ℝ} (hR : 1 < R) (a : ℝ) {x : N}
    (hx : ‖x‖ ≤ 1) : family R a (1, x) = a • x := by
  rw [family, Smale.SmoothRadial.radialMap, Smale.SmoothRadial.shrinkTimeFactor_one,
    scale_inner hR a (by nlinarith [norm_nonneg x])]

theorem Degree.DiskShrinking.family_origin {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (R a t : ℝ) : family R a (t, (0 : N)) = 0 := by
  simp only [family, Smale.SmoothRadial.radialMap, smul_zero]

theorem Degree.DiskShrinking.exists_larger_closedBall_subset {D : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {U : Set D} (hU : IsOpen U)
    (hunit : Metric.closedBall (0 : D) 1 ⊆ U) :
    ∃ R : ℝ, 1 < R ∧ Metric.closedBall (0 : D) R ⊆ U := by
  let T : Set ℝ := {r | ∀ x ∈ Metric.closedBall (0 : D) 1, r • x ∈ U}
  have hT : IsOpen T :=
    Smale.MorsePerturbation.isOpen_forall_mem_compact (ProperSpace.isCompact_closedBall (0 : D) 1)
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

theorem Degree.DiskShrinking.exists_disk_ellipsoid_in_open {D Z : Type*} [NormedAddCommGroup D]
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

theorem Smale.SupportedDiffeomorph.exists_supported_isotopy_extension {E F H H' X Y : Type*}
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

theorem Degree.DiskShrinking.exists_chart_disk_shrinking {D Z E H M : Type*}
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
            Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy P K {Φ (0, 0)}) ∧
              ∀ x : D, ‖x‖ ≤ 1 → P (Φ (x, 0)) = Φ (a • x, 0) := by
  obtain ⟨R, hR, L, hLzero, hLsource⟩ := exists_disk_ellipsoid_in_open Φ.open_source hzero
  let Ψ := L.toDiffeomorph.toPartialDiffeomorph.trans Φ
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
    Smale.SupportedDiffeomorph.exists_supported_isotopy_extension Ψ (contMDiff_family R a)
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

theorem Smale.SupportedDiffeomorph.IsotopicToIdentity.symm {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] {e : Diffeomorph J J M M ∞}
    (he : Smale.SupportedDiffeomorph.IsotopicToIdentity e) :
    Smale.SupportedDiffeomorph.IsotopicToIdentity e.symm := by
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

theorem Degree.SupportedGerms.exists_disk_chart_isotopy {A B E H M ι κ : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [Finite ι] [Finite κ] [Nontrivial κ] (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B)) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, A × B) J (A × B) M ∞)
    (hΦ : Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} ⊆ Φ.source)
    (hΨ : Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} ⊆ Ψ.source) (hcenter : Φ 0 = Ψ 0) :
    ∃ D : Diffeomorph J J M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity D ∧
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
  obtain ⟨KΦ, -, -, P, ⟨HP⟩, hP⟩ := Degree.DiskShrinking.exists_chart_disk_shrinking Φ hΦ ha ha1
  obtain ⟨KΨ, -, -, Q, ⟨HQ⟩, hQ⟩ := Degree.DiskShrinking.exists_chart_disk_shrinking Ψ hΨ ha ha1
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

theorem Degree.DiskShrinking.exists_embedded_disk_isotopy_of_same_center {D E M : Type*}
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
      Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧
        ∀ x ∈ Metric.closedBall (0 : D) 1, P (f x) = g x := by
  classical
  let B := EuclideanSpace ℝ (Fin n)
  obtain ⟨ε, hε, Φ, hΦprod, hΦzero, -⟩ :=
    Smale.exists_tubularNeighborhood_in_open_of_embedded_closedBall hf hfi hfd n hdim isOpen_univ
      (Set.mapsTo_univ _ _)
  obtain ⟨δ, hδ, Ψ, hΨprod, hΨzero, -⟩ :=
    Smale.exists_tubularNeighborhood_in_open_of_embedded_closedBall hg hgi hgd n hdim isOpen_univ
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
    Degree.SupportedGerms.exists_disk_chart_isotopy (Module.finBasis ℝ B) ⟨0, hB⟩
      (Module.finBasis ℝ (D × B)) Φ Ψ hΦ hΨ hcenter'
  refine ⟨P, hP, ?_⟩
  intro x hx
  rw [← hΦzero x hx, hformula x hx, hΨzero x hx]

theorem Smale.SupportedDiffeomorph.exists_supported_pointMoving {E F H M : Type*}
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

theorem Smale.SupportedDiffeomorph.exists_open_pointMoving {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ V : Set M,
      IsOpen V ∧
        x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) x
  let Φ := Smale.PartialChart.restrictTarget c.symm hU
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

theorem MorseCancel.exists_open_isotopic_pointMoving {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ V : Set M,
      IsOpen V ∧
        x ∈ V ∧
          V ⊆ U ∧
            ∀ y ∈ V,
              ∃ d : Diffeomorph J J M M ∞,
                Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) x
  let Φ := Smale.PartialChart.restrictTarget c.symm hU
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv' hxc
  have hxΦ : c x ∈ Φ.source := by
    refine ⟨c.map_source' hxc, ?_⟩
    change c.symm (c x) ∈ U
    rw [hcx]
    exact hx
  have hΦx : Φ (c x) = x := hcx
  obtain ⟨ε, hε, hball, hmove⟩ := Smale.SupportedDiffeomorph.exists_supported_pointMoving Φ hxΦ
  refine
    ⟨Φ '' Metric.ball (c x) ε,
      Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hball,
      ⟨c x, Metric.mem_ball_self hε, hΦx⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (Φ.map_source' (hball hv)).2
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨A, hA, hzero, hdiff, hfix, hend⟩ := hmove v hv
    obtain ⟨d, hd⟩ := hdiff 1
    refine ⟨d, ⟨A, hA, hzero, hd, hdiff⟩, ?_, ?_⟩
    · rw [hΦx] at hend
      exact (hd x).symm.trans hend
    · intro z hz
      exact (hd z).symm.trans (hfix 1 z (fun h => hz h.2))

theorem MorseCancel.exists_isotopic_two_points_in_dense {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {B : Set M} (hB : Dense B) {x y : M} (hxy : x ≠ y) :
    ∃ d : Diffeomorph J J M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧ d x ∈ B ∧ d y ∈ B := by
  obtain ⟨U, V, hU, hV, hx, hy, hdisj⟩ := t2_separation hxy
  obtain ⟨U', hU', hx', hU'U, hmoveU⟩ := exists_open_isotopic_pointMoving (J := J) hU hx
  obtain ⟨V', hV', hy', hV'V, hmoveV⟩ := exists_open_isotopic_pointMoving (J := J) hV hy
  obtain ⟨x', hx'B, hx'U⟩ := hB.exists_mem_open hU' ⟨x, hx'⟩
  obtain ⟨y', hy'B, hy'V⟩ := hB.exists_mem_open hV' ⟨y, hy'⟩
  obtain ⟨d, hd, hdx, hdfix⟩ := hmoveU x' hx'U
  obtain ⟨e, he, hey, hefix⟩ := hmoveV y' hy'V
  have hyU : y ∉ U := fun h => Set.disjoint_left.mp hdisj h hy
  have hxV : x' ∉ V := fun h => Set.disjoint_left.mp hdisj (hU'U hx'U) h
  refine ⟨d.trans e, hd.trans he, ?_, ?_⟩
  · change e (d x) ∈ B
    rw [hdx, hefix x' hxV]
    exact hx'B
  · change e (d y) ∈ B
    rw [hdfix y hyU, hey]
    exact hy'B

theorem MorseCancel.isotopicToIdentity_joined {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {d : Diffeomorph J J M M ∞} (hd : Smale.SupportedDiffeomorph.IsotopicToIdentity d) (x : M) :
    Joined x (d x) := by
  obtain ⟨A, hA, hzero, hone, -⟩ := hd
  exact
    ⟨{  toFun := fun t => A ((t : ℝ), x)
        continuous_toFun := hA.continuous.comp (continuous_subtype_val.prodMk continuous_const)
        source' := hzero x
        target' := hone x }⟩

def MorseCancel.isotopicPointOrbit {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (J : ModelWithCorners ℝ E H)
    (U : Set M) (x : M) : Set M :=
  {y |
    y ∈ U ∧
      ∃ d : Diffeomorph J J M M ∞,
        Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z}

theorem MorseCancel.isOpen_isotopicPointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (isotopicPointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, d, hd, hdx, hdfix⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_isotopic_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  obtain ⟨e, he, hey, hefix⟩ := hmove z hz
  refine ⟨hVU hz, d.trans e, hd.trans he, ?_, ?_⟩
  · change e (d x) = z
    rw [hdx, hey]
  · intro w hw
    change e (d w) = w
    rw [hdfix w hw, hefix w hw]

theorem MorseCancel.isOpen_sdiff_isotopicPointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (U \ isotopicPointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, hyOrbit⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_isotopic_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  refine ⟨hVU hz, ?_⟩
  rintro ⟨_, d, hd, hdx, hdfix⟩
  obtain ⟨e, he, hey, hefix⟩ := hmove z hz
  apply hyOrbit
  refine ⟨hyU, d.trans e.symm, hd.trans he.symm, ?_, ?_⟩
  · change e.symm (d x) = y
    rw [hdx, ← hey, e.symm_apply_apply]
  · intro w hw
    change e.symm (d w) = w
    rw [hdfix w hw]
    exact Smale.SupportedDiffeomorph.inverse_fixed_outside e.toEquiv hefix w hw

theorem MorseCancel.exists_isotopic_pointMoving_of_preconnected {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold J ∞ M] [T2Space M] {U A : Set M} (hU : IsOpen U) (hA : IsPreconnected A)
    (hAU : A ⊆ U) {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
    ∃ d : Diffeomorph J J M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z := by
  have hxOrbit : x ∈ isotopicPointOrbit J U x :=
    ⟨hAU hx, Diffeomorph.refl J M ∞, Smale.SupportedDiffeomorph.isotopicToIdentity_refl, rfl,
      fun _ _ => rfl⟩
  have hcover : A ⊆ isotopicPointOrbit J U x ∪ (U \ isotopicPointOrbit J U x) := by
    intro z hz
    by_cases hh : z ∈ isotopicPointOrbit J U x
    · exact Or.inl hh
    · exact Or.inr ⟨hAU hz, hh⟩
  have hdisjoint : Disjoint (isotopicPointOrbit J U x) (U \ isotopicPointOrbit J U x) := by
    rw [Set.disjoint_left]
    exact fun _ hz hw => hw.2 hz
  have hsub :=
    hA.subset_left_of_subset_union (isOpen_isotopicPointOrbit hU x)
      (isOpen_sdiff_isotopicPointOrbit hU x) hdisjoint hcover ⟨x, hx, hxOrbit⟩
  exact (hsub hy).2

theorem MorseCancel.exists_isotopic_pointMoving_of_path {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) {x y : M} (γ : Path x y) (hγ : ∀ t, γ t ∈ U) :
    ∃ d : Diffeomorph J J M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z := by
  apply
    exists_isotopic_pointMoving_of_preconnected (J := J) hU
      (isConnected_range γ.continuous).isPreconnected
      (show Set.range γ ⊆ U from by rintro _ ⟨t, rfl⟩; exact hγ t)
  · exact ⟨0, γ.source⟩
  · exact ⟨1, γ.target⟩

def Smale.CurveImmersion.smoothTime (t : ℝ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (Real.smoothTransition t)

theorem Smale.CurveImmersion.contMDiff_smoothTime : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ smoothTime := by
  let : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc (0 : ℝ) 1 zero_le_one) (Set.Icc 0 1) :=
    contMDiffOn_projIcc
  have ht : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  apply contMDiffOn_univ.mp
  exact
    hp.comp ht.contMDiff.contMDiffOn
      (fun t _ => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩)

theorem Smale.CurveImmersion.smoothTime_zero : smoothTime 0 = 0 := by
  apply Subtype.ext
  simp [smoothTime]

theorem Smale.CurveImmersion.smoothTime_one : smoothTime 1 = 1 := by
  apply Subtype.ext
  simp [smoothTime]

theorem Smale.exists_smooth_connecting_curve {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {x y : N} (γ : Path x y) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧ f 0 = x ∧ f 1 = y := by
  let Z := EuclideanSpace ℝ (Fin 0)
  let f₀ : C(Z, N) := ContinuousMap.const Z x
  let f₁ : C(Z, N) := ContinuousMap.const Z y
  let H : f₀.Homotopy f₁ :=
    { toFun := fun q => γ q.1
      continuous_toFun := γ.continuous.comp continuous_fst
      map_zero_left := fun _ => γ.source
      map_one_left := fun _ => γ.target }
  obtain ⟨H', hH', -, -⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars (I := 𝓘(ℝ, Z)) (J := J) contMDiff_const
      contMDiff_const H
  let f : ℝ → N := fun t => H' (CurveImmersion.smoothTime t, (0 : Z))
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f :=
    hH'.comp (CurveImmersion.contMDiff_smoothTime.prodMk contMDiff_const)
  refine ⟨⟨f, hf.continuous⟩, hf, ?_, ?_⟩
  · change H' (CurveImmersion.smoothTime 0, (0 : Z)) = x
    rw [CurveImmersion.smoothTime_zero, H'.apply_zero]
    rfl
  · change H' (CurveImmersion.smoothTime 1, (0 : Z)) = y
    rw [CurveImmersion.smoothTime_one, H'.apply_one]
    rfl

def Smale.SupportedDiffeomorph.pointOrbit {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (J : ModelWithCorners ℝ E H)
    (U : Set M) (x : M) : Set M :=
  {y | y ∈ U ∧ ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z}

theorem Smale.SupportedDiffeomorph.isOpen_pointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (pointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, d, hd, hdfix⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  obtain ⟨e, he, hefix⟩ := hmove z hz
  refine ⟨hVU hz, d.trans e, ?_, ?_⟩
  · change e (d x) = z
    rw [hd, he]
  · intro w hw
    change e (d w) = w
    rw [hdfix w hw, hefix w hw]

theorem Smale.SupportedDiffeomorph.isOpen_sdiff_pointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (U \ pointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, hyOrbit⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  refine ⟨hVU hz, ?_⟩
  rintro ⟨_, d, hd, hdfix⟩
  obtain ⟨e, he, hefix⟩ := hmove z hz
  apply hyOrbit
  refine ⟨hyU, d.trans e.symm, ?_, ?_⟩
  · change e.symm (d x) = y
    rw [hd, ← he]
    exact e.toEquiv.symm_apply_apply y
  · intro w hw
    change e.symm (d w) = w
    rw [hdfix w hw]
    exact inverse_fixed_outside e.toEquiv hefix w hw

theorem Smale.SupportedDiffeomorph.exists_pointMoving_of_preconnected {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold J ∞ M] [T2Space M] {U S : Set M} (hU : IsOpen U) (hS : IsPreconnected S)
    (hSU : S ⊆ U) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  have hxOrbit : x ∈ pointOrbit J U x := ⟨hSU hx, Diffeomorph.refl J M ∞, rfl, fun _ _ => rfl⟩
  have hcover : S ⊆ pointOrbit J U x ∪ (U \ pointOrbit J U x) := by
    intro z hz
    by_cases h : z ∈ pointOrbit J U x
    · exact Or.inl h
    · exact Or.inr ⟨hSU hz, h⟩
  have hdisjoint : Disjoint (pointOrbit J U x) (U \ pointOrbit J U x) := by
    rw [Set.disjoint_left]
    exact fun _ hz hw => hw.2 hz
  have hsub :=
    hS.subset_left_of_subset_union (isOpen_pointOrbit hU x) (isOpen_sdiff_pointOrbit hU x)
      hdisjoint hcover ⟨x, hx, hxOrbit⟩
  exact (hsub hy).2

theorem Smale.SupportedDiffeomorph.exists_pointMoving_of_path {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold J ∞ M] [T2Space M] {U : Set M} (hU : IsOpen U) {x y : M} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ U) : ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  apply
    exists_pointMoving_of_preconnected (J := J) hU (isConnected_range γ.continuous).isPreconnected
      (show Set.range γ ⊆ U from by rintro _ ⟨t, rfl⟩; exact hγ t)
  · exact ⟨0, γ.source⟩
  · exact ⟨1, γ.target⟩

theorem Smale.exists_smooth_path_avoiding_finite {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {x y : N} (γ : Path x y) (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite)
    (hx : x ∉ S) (hy : y ∉ S) : ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, η t ∉ S := by
  let : Fintype S := hS.fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z S := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ S := IsManifold.of_discreteTopology _
  let g : C(S, N) := ⟨Subtype.val, continuous_subtype_val⟩
  have hg : ContMDiff 𝓘(ℝ, Z) J ∞ g := contMDiff_of_discreteTopology
  have hrange : Set.range g = S := by ext z; simp [g]
  obtain ⟨f, hf, hf0, hf1⟩ := exists_smooth_connecting_curve (J := J) γ
  let fI : C(unitInterval, N) := ⟨fun t => f t, f.continuous.comp continuous_subtype_val⟩
  have hfI : ContMDiff (𝓡∂ 1) J ∞ fI := hf.comp contMDiff_subtypeVal_Icc
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) + Module.finrank ℝ Z < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin]
    omega
  have hfixed : ∀ t ∈ ({0, 1} : Set unitInterval), fI t ∉ Set.range g := by
    intro t ht
    rw [hrange]
    rcases ht with rfl | ht
    · change f 0 ∉ S
      rw [hf0]
      exact hx
    · have ht1 : t = 1 := ht
      subst t
      change f 1 ∉ S
      rw [hf1]
      exact hy
  obtain ⟨f', hf', hrel, hdisjoint⟩ :=
    GeneralPosition.exists_disjoint_smooth_map_homotopicRel fI g hfI hg hdim'
      ((Set.finite_singleton (1 : unitInterval)).insert 0).isClosed hfixed
  have hf'0 : f' 0 = x := (hrel.fst_eq_snd (by simp)).symm.trans hf0
  have hf'1 : f' 1 = y := (hrel.fst_eq_snd (by simp)).symm.trans hf1
  let η : Path x y := { toContinuousMap := f', source' := hf'0, target' := hf'1 }
  refine ⟨η, hf', ?_⟩
  intro t ht
  rw [hrange] at hdisjoint
  exact Set.disjoint_left.mp hdisjoint ⟨t, rfl⟩ ht

theorem Smale.exists_pointMoving_fixing_finite {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {x y : N} (γ : Path x y) (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite)
    (hx : x ∉ S) (hy : y ∉ S) : ∃ d : Diffeomorph J J N N ∞, d x = y ∧ ∀ z ∈ S, d z = z := by
  obtain ⟨η, _, hη⟩ := exists_smooth_path_avoiding_finite (J := J) γ hdim hS hx hy
  obtain ⟨d, hd, hfix⟩ :=
    SupportedDiffeomorph.exists_pointMoving_of_path (J := J) hS.isClosed.isOpen_compl η hη
  exact ⟨d, hd, fun z hz => hfix z (fun hn => hn hz)⟩

def Smale.ChartMapPerturbation.collisionDomain {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) : Set (X × X) :=
  {q | f q.1 ∈ c.source ∧ f q.2 ∈ c.source ∧ β q.1 - β q.2 ≠ 0}

def Smale.ChartMapPerturbation.collisionParameter {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (q : X × X) : F :=
  (β q.1 - β q.2)⁻¹ • (c (f q.2) - c (f q.1))

theorem Smale.ChartMapPerturbation.isOpen_collisionDomain {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) : IsOpen (collisionDomain c f β) :=
  (c.open_source.preimage (hf.comp continuous_fst)).inter
    ((c.open_source.preimage (hf.comp continuous_snd)).inter
      (isOpen_ne_fun ((hβ.comp continuous_fst).sub (hβ.comp continuous_snd)) continuous_const))

theorem Smale.ChartMapPerturbation.contMDiffOn_collisionParameter {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) :
    ContMDiffOn (I.prod I) 𝓘(ℝ, F) ∞ (collisionParameter c f β) (collisionDomain c f β) := by
  intro q hq
  have hcf : ContMDiffAt (I.prod I) 𝓘(ℝ, F) ∞ (fun r : X × X => c (f r.1)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.1)).comp q
      (hf.comp contMDiff_fst).contMDiffAt
  have hcg : ContMDiffAt (I.prod I) 𝓘(ℝ, F) ∞ (fun r : X × X => c (f r.2)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.2.1)).comp q
      (hf.comp contMDiff_snd).contMDiffAt
  have hb : ContMDiffAt (I.prod I) 𝓘(ℝ, ℝ) ∞ (fun r : X × X => β r.1 - β r.2) q :=
    (hβ.comp contMDiff_fst).contMDiffAt.sub (hβ.comp contMDiff_snd).contMDiffAt
  exact ((hb.inv₀ hq.2.2).smul (hcg.sub hcf)).contMDiffWithinAt

theorem Smale.ChartMapPerturbation.collision_imp_old_and_equal_cutoff {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : F} (hvalid : Valid c f β a)
    (hgood : a ∉ collisionParameter c f β '' collisionDomain c f β) {x y : X}
    (heq : perturb c f β a x = perturb c f β a y) : f x = f y ∧ β x = β y := by
  classical
  by_cases hx : f x ∈ c.source
  · have hpy : perturb c f β a y ∈ c.source := heq ▸ perturb_mem_source c f β hvalid hx
    have hy : f y ∈ c.source := by
      by_contra hn
      simp only [perturb, hn, if_false] at hpy
    have hcoord : c (f x) + β x • a = c (f y) + β y • a := by
      have hh := congrArg c heq
      simpa only [chart_perturb c f β hvalid hx, chart_perturb c f β hvalid hy,
        coordinateFamily] using hh
    by_cases hb : β x = β y
    · refine ⟨c.toPartialEquiv.injOn hx hy ?_, hb⟩
      rw [hb] at hcoord
      exact add_right_cancel hcoord
    · have hd : β x - β y ≠ 0 := sub_ne_zero.mpr hb
      have hs : (β x - β y) • a = c (f y) - c (f x) := by
        rw [sub_smul]
        exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hcoord)
      exfalso
      apply hgood
      refine ⟨(x, y), ⟨hx, hy, hd⟩, ?_⟩
      change (β x - β y)⁻¹ • (c (f y) - c (f x)) = a
      rw [← hs, inv_smul_smul₀ hd]
  · have hpx : perturb c f β a x = f x := by simp only [perturb, hx, if_false]
    have hy : f y ∉ c.source := by
      intro hy
      have hpy := perturb_mem_source c f β hvalid hy
      rw [← heq, hpx] at hpy
      exact hx hpy
    have hpy : perturb c f β a y = f y := by simp only [perturb, hy, if_false]
    have hβx : β x = 0 := by
      by_contra hn
      exact hx (hsupport (subset_tsupport β hn))
    have hβy : β y = 0 := by
      by_contra hn
      exact hy (hsupport (subset_tsupport β hn))
    exact ⟨hpx.symm.trans (heq.trans hpy), hβx.trans hβy.symm⟩

theorem Smale.ChartMapPerturbation.exists_small_collision_removing_parameter
    {E G F H K X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [IsManifold I ∞ X] [LindelofSpace (X × X)] (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        Valid c f β a ∧
          ContMDiff I J ∞ (perturb c f β a) ∧
            ∀ x y, perturb c f β a x = perturb c f β a y → f x = f y ∧ β x = β y := by
  have hd : Module.finrank ℝ (E × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod, two_mul] using hdim
  have hdense :=
    Smale.GeneralPosition.dense_compl_manifold_image
      (isOpen_collisionDomain c hf.continuous hβ.continuous)
      (contMDiffOn_collisionParameter c hf hβ) hd
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, hgood, har⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have ha : ‖a‖ < Min.min ε δ := by simpa only [dist_zero_left] using har
  have hv := hvalid a (lt_of_lt_of_le ha (min_le_right _ _))
  exact
    ⟨a, lt_of_lt_of_le ha (min_le_left _ _), hv, contMDiff_perturb c hf hβ hsupport hv,
      fun _ _ heq => collision_imp_old_and_equal_cutoff c hsupport hv hgood heq⟩

def Smale.ChartMapPerturbation.obstacleDomain {G F K X Y N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (g : Y → N) (β : X → ℝ) : Set (X × Y) :=
  {q | f q.1 ∈ c.source ∧ g q.2 ∈ c.source ∧ β q.1 ≠ 0}

def Smale.ChartMapPerturbation.obstacleParameter {G F K X Y N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (g : Y → N) (β : X → ℝ) (q : X × Y) :
    F :=
  (β q.1)⁻¹ • (c (g q.2) - c (f q.1))

theorem Smale.ChartMapPerturbation.isOpen_obstacleDomain {G F K X Y N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N}
    {g : Y → N} {β : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hβ : Continuous β) :
    IsOpen (obstacleDomain c f g β) :=
  (c.open_source.preimage (hf.comp continuous_fst)).inter
    ((c.open_source.preimage (hg.comp continuous_snd)).inter
      (isOpen_ne_fun (hβ.comp continuous_fst) continuous_const))

theorem Smale.ChartMapPerturbation.contMDiffOn_obstacleParameter {E E' G F H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N}
    {β : X → ℝ} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) :
    ContMDiffOn (I.prod I') 𝓘(ℝ, F) ∞ (obstacleParameter c f g β) (obstacleDomain c f g β) := by
  intro q hq
  have hcf : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun r : X × Y => c (f r.1)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.1)).comp q
      (hf.comp contMDiff_fst).contMDiffAt
  have hcg : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun r : X × Y => c (g r.2)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.2.1)).comp q
      (hg.comp contMDiff_snd).contMDiffAt
  exact (((hβ.comp contMDiff_fst).contMDiffAt.inv₀ hq.2.2).smul (hcg.sub hcf)).contMDiffWithinAt

theorem Smale.ChartMapPerturbation.avoids_of_not_obstacle_parameter {G F K X Y N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N}
    {β : X → ℝ} (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : F} (ha : Valid c f β a)
    (hgood : a ∉ obstacleParameter c f g β '' obstacleDomain c f g β) (x : X) (hx : β x ≠ 0)
    (y : Y) : perturb c f β a x ≠ g y := by
  intro heq
  have hfx : f x ∈ c.source := hsupport (subset_tsupport β hx)
  have hgy : g y ∈ c.source := heq ▸ perturb_mem_source c f β ha hfx
  have hcoord : c (f x) + β x • a = c (g y) := by
    rw [← heq, chart_perturb c f β ha hfx]
    rfl
  apply hgood
  refine ⟨(x, y), ⟨hfx, hgy, hx⟩, ?_⟩
  change (β x)⁻¹ • (c (g y) - c (f x)) = a
  rw [← hcoord, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hx, one_smul]

theorem Smale.ChartMapPerturbation.exists_small_embedding_avoiding_parameter
    {E E' G F H H' K X Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N] [ChartedSpace K N]
    [LindelofSpace (X × X)] [LindelofSpace (X × Y)] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : X → N} {g : Y → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ F)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        Valid c f β a ∧
          ContMDiff I J ∞ (perturb c f β a) ∧
            (∀ x y, perturb c f β a x = perturb c f β a y → f x = f y) ∧
              ∀ x, β x ≠ 0 → ∀ y, perturb c f β a x ≠ g y := by
  have hdself : Module.finrank ℝ (E × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod, two_mul] using hself
  have hdobstacle : Module.finrank ℝ (E × E') < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hobstacle
  have hs :=
    Smale.GeneralPosition.dimH_image_manifold_le
      (isOpen_collisionDomain c hf.continuous hβ.continuous)
      (contMDiffOn_collisionParameter c hf hβ)
  have ho :=
    Smale.GeneralPosition.dimH_image_manifold_le
      (isOpen_obstacleDomain c hf.continuous hg.continuous hβ.continuous)
      (contMDiffOn_obstacleParameter c hf hg hβ)
  have hdense :
    Dense
      ((collisionParameter c f β '' collisionDomain c f β) ∪
          (obstacleParameter c f g β '' obstacleDomain c f g β))ᶜ := by
    apply dense_compl_of_dimH_lt_finrank
    rw [dimH_union]
    exact max_lt (hs.trans_lt (Nat.cast_lt.mpr hdself)) (ho.trans_lt (Nat.cast_lt.mpr hdobstacle))
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, hgood, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have ha : ‖a‖ < Min.min ε δ := by simpa only [dist_zero_left] using hnorm
  have hv := hvalid a (lt_min_iff.mp ha).2
  refine ⟨a, (lt_min_iff.mp ha).1, hv, contMDiff_perturb c hf hβ hsupport hv, ?_, ?_⟩
  · intro x y hxy
    exact (collision_imp_old_and_equal_cutoff c hsupport hv (fun h => hgood (Or.inl h)) hxy).1
  · exact avoids_of_not_obstacle_parameter c hsupport hv (fun h => hgood (Or.inr h))

theorem Smale.ManifoldImmersion.injective_fderiv_chart_iff {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) J f x) (hx : f x ∈ c.source) :
    Function.Injective (fderiv ℝ (c ∘ f) x) ↔ Function.Injective (mfderiv 𝓘(ℝ, E) J f x) := by
  have hderiv : fderiv ℝ (c ∘ f) x = (mfderiv J 𝓘(ℝ, F) c (f x)).comp (mfderiv 𝓘(ℝ, E) J f x) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf]
  have hc : Function.Injective (mfderiv J 𝓘(ℝ, F) c (f x)) :=
    ((c.isLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ hx).mfderivToContinuousLinearEquiv (by simp)).injective
  rw [hderiv]
  constructor
  · intro h v w hvw
    exact h (congrArg (mfderiv J 𝓘(ℝ, F) c (f x)) hvw)
  · exact fun h => hc.comp h

theorem Smale.ManifoldImmersion.fderiv_chart_eq_zero_iff {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) J f x) (hx : f x ∈ c.source) (v : E) :
    fderiv ℝ (c ∘ f) x v = 0 ↔ mfderiv 𝓘(ℝ, E) J f x v = 0 := by
  have hderiv : fderiv ℝ (c ∘ f) x = (mfderiv J 𝓘(ℝ, F) c (f x)).comp (mfderiv 𝓘(ℝ, E) J f x) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf]
  have hc : Function.Injective (mfderiv J 𝓘(ℝ, F) c (f x)) :=
    ((c.isLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ hx).mfderivToContinuousLinearEquiv (by simp)).injective
  rw [hderiv]
  change (mfderiv J 𝓘(ℝ, F) c (f x)) (mfderiv 𝓘(ℝ, E) J f x v) = 0 ↔ _
  constructor
  · intro h
    apply hc
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

theorem Smale.ManifoldImmersion.isOpen_injective_nativeDerivative {P E G H N : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : P → E → N} {W : Set (P × E)} (hW : IsOpen W)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) J ∞ (Function.uncurry f) W) :
    IsOpen {q : P × E | q ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J (f q.1) q.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqinj⟩
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f q.1 q.2)
  let U := W ∩ (Function.uncurry f) ⁻¹' c.source
  have hU : IsOpen U := hf.continuousOn.isOpen_inter_preimage hW c.open_source
  have hqU : q ∈ U := ⟨hq, mem_extChartAt_source (f q.1 q.2)⟩
  have hc : ContDiffOn ℝ ∞ (fun r : P × E => c (f r.1 r.2)) U := by
    intro r hr
    have hmap :
      ContMDiffAt 𝓘(ℝ, P × E) (𝓘(ℝ, P).prod 𝓘(ℝ, E)) ∞ (fun s : P × E => (s.1, s.2)) r :=
      contDiffAt_fst.contMDiffAt.prodMk contDiffAt_snd.contMDiffAt
    have hfr := (hf.contMDiffAt (hW.mem_nhds hr.1)).comp r hmap
    exact
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hr.2)).comp r
          hfr) |>.contDiffAt.contDiffWithinAt
  have hd :=
    Smale.MorsePerturbation.contDiffOn_spatialDerivative (f := fun a x => c (f a x)) hU hc
  have hgood :
    IsOpen
      (U ∩
        (fun r : P × E => fderiv ℝ (c ∘ f r.1) r.2) ⁻¹' {L : E →L[ℝ] G | Function.Injective L}) :=
    hd.continuousOn.isOpen_inter_preimage hU ContinuousLinearMap.isOpen_injective
  have hiff (r : P × E) (hr : r ∈ U) :
    Function.Injective (fderiv ℝ (c ∘ f r.1) r.2) ↔
      Function.Injective (mfderiv 𝓘(ℝ, E) J (f r.1) r.2) := by
    have hs : ContMDiffAt 𝓘(ℝ, E) J ∞ (f r.1) r.2 :=
      (hf.contMDiffAt (hW.mem_nhds hr.1)).comp r.2 (f := fun x : E => (r.1, x))
        (contMDiffAt_const.prodMk contMDiffAt_id)
    exact injective_fderiv_chart_iff c (hs.mdifferentiableAt (by simp)) hr.2
  have hn := hgood.mem_nhds ⟨hqU, (hiff q hqU).mpr hqinj⟩
  apply Filter.mem_of_superset hn
  intro r hr
  exact ⟨hr.1.1, (hiff r hr.1).mp hr.2⟩

theorem Smale.ManifoldImmersion.isOpen_injective_derivative_on {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {f : E → N} {W : Set E}
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) :
    IsOpen {x : E | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} := by
  have hfamily :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) J ∞ (fun q : ℝ × E => f q.2) (Prod.snd ⁻¹' W) :=
    hf.comp contMDiff_snd.contMDiffOn (fun _ hp => hp)
  have hopen :=
    (isOpen_injective_nativeDerivative (f := fun (_ : ℝ) => f) (hW.preimage continuous_snd)
          hfamily).preimage
      ((continuous_const (y := (0 : ℝ))).prodMk (continuous_id : Continuous (id : E → E)))
  exact hopen

theorem Smale.ManifoldImmersion.isOpen_injective_derivative {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) :
    IsOpen {x : E | Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} := by
  have hfamily : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) J ∞ (fun q : ℝ × E => f q.2) :=
    hf.comp contMDiff_snd
  have hopen :=
    (isOpen_injective_nativeDerivative (f := fun (_ : ℝ) => f) isOpen_univ
          hfamily.contMDiffOn).preimage
      ((continuous_const (y := (0 : ℝ))).prodMk (continuous_id : Continuous (id : E → E)))
  change IsOpen {x : E | True ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} at hopen
  simpa only [true_and] using hopen

theorem Smale.ManifoldImmersion.eventually_injective_nativeDerivative {P E G H N : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : P → E → N} {W : Set (P × E)} (hW : IsOpen W)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) J ∞ (Function.uncurry f) W) {K : Set E}
    (hK : IsCompact K) {a₀ : P} (hmem : ∀ x ∈ K, (a₀, x) ∈ W)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (f a₀) x)) :
    ∀ᶠ a in 𝓝 a₀, ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (f a) x) := by
  have hopen :=
    Smale.MorsePerturbation.isOpen_forall_mem_compact hK (isOpen_injective_nativeDerivative hW hf)
  have hn := hopen.mem_nhds (fun x hx => ⟨hmem x hx, hinj x hx⟩)
  filter_upwards [hn] with a ha x hx
  exact (ha x hx).2

theorem Smale.ChartMapPerturbation.eventually_perturb_injective_derivative {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N} {β : E → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hβ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {K : Set E}
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∀ᶠ a : F in 𝓝 0, ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (perturb c f β a) x) := by
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  let W : Set (F × E) := {q | ‖q.1‖ < δ}
  have hW : IsOpen W := isOpen_lt continuous_fst.norm continuous_const
  have hfamily :
    ContMDiffOn (𝓘(ℝ, F).prod 𝓘(ℝ, E)) J ∞ (fun q : F × E => perturb c f β q.1 q.2) W := by
    intro q hq
    exact (contMDiffAt_perturb c hf hβ hsupport q (hvalid q.1 hq)).contMDiffWithinAt
  apply Smale.ManifoldImmersion.eventually_injective_nativeDerivative hW hfamily hK
  · intro x _
    change ‖(0 : F)‖ < δ
    simpa only [norm_zero] using hδ
  · intro x hx
    have heq : perturb c f β (0 : F) = f := funext (perturb_zero c f β)
    change Function.Injective (mfderiv 𝓘(ℝ, E) J (perturb c f β (0 : F)) x)
    rw [heq]
    exact hinj x hx

theorem Smale.ManifoldImmersion.exists_embedded_image_avoidance_step_controlled
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    {C K : Set E} (p : ι → Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι)
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) (hK : IsCompact K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        (∀ j, (p j).Compatible f') ∧
          Smale.HomotopicRelWithin f f' C K O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧ ∀ x, (f x ∉ g '' A ∨ (p i).cutoff x ≠ 0) → f' x ∉ g '' A := by
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
        (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    Smale.ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf (p i).smooth
      (p i).compact (hcompatible i) hK hderiv
  have hstay :=
    Smale.ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
      (hcompatible i) hK hO hmaps
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp (hkeep.and (hold.and hstay))
  obtain ⟨r, hr, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid (p i).chart hf (p i).smooth (p i).compact
      (hcompatible i)
  obtain ⟨a, ha, -, hsmooth, hnoNew, havoid⟩ :=
    Smale.ChartMapPerturbation.exists_small_embedding_avoiding_parameter (p i).chart hf hg
      (p i).smooth (p i).compact (hcompatible i) hself hobstacle (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let f' : C(E, N) := ⟨_, hsmooth.continuous⟩
  have hretained :=
    hδkeep (show a ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  let Hrel :=
    Smale.ChartMapPerturbation.homotopyRel (p i).chart hf (p i).smooth (hcompatible i) hvalid har
  refine ⟨f', hsmooth, hretained.1, ?_, hretained.2.1, hnoNew, hretained.2.2, ?_⟩
  · refine ⟨{ Hrel.toHomotopy with prop' := fun t x hx => Hrel.eq_fst t ((p i).fixed x hx) }, ?_⟩
    intro t x hx
    change Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff ((t : ℝ) • a) x ∈ O
    have hsmall : (t : ℝ) • a ∈ Metric.ball (0 : G) δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        Smale.ChartMapPerturbation.norm_interval_smul_lt haδ t
    exact (hδkeep hsmall).2.2 hx
  · intro x hx
    by_cases hzero : (p i).cutoff x = 0
    · have hold : f x ∉ g '' A := hx.resolve_right (Classical.not_not.mpr hzero)
      change Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a x ∉ g '' A
      rwa [Smale.ChartMapPerturbation.perturb_eq_of_zero _ _ _ _ hzero]
    · rintro ⟨y, _, hy⟩
      exact havoid x hzero y hy.symm

theorem Smale.ManifoldImmersion.exists_finite_embedded_image_avoidance_controlled
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    {C K : Set E} (p : ι → Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C)
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) (hK : IsCompact K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) (s : Finset ι) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        (∀ j, (p j).Compatible f') ∧
          Smale.HomotopicRelWithin f f' C K O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧
                  ∀ x, (f x ∉ g '' A ∨ ∃ i ∈ s, (p i).cutoff x ≠ 0) → f' x ∉ g '' A := by
  classical
    induction s using Finset.induction_on with
  |
    empty =>
    refine
      ⟨f, hf, hcompatible, Smale.HomotopicRelWithin.refl f C hmaps, hderiv, (fun _ _ hxy => hxy),
        hmaps, ?_⟩
    intro x hx
    simpa only [Finset.notMem_empty, false_and, exists_false, or_false] using hx
  | @insert i s _
    ih =>
    obtain ⟨f₁, hf₁, hc₁, hhom₁, hd₁, hnoNew₁, hmaps₁, havoid₁⟩ := ih
    obtain ⟨f₂, hf₂, hc₂, hhom₂, hd₂, hnoNew₂, hmaps₂, havoid₂⟩ :=
      exists_embedded_image_avoidance_step_controlled p i f₁ g A hf₁ hg hc₁ hself hobstacle hK hd₁
        hO hmaps₁
    refine
      ⟨f₂, hf₂, hc₂, hhom₁.trans hhom₂, hd₂, (fun x y hxy => hnoNew₁ x y (hnoNew₂ x y hxy)),
        hmaps₂, ?_⟩
    intro x hx
    apply havoid₂ x
    rcases hx with hold | ⟨j, hj, hactive⟩
    · exact Or.inl (havoid₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hactive
      · exact Or.inl (havoid₁ x (Or.inr ⟨j, hjs, hactive⟩))

theorem Smale.ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_image_controlled
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K L C : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A) {O : Set N} (hO : IsOpen O) (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        Smale.HomotopicRelWithin f f' C K O ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧ ∀ x, (f x ∉ g '' A ∨ x ∈ L) → f' x ∉ g '' A := by
  classical
  let bad : Set E := L ∩ f ⁻¹' g '' A
  have hbad : IsCompact bad := hL.inter_right (hclosed.preimage f.continuous)
  have hp (x : bad) :
    ∃ p : Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x.1 ≠ 0 :=
    Smale.GeneralPosition.exists_avoidance_patch_at (I := 𝓘(ℝ, E)) (J := J) f hC
      (fun hx => hfixed x.1 ⟨x.property.1, hx⟩ x.property.2)
  choose p hpcompatible hpactive using hp
  have hopen (x : bad) : IsOpen (Function.support (p x).cutoff) :=
    isOpen_ne_fun (p x).smooth.continuous continuous_const
  have hcover : bad ⊆ ⋃ x : bad, Function.support (p x).cutoff := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpactive ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ :=
    hbad.elim_finite_subcover (fun x : bad => Function.support (p x).cutoff) hopen hcover
  obtain ⟨f', hf', -, hhom, hderiv', hnoNew, hmaps', havoid⟩ :=
    exists_finite_embedded_image_avoidance_controlled (fun i : s => p i.1) f g A hf hg
      (fun i => hpcompatible i.1) hself hobstacle hK hderiv hO hmaps Finset.univ
  refine ⟨f', hf', hhom, ?_, hderiv', hnoNew, hmaps', ?_⟩
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (f'.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property (hnoNew x y hxy))
  · intro x hx
    apply havoid x
    rcases hx with hold | hxL
    · exact Or.inl hold
    · by_cases hxg : f x ∈ g '' A
      · have hx : x ∈ bad := ⟨hxL, hxg⟩
        obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hs hx)
        exact Or.inr ⟨⟨i, hi⟩, Finset.mem_univ _, hix⟩
      · exact Or.inl hxg

theorem Smale.ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_image
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K L C : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A) {O : Set N} (hO : IsOpen O) (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧ ∀ x, (f x ∉ g '' A ∨ x ∈ L) → f' x ∉ g '' A := by
  obtain ⟨f', hf', hhom, hemb, hd, hnoNew, hmaps', havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image_controlled f g A hf hg hclosed hself
      hobstacle hK hL hC hinj hderiv hfixed hO hmaps
  exact ⟨f', hf', hhom.homotopicRel, hemb, hd, hnoNew, hmaps', havoid⟩

theorem Smale.ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K L C : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                ∀ x, (f x ∉ Set.range g ∨ x ∈ L) → f' x ∉ Set.range g := by
  obtain ⟨f', hf', hhom, hemb, hd, hnoNew, -, havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image f g Set.univ hf hg
      (by simpa only [Set.image_univ] using hclosed) hself hobstacle hK hL hC hinj hderiv
      (by simpa only [Set.image_univ] using hfixed) isOpen_univ (fun _ _ => Set.mem_univ _)
  refine ⟨f', hf', hhom, hemb, hd, hnoNew, ?_⟩
  simpa only [Set.image_univ] using havoid

abbrev Smale.PlaneImmersion.Plane :=
  ℝ × ℝ

def Smale.PlaneImmersion.linearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F × F) : Plane →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight A.1 + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight A.2

theorem Smale.PlaneImmersion.linearMap_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F × F) (v : Plane) : linearMap A v = v.1 • A.1 + v.2 • A.2 :=
  rfl

def Smale.PlaneImmersion.perturb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (A : F × F) (x : Plane) : F :=
  f x + linearMap A x

theorem Smale.PlaneImmersion.contDiff_perturb_family {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun q : (F × F) × Plane => perturb f q.1 q.2) :=
  (hf.comp contDiff_snd).add
    (((contDiff_fst.comp contDiff_snd).smul (contDiff_fst.comp contDiff_fst)).add
      ((contDiff_snd.comp contDiff_snd).smul (contDiff_snd.comp contDiff_fst)))

theorem Smale.PlaneImmersion.fderiv_perturb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} (hf : ContDiff ℝ ∞ f) (A : F × F) (x : Plane) :
    fderiv ℝ (perturb f A) x = fderiv ℝ f x + linearMap A :=
  ((hf.differentiable (by simp) x).hasFDerivAt.add (linearMap A).hasFDerivAt).fderiv

def Smale.PlaneImmersion.firstCollisionDomain {F : Type*} : Set (Plane × (Plane × F)) :=
  {q | q.1.1 - q.2.1.1 ≠ 0}

def Smale.PlaneImmersion.secondCollisionDomain {F : Type*} : Set (Plane × (Plane × F)) :=
  {q | q.1.2 - q.2.1.2 ≠ 0}

def Smale.PlaneImmersion.firstCollision {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (Plane × F)) : F × F :=
  ((q.1.1 - q.2.1.1)⁻¹ • (f q.2.1 - f q.1 - (q.1.2 - q.2.1.2) • q.2.2), q.2.2)

def Smale.PlaneImmersion.secondCollision {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (Plane × F)) : F × F :=
  (q.2.2, (q.1.2 - q.2.1.2)⁻¹ • (f q.2.1 - f q.1 - (q.1.1 - q.2.1.1) • q.2.2))

theorem Smale.PlaneImmersion.isOpen_firstCollisionDomain {F : Type*} [NormedAddCommGroup F] :
    IsOpen (firstCollisionDomain (F := F)) :=
  isOpen_ne.preimage (continuous_fst.fst.sub continuous_snd.fst.fst)

theorem Smale.PlaneImmersion.isOpen_secondCollisionDomain {F : Type*} [NormedAddCommGroup F] :
    IsOpen (secondCollisionDomain (F := F)) :=
  isOpen_ne.preimage (continuous_fst.snd.sub continuous_snd.fst.snd)

theorem Smale.PlaneImmersion.contDiffOn_firstCollision {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (firstCollision f) firstCollisionDomain := by
  have h₁ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.1 - q.2.1.1) :=
    contDiff_fst.fst.sub contDiff_snd.fst.fst
  have h₂ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.2 - q.2.1.2) :=
    contDiff_fst.snd.sub contDiff_snd.fst.snd
  exact
    ((h₁.contDiffOn.inv (fun _ h => h)).smul
          (((hf.comp contDiff_snd.fst).sub (hf.comp contDiff_fst)).sub
              (h₂.smul contDiff_snd.snd)).contDiffOn).prodMk
      contDiff_snd.snd.contDiffOn

theorem Smale.PlaneImmersion.contDiffOn_secondCollision {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (secondCollision f) secondCollisionDomain := by
  have h₁ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.1 - q.2.1.1) :=
    contDiff_fst.fst.sub contDiff_snd.fst.fst
  have h₂ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.2 - q.2.1.2) :=
    contDiff_fst.snd.sub contDiff_snd.fst.snd
  exact
    contDiff_snd.snd.contDiffOn.prodMk
      ((h₂.contDiffOn.inv (fun _ h => h)).smul
        (((hf.comp contDiff_snd.fst).sub (hf.comp contDiff_fst)).sub
            (h₁.smul contDiff_snd.snd)).contDiffOn)

theorem Smale.PlaneImmersion.mem_collision_of_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) (A : F × F) {x y : Plane} (hxy : x ≠ y)
    (heq : perturb f A x = perturb f A y) :
    A ∈ firstCollision f '' firstCollisionDomain ∪ secondCollision f '' secondCollisionDomain := by
  have hlinear : linearMap A (x - y) = f y - f x := by
    rw [map_sub]
    change f x + linearMap A x = f y + linearMap A y at heq
    exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using heq)
  change (x.1 - y.1) • A.1 + (x.2 - y.2) • A.2 = f y - f x at hlinear
  by_cases hfirst : x.1 - y.1 = 0
  · have hsecond : x.2 - y.2 ≠ 0 := by
      intro h
      exact hxy (Prod.ext (sub_eq_zero.mp hfirst) (sub_eq_zero.mp h))
    apply Or.inr
    refine ⟨(x, (y, A.1)), hsecond, Prod.ext rfl ?_⟩
    change (x.2 - y.2)⁻¹ • (f y - f x - (x.1 - y.1) • A.1) = A.2
    rw [← eq_sub_of_add_eq' hlinear, inv_smul_smul₀ hsecond]
  · apply Or.inl
    refine ⟨(x, (y, A.2)), hfirst, Prod.ext ?_ rfl⟩
    change (x.1 - y.1)⁻¹ • (f y - f x - (x.2 - y.2) • A.2) = A.1
    rw [← eq_sub_of_add_eq hlinear, inv_smul_smul₀ hfirst]

theorem Smale.PlaneImmersion.injective_perturb_of_not_collision {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) {A : F × F}
    (hA :
      A ∉ firstCollision f '' firstCollisionDomain ∪ secondCollision f '' secondCollisionDomain) :
    Function.Injective (perturb f A) := by
  intro x y heq
  by_contra hxy
  exact hA (mem_collision_of_eq f A hxy heq)

def Smale.PlaneImmersion.badFirst {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (ℝ × F)) : F × F :=
  (-fderiv ℝ f q.1 (1, q.2.1) - q.2.1 • q.2.2, q.2.2)

def Smale.PlaneImmersion.badSecond {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (ℝ × F)) : F × F :=
  (q.2.2, -fderiv ℝ f q.1 (q.2.1, 1) - q.2.1 • q.2.2)

theorem Smale.PlaneImmersion.contDiff_badFirst {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (badFirst f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he : ContDiff ℝ ∞ (fun q : Plane × (ℝ × F) => fderiv ℝ f q.1 (1, q.2.1)) :=
    (hd.comp contDiff_fst).clm_apply (contDiff_const.prodMk (contDiff_fst.comp contDiff_snd))
  exact
    (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul (contDiff_snd.comp contDiff_snd))).prodMk
      (contDiff_snd.comp contDiff_snd)

theorem Smale.PlaneImmersion.contDiff_badSecond {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (badSecond f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he : ContDiff ℝ ∞ (fun q : Plane × (ℝ × F) => fderiv ℝ f q.1 (q.2.1, 1)) :=
    (hd.comp contDiff_fst).clm_apply ((contDiff_fst.comp contDiff_snd).prodMk contDiff_const)
  exact
    (contDiff_snd.comp contDiff_snd).prodMk
      (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul (contDiff_snd.comp contDiff_snd)))

theorem Smale.PlaneImmersion.mem_bad_of_nonzero_kernel {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) (A : F × F) (x v : Plane) (hv : v ≠ 0)
    (hker : (fderiv ℝ f x + linearMap A) v = 0) :
    A ∈ Set.range (badFirst f) ∪ Set.range (badSecond f) := by
  by_cases hfirst : v.1 = 0
  · have hsecond : v.2 ≠ 0 := by
      intro h
      exact hv (Prod.ext hfirst h)
    let r := v.1 / v.2
    have hvec : (r, (1 : ℝ)) = v.2⁻¹ • v := by
      apply Prod.ext
      · change v.1 / v.2 = v.2⁻¹ * v.1
        rw [div_eq_mul_inv, mul_comm]
      · change (1 : ℝ) = v.2⁻¹ * v.2
        rw [inv_mul_cancel₀ hsecond]
    have hz : (fderiv ℝ f x + linearMap A) (r, 1) = 0 := by rw [hvec, map_smul, hker, smul_zero]
    change fderiv ℝ f x (r, 1) + (r • A.1 + (1 : ℝ) • A.2) = 0 at hz
    rw [one_smul, ← add_assoc] at hz
    have hsolve : A.2 = -(fderiv ℝ f x (r, 1) + r • A.1) := eq_neg_of_add_eq_zero_right hz
    apply Or.inr
    refine ⟨(x, (r, A.1)), Prod.ext rfl ?_⟩
    change -fderiv ℝ f x (r, 1) - r • A.1 = A.2
    simpa only [neg_add, sub_eq_add_neg] using hsolve.symm
  · let r := v.2 / v.1
    have hvec : ((1 : ℝ), r) = v.1⁻¹ • v := by
      apply Prod.ext
      · change (1 : ℝ) = v.1⁻¹ * v.1
        rw [inv_mul_cancel₀ hfirst]
      · change v.2 / v.1 = v.1⁻¹ * v.2
        rw [div_eq_mul_inv, mul_comm]
    have hz : (fderiv ℝ f x + linearMap A) (1, r) = 0 := by rw [hvec, map_smul, hker, smul_zero]
    change fderiv ℝ f x (1, r) + ((1 : ℝ) • A.1 + r • A.2) = 0 at hz
    rw [one_smul, ← add_assoc] at hz
    have hsolve : fderiv ℝ f x (1, r) + A.1 = -(r • A.2) := eq_neg_of_add_eq_zero_left hz
    apply Or.inl
    refine ⟨(x, (r, A.2)), Prod.ext ?_ rfl⟩
    change -fderiv ℝ f x (1, r) - r • A.2 = A.1
    rw [sub_eq_add_neg, ← hsolve, neg_add_cancel_left]

theorem Smale.PlaneImmersion.injective_add_linearMap_of_not_bad {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) {A : F × F}
    (hA : A ∉ Set.range (badFirst f) ∪ Set.range (badSecond f)) (x : Plane) :
    Function.Injective (fderiv ℝ f x + linearMap A) := by
  intro v w hvw
  have hz : (fderiv ℝ f x + linearMap A) (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have heq : v - w = 0 := by
    by_contra hne
    exact hA (mem_bad_of_nonzero_kernel f A x (v - w) hne hz)
  exact sub_eq_zero.mp heq

theorem Smale.PlaneImmersion.dimH_bad_parameters_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    dimH (Set.range (badFirst f) ∪ Set.range (badSecond f)) ≤
      (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
  have hfirst : dimH (Set.range (badFirst f)) ≤ (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
    rw [← Set.image_univ]
    exact
      Smale.GeneralPosition.dimH_image_manifold_le isOpen_univ
        (contDiff_badFirst hf).contMDiff.contMDiffOn
  have hsecond : dimH (Set.range (badSecond f)) ≤ (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
    rw [← Set.image_univ]
    exact
      Smale.GeneralPosition.dimH_image_manifold_le isOpen_univ
        (contDiff_badSecond hf).contMDiff.contMDiffOn
  rw [dimH_union]
  exact max_le hfirst hsecond

theorem Smale.PlaneImmersion.dimH_collision_parameters_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    dimH (firstCollision f '' firstCollisionDomain ∪ secondCollision f '' secondCollisionDomain) ≤
      (Module.finrank ℝ (Plane × (Plane × F)) : ℝ≥0∞) := by
  have hfirst :=
    Smale.GeneralPosition.dimH_image_manifold_le (isOpen_firstCollisionDomain (F := F))
      (contDiffOn_firstCollision hf).contMDiffOn
  have hsecond :=
    Smale.GeneralPosition.dimH_image_manifold_le (isOpen_secondCollisionDomain (F := F))
      (contDiffOn_secondCollision hf).contMDiffOn
  rw [dimH_union]
  exact max_le hfirst hsecond

theorem Smale.PlaneImmersion.dense_injective_immersive_parameters {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (hdim : 5 ≤ Module.finrank ℝ F) :
    Dense
      ((Set.range (badFirst f) ∪ Set.range (badSecond f)) ∪
          (firstCollision f '' firstCollisionDomain ∪
            secondCollision f '' secondCollisionDomain))ᶜ := by
  have hd₁ : Module.finrank ℝ (Plane × (ℝ × F)) < Module.finrank ℝ (F × F) := by
    change Module.finrank ℝ ((ℝ × ℝ) × (ℝ × F)) < Module.finrank ℝ (F × F)
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  have hd₂ : Module.finrank ℝ (Plane × (Plane × F)) < Module.finrank ℝ (F × F) := by
    change Module.finrank ℝ ((ℝ × ℝ) × ((ℝ × ℝ) × F)) < Module.finrank ℝ (F × F)
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  apply dense_compl_of_dimH_lt_finrank
  rw [dimH_union]
  exact
    max_lt ((dimH_bad_parameters_le hf).trans_lt (Nat.cast_lt.mpr hd₁))
      ((dimH_collision_parameters_le hf).trans_lt (Nat.cast_lt.mpr hd₂))

theorem Smale.PlaneImmersion.exists_small_affine_injective_immersion {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (hdim : 5 ≤ Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : F × F,
      ‖A‖ < ε ∧
        ContDiff ℝ ∞ (perturb f A) ∧
          Function.Injective (perturb f A) ∧ ∀ x, Function.Injective (fderiv ℝ (perturb f A) x) :=
  by
  obtain ⟨A, hA, hnorm⟩ := (dense_injective_immersive_parameters hf hdim).exists_dist_lt 0 hε
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · simpa only [dist_zero_left] using hnorm
  · exact (contDiff_perturb_family hf).comp (contDiff_const.prodMk contDiff_id)
  · exact injective_perturb_of_not_collision f (fun h => hA (Or.inr h))
  · intro x
    rw [fderiv_perturb hf]
    exact injective_add_linearMap_of_not_bad f (fun h => hA (Or.inl h)) x

def Smale.PlaneImmersion.displacement {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (β : Plane → ℝ) (A : F × F) (x : Plane) : F :=
  β x • linearMap A x

theorem Smale.PlaneImmersion.contDiff_displacement_family {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun q : (F × F) × Plane => displacement β q.1 q.2) :=
  (hβ.comp contDiff_snd).smul
    ((contDiff_snd.fst.smul contDiff_fst.fst).add (contDiff_snd.snd.smul contDiff_fst.snd))

theorem Smale.PlaneImmersion.displacement_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (β : Plane → ℝ) (x : Plane) : displacement β (0 : F × F) x = 0 := by
  simp only [displacement, linearMap_apply, Prod.fst_zero, Prod.snd_zero, smul_zero, add_zero]

theorem Smale.PlaneImmersion.displacement_of_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (A : F × F) {x : Plane} (hx : β x = 0) :
    displacement β A x = 0 := by simp only [displacement, hx, zero_smul]

theorem Smale.PlaneImmersion.eventually_displacement_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ A : F × F in 𝓝 0, ∀ x, ‖displacement β A x‖ < ε := by
  have hsupport : ∀ᶠ A : F × F in 𝓝 0, ∀ x ∈ tsupport β, ‖displacement β A x‖ < ε := by
    apply hcompact.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have hc :=
      (contDiff_displacement_family (F := F) hβ).continuous.norm.continuousAt (x :=
        ((0 : F × F), x))
    have hval : ‖displacement β (0 : F × F) x‖ < ε := by
      simpa only [displacement_zero, norm_zero] using hε
    exact hc.preimage_mem_nhds (isOpen_Iio.mem_nhds hval)
  filter_upwards [hsupport] with A hA x
  by_cases hx : x ∈ tsupport β
  · exact hA x hx
  · have hzero : β x = 0 := by
      by_contra hne
      exact hx (subset_tsupport β hne)
    simpa only [displacement_of_zero A hzero, norm_zero] using hε

theorem Smale.PlaneImmersion.exists_radius_displacement_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > (0 : ℝ), ∀ A : F × F, ‖A‖ < δ → ∀ x, ‖displacement β A x‖ < ε := by
  have hn : {A : F × F | ∀ x, ‖displacement β A x‖ < ε} ∈ 𝓝 0 :=
    eventually_displacement_lt hβ hcompact hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  exact ⟨δ, hδ, fun A hA => hball (by simpa only [Metric.mem_ball, dist_zero_right] using hA)⟩

def Smale.ManifoldImmersion.affinePatch {G F H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    (f : Smale.PlaneImmersion.Plane → N) (β : Smale.PlaneImmersion.Plane → ℝ) (A : F × F) :
    Smale.PlaneImmersion.Plane → N :=
  Smale.ChartMapPerturbation.variablePerturb c f β (Smale.PlaneImmersion.displacement β A)

theorem Smale.ManifoldImmersion.chart_affinePatch_on_plateau {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : Smale.PlaneImmersion.Plane → N}
    {β χ : Smale.PlaneImmersion.Plane → ℝ} {A : F × F} (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hχ : ∀ x ∈ tsupport β, χ x = 1)
    (hvalid :
      ∀ x, Smale.ChartMapPerturbation.Valid c f β (Smale.PlaneImmersion.displacement β A x))
    {x : Smale.PlaneImmersion.Plane} (hx : β x = 1) :
    c (affinePatch c f β A x) =
      Smale.PlaneImmersion.perturb (Smale.ChartMapPerturbation.cutoffCoordinates c f χ) A x := by
  have hxs : x ∈ tsupport β := subset_tsupport β (by change β x ≠ 0; rw [hx]; norm_num)
  change
    c (Smale.ChartMapPerturbation.perturb c f β (Smale.PlaneImmersion.displacement β A x) x) = _
  rw [Smale.ChartMapPerturbation.chart_perturb c f β (hvalid x) (hsupport hxs)]
  simp only [Smale.ChartMapPerturbation.coordinateFamily, Smale.PlaneImmersion.perturb,
    Smale.ChartMapPerturbation.cutoffCoordinates, Smale.PlaneImmersion.displacement, hx, hχ x hxs,
    one_smul]

theorem Smale.ManifoldImmersion.contMDiff_affinePatch {G F H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : Smale.PlaneImmersion.Plane → N}
    {β : Smale.PlaneImmersion.Plane → ℝ} {A : F × F}
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hvalid :
      ∀ x, Smale.ChartMapPerturbation.Valid c f β (Smale.PlaneImmersion.displacement β A x)) :
    ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ (affinePatch c f β A) := by
  have hd :=
    (Smale.PlaneImmersion.contDiff_displacement_family (F := F) hβ).comp
      (contDiff_const (c := A) |>.prodMk contDiff_id)
  intro x
  exact
    Smale.ChartMapPerturbation.contMDiffAt_variablePerturb c hsupport hf.contMDiffAt
      hβ.contMDiff.contMDiffAt hd.contMDiff.contMDiffAt (hvalid x)

theorem Smale.ManifoldImmersion.exists_affine_embedding_patch_with_property {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) [FiniteDimensional ℝ F] [T2Space N]
    (f : C(Smale.PlaneImmersion.Plane, N)) (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f)
    {β χ : Smale.PlaneImmersion.Plane → ℝ} (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ)
    (hcompact : HasCompactSupport β) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source)
    (hχone : ∀ x ∈ tsupport β, χ x = 1) (hdim : 5 ≤ Module.finrank ℝ F)
    (Q : (Smale.PlaneImmersion.Plane → N) → Prop)
    (hQ : ∀ᶠ A : F × F in 𝓝 0, Q (affinePatch c f β A)) {K : Set Smale.PlaneImmersion.Plane}
    (hK : IsCompact K) (hKsub : K ⊆ interior {x | β x = 1}) :
    ∃ g : C(Smale.PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ g ∧
        Q g ∧
          Nonempty (f.HomotopyRel g {x | β x = 0}) ∧
            Topology.IsClosedEmbedding (fun x : K => g x) ∧
              ∀ x ∈ interior {x | β x = 1},
                Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x) := by
  have hsupport : tsupport β ⊆ f ⁻¹' c.source := by
    intro x hx
    exact hχsupport (subset_tsupport χ (by change χ x ≠ 0; rw [hχone x hx]; norm_num))
  let k := Smale.ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) 𝓘(ℝ, F) ∞ k := fun x =>
      Smale.ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff hcompact hsupport
  obtain ⟨δ, hδ, hδbound⟩ :=
    Smale.PlaneImmersion.exists_radius_displacement_lt (F := F) hβ hcompact hε
  have hQmem : {A : F × F | Q (affinePatch c f β A)} ∈ 𝓝 0 := hQ
  obtain ⟨η, hη, hηkeep⟩ := Metric.mem_nhds_iff.mp hQmem
  obtain ⟨A, hA, -, hinj, hderiv⟩ :=
    Smale.PlaneImmersion.exists_small_affine_injective_immersion hk hdim (lt_min hδ hη)
  have hbound : ∀ x, ‖Smale.PlaneImmersion.displacement β A x‖ < ε :=
    hδbound A (lt_of_lt_of_le hA (min_le_left _ _))
  have hv :
    ∀ x, Smale.ChartMapPerturbation.Valid c f β (Smale.PlaneImmersion.displacement β A x) :=
    fun x => hvalid _ (hbound x)
  have hsmooth := contMDiff_affinePatch c hf hβ hsupport hv
  let g : C(Smale.PlaneImmersion.Plane, N) := ⟨affinePatch c f β A, hsmooth.continuous⟩
  have hcoord (x : Smale.PlaneImmersion.Plane) (hx : β x = 1) :
    c (g x) = Smale.PlaneImmersion.perturb k A x :=
    chart_affinePatch_on_plateau c hsupport hχone hv hx
  have hQg : Q g :=
    hηkeep
      (show A ∈ Metric.ball 0 η by
        simpa only [Metric.mem_ball, dist_zero_right] using
          (lt_of_lt_of_le hA (min_le_right δ η)))
  refine ⟨g, hsmooth, hQg, ?_, ?_, ?_⟩
  · have hd :=
      (Smale.PlaneImmersion.contDiff_displacement_family (F := F) hβ).comp
        (contDiff_const (c := A) |>.prodMk contDiff_id)
    exact
      ⟨Smale.ChartMapPerturbation.variableHomotopyRel c f.continuous hβ.continuous hsupport
          hd.continuous hvalid hbound (fun _ hx => Or.inl hx)⟩
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    change g x = g y at hxy
    apply Subtype.ext
    apply hinj
    rw [← hcoord x (interior_subset (s := {z | β z = 1}) (hKsub x.property)), ←
      hcoord y (interior_subset (s := {z | β z = 1}) (hKsub y.property)), hxy]
  · intro x hx
    have hβx : β x = 1 := interior_subset (s := {z | β z = 1}) hx
    have hxs : f x ∈ c.source :=
      hsupport (subset_tsupport β (by change β x ≠ 0; rw [hβx]; norm_num))
    have hgs : g x ∈ c.source := Smale.ChartMapPerturbation.perturb_mem_source c f β (hv x) hxs
    apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgs).mp
    have heq : (c ∘ g) =ᶠ[𝓝 x] Smale.PlaneImmersion.perturb k A := by
      filter_upwards [isOpen_interior.mem_nhds hx] with y hy
      exact hcoord y (interior_subset (s := {z | β z = 1}) hy)
    change Function.Injective (fderiv ℝ (c ∘ g) x)
    rw [heq.fderiv_eq]
    exact hderiv x

theorem Smale.ManifoldImmersion.affinePatch_zero {G F H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : Smale.PlaneImmersion.Plane → N)
    (β : Smale.PlaneImmersion.Plane → ℝ) : affinePatch c f β (0 : F × F) = f := by
  funext x
  change
    Smale.ChartMapPerturbation.perturb c f β (Smale.PlaneImmersion.displacement β 0 x) x = f x
  rw [Smale.PlaneImmersion.displacement_zero, Smale.ChartMapPerturbation.perturb_zero]

theorem Smale.ManifoldImmersion.contMDiffAt_affinePatch_family {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : Smale.PlaneImmersion.Plane → N}
    {β : Smale.PlaneImmersion.Plane → ℝ} (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (q : (F × F) × Smale.PlaneImmersion.Plane)
    (hvalid :
      Smale.ChartMapPerturbation.Valid c f β (Smale.PlaneImmersion.displacement β q.1 q.2)) :
    ContMDiffAt (𝓘(ℝ, F × F).prod 𝓘(ℝ, Smale.PlaneImmersion.Plane)) J ∞
      (fun r : (F × F) × Smale.PlaneImmersion.Plane => affinePatch c f β r.1 r.2) q := by
  have hid :
    ContMDiffAt (𝓘(ℝ, F × F).prod 𝓘(ℝ, Smale.PlaneImmersion.Plane))
      𝓘(ℝ, (F × F) × Smale.PlaneImmersion.Plane) ∞
      (fun r : (F × F) × Smale.PlaneImmersion.Plane => r) q :=
    (contMDiffAt_prod_module_iff _).mpr ⟨contMDiffAt_fst, contMDiffAt_snd⟩
  have hd :=
    (Smale.PlaneImmersion.contDiff_displacement_family (F := F) hβ).contMDiff.contMDiffAt |>.comp
      q hid
  exact
    (Smale.ChartMapPerturbation.contMDiffAt_perturb c hf hβ.contMDiff hsupport
          (Smale.PlaneImmersion.displacement β q.1 q.2, q.2) hvalid).comp
      q (f := fun r : (F × F) × Smale.PlaneImmersion.Plane =>
      (Smale.PlaneImmersion.displacement β r.1 r.2, r.2)) (hd.prodMk contMDiffAt_snd)

theorem Smale.ManifoldImmersion.eventually_affinePatch_maps_compact_into_open {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : Smale.PlaneImmersion.Plane → N}
    {β : Smale.PlaneImmersion.Plane → ℝ} (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {K : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K) {U : Set N} (hU : IsOpen U)
    (hmap : Set.MapsTo f K U) : ∀ᶠ A : F × F in 𝓝 0, Set.MapsTo (affinePatch c f β A) K U := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hvalid :
    Smale.ChartMapPerturbation.Valid c f β (Smale.PlaneImmersion.displacement β (0 : F × F) x) := by
    rw [Smale.PlaneImmersion.displacement_zero]
    exact Smale.ChartMapPerturbation.valid_zero c f β hsupport
  have hc := (contMDiffAt_affinePatch_family c hf hβ hsupport (0, x) hvalid).continuousAt
  apply hc.preimage_mem_nhds
  apply hU.mem_nhds
  rw [affinePatch_zero]
  exact hmap hx

theorem Smale.ManifoldImmersion.eventually_affinePatch_injective_derivative {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) [J.Boundaryless] [IsManifold J ∞ N]
    {f : Smale.PlaneImmersion.Plane → N} {β : Smale.PlaneImmersion.Plane → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {K : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x)) :
    ∀ᶠ A : F × F in 𝓝 0,
      ∀ x ∈ K,
        Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J (affinePatch c f β A) x) :=
  by
  obtain ⟨ε, hε, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff hcompact hsupport
  obtain ⟨δ, hδ, hδbound⟩ :=
    Smale.PlaneImmersion.exists_radius_displacement_lt (F := F) hβ hcompact hε
  let W : Set ((F × F) × Smale.PlaneImmersion.Plane) := {q | ‖q.1‖ < δ}
  have hW : IsOpen W := isOpen_lt continuous_fst.norm continuous_const
  have hfamily :
    ContMDiffOn (𝓘(ℝ, F × F).prod 𝓘(ℝ, Smale.PlaneImmersion.Plane)) J ∞
      (fun q : (F × F) × Smale.PlaneImmersion.Plane => affinePatch c f β q.1 q.2) W := by
    intro q hq
    exact
      (contMDiffAt_affinePatch_family c hf hβ hsupport q
          (hvalid _ (hδbound q.1 hq q.2))).contMDiffWithinAt
  apply eventually_injective_nativeDerivative hW hfamily hK
  · intro x _
    change ‖(0 : F × F)‖ < δ
    simpa only [norm_zero] using hδ
  · intro x hx
    change
      Function.Injective
        (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J (affinePatch c f β (0 : F × F)) x)
    rw [affinePatch_zero]
    exact hinj x hx

theorem Smale.ManifoldImmersion.exists_immersion_patch_step {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {ι : Type*} [Finite ι]
    (p :
      ι →
        Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, Smale.PlaneImmersion.Plane) J (X :=
          Smale.PlaneImmersion.Plane) (N := N))
    (i : ι) (f : C(Smale.PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K L C : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x))
    (hLsub : L ⊆ (p i).plateau) (hfixed : ∀ x ∈ C, (p i).cutoff x = 0) :
    ∃ g : C(Smale.PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          f.HomotopicRel g C ∧
            Topology.IsClosedEmbedding (fun x : L => g x) ∧
              ∀ x ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x) := by
  have hinner := (p i).inner_compatible (hcompatible i)
  have hkeep :
    ∀ᶠ A : G × G in 𝓝 0, ∀ j, (p j).Compatible (affinePatch (p i).chart f (p i).cutoff A) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      eventually_affinePatch_maps_compact_into_open (p i).chart hf (p i).smooth.contDiff hinner
        (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    eventually_affinePatch_injective_derivative (p i).chart hf (p i).smooth.contDiff (p i).compact
      hinner hK hinj
  let Q : (Smale.PlaneImmersion.Plane → N) → Prop := fun g =>
    (∀ j, (p j).Compatible g) ∧
      ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x)
  have hQ : ∀ᶠ A : G × G in 𝓝 0, Q (affinePatch (p i).chart f (p i).cutoff A) := hkeep.and hold
  obtain ⟨g, hg, ⟨hc, hKnew⟩, ⟨Hrel⟩, hemb, hplateau⟩ :=
    exists_affine_embedding_patch_with_property (p i).chart f hf (p i).smooth.contDiff
      (p i).outer_smooth.contDiff (p i).compact (hcompatible i) (p i).nested hdim Q hQ hL hLsub
  refine ⟨g, hg, hc, ?_, hemb, ?_⟩
  · exact ⟨{ Hrel.toHomotopy with prop' := fun t x hx => Hrel.eq_fst t (hfixed x hx) }⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hKnew x hx
    · exact hplateau x (hLsub hx)

theorem Smale.ManifoldImmersion.exists_finite_patch_immersion {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {ι : Type*} [Finite ι]
    (p :
      ι →
        Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, Smale.PlaneImmersion.Plane) J (X :=
          Smale.PlaneImmersion.Plane) (N := N))
    (L : ι → Set Smale.PlaneImmersion.Plane) (hL : ∀ i, IsCompact (L i))
    (hLsub : ∀ i, L i ⊆ (p i).plateau) (f : C(Smale.PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f)
    (hcompatible : ∀ i, (p i).Compatible f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K C : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x))
    (hfixed : ∀ i x, x ∈ C → (p i).cutoff x = 0) (s : Finset ι) :
    ∃ g : C(Smale.PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ g ∧
        (∀ i, (p i).Compatible g) ∧
          f.HomotopicRel g C ∧
            ∀ x ∈ K ∪ ⋃ i ∈ s, L i,
              Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, ContinuousMap.HomotopicRel.refl f, ?_⟩
    simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] using
      hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) := hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, -, hinj₂⟩ :=
      exists_immersion_patch_step p i g₁ hg₁ hc₁ hdim hKold (hL i) hinj₁ (hLsub i) (hfixed i)
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply hinj₂ x
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hxj
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjs, hxj⟩))

theorem Smale.ManifoldImmersion.exists_relative_immersion_patch_at_in_open {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∉ C) {O : Set N} (hO : IsOpen O) (hxO : f x ∈ O) :
    ∃ p : Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ L : Set E,
        p.Compatible f ∧
          IsCompact L ∧
            L ∈ 𝓝 x ∧ L ⊆ p.plateau ∧ (∀ y ∈ C, p.cutoff y = 0) ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  let c := Smale.PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∩ Cᶜ ∈ 𝓝 x :=
    ((c.open_source.preimage f.continuous).inter hC.isOpen_compl).mem_nhds ⟨hsource, hx⟩
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hU
  have hχone : {y : E | χ y = 1} ∈ 𝓝 x := χ.eventuallyEq_one
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hχone
  let p : Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N) :=
    { chart := c
      cutoff := β
      outer := χ
      smooth := β.contMDiff
      outer_smooth := χ.contMDiff
      compact := β.hasCompactSupport
      outer_compact := χ.hasCompactSupport
      nested := fun y hy => hβ hy }
  have hxp : x ∈ p.plateau := mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one
  obtain ⟨L, hxL, hLp, hL⟩ := local_compact_nhds (isOpen_interior.mem_nhds hxp)
  refine ⟨p, L, (fun _ hy => (hχ hy).1), hL, hxL, hLp, ?_, fun _ hz => hz.2⟩
  intro y hy
  change β y = 0
  by_contra hne
  have hi : y ∈ tsupport β := subset_tsupport β hne
  have ho : y ∈ tsupport χ :=
    subset_tsupport χ
      (by
        change χ y ≠ 0
        rw [hβ hi]
        exact one_ne_zero)
  exact (hχ ho).2 hy

theorem Smale.ManifoldImmersion.exists_relative_immersion_patch_at {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∉ C) :
    ∃ p : Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ L : Set E,
        p.Compatible f ∧ IsCompact L ∧ L ∈ 𝓝 x ∧ L ⊆ p.plateau ∧ ∀ y ∈ C, p.cutoff y = 0 := by
  obtain ⟨p, L, hc, hL, hn, hp, hfix, _⟩ :=
    exists_relative_immersion_patch_at_in_open (J := J) f hC hx isOpen_univ (Set.mem_univ _)
  exact ⟨p, L, hc, hL, hn, hp, hfix⟩

theorem Smale.ManifoldImmersion.exists_immersion_on_compact_rel {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(Smale.PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K L C : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x))
    (hC : IsClosed C) (hdis : Disjoint L C) :
    ∃ g : C(Smale.PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ g ∧
        f.HomotopicRel g C ∧
          ∀ x ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x) := by
  classical
  have hp (x : L) :=
    exists_relative_immersion_patch_at (J := J) f hC
      (show (x : Smale.PlaneImmersion.Plane) ∉ C from fun hx =>
        Set.disjoint_left.mp hdis x.property hx)
  choose p T hcompatible hT hn hsub hfixed using hp
  have hcover : L ⊆ ⋃ x : L, interior (T x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ :=
    hL.elim_finite_subcover (fun x : L => interior (T x)) (fun _ => isOpen_interior) hcover
  obtain ⟨g, hg, -, hhom, hderiv⟩ :=
    exists_finite_patch_immersion (fun i : s => p i.1) (fun i : s => T i.1) (fun i => hT i.1)
      (fun i => hsub i.1) f hf (fun i => hcompatible i.1) hdim hK hinj (fun i => hfixed i.1)
      Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro x hx
  apply hderiv x
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨⟨i, his⟩, Finset.mem_univ _, interior_subset hxi⟩)

theorem Smale.ManifoldImmersion.exists_selfIntersection_removal_step_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {D : Set E} {O : Set N}
    (hsource : (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          Smale.HomotopicRelWithin f g C D O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x)) ∧
              ∀ x y, g x = g y → f x = f y ∧ (p i).cutoff x = (p i).cutoff y := by
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
        (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    Smale.ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf (p i).smooth
      (p i).compact (hcompatible i) hK hinj
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp (hkeep.and hold)
  obtain ⟨r, hr, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid (p i).chart hf (p i).smooth (p i).compact
      (hcompatible i)
  obtain ⟨a, ha, -, hsmooth, hremove⟩ :=
    Smale.ChartMapPerturbation.exists_small_collision_removing_parameter (p i).chart hf
      (p i).smooth (p i).compact (hcompatible i) hdim (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let g : C(E, N) := ⟨_, hsmooth.continuous⟩
  have hretained :=
    hδkeep (show a ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  refine ⟨g, hsmooth, hretained.1, ?_, hretained.2, hremove⟩
  have hrel :=
    Smale.ChartMapPerturbation.homotopicRelWithin_of_source_subset (p i).chart hf (p i).smooth
      (hcompatible i) hvalid har hsource hmaps
  exact hrel.mono (fun x hx => (p i).fixed x hx) (Set.Subset.refl D) (Set.Subset.refl O)

theorem Smale.ManifoldImmersion.exists_finite_selfIntersection_removal_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {D : Set E} {O : Set N}
    (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) (s : Finset ι) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          Smale.HomotopicRelWithin f g C D O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x)) ∧
              ∀ x y, g x = g y → f x = f y ∧ ∀ i ∈ s, (p i).cutoff x = (p i).cutoff y := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    exact
      ⟨f, hf, hcompatible, Smale.HomotopicRelWithin.refl f C hmaps, hinj, fun _ _ hxy =>
        ⟨hxy, fun _ hi => False.elim (Finset.notMem_empty _ hi)⟩⟩
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁, hpair₁⟩ := ih
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hinj₂, hpair₂⟩ :=
      exists_selfIntersection_removal_step_within_target p i g₁ hg₁ hc₁ hdim hK hinj₁ (hsource i)
        hhom₁.mapsTo_right
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, hinj₂, ?_⟩
    intro x y hxy
    have hnew := hpair₂ x y hxy
    have hold := hpair₁ x y hnew.1
    refine ⟨hold.1, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact hnew.2
    · exact hold.2 j hjs

theorem Smale.ManifoldImmersion.exists_embedding_of_finite_separating_patches_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hseparate : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → f x = f y → ∃ i, (p i).cutoff x ≠ (p i).cutoff y)
    {D : Set E} {O : Set N} (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        Smale.HomotopicRelWithin f g C D O ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨g, hg, -, hhom, hinjg, hpairs⟩ :=
    exists_finite_selfIntersection_removal_within_target p f hf hcompatible hdim hK hinj hsource
      hmaps Finset.univ
  refine ⟨g, hg, hhom, ?_, hinjg⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  obtain ⟨hold, hcutoffs⟩ := hpairs x y hxy
  obtain ⟨i, hi⟩ := hseparate x x.property y y.property hne hold
  exact hi (hcutoffs i (Finset.mem_univ i))

theorem Smale.ManifoldImmersion.exists_separating_patch_in_open {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x y : E} (hx : x ∉ C) (hxy : x ≠ y) {O : Set N} (hO : IsOpen O)
    (hxO : f x ∈ O) :
    ∃ p : Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x = 1 ∧ p.cutoff y = 0 ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  let c := Smale.PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∩ (C ∪ { y })ᶜ ∈ 𝓝 x := by
    apply
      ((c.open_source.preimage f.continuous).inter
          ((hC.union isClosed_singleton).isOpen_compl)).mem_nhds
    exact ⟨hsource, fun h => h.elim hx (fun h => hxy h)⟩
  obtain ⟨β, -, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hU
  let p : Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C :=
    { chart := c
      cutoff := β
      smooth := β.contMDiff
      compact := β.hasCompactSupport
      fixed := fun z hz => image_eq_zero_of_notMem_tsupport (fun ht => (hβ ht).2 (Or.inl hz)) }
  refine ⟨p, (fun _ ht => (hβ ht).1), β.eq_one, ?_, fun _ hz => hz.2⟩
  exact image_eq_zero_of_notMem_tsupport (fun ht => (hβ ht).2 (Or.inr rfl))

theorem Smale.ManifoldImmersion.exists_separating_patch_of_not_both_fixed_in_open
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N))
    {C : Set E} (hC : IsClosed C) {x y : E} (hxy : x ≠ y) (hfixed : ¬(x ∈ C ∧ y ∈ C)) {O : Set N}
    (hO : IsOpen O) (hxO : x ∉ C → f x ∈ O) (hyO : y ∉ C → f y ∈ O) :
    ∃ p : Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x ≠ p.cutoff y ∧ p.chart.source ⊆ O := by
  by_cases hx : x ∈ C
  · have hy : y ∉ C := fun hy => hfixed ⟨hx, hy⟩
    obtain ⟨p, hp, hpy, hpx, hs⟩ :=
      exists_separating_patch_in_open (J := J) f hC hy hxy.symm hO (hyO hy)
    exact ⟨p, hp, by rw [hpx, hpy]; exact zero_ne_one, hs⟩
  · obtain ⟨p, hp, hpx, hpy, hs⟩ :=
      exists_separating_patch_in_open (J := J) f hC hx hxy hO (hxO hx)
    exact ⟨p, hp, by rw [hpx, hpy]; exact one_ne_zero, hs⟩

theorem Smale.ManifoldImmersion.exists_open_injOn_of_injective_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {U : Set E} {x : E} (hU : IsOpen U)
    (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U) (hinj : Function.Injective (fderiv ℝ f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ Set.InjOn f V := by
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  have hdf := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hderiv : HasFDerivAt (L ∘ f) (ContinuousLinearMap.id ℝ E) x := by
    convert L.hasFDerivAt.comp x hdf.hasFDerivAt using 1
    ext v
    exact (hL v).symm
  have hcomp : ContDiffOn ℝ ∞ (L ∘ f) U := L.contDiff.comp_contDiffOn hf
  have hinv : (fderiv ℝ (L ∘ f) x).IsInvertible := by
    rw [hderiv.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  obtain ⟨φ, hxφ, hφU, hφeq⟩ := NoExotic.exists_partialDiffeomorph_of_contDiffOn hU hx hcomp hinv
  refine ⟨φ.source, φ.open_source, hxφ, hφU, ?_⟩
  intro y hy z hz hyz
  apply φ.toPartialEquiv.injOn hy hz
  rw [hφeq]
  exact congrArg L hyz

theorem Smale.ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative_on {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : E → N} {W : Set E} (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W)
    {x : E} (hxW : x ∈ W) (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ Set.InjOn f V := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  have hx : f x ∈ c.source := mem_extChartAt_source (f x)
  let U := W ∩ f ⁻¹' c.source
  have hU : IsOpen U := hf.continuousOn.isOpen_inter_preimage hW c.open_source
  have hc : ContDiffOn ℝ ∞ (c ∘ f) U :=
    (c.contMDiffOn_toFun.comp (hf.mono Set.inter_subset_left) (fun _ h => h.2)).contDiffOn
  have hfx := hf.contMDiffAt (hW.mem_nhds hxW)
  have hi := (injective_fderiv_chart_iff c (hfx.mdifferentiableAt (by simp)) hx).mpr hinj
  obtain ⟨V, hV, hxV, hVU, hinjV⟩ := exists_open_injOn_of_injective_fderiv hU ⟨hxW, hx⟩ hc hi
  exact
    ⟨V, hV, hxV, hVU.trans Set.inter_subset_left, fun _ hy _ hz heq =>
      hinjV hy hz (congrArg c heq)⟩

theorem Smale.ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : E → N} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {x : E}
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ Set.InjOn f V := by
  obtain ⟨V, hV, hxV, _, hinjV⟩ :=
    exists_open_injOn_of_injective_nativeDerivative_on isOpen_univ hf.contMDiffOn (Set.mem_univ x)
      hinj
  exact ⟨V, hV, hxV, hinjV⟩

theorem Smale.ManifoldImmersion.exists_open_injOn_near_compact_on {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : E → N} {W : Set E} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    (hinj : Set.InjOn f K) (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ Set.InjOn f V := by
  have hc : ∀ x ∈ K, ContinuousAt f x := fun x hx =>
    hf.continuousOn.continuousAt (hW.mem_nhds (hKW hx))
  have hlocal : ∀ x ∈ K, ∃ V ∈ nhds x, Set.InjOn f V := by
    intro x hx
    obtain ⟨V, hV, hxV, _, hinjV⟩ :=
      exists_open_injOn_of_injective_nativeDerivative_on hW hf (hKW hx) (hi x hx)
    exact ⟨V, hV.mem_nhds hxV, hinjV⟩
  obtain ⟨V, hV, hKV, hinjV⟩ := hinj.exists_isOpen_superset hK hc hlocal
  exact
    ⟨V ∩ W, hV.inter hW, fun _ hx => ⟨hKV hx, hKW hx⟩, Set.inter_subset_right,
      hinjV.mono Set.inter_subset_left⟩

theorem Smale.ManifoldImmersion.exists_open_embedded_immersive_neighborhood {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : E → N} {W : Set E} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    (hinj : Set.InjOn f K) (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧ V ⊆ W ∧ Set.InjOn f V ∧ ∀ x ∈ V, Function.Injective (mfderiv 𝓘(ℝ, E) J f x) := by
  let O := {x : E | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)}
  have hO : IsOpen O := isOpen_injective_derivative_on hW hf
  have hOW : O ⊆ W := fun _ hx => hx.1
  obtain ⟨V, hV, hKV, hVO, hinjV⟩ :=
    exists_open_injOn_near_compact_on hO (hf.mono hOW) hK (fun x hx => ⟨hKW hx, hi x hx⟩) hinj hi
  exact ⟨V, hV, hKV, hVO.trans hOW, hinjV, fun x hx => (hVO hx).2⟩

theorem Smale.ManifoldImmersion.exists_open_injOn_near_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {f : E → N} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {K : Set E} (hK : IsCompact K)
    (hinj : Set.InjOn f K) (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ Set.InjOn f V := by
  apply hinj.exists_isOpen_superset hK (fun _ _ => hf.continuous.continuousAt)
  intro x hx
  obtain ⟨V, hV, hxV, hinjV⟩ := exists_open_injOn_of_injective_nativeDerivative hf (hi x hx)
  exact ⟨V, hV.mem_nhds hxV, hinjV⟩

def Smale.ManifoldImmersion.doublePoints {X N : Type*} (f : X → N) (K : Set X) : Set (X × X) :=
  {q | q.1 ∈ K ∧ q.2 ∈ K ∧ q.1 ≠ q.2 ∧ f q.1 = f q.2}

theorem Smale.ManifoldImmersion.isCompact_doublePoints_of_locally_injective {X N : Type*}
    [TopologicalSpace X] [TopologicalSpace N] [T2Space N] {f : X → N} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U) :
    IsCompact (doublePoints f K) := by
  classical
  choose U hU hmem hinj using (fun x : K => hlocal x x.property)
  let V : Set (X × X) := ⋃ x : K, (U x) ×ˢ (U x)
  have hV : IsOpen V := isOpen_iUnion (fun x => (hU x).prod (hU x))
  have hclosed : IsClosed {q : X × X | f q.1 = f q.2} :=
    isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)
  have heq : doublePoints f K = ((K ×ˢ K) ∩ {q : X × X | f q.1 = f q.2}) ∩ Vᶜ := by
    ext q
    constructor
    · rintro ⟨hx, hy, hne, hcoll⟩
      refine ⟨⟨⟨hx, hy⟩, hcoll⟩, ?_⟩
      intro hv
      obtain ⟨x, hxU, hyU⟩ := Set.mem_iUnion.mp hv
      exact hne (hinj x hxU hyU hcoll)
    · rintro ⟨⟨⟨hx, hy⟩, hcoll⟩, hv⟩
      refine ⟨hx, hy, ?_, hcoll⟩
      intro hxy
      apply hv
      apply Set.mem_iUnion.mpr
      refine ⟨⟨q.1, hx⟩, hmem ⟨q.1, hx⟩, ?_⟩
      rw [← hxy]
      exact hmem ⟨q.1, hx⟩
  rw [heq]
  exact ((hK.prod hK).inter_right hclosed).inter_right hV.isClosed_compl

theorem Smale.ManifoldImmersion.isCompact_doublePoints_of_injective_nativeDerivative
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : E → N} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {K : Set E}
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    IsCompact (doublePoints f K) :=
  isCompact_doublePoints_of_locally_injective hf.continuous hK
    (fun _ hx => exists_open_injOn_of_injective_nativeDerivative hf (hinj _ hx))

theorem Smale.ManifoldImmersion.exists_compact_embedding_of_immersion_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) {K C : Set E} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C)) {O : Set N} (hO : IsOpen O) (hmaps : Set.MapsTo f (K \ C) O) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        Smale.HomotopicRelWithin f g C (K \ C) O ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  classical
  let bad := doublePoints f K
  have hbad : IsCompact bad := isCompact_doublePoints_of_injective_nativeDerivative hf hK hinj
  have hp (q : bad) :
    ∃ p : Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff q.1.1 ≠ p.cutoff q.1.2 ∧ p.chart.source ⊆ O := by
    have hq := q.property
    rcases hq with ⟨hx, hy, hne, heq⟩
    have hnot : ¬(q.1.1 ∈ C ∧ q.1.2 ∈ C) := by
      rintro ⟨hxC, hyC⟩
      exact hne (hfixed ⟨hx, hxC⟩ ⟨hy, hyC⟩ heq)
    exact
      exists_separating_patch_of_not_both_fixed_in_open f hC hne hnot hO
        (fun hxC => hmaps ⟨hx, hxC⟩) (fun hyC => hmaps ⟨hy, hyC⟩)
  choose p hpcompatible hpactive hpsource using hp
  let U (q : bad) : Set (E × E) := {r | (p q).cutoff r.1 ≠ (p q).cutoff r.2}
  have hU (q : bad) : IsOpen (U q) :=
    isOpen_ne_fun ((p q).smooth.continuous.comp continuous_fst)
      ((p q).smooth.continuous.comp continuous_snd)
  have hcover : bad ⊆ ⋃ q : bad, U q := by
    intro q hq
    exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hpactive ⟨q, hq⟩⟩
  obtain ⟨s, hs⟩ := hbad.elim_finite_subcover U hU hcover
  refine
    exists_embedding_of_finite_separating_patches_within_target (fun i : s => p i.1) f hf
      (fun i => hpcompatible i.1) hdim hK hinj ?_ (fun i => hpsource i.1) hmaps
  intro x hx y hy hne heq
  have hxy : (x, y) ∈ bad := ⟨hx, hy, hne, heq⟩
  obtain ⟨i, hi, hsep⟩ := Set.mem_iUnion₂.mp (hs hxy)
  exact ⟨⟨i, hi⟩, hsep⟩

theorem Smale.ManifoldImmersion.exists_compact_embedding_of_immersion {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) {K C : Set E} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C)) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  obtain ⟨g, hg, hrel, he, hi⟩ :=
    exists_compact_embedding_of_immersion_within_target f hf hdim hK hinj hC hfixed isOpen_univ
      (Set.mapsTo_univ f (K \ C))
  exact ⟨g, hg, hrel.homotopicRel, he, hi⟩

theorem Smale.ManifoldImmersion.exists_relative_compact_embedding {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(Smale.PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K C : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x)) :
    ∃ g : C(Smale.PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x) := by
  let U : Set Smale.PlaneImmersion.Plane :=
    {x | Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x)}
  have hU : IsOpen U := isOpen_injective_derivative hf
  have hCU : K ∩ C ⊆ U := fun x hx => hderiv x hx
  obtain ⟨D, hD, hCD, hDU⟩ := exists_compact_between (hK.inter_right hC) hU hCU
  let L := K \ interior D
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hdis : Disjoint L C := Set.disjoint_left.mpr (fun _ hx hxC => hx.2 (hCD ⟨hx.1, hxC⟩))
  obtain ⟨g₁, hg₁, hhom₁, hinj₁⟩ :=
    exists_immersion_on_compact_rel f hf hdim hD hL (fun x hx => hDU hx) hC hdis
  have hKinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g₁ x) := by
    intro x hx
    apply hinj₁ x
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr ⟨hx, fun hi => hxD (interior_subset hi)⟩
  have hfixed₁ : Set.InjOn g₁ (K ∩ C) := by
    intro x hx y hy hxy
    apply hfixed hx hy
    rw [hhom₁.fst_eq_snd hx.2, hhom₁.fst_eq_snd hy.2]
    exact hxy
  have hd : 2 * Module.finrank ℝ Smale.PlaneImmersion.Plane < Module.finrank ℝ G := by
    simp only [Smale.PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨g₂, hg₂, hhom₂, hemb, hinj₂⟩ :=
    exists_compact_embedding_of_immersion g₁ hg₁ hd hK hKinj hC hfixed₁
  exact ⟨g₂, hg₂, hhom₁.trans hhom₂, hemb, hinj₂⟩

theorem Smale.ManifoldImmersion.injective_mfderiv_comp_linearEquiv_iff {E E' G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (e : E' ≃L[ℝ] E) {f : E → N} {x : E'}
    (hf : MDifferentiableAt 𝓘(ℝ, E) J f (e x)) :
    Function.Injective (mfderiv 𝓘(ℝ, E') J (f ∘ e) x) ↔
      Function.Injective (mfderiv 𝓘(ℝ, E) J f (e x)) := by
  have he : mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) e x = e.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact e.toContinuousLinearMap.fderiv
  have hesmooth : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ e := e.contDiff.contMDiff
  rw [mfderiv_comp x hf (hesmooth.mdifferentiableAt (by simp)), he]
  constructor
  · intro h v w hvw
    apply e.symm.injective
    apply h
    change (mfderiv 𝓘(ℝ, E) J f (e x)) (e (e.symm v)) = (mfderiv 𝓘(ℝ, E) J f (e x)) (e (e.symm w))
    exact
      (congrArg (mfderiv 𝓘(ℝ, E) J f (e x)) (e.apply_symm_apply (v : E))).trans
        (hvw.trans (congrArg (mfderiv 𝓘(ℝ, E) J f (e x)) (e.apply_symm_apply (w : E))).symm)
  · exact fun h => h.comp e.injective

theorem Smale.ManifoldImmersion.exists_relative_compact_embedding_twoDimensional {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N]
    [T2Space N] (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hsourceDim : Module.finrank ℝ E = 2)
    (hdim : 5 ≤ Module.finrank ℝ G) {K C : Set E} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  let e : Smale.PlaneImmersion.Plane ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq
      (by
        simp only [Smale.PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
        omega)
  let fp : C(Smale.PlaneImmersion.Plane, N) := ⟨f ∘ e, f.continuous.comp e.continuous⟩
  have hfp : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ fp := hf.comp e.contDiff.contMDiff
  have hKp : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hCp : IsClosed (e ⁻¹' C) := hC.preimage e.continuous
  have hfixedp : Set.InjOn fp ((e ⁻¹' K) ∩ (e ⁻¹' C)) := by
    intro x hx y hy hxy
    exact e.injective (hfixed ⟨hx.1, hx.2⟩ ⟨hy.1, hy.2⟩ hxy)
  have hderivp :
    ∀ x ∈ (e ⁻¹' K) ∩ (e ⁻¹' C),
      Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J fp x) := by
    intro x hx
    exact
      (injective_mfderiv_comp_linearEquiv_iff e (hf.mdifferentiableAt (by simp))).mpr
        (hderiv (e x) ⟨hx.1, hx.2⟩)
  obtain ⟨gp, hgp, ⟨Hrel⟩, hembp, hgpderiv⟩ :=
    exists_relative_compact_embedding fp hfp hdim hKp hCp hfixedp hderivp
  let g : C(E, N) := ⟨gp ∘ e.symm, gp.continuous.comp e.symm.continuous⟩
  have hg : ContMDiff 𝓘(ℝ, E) J ∞ g := hgp.comp e.symm.contDiff.contMDiff
  have hpreK (x : E) (hx : x ∈ K) : e.symm x ∈ e ⁻¹' K := by
    change e (e.symm x) ∈ K
    simpa only [e.apply_symm_apply] using hx
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · refine
      ⟨{  toFun := fun q => Hrel (q.1, e.symm q.2)
          continuous_toFun :=
            Hrel.continuous.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
          map_zero_left := ?_
          map_one_left := ?_
          prop' := ?_ }⟩
    · intro x
      rw [Hrel.apply_zero]
      exact congrArg f (e.apply_symm_apply x)
    · intro x
      exact Hrel.apply_one (e.symm x)
    · intro t x hx
      change Hrel (t, e.symm x) = f x
      have hpreC : e.symm x ∈ e ⁻¹' C := by
        change e (e.symm x) ∈ C
        simpa only [e.apply_symm_apply] using hx
      rw [Hrel.eq_fst t hpreC]
      exact congrArg f (e.apply_symm_apply x)
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    apply Subtype.ext
    apply e.symm.injective
    have hpeq : gp (e.symm x) = gp (e.symm y) := hxy
    exact
      congrArg Subtype.val
        (hembp.injective (a₁ := ⟨e.symm x, hpreK x x.property⟩) (a₂ :=
          ⟨e.symm y, hpreK y y.property⟩) hpeq)
  · intro x hx
    exact
      (injective_mfderiv_comp_linearEquiv_iff e.symm (hgp.mdifferentiableAt (by simp))).mpr
        (hgpderiv (e.symm x) (hpreK x hx))

theorem Smale.ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ g '' A) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              Set.MapsTo f' K O ∧ ∀ x ∈ K \ B, f' x ∉ g '' A := by
  let L : Set E := K \ interior C
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A := by
    intro x hx
    exact hclean x ⟨hx.1.1, hx.2⟩ (fun hxB => hx.1.2 (hBC hxB))
  obtain ⟨f', hf', hhom, hemb, hderiv', -, hmaps', havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image f g A hf hg hclosed hself hobstacle hK
      hL hC hinj hderiv hfixed hO hmaps
  refine ⟨f', hf', hhom, hemb, hderiv', hmaps', ?_⟩
  intro x hx
  by_cases hxC : x ∈ C
  · exact havoid x (Or.inl (hclean x ⟨hx.1, hxC⟩ hx.2))
  · exact havoid x (Or.inr ⟨hx.1, fun hi => hxC (interior_subset hi)⟩)

theorem Smale.ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, f' x ∉ Set.range g := by
  obtain ⟨f', hf', hhom, hemb, hd, -, havoid⟩ :=
    exists_embedded_image_avoidance_relative_neighborhood f g Set.univ hf hg
      (by simpa only [Set.image_univ] using hclosed) hself hobstacle hK hC hBC hinj hderiv
      (by simpa only [Set.image_univ] using hclean) isOpen_univ (fun _ _ => Set.mem_univ _)
  refine ⟨f', hf', hhom, hemb, hd, ?_⟩
  simpa only [Set.image_univ] using havoid

theorem
  Smale.ManifoldImmersion.exists_relative_embedded_avoidance_of_clean_neighborhood_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hsourceDim : Module.finrank ℝ E = 2)
    (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, f' x ∉ Set.range g := by
  obtain ⟨f₁, hf₁, hhom₁, hemb₁, hderiv₁⟩ :=
    exists_relative_compact_embedding_twoDimensional f hf hsourceDim hdim hK hC hinj hderiv
  have hinj₁ : Set.InjOn f₁ K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb₁.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hclean₁ : ∀ x ∈ K ∩ C, x ∉ B → f₁ x ∉ Set.range g := by
    intro x hx hxB
    rw [← hhom₁.fst_eq_snd hx.2]
    exact hclean x hx hxB
  have hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G := by omega
  obtain ⟨f₂, hf₂, hhom₂, hemb₂, hderiv₂, havoid₂⟩ :=
    exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f₁ g hf₁ hg hclosed hself
      hobstacle hK hC hBC hinj₁ hderiv₁ hclean₁
  exact ⟨f₂, hf₂, hhom₁.trans hhom₂, hemb₂, hderiv₂, havoid₂⟩

theorem Smale.ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] [CompactSpace Y]
    (f : C(E, N)) (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, f' x ∉ Set.range g :=
  exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f g hf hg
    (isCompact_range g.continuous).isClosed hself hobstacle hK hC hBC hinj hderiv hclean

def Smale.OpenObstacle.source {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) : TopologicalSpace.Opens Y :=
  ⟨g ⁻¹' (U : Set N), U.isOpen.preimage g.continuous⟩

def Smale.OpenObstacle.restrict {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) : C(source g U, U)
    where
  toFun y := ⟨g y, y.property⟩
  continuous_toFun := (g.continuous.comp continuous_subtype_val).subtype_mk _

theorem Smale.OpenObstacle.mem_range_restrict_iff {Y N : Type*} [TopologicalSpace Y]
    [TopologicalSpace N] (g : C(Y, N)) (U : TopologicalSpace.Opens N) (x : U) :
    x ∈ Set.range (Smale.OpenObstacle.restrict g U) ↔ (x : N) ∈ Set.range g := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    have hyU : y ∈ source g U := by
      change g y ∈ U
      exact hy.symm ▸ x.property
    exact ⟨⟨y, hyU⟩, Subtype.ext hy⟩

theorem Smale.OpenObstacle.range_restrict {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) :
    Set.range (Smale.OpenObstacle.restrict g U) = (Subtype.val : U → N) ⁻¹' Set.range g := by
  ext x
  exact mem_range_restrict_iff g U x

theorem Smale.OpenObstacle.isClosed_range_restrict {Y N : Type*} [TopologicalSpace Y]
    [TopologicalSpace N] (g : C(Y, N)) (U : TopologicalSpace.Opens N)
    (hclosed : IsClosed (Set.range g)) : IsClosed (Set.range (Smale.OpenObstacle.restrict g U)) :=
  by
  rw [Smale.OpenObstacle.range_restrict]
  exact hclosed.preimage continuous_subtype_val

theorem Smale.OpenObstacle.image_restrict {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) (A : Set Y) :
    Smale.OpenObstacle.restrict g U '' ((Subtype.val : source g U → Y) ⁻¹' A) =
      (Subtype.val : U → N) ⁻¹' (g '' A) := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    exact ⟨y, hy, congrArg Subtype.val heq⟩
  · rintro ⟨y, hy, heq⟩
    have hyU : y ∈ source g U := by
      change g y ∈ U
      exact heq.symm ▸ x.property
    exact ⟨⟨y, hyU⟩, hy, Subtype.ext heq⟩

theorem Smale.OpenObstacle.isClosed_image_restrict {Y N : Type*} [TopologicalSpace Y]
    [TopologicalSpace N] (g : C(Y, N)) (U : TopologicalSpace.Opens N) (A : Set Y)
    (hclosed : IsClosed (g '' A)) :
    IsClosed (Smale.OpenObstacle.restrict g U '' ((Subtype.val : source g U → Y) ⁻¹' A)) := by
  rw [Smale.OpenObstacle.image_restrict]
  exact hclosed.preimage continuous_subtype_val

theorem Smale.OpenObstacle.contMDiff_restrict {E' G H H' Y N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace H N] (g : C(Y, N))
    (U : TopologicalSpace.Opens N) (hg : ContMDiff I' J ∞ g) :
    ContMDiff I' J ∞ (Smale.OpenObstacle.restrict g U) := by
  apply (ContMDiff.subtypeVal_comp_iff U (Smale.OpenObstacle.restrict g U)).mp
  exact hg.comp contMDiff_subtype_val

theorem MorseCancel.exists_smooth_path_avoiding_closed_image {E G H H' N Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] {x y : N}
    (γ : Path x y) (g : C(Y, N)) (hg : ContMDiff I J ∞ g) (hclosed : IsClosed (Set.range g))
    (hdim : 1 + Module.finrank ℝ E < Module.finrank ℝ G) (hx : x ∉ Set.range g)
    (hy : y ∉ Set.range g) : ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, η t ∉ Set.range g := by
  obtain ⟨f, hf, hf0, hf1⟩ := Smale.exists_smooth_connecting_curve (J := J) γ
  let fI : C(unitInterval, N) := ⟨fun t => f t, f.continuous.comp continuous_subtype_val⟩
  have hfI : ContMDiff (𝓡∂ 1) J ∞ fI := hf.comp contMDiff_subtypeVal_Icc
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) + Module.finrank ℝ E < Module.finrank ℝ G := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  have hfixed : ∀ t ∈ ({0, 1} : Set unitInterval), fI t ∉ Set.range g := by
    intro t ht
    rcases ht with rfl | ht
    · change f 0 ∉ Set.range g
      rwa [hf0]
    · have ht1 : t = 1 := ht
      subst t
      change f 1 ∉ Set.range g
      rwa [hf1]
  obtain ⟨f', hf', hrel, hdisjoint⟩ :=
    Smale.GeneralPosition.exists_disjoint_smooth_map_homotopicRel_of_isClosed_range fI g hfI hg
      hclosed hdim' ((Set.finite_singleton (1 : unitInterval)).insert 0).isClosed hfixed
  have h0 : f' 0 = x := (hrel.fst_eq_snd (by simp)).symm.trans hf0
  have h1 : f' 1 = y := (hrel.fst_eq_snd (by simp)).symm.trans hf1
  let η : Path x y := { toContinuousMap := f', source' := h0, target' := h1 }
  exact ⟨η, hf', fun t ht => Set.disjoint_left.mp hdisjoint ⟨t, rfl⟩ ht⟩

theorem MorseCancel.exists_smooth_path_avoiding_closed_image_in_open {E G H H' N Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
    (U : TopologicalSpace.Opens N) {x y : U} (γ : Path x y) (g : C(Y, N)) (hg : ContMDiff I J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hdim : 1 + Module.finrank ℝ E < Module.finrank ℝ G)
    (hx : x.val ∉ Set.range g) (hy : y.val ∉ Set.range g) :
    ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, (η t).val ∉ Set.range g := by
  obtain ⟨η, hη, havoid⟩ :=
    exists_smooth_path_avoiding_closed_image γ (Smale.OpenObstacle.restrict g U)
      (Smale.OpenObstacle.contMDiff_restrict g U hg)
      (Smale.OpenObstacle.isClosed_range_restrict g U hclosed) hdim
      (fun h => hx ((Smale.OpenObstacle.mem_range_restrict_iff g U x).mp h))
      (fun h => hy ((Smale.OpenObstacle.mem_range_restrict_iff g U y).mp h))
  exact
    ⟨η, hη, fun t ht => havoid t ((Smale.OpenObstacle.mem_range_restrict_iff g U (η t)).mpr ht)⟩

theorem Smale.ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact_within_target
    {E G H H' X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] (f : C(X, N)) {K C U : Set X}
    (hK : IsCompact K) (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (hfK : ContMDiffOn I J ∞ f Kᶜ) {D : Set X} {O : Set N}
    (hO : IsOpen O) (hKO : Set.MapsTo f K O) (hmaps : Set.MapsTo f D O) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ Smale.HomotopicRelWithin f f' C D O := by
  classical
  have hp (x : K) :=
    exists_smoothing_patch_at_in_open (I := I) (J := J) f (x : X) hO (hKO x.property)
  choose p hcompatible hplateau hsource using hp
  have hcover : K ⊆ ⋃ x : K, (p x).plateau := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hplateau ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ :=
    hK.elim_finite_subcover (fun x : K => (p x).plateau) (fun _ => isOpen_interior) hcover
  obtain ⟨f', _, hhom, hsm⟩ :=
    exists_finite_patch_smoothing_within_target (fun i : s => p i.1) f (fun i => hcompatible i.1)
      hC hU hCU hfU (fun i => hsource i.1) hmaps Finset.univ
  refine ⟨f', ?_, hhom⟩
  intro x
  apply hsm x
  by_cases hx : x ∈ K
  · obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Or.inr ⟨⟨i, his⟩, Finset.mem_univ _, hxi⟩
  · exact Or.inl ((hfK x hx).contMDiffAt (hK.isClosed.isOpen_compl.mem_nhds hx))

theorem Smale.ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact
    {E G H H' X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] (f : C(X, N)) {K C U : Set X}
    (hK : IsCompact K) (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (hfK : ContMDiffOn I J ∞ f Kᶜ) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  obtain ⟨f', hf', hrel⟩ :=
    exists_smooth_map_homotopicRel_of_smooth_off_compact_within_target f hK hC hU hCU hfU hfK
      isOpen_univ (Set.mapsTo_univ f K) (Set.mapsTo_univ f Set.univ)
  exact ⟨f', hf', hrel.homotopicRel⟩

theorem Smale.CurveImmersion.exists_continuous_curve_with_endpoint_germs {N : Type*}
    [TopologicalSpace N] (a b : C(ℝ, N)) (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N), Set.EqOn f a (Set.Iic (1 / 4 : ℝ)) ∧ Set.EqOn f b (Set.Ici (3 / 4 : ℝ)) := by
  classical
  let α : Path (a (1 / 4)) (a 0) :=
    Path.ofLine (f := fun t : ℝ => a ((1 - t) / 4))
      ((a.continuous.comp ((continuous_const.sub continuous_id).div_const 4)).continuousOn)
      (by norm_num) (by norm_num)
  let β : Path (b 1) (b (3 / 4)) :=
    Path.ofLine (f := fun t : ℝ => b (1 - t / 4))
      ((b.continuous.comp (continuous_const.sub (continuous_id.div_const 4))).continuousOn)
      (by norm_num) (by norm_num)
  let η := α.trans (γ.trans β)
  let mid : ℝ → N := fun t => η.extend (2 * t - 1 / 2)
  have hmid : Continuous mid :=
    η.continuous_extend.comp ((continuous_const.mul continuous_id).sub continuous_const)
  have hm₀ : mid (1 / 4) = a (1 / 4) := by
    change η.extend (2 * (1 / 4) - 1 / 2) = _
    norm_num
  have hm₁ : mid (3 / 4) = b (3 / 4) := by
    change η.extend (2 * (3 / 4) - 1 / 2) = _
    norm_num
  let right : ℝ → N := fun t => if t ≤ 3 / 4 then mid t else b t
  have hr : Continuous right :=
    hmid.if_le b.continuous continuous_id continuous_const (fun t ht => ht ▸ hm₁)
  let f : ℝ → N := fun t => if t ≤ 1 / 4 then a t else right t
  have hf : Continuous f :=
    a.continuous.if_le hr continuous_id continuous_const
      (by
        intro t ht
        subst t
        simpa only [right, if_pos (show (1 / 4 : ℝ) ≤ 3 / 4 by norm_num)] using hm₀.symm)
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro t ht
    exact if_pos ht
  · intro t ht
    change 3 / 4 ≤ t at ht
    change (if t ≤ 1 / 4 then a t else if t ≤ 3 / 4 then mid t else b t) = b t
    rw [if_neg (show ¬t ≤ 1 / 4 by linarith)]
    by_cases hte : t = 3 / 4
    · subst t
      simpa only [if_pos le_rfl] using hm₁
    · exact if_neg (by intro h; exact hte (le_antisymm h ht))

theorem Smale.exists_smooth_curve_with_endpoint_germs {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (a b : C(ℝ, N))
    (ha : ContMDiff 𝓘(ℝ, ℝ) J ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) J ∞ b) (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        Set.EqOn f a (Set.Iic (1 / 8 : ℝ)) ∧ Set.EqOn f b (Set.Ici (7 / 8 : ℝ)) := by
  obtain ⟨g, hgleft, hgright⟩ := CurveImmersion.exists_continuous_curve_with_endpoint_germs a b γ
  let K := Set.Icc (1 / 4 : ℝ) (3 / 4)
  let U := Set.Iio (1 / 4 : ℝ) ∪ Set.Ioi (3 / 4)
  let C := Set.Iic (1 / 8 : ℝ) ∪ Set.Ici (7 / 8)
  have hU : IsOpen U := isOpen_Iio.union isOpen_Ioi
  have hC : IsClosed C := isClosed_Iic.union isClosed_Ici
  have hCU : C ⊆ U := by
    intro t ht
    rcases ht with ht | ht
    · change t ≤ 1 / 8 at ht
      exact Or.inl (show t < 1 / 4 by linarith)
    · change 7 / 8 ≤ t at ht
      exact Or.inr (show 3 / 4 < t by linarith)
  have hgU : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ g U := by
    intro t ht
    apply ContMDiffAt.contMDiffWithinAt
    rcases ht with ht | ht
    · have heq : g =ᶠ[𝓝 t] a := by
        filter_upwards [isOpen_Iio.mem_nhds (show t ∈ Set.Iio (1 / 4 : ℝ) from ht)] with s hs
        exact hgleft (show s ≤ 1 / 4 from hs.le)
      exact ha.contMDiffAt.congr_of_eventuallyEq heq
    · have heq : g =ᶠ[𝓝 t] b := by
        filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Set.Ioi (3 / 4 : ℝ) from ht)] with s hs
        exact hgright (show 3 / 4 ≤ s from hs.le)
      exact hb.contMDiffAt.congr_of_eventuallyEq heq
  have hKU : Kᶜ ⊆ U := by
    intro t ht
    change ¬(1 / 4 ≤ t ∧ t ≤ 3 / 4) at ht
    change t < 1 / 4 ∨ 3 / 4 < t
    exact not_and_or.mp ht |>.imp lt_of_not_ge lt_of_not_ge
  obtain ⟨f, hf, hrel⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact g
      CompactIccSpace.isCompact_Icc hC hU hCU hgU (hgU.mono hKU)
  refine ⟨f, hf, ?_, ?_⟩
  · intro t ht
    change t ≤ 1 / 8 at ht
    exact
      (hrel.fst_eq_snd (Or.inl ht)).symm.trans
        (hgleft (show t ∈ Set.Iic (1 / 4 : ℝ) from by change t ≤ 1 / 4; linarith))
  · intro t ht
    change 7 / 8 ≤ t at ht
    exact
      (hrel.fst_eq_snd (Or.inr ht)).symm.trans
        (hgright (show t ∈ Set.Ici (3 / 4 : ℝ) from by change 3 / 4 ≤ t; linarith))

theorem Smale.ManifoldImmersion.exists_clean_curve_endpoint_neighborhood {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : ℝ → N} (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hxy : f 0 ≠ f 1)
    (hi0 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f 0))
    (hi1 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f 1)) {S : Set N} (hS : S.Finite) :
    ∃ C : Set ℝ,
      IsCompact C ∧
        {(0 : ℝ), 1} ⊆ interior C ∧
          Set.InjOn f C ∧
            (∀ t ∈ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
              (∀ t ∈ C, t ∉ ({0, 1} : Set ℝ) → f t ∉ S) := by
  let B : Set ℝ := {0, 1}
  have hB : IsCompact B := ((Set.finite_singleton (1 : ℝ)).insert 0).isCompact
  have h0B : (0 : ℝ) ∈ B := by simp [B]
  have h1B : (1 : ℝ) ∈ B := by simp [B]
  have hinjB : Set.InjOn f B := by
    intro s hs t ht heq
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact (hxy heq).elim
    · exact (hxy heq.symm).elim
    · rfl
  have hiB : ∀ t ∈ B, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t) := by
    intro t ht
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hi0
    · exact hi1
  obtain ⟨V, hV, hBV, hinjV⟩ := exists_open_injOn_near_compact hf hB hinjB hiB
  let R := S \ {f 0, f 1}
  have hR : IsClosed R := (hS.subset Set.sdiff_subset).isClosed
  let U := (V ∩ {t | Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)}) ∩ f ⁻¹' Rᶜ
  have hU : IsOpen U :=
    (hV.inter (isOpen_injective_derivative hf)).inter (hR.isOpen_compl.preimage hf.continuous)
  have hBU : B ⊆ U := by
    intro t ht
    refine ⟨⟨hBV ht, hiB t ht⟩, ?_⟩
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> simp [R]
  obtain ⟨C, hC, hBC, hCU⟩ := exists_compact_between hB hU hBU
  refine ⟨C, hC, hBC, hinjV.mono (fun t ht => (hCU ht).1.1), fun t ht => (hCU ht).1.2, ?_⟩
  intro t ht htB htS
  apply (hCU ht).2
  refine ⟨htS, ?_⟩
  intro hends
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
  rcases hends with h0 | h1
  · have ht0 : t = 0 := hinjV (hCU ht).1.1 (hBV h0B) h0
    exact htB (by simp [ht0])
  · have ht1 : t = 1 := hinjV (hCU ht).1.1 (hBV h1B) h1
    exact htB (by simp [ht1])

def Smale.WeightedPerturbation.perturb {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (β : E → ℝ) (a : F) (x : E) : F :=
  f x + β x • a

theorem Smale.WeightedPerturbation.contDiff_perturb {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {β : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) (a : F) : ContDiff ℝ ∞ (perturb f β a) :=
  hf.add (hβ.smul contDiff_const)

theorem Smale.WeightedPerturbation.fderiv_perturb {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {β : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) (a : F) (x : E) :
    fderiv ℝ (perturb f β a) x = fderiv ℝ f x + (fderiv ℝ β x).smulRight a :=
  ((hf.differentiable (by simp) x).hasFDerivAt.add
      ((hβ.differentiable (by simp) x).hasFDerivAt.smul_const a)).fderiv

def Smale.WeightedPerturbation.badDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type*} (b : X → E) (β : E → ℝ) : Set (X × E) :=
  {q | fderiv ℝ β (b q.1) q.2 ≠ 0}

def Smale.WeightedPerturbation.badParameter {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {X : Type*} (b : X → E) (f : E → F) (β : E → ℝ)
    (q : X × E) : F :=
  (fderiv ℝ β (b q.1) q.2)⁻¹ • (-(fderiv ℝ f (b q.1) q.2))

theorem Smale.WeightedPerturbation.contMDiff_scalarDerivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace X] [ChartedSpace H X]
    {b : X → E} {β : E → ℝ} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hβ : ContDiff ℝ ∞ β) :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (fun q : X × E => fderiv ℝ β (b q.1) q.2) :=
  ((hβ.fderiv_right (by simp)).contMDiff.comp (hb.comp contMDiff_fst)).clm_apply contMDiff_snd

theorem Smale.WeightedPerturbation.isOpen_badDomain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace X] [ChartedSpace H X]
    {b : X → E} {β : E → ℝ} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hβ : ContDiff ℝ ∞ β) :
    IsOpen (badDomain b β) :=
  isOpen_ne_fun (contMDiff_scalarDerivative hb hβ).continuous continuous_const

theorem Smale.WeightedPerturbation.contMDiffOn_badParameter {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {B H X : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace X] [ChartedSpace H X] {b : X → E} {f : E → F} {β : E → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (badParameter b f β) (badDomain b β) := by
  have hdf : ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (fun q : X × E => fderiv ℝ f (b q.1) q.2) :=
    ((hf.fderiv_right (by simp)).contMDiff.comp (hb.comp contMDiff_fst)).clm_apply contMDiff_snd
  intro q hq
  exact
    (((contMDiff_scalarDerivative hb hβ).contMDiffAt.inv₀ hq).smul
        hdf.contMDiffAt.neg).contMDiffWithinAt

theorem Smale.WeightedPerturbation.kernel_iff_of_not_bad {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {X : Type*} {b : X → E} {f : E → F}
    {β : E → ℝ} (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) {a : F}
    (hgood : a ∉ badParameter b f β '' badDomain b β) (x : X) (v : E) :
    fderiv ℝ (perturb f β a) (b x) v = 0 ↔ fderiv ℝ f (b x) v = 0 ∧ fderiv ℝ β (b x) v = 0 := by
  rw [fderiv_perturb hf hβ]
  change fderiv ℝ f (b x) v + fderiv ℝ β (b x) v • a = 0 ↔ _
  constructor
  · intro hker
    have hbzero : fderiv ℝ β (b x) v = 0 := by
      by_contra hn
      apply hgood
      refine ⟨(x, v), hn, ?_⟩
      have heq : fderiv ℝ β (b x) v • a = -(fderiv ℝ f (b x) v) :=
        eq_neg_of_add_eq_zero_right hker
      change (fderiv ℝ β (b x) v)⁻¹ • (-(fderiv ℝ f (b x) v)) = a
      rw [← heq, inv_smul_smul₀ hn]
    exact ⟨by simpa only [hbzero, zero_smul, add_zero] using hker, hbzero⟩
  · rintro ⟨hfzero, hbzero⟩
    simp only [hfzero, hbzero, zero_smul, add_zero]

theorem Smale.WeightedPerturbation.exists_small_parameter_with_common_kernel {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace X] [ChartedSpace H X] [FiniteDimensional ℝ B]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ X] [LindelofSpace (X × E)]
    {b : X → E} {f : E → F} {β : E → ℝ} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hf : ContDiff ℝ ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        ContDiff ℝ ∞ (perturb f β a) ∧
          ∀ x v,
            fderiv ℝ (perturb f β a) (b x) v = 0 ↔
              fderiv ℝ f (b x) v = 0 ∧ fderiv ℝ β (b x) v = 0 := by
  have hd : Module.finrank ℝ (B × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hdim
  have hdense :=
    Smale.GeneralPosition.dense_compl_manifold_image (isOpen_badDomain hb hβ)
      (contMDiffOn_badParameter hb hf hβ) hd
  obtain ⟨a, hgood, hnorm⟩ := hdense.exists_dist_lt 0 hε
  exact
    ⟨a, by simpa only [dist_zero_left] using hnorm, contDiff_perturb hf hβ a,
      kernel_iff_of_not_bad hf hβ hgood⟩

def Smale.CurveImmersion.perturb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F)
    (a : F) : ℝ → F :=
  Smale.WeightedPerturbation.perturb f id a

theorem Smale.CurveImmersion.exists_small_affine_immersion {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧ ContDiff ℝ ∞ (perturb f a) ∧ ∀ t, Function.Injective (fderiv ℝ (perturb f a) t) :=
  by
  have hd : Module.finrank ℝ ℝ + Module.finrank ℝ ℝ < Module.finrank ℝ F := by
    simp only [Module.finrank_self]
    omega
  obtain ⟨a, ha, hs, hker⟩ :=
    Smale.WeightedPerturbation.exists_small_parameter_with_common_kernel (I := 𝓘(ℝ, ℝ)) (b := id)
      (β := id) contMDiff_id hf contDiff_id hd hε
  refine ⟨a, ha, hs, ?_⟩
  intro t u v huv
  have hz : fderiv ℝ (perturb f a) t (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hzero := ((hker t (u - v)).mp hz).2
  have huv0 : u - v = 0 := by simpa only [fderiv_id, ContinuousLinearMap.id_apply] using hzero
  exact sub_eq_zero.mp huv0

def Smale.CurveImmersion.weight (β : ℝ → ℝ) (t : ℝ) : ℝ :=
  β t * t

theorem Smale.CurveImmersion.contDiff_weight {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (weight β) :=
  hβ.mul contDiff_id

theorem Smale.CurveImmersion.hasCompactSupport_weight {β : ℝ → ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (weight β) :=
  hβ.mul_right (f' := id)

theorem Smale.CurveImmersion.tsupport_weight_subset (β : ℝ → ℝ) :
    tsupport (weight β) ⊆ tsupport β :=
  tsupport_mul_subset_left (f := β) (g := id)

theorem Smale.CurveImmersion.weight_eq_zero {β : ℝ → ℝ} {t : ℝ} (ht : β t = 0) : weight β t = 0 :=
  by simp only [weight, ht, MulZeroClass.zero_mul]

theorem Smale.ManifoldImmersion.exists_curve_immersion_patch_with_property_within_target
    {G F H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) {β χ : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ)
    (hcompact : HasCompactSupport β) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source)
    (hχone : ∀ t ∈ tsupport β, χ t = 1) (hdim : 3 ≤ Module.finrank ℝ F) (Q : (ℝ → N) → Prop)
    (hQ :
      ∀ᶠ a : F in 𝓝 0,
        Q (Smale.ChartMapPerturbation.perturb c f (Smale.CurveImmersion.weight β) a))
    {D : Set ℝ} {O : Set N} (hsource : c.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        Q g ∧
          Smale.HomotopicRelWithin f g {t | β t = 0} D O ∧
            ∀ t ∈ interior {t | β t = 1}, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  have hsupport : tsupport β ⊆ f ⁻¹' c.source := by
    intro t ht
    exact hχsupport (subset_tsupport χ (by change χ t ≠ 0; rw [hχone t ht]; norm_num))
  have hw := Smale.CurveImmersion.contDiff_weight hβ
  have hwsupport : tsupport (Smale.CurveImmersion.weight β) ⊆ f ⁻¹' c.source :=
    (Smale.CurveImmersion.tsupport_weight_subset β).trans hsupport
  let k := Smale.ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ k := fun t =>
      Smale.ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid c hf hw.contMDiff
      (Smale.CurveImmersion.hasCompactSupport_weight hcompact) hwsupport
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hQ
  obtain ⟨a, ha, -, hderiv⟩ :=
    Smale.CurveImmersion.exists_small_affine_immersion hk hdim (lt_min hε hδ)
  have haε : ‖a‖ < ε := ha.trans_le (min_le_left _ _)
  have hv := hvalid a haε
  have hsmooth := Smale.ChartMapPerturbation.contMDiff_perturb c hf hw.contMDiff hwsupport hv
  let g : C(ℝ, N) :=
    ⟨Smale.ChartMapPerturbation.perturb c f (Smale.CurveImmersion.weight β) a, hsmooth.continuous⟩
  have hcoord (t : ℝ) (ht : β t = 1) : c (g t) = Smale.CurveImmersion.perturb k a t := by
    have hts : t ∈ tsupport β := subset_tsupport β (by change β t ≠ 0; rw [ht]; norm_num)
    change c (Smale.ChartMapPerturbation.perturb c f (Smale.CurveImmersion.weight β) a t) = _
    rw [Smale.ChartMapPerturbation.chart_perturb c f (Smale.CurveImmersion.weight β) hv
        (hsupport hts)]
    simp only [Smale.ChartMapPerturbation.coordinateFamily, Smale.CurveImmersion.perturb,
      Smale.WeightedPerturbation.perturb, k, Smale.ChartMapPerturbation.cutoffCoordinates,
      Smale.CurveImmersion.weight, ht, hχone t hts, one_mul, one_smul, id_eq]
  have hQg : Q g :=
    hδkeep
      (show a ∈ Metric.ball 0 δ by
        simpa only [Metric.mem_ball, dist_zero_right] using ha.trans_le (min_le_right ε δ))
  refine ⟨g, hsmooth, hQg, ?_, ?_⟩
  · have hrel :=
      Smale.ChartMapPerturbation.homotopicRelWithin_of_source_subset c hf hw.contMDiff hwsupport
        hvalid haε hsource hmaps
    exact
      hrel.mono (fun _ hx => Smale.CurveImmersion.weight_eq_zero hx) (Set.Subset.refl D)
        (Set.Subset.refl O)
  · intro t ht
    have hβt : β t = 1 := interior_subset (s := {t | β t = 1}) ht
    have hfs : f t ∈ c.source :=
      hsupport (subset_tsupport β (by change β t ≠ 0; rw [hβt]; norm_num))
    have hgs : g t ∈ c.source :=
      Smale.ChartMapPerturbation.perturb_mem_source c f (Smale.CurveImmersion.weight β) hv hfs
    apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgs).mp
    have heq : (c ∘ g) =ᶠ[𝓝 t] Smale.CurveImmersion.perturb k a := by
      filter_upwards [isOpen_interior.mem_nhds ht] with s hs
      exact hcoord s (interior_subset (s := {t | β t = 1}) hs)
    change Function.Injective (fderiv ℝ (c ∘ g) t)
    rw [heq.fderiv_eq]
    exact hderiv t

theorem Smale.ManifoldImmersion.exists_curve_immersion_patch_step_within_target {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, ℝ) J (X := ℝ) (N := N)) (i : ι)
    (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K L C : Set ℝ} (hK : IsCompact K)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (hLsub : L ⊆ (p i).plateau)
    (hfixed : ∀ t ∈ C, (p i).cutoff t = 0) {D : Set ℝ} {O : Set N}
    (hsource : (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          Smale.HomotopicRelWithin f g C D O ∧
            ∀ t ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let w := Smale.CurveImmersion.weight (p i).cutoff
  have hw : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w :=
    (Smale.CurveImmersion.contDiff_weight (p i).smooth.contDiff).contMDiff
  have hinner := (p i).inner_compatible (hcompatible i)
  have hwsupport : tsupport w ⊆ f ⁻¹' (p i).chart.source :=
    (Smale.CurveImmersion.tsupport_weight_subset (p i).cutoff).trans hinner
  have hkeep :
    ∀ᶠ a : G in 𝓝 0,
      ∀ j, (p j).Compatible (Smale.ChartMapPerturbation.perturb (p i).chart f w a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf hw hwsupport
        (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    Smale.ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf hw
      (Smale.CurveImmersion.hasCompactSupport_weight (p i).compact) hwsupport hK hinj
  let Q : (ℝ → N) → Prop := fun g =>
    (∀ j, (p j).Compatible g) ∧ ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t)
  have hQ : ∀ᶠ a : G in 𝓝 0, Q (Smale.ChartMapPerturbation.perturb (p i).chart f w a) :=
    hkeep.and hold
  obtain ⟨g, hg, ⟨hc, hKnew⟩, hrel, hplateau⟩ :=
    exists_curve_immersion_patch_with_property_within_target (p i).chart f hf
      (p i).smooth.contDiff (p i).outer_smooth.contDiff (p i).compact (hcompatible i) (p i).nested
      hdim Q hQ hsource hmaps
  refine ⟨g, hg, hc, ?_, ?_⟩
  · exact hrel.mono hfixed (Set.Subset.refl D) (Set.Subset.refl O)
  · intro t ht
    rcases ht with ht | ht
    · exact hKnew t ht
    · exact hplateau t (hLsub ht)

theorem Smale.ManifoldImmersion.exists_finite_curve_patch_immersion_within_target {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, ℝ) J (X := ℝ) (N := N))
    (L : ι → Set ℝ) (hL : ∀ i, IsCompact (L i)) (hLsub : ∀ i, L i ⊆ (p i).plateau) (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hcompatible : ∀ i, (p i).Compatible f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K C : Set ℝ} (hK : IsCompact K)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hfixed : ∀ i t, t ∈ C → (p i).cutoff t = 0) {D : Set ℝ} {O : Set N}
    (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) (s : Finset ι) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        (∀ i, (p i).Compatible g) ∧
          Smale.HomotopicRelWithin f g C D O ∧
            ∀ t ∈ K ∪ ⋃ i ∈ s, L i, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, Smale.HomotopicRelWithin.refl f C hmaps, ?_⟩
    simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] using
      hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) := hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hinj₂⟩ :=
      exists_curve_immersion_patch_step_within_target p i g₁ hg₁ hc₁ hdim hKold hinj₁ (hLsub i)
        (hfixed i) (hsource i) hhom₁.mapsTo_right
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro t ht
    apply hinj₂ t
    rcases ht with ht | ht
    · exact Or.inl (Or.inl ht)
    · obtain ⟨j, hj, htj⟩ := Set.mem_iUnion₂.mp ht
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr htj
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjs, htj⟩))

theorem Smale.ManifoldImmersion.exists_curve_immersion_on_compact_rel_within_target
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K L C : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (hC : IsClosed C)
    (hdis : Disjoint L C) {D : Set ℝ} {O : Set N} (hO : IsOpen O) (hLO : Set.MapsTo f L O)
    (hmaps : Set.MapsTo f D O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        Smale.HomotopicRelWithin f g C D O ∧
          ∀ t ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  classical
  have hp (t : L) :=
    exists_relative_immersion_patch_at_in_open (J := J) f hC
      (show (t : ℝ) ∉ C from fun ht => Set.disjoint_left.mp hdis t.property ht) hO
      (hLO t.property)
  choose p T hcompatible hT hn hsub hfixed hsource using hp
  have hcover : L ⊆ ⋃ t : L, interior (T t) := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨t, ht⟩)⟩
  obtain ⟨s, hs⟩ :=
    hL.elim_finite_subcover (fun t : L => interior (T t)) (fun _ => isOpen_interior) hcover
  obtain ⟨g, hg, -, hhom, hderiv⟩ :=
    exists_finite_curve_patch_immersion_within_target (fun i : s => p i.1) (fun i : s => T i.1)
      (fun i => hT i.1) (fun i => hsub i.1) f hf (fun i => hcompatible i.1) hdim hK hinj
      (fun i => hfixed i.1) (fun i => hsource i.1) hmaps Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro t ht
  apply hderiv t
  rcases ht with ht | ht
  · exact Or.inl ht
  · obtain ⟨i, his, hti⟩ := Set.mem_iUnion₂.mp (hs ht)
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨⟨i, his⟩, Finset.mem_univ _, interior_subset hti⟩)

theorem Smale.ManifoldImmersion.exists_relative_compact_curve_embedding_within_target
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K C : Set ℝ} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f (K \ C) O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        Smale.HomotopicRelWithin f g C (K \ C) O ∧
          Topology.IsClosedEmbedding (fun t : K => g t) ∧
            ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let U : Set ℝ := {t | Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)}
  have hU : IsOpen U := isOpen_injective_derivative hf
  have hCU : K ∩ C ⊆ U := fun t ht => hderiv t ht
  obtain ⟨D, hD, hCD, hDU⟩ := exists_compact_between (hK.inter_right hC) hU hCU
  let L := K \ interior D
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hdis : Disjoint L C := Set.disjoint_left.mpr (fun _ ht htC => ht.2 (hCD ⟨ht.1, htC⟩))
  have hLO : Set.MapsTo f L O := fun t ht => hmaps ⟨ht.1, fun htC => ht.2 (hCD ⟨ht.1, htC⟩)⟩
  obtain ⟨g₁, hg₁, hhom₁, hinj₁⟩ :=
    exists_curve_immersion_on_compact_rel_within_target f hf hdim hD hL (fun t ht => hDU ht) hC
      hdis hO hLO hmaps
  have hKinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g₁ t) := by
    intro t ht
    apply hinj₁ t
    by_cases htD : t ∈ D
    · exact Or.inl htD
    · exact Or.inr ⟨ht, fun hi => htD (interior_subset hi)⟩
  have hfixed₁ : Set.InjOn g₁ (K ∩ C) := by
    intro t ht s hs hts
    apply hfixed ht hs
    rw [hhom₁.homotopicRel.fst_eq_snd ht.2, hhom₁.homotopicRel.fst_eq_snd hs.2]
    exact hts
  have hd : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  obtain ⟨g₂, hg₂, hhom₂, hemb, hinj₂⟩ :=
    exists_compact_embedding_of_immersion_within_target g₁ hg₁ hd hK hKinj hC hfixed₁ hO
      hhom₁.mapsTo_right
  exact ⟨g₂, hg₂, hhom₁.trans hhom₂, hemb, hinj₂⟩

theorem Smale.ManifoldImmersion.exists_relative_compact_curve_embedding {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K C : Set ℝ} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun t : K => g t) ∧
            ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨g, hg, hrel, he, hi⟩ :=
    exists_relative_compact_curve_embedding_within_target f hf hdim hK hC hfixed hderiv
      isOpen_univ (Set.mapsTo_univ f (K \ C))
  exact ⟨g, hg, hrel.homotopicRel, he, hi⟩

theorem Smale.ManifoldImmersion.exists_relative_curve_avoidance_of_clean_neighborhood
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] {F H' Y : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [LindelofSpace (ℝ × Y)] (f : C(ℝ, N)) (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hdim : 3 ≤ Module.finrank ℝ G)
    (hobstacle : 1 + Module.finrank ℝ F < Module.finrank ℝ G) {K C B : Set ℝ} (hK : IsCompact K)
    (hC : IsClosed C) (hBC : B ⊆ interior C) (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hclean : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ Set.range g) :
    ∃ f' : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun t : K => f' t) ∧
            (∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f' t)) ∧
              ∀ t ∈ K \ B, f' t ∉ Set.range g := by
  obtain ⟨f₁, hf₁, hhom₁, hemb₁, hderiv₁⟩ :=
    exists_relative_compact_curve_embedding f hf hdim hK hC hfixed hderiv
  have hinj₁ : Set.InjOn f₁ K := by
    intro t ht s hs hts
    exact congrArg Subtype.val (hemb₁.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) hts)
  have hclean₁ : ∀ t ∈ K ∩ C, t ∉ B → f₁ t ∉ Set.range g := by
    intro t ht htB
    rw [← hhom₁.fst_eq_snd ht.2]
    exact hclean t ht htB
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobs : Module.finrank ℝ ℝ + Module.finrank ℝ F < Module.finrank ℝ G := by
    simpa only [Module.finrank_self] using hobstacle
  obtain ⟨f₂, hf₂, hhom₂, hemb₂, hderiv₂, havoid⟩ :=
    exists_embedded_avoidance_relative_neighborhood f₁ g hf₁ hg hself hobs hK hC hBC hinj₁ hderiv₁
      hclean₁
  exact ⟨f₂, hf₂, hhom₁.trans hhom₂, hemb₂, hderiv₂, havoid⟩

theorem Smale.ManifoldImmersion.exists_relative_curve_avoiding_finite {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) {K C B : Set ℝ} (hK : IsCompact K)
    (hC : IsClosed C) (hBC : B ⊆ interior C) (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hclean : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ S) :
    ∃ f' : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun t : K => f' t) ∧
            (∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f' t)) ∧ ∀ t ∈ K \ B, f' t ∉ S := by
  let : Fintype S := hS.fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z S := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ S := IsManifold.of_discreteTopology _
  let g : C(S, N) := ⟨Subtype.val, continuous_subtype_val⟩
  have hg : ContMDiff 𝓘(ℝ, Z) J ∞ g := contMDiff_of_discreteTopology
  have hrange : Set.range g = S := by ext y; simp [g]
  have hobs : 1 + Module.finrank ℝ Z < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin]
    omega
  have hclean' : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ Set.range g := by simpa only [hrange] using hclean
  obtain ⟨f', hf', hrel, hemb, hi, havoid⟩ :=
    exists_relative_curve_avoidance_of_clean_neighborhood f g hf hg hdim hobs hK hC hBC hfixed
      hderiv hclean'
  refine ⟨f', hf', hrel, hemb, hi, ?_⟩
  simpa only [hrange] using havoid

theorem Smale.exists_embedded_arc_with_endpoint_germs {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (a b : C(ℝ, N)) (ha : ContMDiff 𝓘(ℝ, ℝ) J ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) J ∞ b)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1)) (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        (f =ᶠ[𝓝 (0 : ℝ)] a) ∧
          (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S) := by
  obtain ⟨g, hg, hga, hgb⟩ := exists_smooth_curve_with_endpoint_germs a b ha hb γ
  have hga0 : g =ᶠ[𝓝 (0 : ℝ)] a := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num)] with t ht
    change t < 1 / 8 at ht
    exact hga ht.le
  have hgb1 : g =ᶠ[𝓝 (1 : ℝ)] b := by
    filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num)] with t ht
    change 7 / 8 < t at ht
    exact hgb ht.le
  have hgxy : g 0 ≠ g 1 := by
    rw [hga0.eq_of_nhds, hgb1.eq_of_nhds]
    exact hxy
  have hig0 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g 0) := by
    rw [hga0.mfderiv_eq]
    exact hia
  have hig1 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g 1) := by
    rw [hgb1.mfderiv_eq]
    exact hib
  obtain ⟨C, hC, hBC, hinjC, hiC, hclean⟩ :=
    ManifoldImmersion.exists_clean_curve_endpoint_neighborhood hg hgxy hig0 hig1 hS
  obtain ⟨f, hf, hrel, hemb, hi, havoid⟩ :=
    ManifoldImmersion.exists_relative_curve_avoiding_finite g hg hdim hS
      (CompactIccSpace.isCompact_Icc (a := (0 : ℝ)) (b := 1)) hC.isClosed hBC
      (hinjC.mono Set.inter_subset_right) (fun t ht => hiC t ht.2) (fun t ht => hclean t ht.2)
  have hfg (t : ℝ) (ht : t ∈ ({0, 1} : Set ℝ)) : f =ᶠ[𝓝 t] g := by
    filter_upwards [isOpen_interior.mem_nhds (hBC ht)] with s hs
    exact (hrel.fst_eq_snd (interior_subset hs)).symm
  refine ⟨f, hf, (hfg 0 (by simp)).trans hga0, (hfg 1 (by simp)).trans hgb1, hemb, hi, ?_⟩
  intro t ht
  apply havoid t ⟨⟨ht.1.le, ht.2.le⟩, ?_⟩
  intro htB
  rcases htB with ht0 | ht1
  · exact ht.1.ne' ht0
  · exact ht.2.ne ht1

theorem Smale.exists_smooth_curve_with_germ_at {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {a : ℝ → N} {U : Set ℝ} {t₀ : ℝ} (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U)
    (hU : IsOpen U) (ht₀ : t₀ ∈ U) : ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧ (f =ᶠ[𝓝 t₀] a) := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_extension_near_point ha hU ht₀
  exact ⟨⟨f, hf.continuous⟩, hf, heq⟩

theorem Smale.exists_embedded_arc_with_local_endpoint_germs {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {a b : ℝ → N} {U V : Set ℝ} (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U)
    (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b V) (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U)
    (h1V : (1 : ℝ) ∈ V) (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1)) (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        (f =ᶠ[𝓝 (0 : ℝ)] a) ∧
          (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_curve_with_germ_at ha hU h0U
  obtain ⟨b', hb', heqb⟩ := exists_smooth_curve_with_germ_at hb hV h1V
  have hia' : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a' 0) := by
    rw [heqa.mfderiv_eq]
    exact hia
  have hib' : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b' 1) := by
    rw [heqb.mfderiv_eq]
    exact hib
  have hxy' : a' 0 ≠ b' 1 := by
    rw [heqa.eq_of_nhds, heqb.eq_of_nhds]
    exact hxy
  obtain ⟨f, hf, hfa, hfb, hemb, hi, havoid⟩ :=
    exists_embedded_arc_with_endpoint_germs a' b' ha' hb' hia' hib'
      (γ.cast heqa.eq_of_nhds heqb.eq_of_nhds) hxy' hdim hS
  exact ⟨f, hf, hfa.trans heqa, hfb.trans heqb, hemb, hi, havoid⟩

theorem MorseCancel.exists_clean_arc_with_local_endpoint_germs {G V H H' N Y : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I : ModelWithCorners ℝ V H'} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I ∞ Y] [SecondCountableTopology Y] {a b : ℝ → N} {U W : Set ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b W) (hU : IsOpen U)
    (hW : IsOpen W) (h0U : (0 : ℝ) ∈ U) (h1W : (1 : ℝ) ∈ W)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1)) (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) (o : C(Y, N)) (ho : ContMDiff I J ∞ o)
    (hclosed : IsClosed (Set.range o)) (hobdim : 1 + Module.finrank ℝ V < Module.finrank ℝ G)
    (hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ Set.range o → t = 0)
    (hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), b t ∈ Set.range o → t = 1) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        (f =ᶠ[𝓝 (0 : ℝ)] a) ∧
          (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ Set.range o := by
  obtain ⟨f, hf, hfa, hfb, hemb, hfd, -⟩ :=
    Smale.exists_embedded_arc_with_local_endpoint_germs ha hb hU hW h0U h1W hia hib γ hxy hdim
      (S := ∅) Set.finite_empty
  have hnear0 : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ Set.range o → t = 0 := by
    filter_upwards [hfa, hclean0] with t he hc
    rw [he]
    exact hc
  have hnear1 : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ Set.range o → t = 1 := by
    filter_upwards [hfb, hclean1] with t he hc
    rw [he]
    exact hc
  obtain ⟨r, hr, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear0
  obtain ⟨s, hs, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear1
  let C : Set ℝ := Metric.closedBall 0 r ∪ Metric.closedBall 1 s
  have h0C : C ∈ 𝓝 (0 : ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hr)
      (fun _ ht => Or.inl (Metric.ball_subset_closedBall ht))
  have h1C : C ∈ 𝓝 (1 : ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 1 hs)
      (fun _ ht => Or.inr (Metric.ball_subset_closedBall ht))
  have hBC : ({0, 1} : Set ℝ) ⊆ interior C := by
    intro t ht
    rcases ht with rfl | ht
    · exact mem_interior_iff_mem_nhds.mpr h0C
    · have ht1 : t = 1 := ht
      subst t
      exact mem_interior_iff_mem_nhds.mpr h1C
  have hclean : ∀ t ∈ Set.Icc (0 : ℝ) 1 ∩ C, t ∉ ({0, 1} : Set ℝ) → f t ∉ Set.range o := by
    intro t ht htB hto
    rcases ht.2 with ht0 | ht1
    · exact htB (Or.inl (hball0 ht0 hto))
    · exact htB (Or.inr (hball1 ht1 hto))
  have hfi : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy he
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) he)
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobs : Module.finrank ℝ ℝ + Module.finrank ℝ V < Module.finrank ℝ G := by
    simpa only [Module.finrank_self] using hobdim
  obtain ⟨g, hg, hrel, hge, hgd, havoid⟩ :=
    Smale.ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f o
      hf ho hclosed hself hobs CompactIccSpace.isCompact_Icc
      (show IsClosed C from Metric.isClosed_closedBall.union Metric.isClosed_closedBall) hBC hfi
      hfd hclean
  refine ⟨g, hg, ?_, ?_, hge, hgd, ?_⟩
  · filter_upwards [h0C, hfa] with t ht he
    exact (hrel.fst_eq_snd ht).symm.trans he
  · filter_upwards [h1C, hfb] with t ht he
    exact (hrel.fst_eq_snd ht).symm.trans he
  · intro t ht hto
    have htB : t ∉ ({0, 1} : Set ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ne_of_gt ht.1, ne_of_lt ht.2⟩
    exact havoid t ⟨⟨ht.1.le, ht.2.le⟩, htB⟩ hto

theorem Smale.NativeEuclideanEmbedding.exists_smooth_normalFrame_near_starConvex {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : Smale.NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) :
    ∃ V : Set D,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension),
            ContDiffOn ℝ ∞ A V ∧
              ∀ x ∈ K, Function.Injective (A x) ∧ (A x).range = e.diskNormalSpace f x := by
  obtain ⟨U, hU, hKU, hsP, hP⟩ := e.exists_open_diskNormalProjection hf hi
  have hidem : ∀ x ∈ K, IsIdempotentElem (e.diskNormalProjection f x) := by
    intro x hx
    rw [hP x (hKU hx)]
    exact (e.diskNormalSpace f x).isIdempotentElem_starProjection
  obtain ⟨V, hV, hKV, A, hA, hAi⟩ :=
    Smale.DiskFraming.exists_smooth_frame_near_starConvex hK hstar hU hKU
      (e.diskNormalProjection f) hidem hsP
  have hr : (e.diskNormalProjection f 0).range = e.diskNormalSpace f 0 := by
    rw [hP 0 (hKU hz), Submodule.range_starProjection]
  have hdim : Module.finrank ℝ (e.diskNormalSpace f 0) = n := by
    have h := e.finrank_diskTangent_add_normal hf (hi 0 hz)
    omega
  have hcenter : Module.finrank ℝ (e.diskNormalProjection f 0).range = n :=
    (congrArg
          (fun S : Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) => Module.finrank ℝ S)
          hr).trans
      hdim
  let φ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (e.diskNormalProjection f 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  refine
    ⟨V, hV, hKV, fun x => (A x).comp φ.toContinuousLinearMap, hA.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨((hAi x hx).1).comp φ.injective, ?_⟩
  calc
    ((A x).comp φ.toContinuousLinearMap).range = (A x).range :=
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
    _ = (e.diskNormalProjection f x).range := (hAi x hx).2
    _ = e.diskNormalSpace f x := by rw [hP x (hKU hx), Submodule.range_starProjection]

theorem Smale.exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧ (∀ x, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hKV, A, hA, hframe⟩ :=
    e.exists_smooth_normalFrame_near_starConvex hf hK hz hstar hi n hcodim
  obtain ⟨Φ, hzero, -, hΦ⟩ :=
    r.exists_diskTubularNeighborhood hf hK hV hKV hinj hi hA (fun x hx => (hframe x hx).1)
      (fun x hx => (hframe x hx).2)
  let W := Φ.source ∩ Φ ⁻¹' O
  have hW : IsOpen W := Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hO
  have hWloc : IsLocalDiffeomorphOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ Φ W := fun p =>
    ⟨Φ, p.property.1, fun _ _ => rfl⟩
  let Ψ :=
    partialDiffeomorphOfInjectiveLocal hW (Φ.toPartialEquiv.injOn.mono Set.inter_subset_left)
      hWloc
  have hzeroΨ : K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    refine ⟨hzero ⟨hx, rfl⟩, ?_⟩
    change Φ (x, 0) ∈ O
    rw [hΦ, r.diskCoordinates_zero]
    exact hfO hx
  obtain ⟨ε, hε, hprod⟩ := DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hzeroΨ
  refine ⟨ε, hε, Ψ, hprod, ?_, ?_⟩
  · intro x
    change Φ (x, 0) = f x
    rw [hΦ, r.diskCoordinates_zero]
  · change Φ '' W ⊆ O
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2

theorem Smale.exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧ (∀ x, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let D₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ D))
  let e : D₀ ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let f₀ := f ∘ e
  let K₀ := e ⁻¹' K
  have hf₀ : ContMDiff 𝓘(ℝ, D₀) 𝓘(ℝ, E) ∞ f₀ := hf.comp e.contDiff.contMDiff
  have hK₀ : IsCompact K₀ := e.toHomeomorph.isCompact_preimage.mpr hK
  have hz₀ : (0 : D₀) ∈ K₀ := by
    change e 0 ∈ K
    simpa only [map_zero] using hz
  have hstar₀ : StarConvex ℝ (0 : D₀) K₀ := by
    apply StarConvex.linear_preimage e.toLinearMap
    simpa only [ContinuousLinearEquiv.coe_coe, map_zero] using hstar
  have hinj₀ : Set.InjOn f₀ K₀ := fun _ hx _ hy hxy => e.injective (hinj hx hy hxy)
  have hi₀ : ∀ x ∈ K₀, Function.Injective (mfderiv 𝓘(ℝ, D₀) 𝓘(ℝ, E) f₀ x) := by
    intro x hx
    exact
      (ManifoldImmersion.injective_mfderiv_comp_linearEquiv_iff e
            (hf.mdifferentiableAt (by simp))).mpr
        (hi (e x) hx)
  have hcodim₀ : Module.finrank ℝ D₀ + n = Module.finrank ℝ E := by
    simpa only [D₀, finrank_euclideanSpace_fin] using hcodim
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf₀ hK₀ hz₀ hstar₀
      hinj₀ hi₀ n hcodim₀ hO (fun _ hx => hfO hx)
  let eprod := e.symm.prodCongr (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))
  let c := eprod.toDiffeomorph
  let Ψ := c.toPartialDiffeomorph.trans Φ
  have hpre (x : D) (hx : x ∈ K) : e.symm x ∈ K₀ := by
    change e (e.symm x) ∈ K
    simpa only [e.apply_symm_apply] using hx
  refine ⟨ε, hε, Ψ, ?_, ?_, ?_⟩
  · rintro ⟨x, v⟩ ⟨hx, hv⟩
    exact ⟨Set.mem_univ _, hsource ⟨hpre x hx, hv⟩⟩
  · intro x
    change Φ (e.symm x, 0) = f x
    rw [hzero (e.symm x)]
    exact congrArg f (e.apply_symm_apply x)
  · intro y hy
    exact htarget hy.1

theorem Smale.exists_local_tubularNeighborhood_of_embedded_starConvex {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M} {K U : Set D}
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U) (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ Set.univ ∧ (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧ Φ.target ⊆ O :=
  by
  obtain ⟨g, hg, V, hV, hKV, hVU, heq⟩ :=
    exists_smooth_extension_near_starConvex hK hz hstar hU hKU hf
  have hinjg : Set.InjOn g K := by
    intro x hx y hy hxy
    apply hinj hx hy
    simpa only [heq (hKV hx), heq (hKV hy)] using hxy
  have hig : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x) := by
    intro x hx
    have hnear : g =ᶠ[𝓝 x] f := Filter.Eventually.mono (hV.mem_nhds (hKV hx)) heq
    rw [hnear.mfderiv_eq]
    exact hi x hx
  have hgO : Set.MapsTo g K O := by
    intro x hx
    rw [heq (hKV hx)]
    exact hfO hx
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hg hK hz
      hstar hinjg hig n hcodim hO hgO
  let Ψ :=
    PartialChart.restrictSource Φ
      (hV.preimage (continuous_fst : Continuous (Prod.fst : D × EuclideanSpace ℝ (Fin n) → D)))
  refine ⟨ε, hε, Ψ, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨hsource hp, hKV hp.1⟩
  · intro p hp
    exact ⟨hVU hp.2, Set.mem_univ _⟩
  · intro x hx
    change Φ (x, 0) = f x
    exact (hzero x).trans (heq hx.2)
  · intro y hy
    exact htarget hy.1

theorem Smale.exists_clean_tubularNeighborhood_of_embedded_starConvex {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M} {K U : Set D}
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U) (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hemb : Topology.IsEmbedding (fun x : U => f x))
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ Set.univ ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
                  (∀ q ∈ Φ.source, Φ q ∈ f '' U ↔ q.2 = 0) := by
  have hinj : Set.InjOn f K := by
    intro x hx y hy hxy
    exact
      congrArg Subtype.val
        (hemb.injective
          (show (fun u : U => f u) ⟨x, hKU hx⟩ = (fun u : U => f u) ⟨y, hKU hy⟩ from hxy))
  obtain ⟨a, ha, Φ, hprod, hsource, hzero, htarget⟩ :=
    exists_local_tubularNeighborhood_of_embedded_starConvex hf hK hz hstar hU hKU hinj hi n hcodim
      hO hfO
  have hbase : IsOpen {x : U | ((x : D), (0 : EuclideanSpace ℝ (Fin n))) ∈ Φ.source} :=
    Φ.open_source.preimage (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨A, hA, hpreA⟩ := hemb.isInducing.isOpen_iff.mp hbase
  have haxis {x : D} (hx : x ∈ U) (hxA : f x ∈ A) : (x, 0) ∈ Φ.source := by
    have hx' : (⟨x, hx⟩ : U) ∈ (fun u : U => f u) ⁻¹' A := hxA
    rw [hpreA] at hx'
    exact hx'
  have hKA : Set.MapsTo f K A := by
    intro x hx
    have hx' :
      (⟨x, hKU hx⟩ : U) ∈ {u : U | ((u : D), (0 : EuclideanSpace ℝ (Fin n))) ∈ Φ.source} :=
      hprod ⟨hx, Metric.mem_closedBall_self ha.le⟩
    rw [← hpreA] at hx'
    exact hx'
  let Ψ := PartialChart.restrictTarget Φ hA
  have hKzero : K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    have hxΦ := hprod ⟨hx, Metric.mem_closedBall_self ha.le⟩
    refine ⟨hxΦ, ?_⟩
    change Φ (x, 0) ∈ A
    rw [hzero x hxΦ]
    exact hKA hx
  obtain ⟨ε, hε, hεprod⟩ := DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hKzero
  refine
    ⟨ε, hε, Ψ, hεprod, fun _ hq => hsource hq.1, fun _ hy => htarget hy.1, fun x hx =>
      hzero x hx.1, ?_⟩
  rintro ⟨x, z⟩ hq
  constructor
  · rintro ⟨u, hu, heq⟩
    have huA : f u ∈ A := heq ▸ hq.2
    have huΦ := haxis hu huA
    have hpair : (x, z) = (u, 0) :=
      Φ.toPartialEquiv.injOn hq.1 huΦ (heq.symm.trans (hzero u huΦ).symm)
    exact congrArg Prod.snd hpair
  · intro hz
    change z = 0 at hz
    subst z
    exact ⟨x, (hsource hq.1).1, (hzero x hq.1).symm⟩

theorem Smale.exists_clean_embedded_sheet_neighborhood {E M D G N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] {F : N → M} (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hembF : Topology.IsEmbedding F) (c : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, G) D N ∞) {K : Set D}
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K) (hKc : K ⊆ c.source)
    (hiF : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (c x))) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hFO : Set.MapsTo (F ∘ c) K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            Φ.source ⊆ c.source ×ˢ Set.univ ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = F (c x)) ∧
                  (∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) := by
  let f := F ∘ c
  have hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f c.source := hF.comp_contMDiffOn c.contMDiffOn_toFun
  have hembf : Topology.IsEmbedding (fun x : c.source => f x) :=
    hembF.comp c.toOpenPartialHomeomorph.isEmbedding_restrict
  have hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x) := by
    intro x hx
    rw [mfderiv_comp x (hF.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) (hKc hx))]
    exact (hiF x hx).comp (PartialChart.bijective_mfderiv c (hKc hx)).1
  obtain ⟨A, hA, hpreA⟩ := hembF.isInducing.isOpen_iff.mp c.open_target
  have hfA : Set.MapsTo f K A := by
    intro x hx
    change c x ∈ F ⁻¹' A
    rw [hpreA]
    exact c.map_source' (hKc hx)
  obtain ⟨ε, hε, Φ, hprod, hsource, htarget, hzero, himage⟩ :=
    exists_clean_tubularNeighborhood_of_embedded_starConvex hf hK hz hstar c.open_source hKc hembf
      hi n hcodim (hO.inter hA) (fun x hx => ⟨hFO hx, hfA hx⟩)
  refine ⟨ε, hε, Φ, hprod, hsource, fun _ hy => (htarget hy).1, hzero, ?_⟩
  intro q hq
  have hqA := (htarget (Φ.map_source' hq)).2
  have hrange : Φ q ∈ Set.range F ↔ Φ q ∈ f '' c.source := by
    constructor
    · rintro ⟨y, hy⟩
      have hyA : F y ∈ A := hy ▸ hqA
      have hyT : y ∈ c.target := by
        change y ∈ F ⁻¹' A at hyA
        rwa [hpreA] at hyA
      exact ⟨c.invFun y, c.map_target' hyT, (congrArg F (c.right_inv' hyT)).trans hy⟩
    · rintro ⟨u, _, hu⟩
      exact ⟨c u, hu⟩
  exact hrange.trans (himage q hq)

def MorseCancel.sheetAxisShuffle {D B : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup B] [NormedSpace ℝ B] : (ℝ × (D × B)) ≃L[ℝ] (D × (ℝ × B))
    where
  toLinearEquiv :=
    { toFun := fun p => (p.2.1, (p.1, p.2.2))
      invFun := fun p => (p.2.1, (p.1, p.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)
  continuous_invFun := continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)

theorem MorseCancel.exists_clean_sheet_axis_chart {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {E M X : Type*} [FiniteDimensional ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X] [ChartedSpace D X]
    [IsManifold 𝓘(ℝ, D) ∞ X] {f : X → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hemb : Topology.IsEmbedding f) (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hdim : Module.finrank ℝ D + (1 + n) = Module.finrank ℝ E) (x : X) {U : Set M}
    (hU : IsOpen U) (hxU : f x ∈ U) :
    ∃ Φ :
      PartialDiffeomorph 𝓘(ℝ, ℝ × (D × EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, E)
        (ℝ × (D × EuclideanSpace ℝ (Fin n))) M ∞,
      (0 : ℝ × (D × EuclideanSpace ℝ (Fin n))) ∈ Φ.source ∧
        Φ 0 = f x ∧ Φ.target ⊆ U ∧ ∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0 := by
  let c := Smale.NativeParametrization.centered (D := D) x
  have hc0 : (0 : D) ∈ c.source := Smale.NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := Smale.NativeParametrization.centered_zero x
  obtain ⟨ε, hε, Q, hprod, -, hQU, hzero, hrecognition⟩ :=
    Smale.exists_clean_embedded_sheet_neighborhood hf hemb c isCompact_singleton
      (Set.mem_singleton (0 : D)) (starConvex_singleton (0 : D))
      (Set.singleton_subset_iff.mpr hc0) (fun z _ => hi (c z)) (1 + n) hdim hU
      (show Set.MapsTo (f ∘ c) {0} U by
        intro z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        change f (c 0) ∈ U
        rw [hcx]
        exact hxU)
  let B := EuclideanSpace ℝ (Fin n)
  let N := EuclideanSpace ℝ (Fin (1 + n))
  let L : (ℝ × B) ≃L[ℝ] N :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [B, N, Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin])
  let P : (ℝ × (D × B)) ≃L[ℝ] (D × N) :=
    (sheetAxisShuffle (D := D) (B := B)).trans ((ContinuousLinearEquiv.refl ℝ D).prodCongr L)
  let Φ := P.toDiffeomorph.toPartialDiffeomorph.trans Q
  have hQ0 : (0 : D × N) ∈ Q.source :=
    hprod ⟨Set.mem_singleton 0, Metric.mem_closedBall_self hε.le⟩
  have hΦ0 : (0 : ℝ × (D × B)) ∈ Φ.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change P 0 ∈ Q.source
    rw [map_zero]
    exact hQ0
  refine ⟨Φ, hΦ0, ?_, fun z hz => hQU hz.1, ?_⟩
  · change Q (P 0) = f x
    rw [map_zero]
    exact (hzero 0 hQ0).trans (congrArg f hcx)
  · intro z hz
    change Q (P z) ∈ Set.range f ↔ _
    rw [hrecognition (P z) hz.2]
    change L (z.1, z.2.2) = 0 ↔ z.1 = 0 ∧ z.2.2 = 0
    constructor
    · intro h
      have he : (z.1, z.2.2) = (0, (0 : B)) := L.injective (h.trans L.map_zero.symm)
      exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      exact L.map_zero

theorem MorseCancel.chart_axis_curve_properties {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) (p : ℝ) (hp : (p, (0 : V)) ∈ Φ.source) :
    ∃ U : Set ℝ,
      IsOpen U ∧
        p ∈ U ∧
          (∀ t ∈ U, (t, (0 : V)) ∈ Φ.source) ∧
            ContMDiffOn 𝓘(ℝ, ℝ) J ∞ (fun t => Φ (t, (0 : V))) U ∧
              Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => Φ (t, (0 : V))) p) := by
  let L := ContinuousLinearMap.inl ℝ ℝ V
  have hL : ContDiff ℝ ∞ L := L.contDiff
  let U : Set ℝ := L ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage L.continuous
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ (Φ ∘ L) U :=
    Φ.contMDiffOn_toFun.comp hL.contMDiff.contMDiffOn (fun _ ht => ht)
  refine ⟨U, hU, hp, fun _ ht => ht, hcurve, ?_⟩
  change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (Φ ∘ L) p)
  rw [mfderiv_comp p (Φ.mdifferentiableAt (by simp) hp)
      (hL.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, L.fderiv]
  exact
    (Smale.PartialChart.bijective_mfderiv Φ hp).injective.comp (fun _ _ h => congrArg Prod.fst h)

def MorseCancel.terminalSheetCoordinates {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] :
    Diffeomorph 𝓘(ℝ, ℝ × (D × D)) 𝓘(ℝ, ℝ × (D × D)) (ℝ × (D × D)) (ℝ × (D × D)) ∞
    where
  toEquiv :=
    { toFun := fun z => (z.1 - 1, (z.2.2, z.2.1))
      invFun := fun z => (z.1 + 1, (z.2.2, z.2.1))
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp }
  contMDiff_toFun :=
    ((contDiff_fst.sub contDiff_const).prodMk
        (contDiff_snd.snd.prodMk contDiff_snd.fst)).contMDiff
  contMDiff_invFun :=
    ((contDiff_fst.add contDiff_const).prodMk
        (contDiff_snd.snd.prodMk contDiff_snd.fst)).contMDiff

theorem MorseCancel.exists_clean_two_sheet_arc {E M X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [IsManifold (𝓡 2) ∞ X] [CompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y]
    [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y] [SecondCountableTopology Y] {f : X → M} {g : Y → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : Topology.IsEmbedding f) (hge : Topology.IsEmbedding g)
    (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y)) (hdim : Module.finrank ℝ E = 5)
    (x : X) (y : Y) (hx : f x ∉ Set.range g) (hy : g y ∉ Set.range f) (γ : Path (f x) (g y)) :
    ∃ Φ Ψ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
      (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source ∧
        ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Ψ.source ∧
          Φ 0 = f x ∧
            Ψ (1, 0) = g y ∧
              Φ.target ⊆ (Set.range g)ᶜ ∧
                Ψ.target ⊆ (Set.range f)ᶜ ∧
                  (∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                    (∀ z ∈ Ψ.source, Ψ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                      ∃ a : C(ℝ, M),
                        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a ∧
                          (a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ (t, 0)) ∧
                            (a =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0)) ∧
                              Topology.IsClosedEmbedding (fun t : unitInterval => a t) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t)) ∧
                                  (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range f ↔ t = 0) ∧
                                    (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range g ↔ t = 1) := by
  have hclosedf : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  have hclosedg : IsClosed (Set.range g) := (isCompact_range hg.continuous).isClosed
  have hcodim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + (1 + 2) = Module.finrank ℝ E := by
    rw [finrank_euclideanSpace_fin, hdim]
  obtain ⟨Φ, hΦ0, hΦx, hΦavoid, hΦrec⟩ :=
    exists_clean_sheet_axis_chart hf hfe hfi 2 hcodim x hclosedg.isOpen_compl hx
  obtain ⟨Q, hQ0, hQy, hQavoid, hQrec⟩ :=
    exists_clean_sheet_axis_chart hg hge hgi 2 hcodim y hclosedf.isOpen_compl hy
  let T := terminalSheetCoordinates (D := (EuclideanSpace ℝ (Fin 2)))
  let Ψ := T.toPartialDiffeomorph.trans Q
  have hT1 : T ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) = 0 := by
    change ((1 : ℝ) - 1, ((0 : (EuclideanSpace ℝ (Fin 2))), (0 : (EuclideanSpace ℝ (Fin 2))))) = 0
    rw [sub_self]
    rfl
  have hΨ1 :
    ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Ψ.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change T (1, 0) ∈ Q.source
    rw [hT1]
    exact hQ0
  have hΨy : Ψ (1, 0) = g y := by
    change Q (T (1, 0)) = g y
    rw [hT1]
    exact hQy
  have hΨavoid : Ψ.target ⊆ (Set.range f)ᶜ := fun z hz => hQavoid hz.1
  have hΨrec : ∀ z ∈ Ψ.source, Ψ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Q (T z) ∈ Set.range g ↔ _
    rw [hQrec (T z) hz.2]
    change z.1 - 1 = 0 ∧ z.2.1 = 0 ↔ _
    rw [sub_eq_zero]
  let o : C(X ⊕ Y, M) := ⟨Sum.elim f g, hf.continuous.sumElim hg.continuous⟩
  have ho : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ o := hf.sumElim hg
  have horange : Set.range o = Set.range f ∪ Set.range g := by
    ext z
    constructor
    · rintro ⟨a | b, he⟩
      · exact Or.inl ⟨a, he⟩
      · exact Or.inr ⟨b, he⟩
    · rintro (⟨a, he⟩ | ⟨b, he⟩)
      · exact ⟨Sum.inl a, he⟩
      · exact ⟨Sum.inr b, he⟩
  have hoclosed : IsClosed (Set.range o) := by rw [horange]; exact hclosedf.union hclosedg
  obtain ⟨U, hU, h0U, hUΦ, ha, hia⟩ := chart_axis_curve_properties Φ 0 hΦ0
  obtain ⟨W, hW, h1W, hWΨ, hb, hib⟩ := chart_axis_curve_properties Ψ 1 hΨ1
  have hclean0 :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Φ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 0 := by
    filter_upwards [hU.mem_nhds h0U] with t ht
    rw [horange]
    rintro (h | h)
    · exact ((hΦrec (t, 0) (hUΦ t ht)).mp h).1
    · exact (hΦavoid (Φ.map_source' (hUΦ t ht)) h).elim
  have hclean1 :
    ∀ᶠ t in 𝓝 (1 : ℝ),
      Ψ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 1 := by
    filter_upwards [hW.mem_nhds h1W] with t ht
    rw [horange]
    rintro (h | h)
    · exact (hΨavoid (Ψ.map_source' (hWΨ t ht)) h).elim
    · exact ((hΨrec (t, 0) (hWΨ t ht)).mp h).1
  have hxy : f x ≠ g y := fun h => hx ⟨y, h.symm⟩
  have hends : Φ (0, 0) ≠ Ψ (1, 0) := by
    change Φ 0 ≠ Ψ (1, 0)
    rw [hΦx, hΨy]
    exact hxy
  obtain ⟨a, ha', hleft, hright, hemb, hi, havoid⟩ :=
    exists_clean_arc_with_local_endpoint_germs ha hb hU hW h0U h1W hia hib (γ.cast hΦx hΨy) hends
      (by omega) o ho hoclosed (by rw [finrank_euclideanSpace_fin, hdim]; norm_num) hclean0
      hclean1
  have ha0 : a 0 = f x := hleft.eq_of_nhds.trans hΦx
  have ha1 : a 1 = g y := hright.eq_of_nhds.trans hΨy
  refine
    ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦavoid, hΨavoid, hΦrec, hΨrec, a, ha', hleft, hright, hemb, hi,
      ?_, ?_⟩
  · intro t ht
    constructor
    · intro h
      by_contra ht0
      have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at h; exact hy h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inl h)
    · intro he
      subst t
      rw [ha0]
      exact Set.mem_range_self x
  · intro t ht
    constructor
    · intro h
      by_contra ht1
      have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at h; exact hx h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inr h)
    · intro he
      subst t
      rw [ha1]
      exact Set.mem_range_self y

theorem Smale.TransverseCoordinates.surjective_normal_comp {D Z E B : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Q : E →L[ℝ] B) (A : D →L[ℝ] E) (C : Z →L[ℝ] E) (hQ : Function.Surjective Q)
    (hAC : Function.Surjective (A.coprod C)) (hQA : Q.comp A = 0) :
    Function.Surjective (Q.comp C) := by
  intro w
  obtain ⟨z, hz⟩ := hQ w
  obtain ⟨⟨u, v⟩, huv⟩ := hAC z
  have hAu : Q (A u) = 0 := congrArg (fun T : D →L[ℝ] B => T u) hQA
  refine ⟨v, ?_⟩
  change Q (C v) = w
  have hsum : Q (A u + C v) = w := (congrArg Q huv).trans hz
  simpa only [map_add, hAu, zero_add] using hsum

theorem Smale.TransverseCoordinates.bijective_normal_comp {D Z E B : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ Z]
    [FiniteDimensional ℝ B] (Q : E →L[ℝ] B) (A : D →L[ℝ] E) (C : Z →L[ℝ] E)
    (hQ : Function.Surjective Q) (hAC : Function.Surjective (A.coprod C)) (hQA : Q.comp A = 0)
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) : Function.Bijective (Q.comp C) := by
  have hs := surjective_normal_comp Q A C hQ hAC hQA
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hs, hs⟩

def Smale.FrameField.complementQuotient {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : D →L[ℝ] F) (C : Z →L[ℝ] F) : F →L[ℝ] Z :=
  (ContinuousLinearMap.snd ℝ D Z).comp (G.coprod C).inverse

theorem Smale.FrameField.complementQuotient_left {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) (u : D) :
    complementQuotient G C (G u) = 0 := by
  have hi := h.inverse_apply_self (u, 0)
  change (G.coprod C).inverse (G u + C 0) = (u, 0) at hi
  rw [map_zero, add_zero] at hi
  exact congrArg Prod.snd hi

theorem Smale.FrameField.complementQuotient_right {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) (v : Z) :
    complementQuotient G C (C v) = v := by
  have hi := h.inverse_apply_self (0, v)
  change (G.coprod C).inverse (G 0 + C v) = (0, v) at hi
  rw [map_zero, zero_add] at hi
  exact congrArg Prod.snd hi

theorem Smale.FrameField.ker_complementQuotient {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) :
    (complementQuotient G C).ker = G.range := by
  ext w
  constructor
  · intro hw
    let p := (G.coprod C).inverse w
    have hp : p.2 = 0 := hw
    have hi := h.self_apply_inverse w
    change G p.1 + C p.2 = w at hi
    rw [hp, map_zero, add_zero] at hi
    exact ⟨p.1, hi⟩
  · rintro ⟨u, rfl⟩
    exact complementQuotient_left G C h u

theorem Smale.FrameField.bijective_coprod_of_quotient {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C H : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible)
    (hH : Function.Bijective ((complementQuotient G C).comp H)) :
    Function.Bijective (G.coprod H) := by
  have hG : Function.Injective G := by
    intro u v huv
    have hpair : (G.coprod C) (u, 0) = (G.coprod C) (v, 0) := by
      change G u + C 0 = G v + C 0
      rw [huv]
    exact congrArg Prod.fst (h.injective hpair)
  constructor
  · intro p q hpq
    have hq := congrArg (complementQuotient G C) hpq
    change complementQuotient G C (G p.1 + H p.2) = complementQuotient G C (G q.1 + H q.2) at hq
    rw [map_add, map_add, complementQuotient_left G C h, complementQuotient_left G C h, zero_add,
      zero_add] at hq
    have hp₂ : p.2 = q.2 := hH.1 hq
    have hp₁ : p.1 = q.1 := by
      change G p.1 + H p.2 = G q.1 + H q.2 at hpq
      rw [hp₂] at hpq
      exact hG (add_right_cancel hpq)
    exact Prod.ext hp₁ hp₂
  · intro w
    obtain ⟨v, hv⟩ := hH.2 (complementQuotient G C w)
    have hmem : w - H v ∈ G.range := by
      rw [← ker_complementQuotient G C h]
      change complementQuotient G C (w - H v) = 0
      rw [map_sub]
      change complementQuotient G C w - ((complementQuotient G C).comp H) v = 0
      rw [hv, sub_self]
    obtain ⟨u, hu⟩ := hmem
    refine ⟨(u, v), ?_⟩
    change G u + H v = w
    change G u = w - H v at hu
    rw [hu, sub_add_cancel]

def Smale.FrameField.correctedComplement {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z) : Z →L[ℝ] F :=
  L + C.comp (K - (complementQuotient G C).comp L)

theorem Smale.FrameField.quotient_correctedComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z)
    (h : (G.coprod C).IsInvertible) :
    (complementQuotient G C).comp (correctedComplement G C L K) = K := by
  apply ContinuousLinearMap.ext
  intro v
  change complementQuotient G C (L v + C ((K - (complementQuotient G C).comp L) v)) = K v
  rw [map_add, complementQuotient_right G C h]
  change complementQuotient G C (L v) + (K v - complementQuotient G C (L v)) = K v
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem Smale.FrameField.correctedComplement_self {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) :
    correctedComplement G C L ((complementQuotient G C).comp L) = L := by
  simp only [correctedComplement, sub_self, ContinuousLinearMap.comp_zero, add_zero]

theorem Smale.FrameField.bijective_coprod_correctedComplement {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z)
    (h : (G.coprod C).IsInvertible) (hK : Function.Bijective K) :
    Function.Bijective (G.coprod (correctedComplement G C L K)) := by
  apply bijective_coprod_of_quotient G C _ h
  rw [quotient_correctedComplement G C L K h]
  exact hK

theorem Smale.FrameField.contDiffOn_coprod {X D Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] {G : X → (D →L[ℝ] F)}
    {C : X → (Z →L[ℝ] F)} {U : Set X} (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (fun x => (G x).coprod (C x)) U :=
  (hG.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ D Z))).add
    (hC.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ D Z)))

theorem Smale.FrameField.contDiffOn_complementQuotient {X D Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {G : X → (D →L[ℝ] F)} {C : X → (Z →L[ℝ] F)} {U : Set X}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hi : ∀ x ∈ U, ((G x).coprod (C x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => complementQuotient (G x) (C x)) U := by
  have hT := contDiffOn_coprod hG hC
  have hInv : ContDiffOn ℝ ∞ (fun x => ((G x).coprod (C x)).inverse) U := by
    intro x hx
    exact
      ((hi x hx).contDiffAt_map_inverse.comp x (hT.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  exact contDiffOn_const.clm_comp hInv

theorem Smale.FrameField.contDiffOn_correctedComplement {X D Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {G : X → (D →L[ℝ] F)} {C L : X → (Z →L[ℝ] F)} {K : X → (Z →L[ℝ] Z)}
    {U : Set X} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hL : ContDiffOn ℝ ∞ L U) (hK : ContDiffOn ℝ ∞ K U)
    (hi : ∀ x ∈ U, ((G x).coprod (C x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => correctedComplement (G x) (C x) (L x) (K x)) U :=
  hL.add (hC.clm_comp (hK.sub ((contDiffOn_complementQuotient hU hG hC hi).clm_comp hL)))

def Smale.FrameField.shearedBlock {X Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) : (X × Z) →L[ℝ] (X × F) :=
  (ContinuousLinearMap.inl ℝ X F).coprod (A.prod T)

theorem Smale.FrameField.shearedBlock_apply {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (p : X × Z) :
    shearedBlock A T p = (p.1 + A p.2, T p.2) := by
  simp [shearedBlock, ContinuousLinearMap.coprod_apply]

theorem Smale.FrameField.shearedBlock_horizontal {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (x : X) :
    shearedBlock A T (x, 0) = (x, 0) := by simp only [shearedBlock_apply, map_zero, add_zero]

theorem Smale.FrameField.bijective_shearedBlock {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (hi : Function.Bijective T) :
    Function.Bijective (shearedBlock A T) := by
  constructor
  · intro p q hpq
    have hz : p.2 = q.2 := hi.1 (by simpa only [shearedBlock_apply] using congrArg Prod.snd hpq)
    have hx : p.1 + A p.2 = q.1 + A q.2 := by
      simpa only [shearedBlock_apply] using congrArg Prod.fst hpq
    rw [hz] at hx
    exact Prod.ext (add_right_cancel hx) hz
  · intro q
    obtain ⟨z, hz⟩ := hi.2 q.2
    refine ⟨(q.1 - A z, z), ?_⟩
    rw [shearedBlock_apply]
    simp only [sub_add_cancel, hz]

def Smale.FrameField.shearedMap {X Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : X → (Z →L[ℝ] X)) (T : X → (Z →L[ℝ] F)) (p : X × Z) : X × F :=
  (p.1 + A p.1 p.2, T p.1 p.2)

theorem Smale.FrameField.shearedMap_zero {X Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : X → (Z →L[ℝ] X)) (T : X → (Z →L[ℝ] F)) (x : X) : shearedMap A T (x, 0) = (x, 0) := by
  simp only [shearedMap, map_zero, add_zero]

theorem Smale.FrameField.contDiffOn_shearedMap {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {A : X → (Z →L[ℝ] X)} {T : X → (Z →L[ℝ] F)} {U : Set X}
    (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U) :
    ContDiffOn ℝ ∞ (shearedMap A T) (Prod.fst ⁻¹' U) :=
  (contDiffOn_fst.add ((hA.comp contDiffOn_fst (fun _ hp => hp)).clm_apply contDiffOn_snd)).prodMk
    ((hT.comp contDiffOn_fst (fun _ hp => hp)).clm_apply contDiffOn_snd)

theorem Smale.FrameField.hasFDerivAt_shearedMap_zero {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {A : X → (Z →L[ℝ] X)} {T : X → (Z →L[ℝ] F)} {x : X}
    (hA : DifferentiableAt ℝ A x) (hT : DifferentiableAt ℝ T x) :
    HasFDerivAt (shearedMap A T) (shearedBlock (A x) (T x)) (x, 0) := by
  have hAa :
    HasFDerivAt (fun p : X × Z => A p.1) ((fderiv ℝ A x).comp (ContinuousLinearMap.fst ℝ X Z))
      (x, 0) :=
    hA.hasFDerivAt.comp (x, 0) hasFDerivAt_fst
  have hTt :
    HasFDerivAt (fun p : X × Z => T p.1) ((fderiv ℝ T x).comp (ContinuousLinearMap.fst ℝ X Z))
      (x, 0) :=
    hT.hasFDerivAt.comp (x, 0) hasFDerivAt_fst
  have hs : HasFDerivAt (fun p : X × Z => p.2) (ContinuousLinearMap.snd ℝ X Z) (x, 0) :=
    hasFDerivAt_snd
  have hf : HasFDerivAt (fun p : X × Z => p.1) (ContinuousLinearMap.fst ℝ X Z) (x, 0) :=
    hasFDerivAt_fst
  have hd := (hf.add (hAa.clm_apply hs)).prodMk (hTt.clm_apply hs)
  convert hd using 1 <;>
    first
    | rfl
    | (apply ContinuousLinearMap.ext; intro p; simp [shearedBlock_apply])

theorem Smale.FrameField.isInvertible_shearedBlock {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] (A : Z →L[ℝ] X)
    (T : Z →L[ℝ] F) (hi : T.IsInvertible) : (shearedBlock A T).IsInvertible := by
  let e :=
    (LinearEquiv.ofBijective (shearedBlock A T).toLinearMap
        (bijective_shearedBlock A T hi.bijective)).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

theorem Smale.FrameField.exists_sheared_frame_chart {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] {A : X → (Z →L[ℝ] X)}
    {T : X → (Z →L[ℝ] F)} {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U) (hi : ∀ x ∈ K, (T x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, X × F) (X × Z) (X × F) ∞,
      K ×ˢ {(0 : Z)} ⊆ Φ.source ∧
        Φ.source ⊆ Prod.fst ⁻¹' U ∧ (Φ : X × Z → X × F) = shearedMap A T := by
  have hzeroInj : Set.InjOn (shearedMap A T) (K ×ˢ {(0 : Z)}) := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩ ⟨y, w⟩ ⟨hy, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [shearedMap_zero, shearedMap_zero] at heq
    exact Prod.ext (congrArg (fun q : X × F => q.1) heq) rfl
  have hlocal :
    ∀ p ∈ K ×ˢ {(0 : Z)}, IsLocalDiffeomorphAt 𝓘(ℝ, X × Z) 𝓘(ℝ, X × F) ∞ (shearedMap A T) p := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply
      Smale.isLocalDiffeomorphAt_of_contMDiffOn (D := X × Z) (E := X × F) (M := X × F)
        (hU.preimage continuous_fst) (show (x, (0 : Z)) ∈ Prod.fst ⁻¹' U from hKU hx)
        (contDiffOn_shearedMap hA hT).contMDiffOn
    rw [mfderiv_eq_fderiv,
      (hasFDerivAt_shearedMap_zero
          ((hA.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
          ((hT.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))).fderiv]
    exact isInvertible_shearedBlock (A x) (T x) (hi x hx)
  exact
    Smale.exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton) hzeroInj hlocal
      (hU.preimage continuous_fst) (fun _ hp => hKU hp.1)

def Degree.AxisCoordinates.tangentShear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) : V →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ V).comp (L.comp (ContinuousLinearMap.inr ℝ ℝ V))

def Degree.AxisCoordinates.transverseBlock {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) : V →L[ℝ] V :=
  (ContinuousLinearMap.snd ℝ ℝ V).comp (L.comp (ContinuousLinearMap.inr ℝ ℝ V))

theorem Degree.AxisCoordinates.contDiff_tangentShear {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] : ContDiff ℝ ∞ (tangentShear (V := V)) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem Degree.AxisCoordinates.contDiff_transverseBlock {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] : ContDiff ℝ ∞ (transverseBlock (V := V)) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem Degree.AxisCoordinates.axis_block_apply {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0)) (s : ℝ) (z : V) :
    L (s, z) = (s + tangentShear L z, transverseBlock L z) := by
  have hp : (s, z) = s • (1, (0 : V)) + (0, z) := by simp
  rw [hp, map_add, map_smul, hL]
  apply Prod.ext <;> simp [tangentShear, transverseBlock]

theorem Degree.AxisCoordinates.axis_block_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0)) :
    L = Smale.FrameField.shearedBlock (tangentShear L) (transverseBlock L) := by
  apply ContinuousLinearMap.ext
  intro p
  rw [Smale.FrameField.shearedBlock_apply]
  exact axis_block_apply L hL p.1 p.2

theorem Degree.AxisCoordinates.bijective_transverseBlock {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0))
    (hi : Function.Bijective L) : Function.Bijective (transverseBlock L) := by
  constructor
  · intro z w hzw
    have he : L (-tangentShear L z, z) = L (-tangentShear L w, w) := by
      rw [axis_block_apply L hL, axis_block_apply L hL]
      simp only [neg_add_cancel, hzw]
    exact congrArg (fun p : ℝ × V => p.2) (hi.1 he)
  · intro w
    obtain ⟨⟨s, z⟩, hz⟩ := hi.2 (0, w)
    rw [axis_block_apply L hL] at hz
    exact ⟨z, congrArg (fun p : ℝ × V => p.2) hz⟩

theorem Degree.AxisCoordinates.isInvertible_transverseBlock {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0))
    (hi : L.IsInvertible) : (transverseBlock L).IsInvertible := by
  let e :=
    (LinearEquiv.ofBijective (transverseBlock L).toLinearMap
        (bijective_transverseBlock L hL hi.bijective)).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

theorem Degree.AxisCoordinates.derivative_fixes_axis {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : (ℝ × V) → (ℝ × V)} {s : ℝ} (hF : ContDiffAt ℝ ∞ F (s, 0))
    (heq : (fun r : ℝ => F (r, 0)) =ᶠ[𝓝 s] (fun r => (r, (0 : V)))) :
    fderiv ℝ F (s, 0) (1, 0) = (1, 0) := by
  have ha : HasDerivAt (fun r : ℝ => (r, (0 : V))) (1, 0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s 0)
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s ha
  exact hd.deriv.symm.trans (heq.deriv_eq.trans ha.deriv)

theorem Degree.AxisCoordinates.exists_native_axis_transition_data {V E M : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) {s₀ : ℝ}
    (hΦ : (s₀, (0 : V)) ∈ Φ.source) (hΨ : (s₀, (0 : V)) ∈ Ψ.source)
    (haxis : (fun s : ℝ => Φ (s, 0)) =ᶠ[𝓝 s₀] (fun s => Ψ (s, 0))) :
    ∃ U : Set ℝ,
      IsOpen U ∧
        s₀ ∈ U ∧
          (∀ s ∈ U, (s, (0 : V)) ∈ (Φ.trans Ψ.symm).source) ∧
            (∀ s ∈ U, Ψ.symm (Φ (s, 0)) = (s, 0)) ∧
              ContDiffOn ℝ ∞ (fun s => tangentShear (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) U ∧
                ContDiffOn ℝ ∞ (fun s => transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) U ∧
                  (∀ s ∈ U, (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))).IsInvertible) ∧
                    ∀ s ∈ U,
                      fderiv ℝ (Ψ.symm ∘ Φ) (s, 0) =
                        Smale.FrameField.shearedBlock
                          (tangentShear (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0)))
                          (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) := by
  let R := Φ.trans Ψ.symm
  have hR0 : (s₀, (0 : V)) ∈ R.source := by
    refine ⟨hΦ, ?_⟩
    change Φ (s₀, 0) ∈ Ψ.target
    rw [haxis.eq_of_nhds]
    exact Ψ.map_source' hΨ
  have hRsource : ∀ᶠ s in 𝓝 s₀, (s, (0 : V)) ∈ R.source :=
    (continuous_id.prodMk continuous_const).continuousAt (R.open_source.mem_nhds hR0)
  have hΨsource : ∀ᶠ s in 𝓝 s₀, (s, (0 : V)) ∈ Ψ.source :=
    (continuous_id.prodMk continuous_const).continuousAt (Ψ.open_source.mem_nhds hΨ)
  have hRaxis : ∀ᶠ s in 𝓝 s₀, R (s, (0 : V)) = (s, 0) := by
    filter_upwards [haxis, hΨsource] with s hs hsΨ
    change Ψ.symm (Φ (s, 0)) = (s, 0)
    rw [hs]
    exact Ψ.left_inv' hsΨ
  obtain ⟨U, hUN, hU, hs₀⟩ := mem_nhds_iff.mp (hRsource.and hRaxis)
  have hdf : ContDiffOn ℝ ∞ (fun s : ℝ => fderiv ℝ R (s, (0 : V))) U :=
    (R.contMDiffOn_toFun.contDiffOn.fderiv_of_isOpen R.open_source (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun s hs => (hUN hs).1)
  have hfix (s : ℝ) (hs : s ∈ U) : fderiv ℝ R (s, (0 : V)) (1, 0) = (1, 0) := by
    apply
      derivative_fixes_axis
        (R.contMDiffOn_toFun.contDiffOn.contDiffAt (R.open_source.mem_nhds (hUN hs).1))
    filter_upwards [hU.mem_nhds hs] with r hr
    exact (hUN hr).2
  refine
    ⟨U, hU, hs₀, fun s hs => (hUN hs).1, fun s hs => (hUN hs).2,
      (contDiff_tangentShear (V := V)).contDiffOn.comp hdf (fun _ _ => Set.mem_univ _),
      (contDiff_transverseBlock (V := V)).contDiffOn.comp hdf (fun _ _ => Set.mem_univ _), ?_, ?_⟩
  · intro s hs
    have hl : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ R (s, 0) :=
      ⟨R, (hUN hs).1, fun _ _ => rfl⟩
    have hi : (fderiv ℝ R (s, 0)).IsInvertible := by
      refine ⟨hl.mfderivToContinuousLinearEquiv (by simp), ?_⟩
      have he := hl.mfderivToContinuousLinearEquiv_coe (by simp)
      rw [mfderiv_eq_fderiv] at he
      exact he
    exact isInvertible_transverseBlock _ (hfix s hs) hi
  · intro s hs
    exact axis_block_eq _ (hfix s hs)

theorem Smale.exists_smooth_open_curve_with_germ {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (S : TopologicalSpace.Opens B) {a : ℝ → B} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ∈ S) :
    ∃ f : C(ℝ, S), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ f ∧ (fun t => (f t : B)) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → S := fun t => if h : a t ∈ S then ⟨a t, h⟩ else ⟨a t₀, ha0⟩
  let V := U ∩ a ⁻¹' (S : Set B)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU S.isOpen
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hsS : a s ∈ S := hs.2
    simp only [Function.comp_apply, A, dif_pos hsS]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ A V := by
    intro t ht
    have haAt := (ha.contDiffAt (hU.mem_nhds ht.1)).contMDiffAt
    have hvalAt := haAt.congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff S A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨f, hf, heq⟩ := exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨f, hf, ?_⟩
  filter_upwards [heq, hval htV] with t ht hta
  exact (congrArg Subtype.val ht).trans hta

theorem Smale.exists_smooth_open_curve_with_endpoint_germs {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (S : TopologicalSpace.Opens B) {a b : ℝ → B} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V) (ha0 : a 0 ∈ S) (hb1 : b 1 ∈ S)
    (γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S)) :
    ∃ f : ℝ → B, ContDiff ℝ ∞ f ∧ (∀ t, f t ∈ S) ∧ (f =ᶠ[𝓝 (0 : ℝ)] a) ∧ (f =ᶠ[𝓝 (1 : ℝ)] b) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_open_curve_with_germ S ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_smooth_open_curve_with_germ S hb hV h1V hb1
  have hstart : a' 0 = (⟨a 0, ha0⟩ : S) := Subtype.ext heqa.eq_of_nhds
  have hend : b' 1 = (⟨b 1, hb1⟩ : S) := Subtype.ext heqb.eq_of_nhds
  obtain ⟨f, hf, hfa, hfb⟩ :=
    exists_smooth_curve_with_endpoint_germs a' b' ha' hb' (γ.cast hstart hend)
  refine
    ⟨fun t => (f t : B), ((contMDiff_subtype_val (I := 𝓘(ℝ, B)) (U := S)).comp hf).contDiff,
      fun t => (f t).property, ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num), heqa] with t ht hta
    change t < 1 / 8 at ht
    exact (congrArg Subtype.val (hfa ht.le)).trans hta
  · filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num), heqb] with t ht htb
    change 7 / 8 < t at ht
    exact (congrArg Subtype.val (hfb ht.le)).trans htb

def Degree.LinearFramePaths.matrixCoordinates {D ι : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ D) : (D →L[ℝ] D) ≃L[ℝ] Matrix ι ι ℝ :=
  (LinearMap.toContinuousLinearMap.symm.trans (LinearMap.toMatrix b b)).toContinuousLinearEquiv

theorem Degree.LinearFramePaths.det_matrixCoordinates {D ι : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ D)
    (A : D →L[ℝ] D) : Matrix.det (matrixCoordinates b A) = A.toLinearMap.det :=
  LinearMap.det_toMatrix b A.toLinearMap

def Degree.LinearFramePaths.operatorComponent {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (σ : ℝ) : TopologicalSpace.Opens (D →L[ℝ] D) :=
  ⟨{A | 0 < σ * A.toLinearMap.det},
    isOpen_lt continuous_const (continuous_const.mul ContinuousLinearMap.continuous_det)⟩

theorem Degree.LinearFramePaths.joined_operatorComponent {D ι : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Nontrivial ι] [Finite ι] (b : Module.Basis ι ℝ D)
    {σ : ℝ} (A B : operatorComponent (D := D) σ) : Joined A B := by
  classical
  let _ := Fintype.ofFinite ι
  let e := matrixCoordinates b
  let A' : determinantComponent (ι := ι) σ :=
    ⟨e A, by
      change 0 < σ * Matrix.det (matrixCoordinates b A)
      rw [det_matrixCoordinates]
      exact A.property⟩
  let B' : determinantComponent (ι := ι) σ :=
    ⟨e B, by
      change 0 < σ * Matrix.det (matrixCoordinates b B)
      rw [det_matrixCoordinates]
      exact B.property⟩
  let ψ : determinantComponent (ι := ι) σ → operatorComponent (D := D) σ := fun C =>
    ⟨e.symm C, by
      have hd := det_matrixCoordinates b (e.symm C)
      change Matrix.det (e (e.symm C)) = (e.symm C).toLinearMap.det at hd
      rw [e.apply_symm_apply] at hd
      change 0 < σ * (e.symm C).toLinearMap.det
      rw [← hd]
      exact C.property⟩
  have hψ : Continuous ψ := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
  have hA : ψ A' = A := Subtype.ext (e.symm_apply_apply A)
  have hB : ψ B' = B := Subtype.ext (e.symm_apply_apply B)
  have h := (joined_determinantComponent A' B').map hψ
  rwa [hA, hB] at h

theorem Degree.LinearFramePaths.exists_smooth_invertible_frame_join {D ι : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Nontrivial ι] [Finite ι]
    (basis : Module.Basis ι ℝ D) {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ} (ha : ContDiffOn ℝ ∞ a U)
    (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U)
    (h1V : (1 : ℝ) ∈ V) (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  let S := operatorComponent (D := D) σ
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hsign
    exact lt_irrefl _ hsign
  have ha0 : a 0 ∈ S := mul_self_pos.mpr ha0ne
  have hb1 : b 1 ∈ S := hsign
  let γ := (joined_operatorComponent basis (⟨a 0, ha0⟩ : S) ⟨b 1, hb1⟩).somePath
  obtain ⟨L, hL, hmem, hleft, hright⟩ :=
    Smale.exists_smooth_open_curve_with_endpoint_germs S ha hb hU hV h0U h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := hmem t
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  have hdet : (L t).toLinearMap.det ≠ 0 := by
    intro hz
    have hp := hpositive t
    rw [hz, MulZeroClass.mul_zero] at hp
    exact lt_irrefl _ hp
  have hker : (L t).toLinearMap.ker = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hi : Function.Injective (L t) := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

theorem Degree.AxisCoordinates.exists_smooth_sheared_frame_join {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Finite ι] [Nontrivial ι]
    (basis : Module.Basis ι ℝ V) {A₀ A₁ : ℝ → (V →L[ℝ] ℝ)} {T₀ T₁ : ℝ → (V →L[ℝ] V)}
    {U₀ U₁ : Set ℝ} (hA₀ : ContDiffOn ℝ ∞ A₀ U₀) (hA₁ : ContDiffOn ℝ ∞ A₁ U₁)
    (hT₀ : ContDiffOn ℝ ∞ T₀ U₀) (hT₁ : ContDiffOn ℝ ∞ T₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0 : (0 : ℝ) ∈ U₀) (h1 : (1 : ℝ) ∈ U₁)
    (hsign : 0 < (T₀ 0).toLinearMap.det * (T₁ 1).toLinearMap.det) :
    ∃ A : ℝ → (V →L[ℝ] ℝ),
      ∃ T : ℝ → (V →L[ℝ] V),
        ContDiff ℝ ∞ A ∧
          ContDiff ℝ ∞ T ∧
            (∀ s, (T s).IsInvertible) ∧
              (∀ s, (Smale.FrameField.shearedBlock (A s) (T s)).IsInvertible) ∧
                (A =ᶠ[𝓝 (0 : ℝ)] A₀) ∧
                  (A =ᶠ[𝓝 (1 : ℝ)] A₁) ∧ (T =ᶠ[𝓝 (0 : ℝ)] T₀) ∧ (T =ᶠ[𝓝 (1 : ℝ)] T₁) := by
  let S : TopologicalSpace.Opens (V →L[ℝ] ℝ) := ⟨Set.univ, isOpen_univ⟩
  let γ : Path (⟨A₀ 0, Set.mem_univ _⟩ : S) ⟨A₁ 1, Set.mem_univ _⟩ :=
    { toFun := fun t => ⟨(1 - (t : ℝ)) • A₀ 0 + (t : ℝ) • A₁ 1, Set.mem_univ _⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
  obtain ⟨A, hA, -, ha₀, ha₁⟩ :=
    Smale.exists_smooth_open_curve_with_endpoint_germs S hA₀ hA₁ hU₀ hU₁ h0 h1 (Set.mem_univ _)
      (Set.mem_univ _) γ
  obtain ⟨T, hT, hi, -, ht₀, ht₁⟩ :=
    Degree.LinearFramePaths.exists_smooth_invertible_frame_join basis hT₀ hT₁ hU₀ hU₁ h0 h1 hsign
  have hTi (s : ℝ) : (T s).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (T s).toLinearMap (hi s)).toContinuousLinearEquiv, rfl⟩
  exact
    ⟨A, T, hA, hT, hTi, fun s => Smale.FrameField.isInvertible_shearedBlock (A s) (T s) (hTi s),
      ha₀, ha₁, ht₀, ht₁⟩

theorem Degree.AxisCoordinates.exists_smooth_sheared_frame_join_at {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Finite ι] [Nontrivial ι]
    (basis : Module.Basis ι ℝ V) {p q : ℝ} (hpq : p < q) {A₀ A₁ : ℝ → (V →L[ℝ] ℝ)}
    {T₀ T₁ : ℝ → (V →L[ℝ] V)} {U₀ U₁ : Set ℝ} (hA₀ : ContDiffOn ℝ ∞ A₀ U₀)
    (hA₁ : ContDiffOn ℝ ∞ A₁ U₁) (hT₀ : ContDiffOn ℝ ∞ T₀ U₀) (hT₁ : ContDiffOn ℝ ∞ T₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (hp : p ∈ U₀) (hq : q ∈ U₁)
    (hsign : 0 < (T₀ p).toLinearMap.det * (T₁ q).toLinearMap.det) :
    ∃ A : ℝ → (V →L[ℝ] ℝ),
      ∃ T : ℝ → (V →L[ℝ] V),
        ContDiff ℝ ∞ A ∧
          ContDiff ℝ ∞ T ∧
            (∀ s, (T s).IsInvertible) ∧
              (∀ s, (Smale.FrameField.shearedBlock (A s) (T s)).IsInvertible) ∧
                (A =ᶠ[𝓝 p] A₀) ∧ (A =ᶠ[𝓝 q] A₁) ∧ (T =ᶠ[𝓝 p] T₀) ∧ (T =ᶠ[𝓝 q] T₁) := by
  let ξ : ℝ → ℝ := fun t => p + (q - p) * t
  let ζ : ℝ → ℝ := fun s => (s - p) / (q - p)
  have hn : q - p ≠ 0 := ne_of_gt (sub_pos.mpr hpq)
  have hξ : ContDiff ℝ ∞ ξ := by dsimp [ξ]; fun_prop
  have hζ : ContDiff ℝ ∞ ζ := by dsimp [ζ]; fun_prop
  have hξ0 : ξ 0 = p := by simp [ξ]
  have hξ1 : ξ 1 = q := by simp [ξ]
  have hζp : ζ p = 0 := by simp [ζ]
  have hζq : ζ q = 1 := by simp [ζ, hn]
  have hξζ (s : ℝ) : ξ (ζ s) = s := by
    dsimp [ξ, ζ]
    field_simp
    ring
  have h0 : (0 : ℝ) ∈ ξ ⁻¹' U₀ := by simpa only [Set.mem_preimage, hξ0] using hp
  have h1 : (1 : ℝ) ∈ ξ ⁻¹' U₁ := by simpa only [Set.mem_preimage, hξ1] using hq
  have hsgn : 0 < ((T₀ ∘ ξ) 0).toLinearMap.det * ((T₁ ∘ ξ) 1).toLinearMap.det := by
    simpa only [Function.comp_apply, hξ0, hξ1] using hsign
  obtain ⟨A, T, hA, hT, hi, hb, ha₀, ha₁, ht₀, ht₁⟩ :=
    exists_smooth_sheared_frame_join basis (hA₀.comp hξ.contDiffOn (fun _ hs => hs))
      (hA₁.comp hξ.contDiffOn (fun _ hs => hs)) (hT₀.comp hξ.contDiffOn (fun _ hs => hs))
      (hT₁.comp hξ.contDiffOn (fun _ hs => hs)) (hU₀.preimage hξ.continuous)
      (hU₁.preimage hξ.continuous) h0 h1 hsgn
  have hζ0 : Filter.Tendsto ζ (𝓝 p) (𝓝 0) := by
    simpa only [hζp] using hζ.continuous.continuousAt.tendsto (x := p)
  have hζ1 : Filter.Tendsto ζ (𝓝 q) (𝓝 1) := by
    simpa only [hζq] using hζ.continuous.continuousAt.tendsto (x := q)
  refine
    ⟨A ∘ ζ, T ∘ ζ, hA.comp hζ, hT.comp hζ, fun s => hi (ζ s), fun s => hb (ζ s), ?_, ?_, ?_, ?_⟩
  · filter_upwards [hζ0 ha₀] with s hs
    exact hs.trans (congrArg A₀ (hξζ s))
  · filter_upwards [hζ1 ha₁] with s hs
    exact hs.trans (congrArg A₁ (hξζ s))
  · filter_upwards [hζ0 ht₀] with s hs
    exact hs.trans (congrArg T₀ (hξζ s))
  · filter_upwards [hζ1 ht₁] with s hs
    exact hs.trans (congrArg T₁ (hξζ s))

theorem Degree.AxisCoordinates.exists_flat_local_correction {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H R : E → F} {K U : Set E} {x : E} (hH : ContDiff ℝ ∞ H) (hR : ContDiffOn ℝ ∞ R U)
    (hU : IsOpen U) (hx : x ∈ U) (hvalue : ∀ y ∈ K ∩ U, R y = H y)
    (hderiv : ∀ y ∈ K ∩ U, fderiv ℝ R y = fderiv ℝ H y) :
    ∃ G : E → F,
      ContDiff ℝ ∞ G ∧
        (G =ᶠ[𝓝 x] R) ∧
          (∀ y ∉ U, G =ᶠ[𝓝 y] H) ∧ Set.EqOn G H K ∧ Set.EqOn (fderiv ℝ G) (fderiv ℝ H) K := by
  obtain ⟨β, hβ, -, hsupp, hone, -⟩ :=
    Smale.exists_compact_smooth_cutoff (isCompact_singleton : IsCompact ({ x } : Set E)) hU
      (Set.singleton_subset_iff.mpr hx)
  let G : E → F := fun y => H y + β y • (R y - H y)
  have hoff (y : E) (hy : y ∉ tsupport β) : G =ᶠ[𝓝 y] H := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp only [G, hz, Pi.zero_apply, zero_smul, add_zero]
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport β
    · exact
        hH.contDiffAt.add
          (hβ.contDiffAt.smul ((hR.contDiffAt (hU.mem_nhds (hsupp hy))).sub hH.contDiffAt))
    · exact hH.contDiffAt.congr_of_eventuallyEq (hoff y hy)
  have hGeq (y : E) (hy : y ∈ K) : G y = H y := by
    by_cases hb : y ∈ tsupport β
    · simp only [G, hvalue y ⟨hy, hsupp hb⟩, sub_self, smul_zero, add_zero]
    · exact (hoff y hb).eq_of_nhds
  refine ⟨G, hG, ?_, fun y hy => hoff y (fun h => hy (hsupp h)), hGeq, ?_⟩
  · have hone' : ∀ᶠ y in 𝓝 x, β y = 1 := by simpa only [nhdsSet_singleton] using hone
    filter_upwards [hone'] with y hy
    simp only [G, hy, one_smul]
    abel
  · intro y hy
    by_cases hb : y ∈ tsupport β
    · have hr := (hR.contDiffAt (hU.mem_nhds (hsupp hb))).differentiableAt (by simp)
      have hh := hH.differentiable (by simp) y
      have hd : HasFDerivAt (fun z => R z - H z) (0 : E →L[ℝ] F) y := by
        simpa only [hderiv y ⟨hy, hsupp hb⟩, sub_self, Pi.sub_def] using
          hr.hasFDerivAt.sub hh.hasFDerivAt
      have hc : HasFDerivAt (fun z => β z • (R z - H z)) (0 : E →L[ℝ] F) y := by
        simpa only [hvalue y ⟨hy, hsupp hb⟩, sub_self, smul_zero,
          ContinuousLinearMap.smulRight_zero, add_zero, Pi.smul_def'] using
          (hβ.differentiable (by simp) y).hasFDerivAt.smul hd
      simpa only [add_zero, Pi.add_def, G] using (hh.hasFDerivAt.add hc).fderiv
    · exact (hoff y hb).fderiv_eq

theorem Degree.AxisCoordinates.exists_axis_germ_correction {V F : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H R₀ R₁ : (ℝ × V) → F} {U₀ U₁ : Set (ℝ × V)} {p q : ℝ} (hpq : p < q) (hH : ContDiff ℝ ∞ H)
    (hR₀ : ContDiffOn ℝ ∞ R₀ U₀) (hR₁ : ContDiffOn ℝ ∞ R₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0 : (p, (0 : V)) ∈ U₀) (h1 : (q, (0 : V)) ∈ U₁)
    (hv₀ : (fun s : ℝ => R₀ (s, 0)) =ᶠ[𝓝 p] (fun s => H (s, 0)))
    (hv₁ : (fun s : ℝ => R₁ (s, 0)) =ᶠ[𝓝 q] (fun s => H (s, 0)))
    (hd₀ : (fun s : ℝ => fderiv ℝ R₀ (s, 0)) =ᶠ[𝓝 p] (fun s => fderiv ℝ H (s, 0)))
    (hd₁ : (fun s : ℝ => fderiv ℝ R₁ (s, 0)) =ᶠ[𝓝 q] (fun s => fderiv ℝ H (s, 0))) :
    ∃ G : (ℝ × V) → F,
      ContDiff ℝ ∞ G ∧
        (∀ s : ℝ, G (s, 0) = H (s, 0)) ∧
          (∀ s : ℝ, fderiv ℝ G (s, 0) = fderiv ℝ H (s, 0)) ∧
            (G =ᶠ[𝓝 (p, (0 : V))] R₀) ∧ (G =ᶠ[𝓝 (q, (0 : V))] R₁) := by
  obtain ⟨I₀, hI₀sub, hI₀, h0I⟩ := mem_nhds_iff.mp (hv₀.and hd₀)
  obtain ⟨I₁, hI₁sub, hI₁, h1I⟩ := mem_nhds_iff.mp (hv₁.and hd₁)
  let W₀ := U₀ ∩ Prod.fst ⁻¹' (I₀ ∩ Set.Iio ((p + q) / 2))
  let W₁ := U₁ ∩ Prod.fst ⁻¹' (I₁ ∩ Set.Ioi ((p + q) / 2))
  have hW₀ : IsOpen W₀ := hU₀.inter ((hI₀.inter isOpen_Iio).preimage continuous_fst)
  have hW₁ : IsOpen W₁ := hU₁.inter ((hI₁.inter isOpen_Ioi).preimage continuous_fst)
  have h0W : (p, (0 : V)) ∈ W₀ := ⟨h0, h0I, by change p < (p + q) / 2; linarith⟩
  have h1W : (q, (0 : V)) ∈ W₁ := ⟨h1, h1I, by change (p + q) / 2 < q; linarith⟩
  let K : Set (ℝ × V) := Set.univ ×ˢ {0}
  have hv0 (y : ℝ × V) (hy : y ∈ K ∩ W₀) : R₀ y = H y := by
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₀sub hy.2.2.1).1
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  have hd0 (y : ℝ × V) (hy : y ∈ K ∩ W₀) : fderiv ℝ R₀ y = fderiv ℝ H y := by
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₀sub hy.2.2.1).2
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  obtain ⟨G₀, hG₀, hg₀, -, hvG₀, hdG₀⟩ :=
    exists_flat_local_correction hH (hR₀.mono Set.inter_subset_left) hW₀ h0W hv0 hd0
  have hv1 (y : ℝ × V) (hy : y ∈ K ∩ W₁) : R₁ y = G₀ y := by
    rw [hvG₀ hy.1]
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₁sub hy.2.2.1).1
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  have hd1 (y : ℝ × V) (hy : y ∈ K ∩ W₁) : fderiv ℝ R₁ y = fderiv ℝ G₀ y := by
    rw [hdG₀ hy.1]
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₁sub hy.2.2.1).2
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  obtain ⟨G, hG, hg₁, hoff, hvG, hdG⟩ :=
    exists_flat_local_correction hG₀ (hR₁.mono Set.inter_subset_left) hW₁ h1W hv1 hd1
  have h0not : (p, (0 : V)) ∉ W₁ := by
    intro hh
    have hbad : (p + q) / 2 < p := hh.2.2
    linarith
  refine ⟨G, hG, ?_, ?_, (hoff _ h0not).trans hg₀, hg₁⟩
  · intro s
    have hs : (s, (0 : V)) ∈ K := ⟨Set.mem_univ s, rfl⟩
    exact (hvG hs).trans (hvG₀ hs)
  · intro s
    have hs : (s, (0 : V)) ∈ K := ⟨Set.mem_univ s, rfl⟩
    exact (hdG hs).trans (hdG₀ hs)

theorem Smale.FrameField.exists_sheared_tubular_chart {X Z F E M : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Ψ : PartialDiffeomorph 𝓘(ℝ, X × F) 𝓘(ℝ, E) (X × F) M ∞) {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hzero : K ×ˢ {(0 : F)} ⊆ Ψ.source) {A : X → (Z →L[ℝ] X)}
    {T : X → (Z →L[ℝ] F)} (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U)
    (hi : ∀ x ∈ K, (T x).IsInvertible) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, E) (X × Z) M ∞,
          K ×ˢ Metric.closedBall (0 : Z) ε ⊆ Φ.source ∧
            (∀ p, Φ p = Ψ (shearedMap A T p)) ∧
              Φ.target ⊆ Ψ.target ∧
                (∀ x ∈ K, (Ψ.symm ∘ Φ) =ᶠ[𝓝 (x, (0 : Z))] shearedMap A T) ∧
                  ∀ x ∈ K, HasFDerivAt (Ψ.symm ∘ Φ) (shearedBlock (A x) (T x)) (x, 0) := by
  obtain ⟨χ, hzeroχ, -, hχ⟩ := exists_sheared_frame_chart hK hU hKU hA hT hi
  let Φ := χ.trans Ψ
  have hzeroΦ : K ×ˢ {(0 : Z)} ⊆ Φ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hzeroχ ⟨hx, rfl⟩, ?_⟩
    change χ (x, 0) ∈ Ψ.source
    rw [hχ, shearedMap_zero]
    exact hzero ⟨hx, rfl⟩
  obtain ⟨ε, hε, hprod⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset hK Φ.open_source hzeroΦ
  have hgerm : ∀ x ∈ K, (Ψ.symm ∘ Φ) =ᶠ[𝓝 (x, (0 : Z))] shearedMap A T := by
    intro x hx
    filter_upwards [Φ.open_source.mem_nhds (hzeroΦ ⟨hx, rfl⟩)] with p hp
    change Ψ.symm (Ψ (χ p)) = shearedMap A T p
    have hpΨ : χ p ∈ Ψ.source := hp.2
    exact (Ψ.left_inv' hpΨ).trans (congrFun hχ p)
  refine ⟨ε, hε, Φ, hprod, ?_, fun _ hy => hy.1, hgerm, ?_⟩
  · intro p
    change Ψ (χ p) = Ψ (shearedMap A T p)
    rw [hχ]
  · intro x hx
    apply (hgerm x hx).hasFDerivAt_iff.mpr
    exact
      hasFDerivAt_shearedMap_zero
        ((hA.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
        ((hT.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))

theorem Degree.AxisCoordinates.exists_native_axis_chart_with_endpoint_germs {V E M ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Finite ι] [Nontrivial ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (basis : Module.Basis ι ℝ V) (Ψ Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    {p q : ℝ} (hpq : p < q) {K : Set ℝ} (hK : IsCompact K) (hzero : K ×ˢ {(0 : V)} ⊆ Ψ.source)
    (hΨ₀ : (p, (0 : V)) ∈ Ψ.source) (hΨ₁ : (q, (0 : V)) ∈ Ψ.source)
    (hΦ₀ : (p, (0 : V)) ∈ Φ₀.source) (hΦ₁ : (q, (0 : V)) ∈ Φ₁.source)
    (haxis₀ : (fun s : ℝ => Φ₀ (s, 0)) =ᶠ[𝓝 p] (fun s => Ψ (s, 0)))
    (haxis₁ : (fun s : ℝ => Φ₁ (s, 0)) =ᶠ[𝓝 q] (fun s => Ψ (s, 0)))
    (hsign :
      0 <
        (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det *
          (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₁) (q, 0))).toLinearMap.det) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞,
          K ×ˢ Metric.closedBall (0 : V) ε ⊆ Φ.source ∧
            Φ.target ⊆ Ψ.target ∧
              (∀ s : ℝ, Φ (s, 0) = Ψ (s, 0)) ∧
                ((Φ : (ℝ × V) → M) =ᶠ[𝓝 (p, (0 : V))] Φ₀) ∧
                  ((Φ : (ℝ × V) → M) =ᶠ[𝓝 (q, (0 : V))] Φ₁) := by
  let R₀ := Φ₀.trans Ψ.symm
  let R₁ := Φ₁.trans Ψ.symm
  obtain ⟨U₀, hU₀, h0U, hs₀, hx₀, ha₀, ht₀, -, hb₀⟩ :=
    exists_native_axis_transition_data Φ₀ Ψ hΦ₀ hΨ₀ haxis₀
  obtain ⟨U₁, hU₁, h1U, hs₁, hx₁, ha₁, ht₁, -, hb₁⟩ :=
    exists_native_axis_transition_data Φ₁ Ψ hΦ₁ hΨ₁ haxis₁
  obtain ⟨A, T, hA, hT, -, hinv, hA₀, hA₁, hT₀, hT₁⟩ :=
    exists_smooth_sheared_frame_join_at basis hpq ha₀ ha₁ ht₀ ht₁ hU₀ hU₁ h0U h1U hsign
  let H := Smale.FrameField.shearedMap A T
  have hH : ContDiff ℝ ∞ H :=
    (contDiff_fst.add ((hA.comp contDiff_fst).clm_apply contDiff_snd)).prodMk
      ((hT.comp contDiff_fst).clm_apply contDiff_snd)
  have hHd (s : ℝ) : fderiv ℝ H (s, (0 : V)) = Smale.FrameField.shearedBlock (A s) (T s) :=
    (Smale.FrameField.hasFDerivAt_shearedMap_zero (hA.differentiable (by simp) s)
        (hT.differentiable (by simp) s)).fderiv
  have hv₀ : (fun s : ℝ => R₀ (s, (0 : V))) =ᶠ[𝓝 p] (fun s => H (s, 0)) := by
    filter_upwards [hU₀.mem_nhds h0U] with s hs
    exact (hx₀ s hs).trans (Smale.FrameField.shearedMap_zero A T s).symm
  have hv₁ : (fun s : ℝ => R₁ (s, (0 : V))) =ᶠ[𝓝 q] (fun s => H (s, 0)) := by
    filter_upwards [hU₁.mem_nhds h1U] with s hs
    exact (hx₁ s hs).trans (Smale.FrameField.shearedMap_zero A T s).symm
  have hd₀ : (fun s : ℝ => fderiv ℝ R₀ (s, (0 : V))) =ᶠ[𝓝 p] (fun s => fderiv ℝ H (s, 0)) := by
    filter_upwards [hU₀.mem_nhds h0U, hA₀, hT₀] with s hs ha ht
    change fderiv ℝ (Ψ.symm ∘ Φ₀) (s, 0) = _
    rw [hb₀ s hs, hHd s, ha, ht]
  have hd₁ : (fun s : ℝ => fderiv ℝ R₁ (s, (0 : V))) =ᶠ[𝓝 q] (fun s => fderiv ℝ H (s, 0)) := by
    filter_upwards [hU₁.mem_nhds h1U, hA₁, hT₁] with s hs ha ht
    change fderiv ℝ (Ψ.symm ∘ Φ₁) (s, 0) = _
    rw [hb₁ s hs, hHd s, ha, ht]
  obtain ⟨G, hG, hvG, hdG, hg₀, hg₁⟩ :=
    exists_axis_germ_correction hpq hH R₀.contMDiffOn_toFun.contDiffOn
      R₁.contMDiffOn_toFun.contDiffOn R₀.open_source R₁.open_source (hs₀ p h0U) (hs₁ q h1U) hv₀
      hv₁ hd₀ hd₁
  have hGaxis (s : ℝ) : G (s, (0 : V)) = (s, 0) :=
    (hvG s).trans (Smale.FrameField.shearedMap_zero A T s)
  have hGi : Set.InjOn G (K ×ˢ {(0 : V)}) := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩ ⟨t, w⟩ ⟨ht, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    simpa only [hGaxis] using heq
  have hGl : ∀ p ∈ K ×ˢ {(0 : V)}, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ G p := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply
      Smale.isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ _)
        hG.contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv, hdG s, hHd s]
    exact hinv s
  have hGO : K ×ˢ {(0 : V)} ⊆ G ⁻¹' Ψ.source := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change G (s, 0) ∈ Ψ.source
    rw [hGaxis]
    exact hzero ⟨hs, rfl⟩
  obtain ⟨χ, hχzero, hχsub, hχ⟩ :=
    Smale.exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton) hGi hGl
      (Ψ.open_source.preimage hG.continuous) hGO
  let Φ := χ.trans Ψ
  have hΦzero : K ×ˢ {(0 : V)} ⊆ Φ.source := by
    intro p hp
    refine ⟨hχzero hp, ?_⟩
    change χ p ∈ Ψ.source
    rw [hχ]
    exact hχsub (hχzero hp)
  obtain ⟨ε, hε, hprod⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset hK Φ.open_source hΦzero
  have hformula (p : ℝ × V) : Φ p = Ψ (G p) := by
    change Ψ (χ p) = Ψ (G p)
    rw [hχ]
  refine ⟨ε, hε, Φ, hprod, fun _ hy => hy.1, ?_, ?_, ?_⟩
  · intro s
    rw [hformula, hGaxis]
  · filter_upwards [hg₀, R₀.open_source.mem_nhds (hs₀ p h0U)] with p hp hs
    rw [hformula, hp]
    exact Ψ.right_inv' hs.2
  · filter_upwards [hg₁, R₁.open_source.mem_nhds (hs₁ q h1U)] with p hp hs
    rw [hformula, hp]
    exact Ψ.right_inv' hs.2

def MorseCancel.linearTransverseChart {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (C : V ≃L[ℝ] V) (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞ :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C).toDiffeomorph.toPartialDiffeomorph.trans Φ

theorem MorseCancel.linearTransverseChart_axis {V E M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (C : V ≃L[ℝ] V) (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    (t : ℝ) : linearTransverseChart C Φ (t, 0) = Φ (t, 0) := by
  change Φ (t, C 0) = Φ (t, 0)
  rw [map_zero]

theorem MorseCancel.linearTransverseChart_axis_source {V E M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (C : V ≃L[ℝ] V) (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    (t : ℝ) : (t, (0 : V)) ∈ (linearTransverseChart C Φ).source ↔ (t, (0 : V)) ∈ Φ.source := by
  change (t, (0 : V)) ∈ Set.univ ∧ (t, C 0) ∈ Φ.source ↔ _
  simp only [Set.mem_univ, map_zero, true_and]

theorem MorseCancel.transverseBlock_comp_linear {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (C : V ≃L[ℝ] V) (L : (ℝ × V) →L[ℝ] (ℝ × V)) :
    Degree.AxisCoordinates.transverseBlock
        (L.comp ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C).toContinuousLinearMap) =
      (Degree.AxisCoordinates.transverseBlock L).comp C.toContinuousLinearMap := by
  ext z
  rfl

theorem MorseCancel.det_transition_linearTransverseChart {V E M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (C : V ≃L[ℝ] V) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    {t : ℝ} (ht : (t, (0 : V)) ∈ (Φ.trans Ψ.symm).source) :
    (Degree.AxisCoordinates.transverseBlock
          (fderiv ℝ (Ψ.symm ∘ linearTransverseChart C Φ) (t, 0))).toLinearMap.det =
      (Degree.AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (t, 0))).toLinearMap.det *
        C.toLinearMap.det := by
  let P := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C
  have hP (s : ℝ) : P (s, (0 : V)) = (s, 0) := by
    change (s, C 0) = (s, 0)
    rw [map_zero]
  have hr : DifferentiableAt ℝ (Ψ.symm ∘ Φ) (t, (0 : V)) :=
    ((Φ.trans Ψ.symm).contMDiffOn_toFun.contDiffOn.contDiffAt
          ((Φ.trans Ψ.symm).open_source.mem_nhds ht)).differentiableAt
      (by simp)
  have hre : DifferentiableAt ℝ (Ψ.symm ∘ Φ) (P (t, (0 : V))) := by
    rw [hP]
    exact hr
  have heq : (Ψ.symm ∘ linearTransverseChart C Φ) = (Ψ.symm ∘ Φ) ∘ P := rfl
  rw [heq, fderiv_comp _ hre P.differentiableAt, P.fderiv, hP, transverseBlock_comp_linear]
  exact LinearMap.det_comp _ _

theorem MorseCancel.det_ne_zero_of_isInvertible {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (T : V →L[ℝ] V) (hT : T.IsInvertible) : T.toLinearMap.det ≠ 0 := by
  obtain ⟨e, he⟩ := hT
  rw [← he]
  exact e.toLinearEquiv.isUnit_det'.ne_zero

theorem MorseCancel.exists_compatible_sheet_endpoint_orientation {A B E M ι : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (basis : Module.Basis ι ℝ B) (i : ι)
    (Ψ Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (A × B)) 𝓘(ℝ, E) (ℝ × (A × B)) M ∞) {p q : ℝ}
    (hΨ₀ : (p, (0 : A × B)) ∈ Ψ.source) (hΨ₁ : (q, (0 : A × B)) ∈ Ψ.source)
    (hΦ₀ : (p, (0 : A × B)) ∈ Φ₀.source) (hΦ₁ : (q, (0 : A × B)) ∈ Φ₁.source)
    (haxis₀ : (fun s : ℝ => Φ₀ (s, 0)) =ᶠ[𝓝 p] (fun s => Ψ (s, 0)))
    (haxis₁ : (fun s : ℝ => Φ₁ (s, 0)) =ᶠ[𝓝 q] (fun s => Ψ (s, 0))) :
    ∃ R : B ≃L[ℝ] B,
      0 <
        (Degree.AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det *
          (Degree.AxisCoordinates.transverseBlock
              (fderiv ℝ
                (Ψ.symm ∘ linearTransverseChart ((ContinuousLinearEquiv.refl ℝ A).prodCongr R) Φ₁)
                (q, 0))).toLinearMap.det := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨U₀, -, hp, -, -, -, -, hi₀, -⟩ :=
    Degree.AxisCoordinates.exists_native_axis_transition_data Φ₀ Ψ hΦ₀ hΨ₀ haxis₀
  obtain ⟨U₁, -, hq, hs₁, -, -, -, hi₁, -⟩ :=
    Degree.AxisCoordinates.exists_native_axis_transition_data Φ₁ Ψ hΦ₁ hΨ₁ haxis₁
  let d₀ :=
    (Degree.AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det
  let d₁ :=
    (Degree.AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₁) (q, 0))).toLinearMap.det
  have h₀ : d₀ ≠ 0 := det_ne_zero_of_isInvertible _ (hi₀ p hp)
  have h₁ : d₁ ≠ 0 := det_ne_zero_of_isInvertible _ (hi₁ q hq)
  obtain ⟨R, hR⟩ :=
    Degree.SupportedGerms.exists_linearEquiv_with_det basis i (inv_ne_zero (mul_ne_zero h₀ h₁))
  refine ⟨R, ?_⟩
  rw [det_transition_linearTransverseChart _ Φ₁ Ψ (hs₁ q hq)]
  have hdet : ((ContinuousLinearEquiv.refl ℝ A).prodCongr R).toLinearMap.det = (d₀ * d₁)⁻¹ := by
    change ((LinearMap.id : A →ₗ[ℝ] A).prodMap R.toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul, hR]
  rw [hdet]
  change 0 < d₀ * (d₁ * (d₀ * d₁)⁻¹)
  have hone : d₀ * (d₁ * (d₀ * d₁)⁻¹) = 1 := by
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero h₀ h₁)]
  rw [hone]
  exact zero_lt_one

theorem MorseCancel.exists_sheet_arc_tube {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {a : ℝ → M} (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a)
    (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞)
    (hΦ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source)
    (hΦ₁ : ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0)) (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {O : Set M} (hO : IsOpen O) (haO : Set.MapsTo a (Set.Icc (0 : ℝ) 1) O) :
    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
            𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
          Set.Icc (0 : ℝ) 1 ×ˢ
                Metric.closedBall (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                  ε ⊆
              Φ.source ∧
            (∀ t : ℝ, Φ (t, 0) = a t) ∧
              ((Φ :
                    (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                      M) =ᶠ[𝓝
                    (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                  Φ₀) ∧
                ((Φ :
                      (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                        M) =ᶠ[𝓝
                      ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                    linearTransverseChart
                      ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr R)
                      Φ₁) ∧
                  Φ.target ⊆ O := by
  have h0K : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1K : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨r, hr, Ξ, hΞprod, hΞaxis, hΞO⟩ :=
    Smale.exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero ha
      CompactIccSpace.isCompact_Icc h0K ((convex_Icc (0 : ℝ) 1).starConvex h0K) hinj hi 4
      (by rw [Module.finrank_self, hdim]) hO haO
  let L :
    ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin])
  let P := ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr L).toDiffeomorph
  let Ψ := P.toPartialDiffeomorph.trans Ξ
  have hΨaxis (t : ℝ) : Ψ (t, 0) = a t := by
    change Ξ (t, L 0) = a t
    rw [map_zero, hΞaxis]
  have hzero :
    Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))} ⊆
      Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change
      (t, (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Set.univ ∧
        (t, L 0) ∈ Ξ.source
    rw [map_zero]
    exact ⟨Set.mem_univ _, hΞprod ⟨ht, Metric.mem_closedBall_self hr.le⟩⟩
  have hΨ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Ψ.source :=
    hzero ⟨h0K, rfl⟩
  have hΨ₁ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Ψ.source :=
    hzero ⟨h1K, rfl⟩
  have haxis₀ : (fun t : ℝ => Φ₀ (t, 0)) =ᶠ[𝓝 (0 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [hleft] with t ht
    exact ht.symm.trans (hΨaxis t).symm
  have haxis₁ : (fun t : ℝ => Φ₁ (t, 0)) =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [hright] with t ht
    exact ht.symm.trans (hΨaxis t).symm
  obtain ⟨R, hsign⟩ :=
    exists_compatible_sheet_endpoint_orientation (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 2)))
      ⟨0, by simp only [finrank_euclideanSpace_fin]; norm_num⟩ Ψ Φ₀ Φ₁ hΨ₀ hΨ₁ hΦ₀ hΦ₁ haxis₀
      haxis₁
  let C := (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr R
  let Φ₂ := linearTransverseChart C Φ₁
  have hΦ₂ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source C Φ₁ 1).mpr hΦ₁
  have haxis₂ : (fun t : ℝ => Φ₂ (t, 0)) =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [haxis₁] with t ht
    exact (linearTransverseChart_axis C Φ₁ t).trans ht
  let _ :
    Nontrivial
      (Fin (Module.finrank ℝ ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) :=
    Fin.nontrivial_iff_two_le.mpr
      (by
        simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
        norm_num)
  obtain ⟨ε, hε, Φ, hprod, htarget, haxis, hgl, hgr⟩ :=
    Degree.AxisCoordinates.exists_native_axis_chart_with_endpoint_germs
      (Module.finBasis ℝ ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) Ψ Φ₀ Φ₂
      zero_lt_one CompactIccSpace.isCompact_Icc hzero hΨ₀ hΨ₁ hΦ₀ hΦ₂ haxis₀ haxis₂ hsign
  exact
    ⟨R, ε, hε, Φ, hprod, fun t => (haxis t).trans (hΨaxis t), hgl, hgr, fun z hz =>
      hΞO (htarget hz).1⟩

theorem MorseCancel.exists_open_tube_sheet_recognition {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) {K : Set ℝ}
    (hKsource : K ×ˢ {(0 : V)} ⊆ Φ.source) {S : Set M} (hS : IsClosed S) (p : ℝ) (N : Set V)
    (hlocal : ∀ᶠ z in 𝓝 (p, (0 : V)), Φ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N)
    (haway : ∀ t ∈ K, t ≠ p → Φ (t, 0) ∉ S) :
    ∃ W : Set (ℝ × V),
      IsOpen W ∧ K ×ˢ {(0 : V)} ⊆ W ∧ W ⊆ Φ.source ∧ ∀ z ∈ W, Φ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N := by
  obtain ⟨U, hUgood, hU, hpU⟩ := _root_.mem_nhds_iff.mp hlocal
  let A : Set (ℝ × V) := (Φ.source ∩ Φ ⁻¹' Sᶜ) ∩ {z | z.1 ≠ p}
  have hA : IsOpen A :=
    (Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hS.isOpen_compl).inter
      (isOpen_ne_fun continuous_fst continuous_const)
  let W := Φ.source ∩ (U ∪ A)
  refine ⟨W, Φ.open_source.inter (hU.union hA), ?_, Set.inter_subset_left, ?_⟩
  · rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hKsource ⟨ht, rfl⟩, ?_⟩
    by_cases htp : t = p
    · subst t
      exact Or.inl hpU
    · exact Or.inr ⟨⟨hKsource ⟨ht, rfl⟩, haway t ht htp⟩, htp⟩
  · intro z hz
    rcases hz.2 with hzU | hzA
    · exact hUgood hzU
    · constructor
      · intro h
        exact (hzA.1.2 h).elim
      · rintro ⟨h, -⟩
        exact (hzA.2 h).elim

theorem MorseCancel.exists_clean_axis_tube_restriction {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) {K : Set ℝ} (hK : IsCompact K)
    (hKsource : K ×ˢ {(0 : V)} ⊆ Φ.source) {S T : Set M} (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℝ) (N P : Set V) (hlocalS : ∀ᶠ z in 𝓝 (p, (0 : V)), Φ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N)
    (hlocalT : ∀ᶠ z in 𝓝 (q, (0 : V)), Φ z ∈ T ↔ z.1 = q ∧ z.2 ∈ P)
    (hawayS : ∀ t ∈ K, t ≠ p → Φ (t, 0) ∉ S) (hawayT : ∀ t ∈ K, t ≠ q → Φ (t, 0) ∉ T) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞,
          K ×ˢ Metric.closedBall (0 : V) ε ⊆ Ψ.source ∧
            (∀ z, Ψ z = Φ z) ∧
              Ψ.target ⊆ Φ.target ∧
                (∀ z ∈ Ψ.source, Ψ z ∈ S ↔ z.1 = p ∧ z.2 ∈ N) ∧
                  (∀ z ∈ Ψ.source, Ψ z ∈ T ↔ z.1 = q ∧ z.2 ∈ P) := by
  obtain ⟨U, hU, hKU, -, hSU⟩ :=
    exists_open_tube_sheet_recognition Φ hKsource hS p N hlocalS hawayS
  obtain ⟨W, hW, hKW, -, hTW⟩ :=
    exists_open_tube_sheet_recognition Φ hKsource hT q P hlocalT hawayT
  let Ψ := Smale.PartialChart.restrictSource Φ (hU.inter hW)
  have hzero : K ×ˢ {(0 : V)} ⊆ Ψ.source := fun z hz => ⟨hKsource hz, hKU hz, hKW hz⟩
  obtain ⟨ε, hε, hprod⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hzero
  exact
    ⟨ε, hε, Ψ, hprod, fun _ => rfl, fun _ hz => hz.1, fun z hz => hSU z hz.2.1, fun z hz =>
      hTW z hz.2.2⟩

theorem MorseCancel.exists_tube_support_box {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞)
    (haxis : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : V)} ⊆ Φ.source) :
    ∃ l u r : ℝ, l < 0 ∧ 1 < u ∧ 0 < r ∧ Set.Icc l u ×ˢ Metric.closedBall (0 : V) r ⊆ Φ.source := by
  let U : Set ℝ := (fun t : ℝ => (t, (0 : V))) ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage (continuous_id.prodMk continuous_const)
  have h0U : (0 : ℝ) ∈ U := haxis ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have h1U : (1 : ℝ) ∈ U := haxis ⟨⟨zero_le_one, le_rfl⟩, rfl⟩
  obtain ⟨a, ha, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h0U)
  obtain ⟨b, hb, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h1U)
  have hwide : Set.Icc (-a) (1 + b) ⊆ U := by
    intro t ht
    by_cases ht0 : t < 0
    · apply hball0
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_neg ht0]
      linarith [ht.1]
    · by_cases ht1 : 1 < t
      · apply hball1
        rw [Metric.mem_closedBall, Real.dist_eq, abs_of_pos (sub_pos.mpr ht1)]
        linarith [ht.2]
      · exact haxis ⟨⟨le_of_not_gt ht0, le_of_not_gt ht1⟩, rfl⟩
  have hwideAxis : Set.Icc (-a) (1 + b) ×ˢ {(0 : V)} ⊆ Φ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hwide ht
  obtain ⟨r, hr, hprod⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc
      Φ.open_source hwideAxis
  exact ⟨-a, 1 + b, r, by linarith, by linarith, hr, hprod⟩

def Degree.RegularHeightCoordinates.heightMap {V : Type*} (F : ℝ × V → ℝ) (p : ℝ × V) : ℝ × V :=
  (F p, p.2)

theorem Degree.RegularHeightCoordinates.linear_decomposition {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℝ × V →L[ℝ] ℝ) (s : ℝ) (z : V) : L (s, z) = s * L (1, 0) + L (0, z) := by
  have he : (s, z) = s • (1, (0 : V)) + (0, z) := by simp
  rw [he, map_add, map_smul]
  rfl

theorem Degree.RegularHeightCoordinates.triangular_bijective {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℝ × V →L[ℝ] ℝ) (hL : L (1, 0) ≠ 0) :
    Function.Bijective (L.prod (ContinuousLinearMap.snd ℝ ℝ V)) := by
  constructor
  · rintro ⟨s, z⟩ ⟨t, w⟩ h
    have hzw : z = w := congrArg Prod.snd h
    subst w
    have he : L (s, z) = L (t, z) := congrArg Prod.fst h
    rw [linear_decomposition L s z, linear_decomposition L t z] at he
    have hst : s = t := (mul_right_cancel₀ hL) (by linarith)
    exact Prod.ext hst rfl
  · rintro ⟨s, z⟩
    refine ⟨((s - L (0, z)) / L (1, 0), z), ?_⟩
    apply Prod.ext
    · change L ((s - L (0, z)) / L (1, 0), z) = s
      rw [linear_decomposition L, div_mul_cancel₀ _ hL]
      ring
    · rfl

def Degree.RegularHeightCoordinates.triangularEquiv {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : ℝ × V →L[ℝ] ℝ) (hL : L (1, 0) ≠ 0) :
    (ℝ × V) ≃L[ℝ] (ℝ × V) :=
  (LinearEquiv.ofBijective (L.prod (ContinuousLinearMap.snd ℝ ℝ V)).toLinearMap
      (triangular_bijective L hL)).toContinuousLinearEquiv

theorem Degree.RegularHeightCoordinates.contDiff_heightMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (heightMap F) :=
  hF.prodMk contDiff_snd

theorem Degree.RegularHeightCoordinates.fderiv_heightMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) (p : ℝ × V) :
    fderiv ℝ (heightMap F) p = (fderiv ℝ F p).prod (ContinuousLinearMap.snd ℝ ℝ V) :=
  (((hF.differentiable (by simp) p).hasFDerivAt).prodMk
      (ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt).fderiv

theorem Degree.RegularHeightCoordinates.heightMap_localDiffeomorph {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {F : ℝ × V → ℝ}
    (hF : ContDiff ℝ ∞ F) {p : ℝ × V} (hreg : fderiv ℝ F p (1, 0) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ (heightMap F) p := by
  have hinv : (fderiv ℝ (heightMap F) p).IsInvertible := by
    refine ⟨triangularEquiv (fderiv ℝ F p) hreg, ?_⟩
    rw [fderiv_heightMap hF]
    rfl
  obtain ⟨Φ, hp, _, hΦ⟩ :=
    NoExotic.exists_partialDiffeomorph_of_contDiffOn isOpen_univ (Set.mem_univ p)
      (contDiff_heightMap hF).contDiffOn hinv
  exact ⟨Φ, hp, fun _ _ => congrFun hΦ.symm _⟩

def Degree.RegularHeightCoordinates.displacedHeight {V : Type*} (u : ℝ × V → ℝ) (p : ℝ × V) : ℝ :=
  p.1 + u p

theorem Degree.RegularHeightCoordinates.contDiff_displacedHeight {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (displacedHeight u) :=
  contDiff_fst.add hu

theorem Degree.RegularHeightCoordinates.scalar_derivative {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) (s : ℝ) (z : V) :
    HasDerivAt (fun t : ℝ => F (t, z)) (fderiv ℝ F (s, z) (1, 0)) s :=
  ((hF.differentiable (by simp) (s, z)).hasFDerivAt).comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))

theorem Degree.RegularHeightCoordinates.heightMap_injective_of_positive {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hpos : ∀ p, 0 < fderiv ℝ F p (1, 0)) : Function.Injective (heightMap F) := by
  have hmono (z : V) : StrictMono (fun s : ℝ => F (s, z)) :=
    strictMono_of_deriv_pos (fun s => by rw [(scalar_derivative hF s z).deriv]; exact hpos _)
  rintro ⟨s, z⟩ ⟨t, w⟩ he
  have hzw : z = w := congrArg Prod.snd he
  subst w
  have hst : s = t := (hmono z).injective (congrArg Prod.fst he)
  exact Prod.ext hst rfl

theorem Degree.RegularHeightCoordinates.heightMap_surjective_of_bounded {V : Type*}
    [NormedAddCommGroup V] {u : ℝ × V → ℝ} (hu : Continuous u) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p, |u p| ≤ C) : Function.Surjective (heightMap (displacedHeight u)) := by
  rintro ⟨r, z⟩
  let a := r - (C + 1)
  let b := r + (C + 1)
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hs : Continuous (fun s : ℝ => displacedHeight u (s, z)) :=
    continuous_id.add (hu.comp (continuous_id.prodMk continuous_const))
  have hlo : displacedHeight u (a, z) ≤ r := by
    have h := (abs_le.mp (hbound (a, z))).2
    dsimp [displacedHeight, a] at *
    linarith
  have hhi : r ≤ displacedHeight u (b, z) := by
    have h := (abs_le.mp (hbound (b, z))).1
    dsimp [displacedHeight, b] at *
    linarith
  obtain ⟨s, _, he⟩ := intermediate_value_Icc hab hs.continuousOn ⟨hlo, hhi⟩
  exact ⟨(s, z), Prod.ext he rfl⟩

theorem Degree.RegularHeightCoordinates.heightMap_surjective_of_compactSupport {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : Function.Surjective (heightMap (displacedHeight u)) := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hu.continuous).isBounded.exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg (u 0)).trans (hC _ ⟨0, rfl⟩)
  exact
    heightMap_surjective_of_bounded hu.continuous C hC0
      (fun p => by simpa only [Real.norm_eq_abs] using hC _ ⟨p, rfl⟩)

def Degree.RegularHeightCoordinates.longitudinalDiffeomorph {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hpos : ∀ p, 0 < fderiv ℝ (displacedHeight u) p (1, 0)) :
    (ℝ × V) ≃ₘ⟮𝓘(ℝ, ℝ × V), 𝓘(ℝ, ℝ × V)⟯ (ℝ × V) := by
  have hs := contDiff_displacedHeight hu
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ (heightMap (displacedHeight u)) :=
    fun p => heightMap_localDiffeomorph hs (hpos p).ne'
  exact
    hloc.diffeomorphOfBijective
      ⟨heightMap_injective_of_positive hs hpos, heightMap_surjective_of_compactSupport hu hc⟩

def Degree.MorseRearrangement.IntervalTranslation (a b x y : ℝ) : Prop :=
  ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
    (∀ z, z ∉ Set.Ioo a b → D z = z) ∧ D =ᶠ[𝓝 x] fun z => z + (y - x)

theorem Degree.MorseRearrangement.translation_germ_apply (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    {x y : ℝ} (hD : D =ᶠ[𝓝 x] fun z => z + (y - x)) : D x = y := by
  have h := hD.self_of_nhds
  linarith

theorem Degree.MorseRearrangement.intervalTranslation_refl (a b x : ℝ) :
    IntervalTranslation a b x x := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞, fun _ _ => rfl, Filter.Eventually.of_forall ?_⟩
  intro z
  change z = z + (x - x)
  ring

theorem Degree.MorseRearrangement.intervalTranslation_symm {a b x y : ℝ}
    (h : IntervalTranslation a b x y) : IntervalTranslation a b y x := by
  obtain ⟨D, hfix, hgerm⟩ := h
  have hxy := translation_germ_apply D hgerm
  have hback : D.symm y = x := by rw [← hxy, D.symm_apply_apply]
  have ht : Filter.Tendsto D.symm (𝓝 y) (𝓝 x) := hback ▸ D.symm.continuous.continuousAt.tendsto
  refine ⟨D.symm, ?_, ?_⟩
  · intro z hz
    have hh := D.symm_apply_apply z
    rwa [hfix z hz] at hh
  · filter_upwards [hgerm.comp_tendsto ht] with z hz
    change D (D.symm z) = D.symm z + (y - x) at hz
    rw [D.apply_symm_apply] at hz
    linarith

theorem Degree.MorseRearrangement.intervalTranslation_trans {a b x y z : ℝ}
    (hxy : IntervalTranslation a b x y) (hyz : IntervalTranslation a b y z) :
    IntervalTranslation a b x z := by
  obtain ⟨D, hDfix, hD⟩ := hxy
  obtain ⟨G, hGfix, hG⟩ := hyz
  have hxy := translation_germ_apply D hD
  have ht : Filter.Tendsto D (𝓝 x) (𝓝 y) := hxy ▸ D.continuous.continuousAt.tendsto
  refine ⟨D.trans G, ?_, ?_⟩
  · intro w hw
    change G (D w) = w
    rw [hDfix w hw, hGfix w hw]
  · filter_upwards [hD, hG.comp_tendsto ht] with w hwD hwG
    change G (D w) = w + (z - x)
    change G (D w) = D w + (z - y) at hwG
    rw [hwG, hwD]
    ring

theorem Degree.MorseRearrangement.exists_local_interval_translation {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b) : ∃ ε, 0 < ε ∧ ∀ y, Dist.dist y x < ε → IntervalTranslation a b x y := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_Ioo.mem_nhds hx)
  let β : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hsupp : tsupport (fun z : ℝ => β z) ⊆ Set.Ioo a b := by
    rw [β.tsupport_eq]
    intro z hz
    apply hsub
    have hh : Dist.dist z x ≤ r / 2 := hz
    change Dist.dist z x < r
    linarith
  have hcompact : HasCompactSupport (fun z : ℝ => β z) := by
    change IsCompact (tsupport (fun z : ℝ => β z))
    rw [β.tsupport_eq]
    exact ProperSpace.isCompact_closedBall _ _
  obtain ⟨ε, hε, hmove⟩ :=
    Smale.SmallPerturbation.exists_radius_bumpTranslation β.contDiff hcompact
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hnorm : ‖y - x‖ < ε := by simpa only [dist_eq_norm] using hy
  obtain ⟨D, hD, hfix⟩ := hmove (y - x) hnorm
  refine ⟨D, fun z hz => hfix z (fun h => hz (hsupp h)), ?_⟩
  filter_upwards [Metric.ball_mem_nhds x β.rIn_pos] with z hz
  rw [hD, β.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_smul]

theorem Degree.MorseRearrangement.exists_supported_interval_translation {a b x y : ℝ}
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) : IntervalTranslation a b x y := by
  let U := Set.Ioo a b
  let P : U → Prop := fun z => IntervalTranslation a b x z
  have hlocal : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro z
    obtain ⟨ε, hε, hmove⟩ := exists_local_interval_translation z.property
    filter_upwards [Metric.ball_mem_nhds z hε] with w hw
    have hzw : IntervalTranslation a b z w := hmove w hw
    apply propext
    exact
      ⟨fun hw => intervalTranslation_trans hw (intervalTranslation_symm hzw), fun hz =>
        intervalTranslation_trans hz hzw⟩
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have heq : P ⟨x, hx⟩ = P ⟨y, hy⟩ := hlocal.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩
  have hstart : P ⟨x, hx⟩ := intervalTranslation_refl a b x
  have hfinish : P ⟨y, hy⟩ := heq ▸ hstart
  exact hfinish

theorem Degree.MorseRearrangement.strictMono_of_fixed_exterior
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) {a b : ℝ} (hfix : ∀ z, z ∉ Set.Ioo a b → D z = z) :
    StrictMono D := by
  rcases D.continuous.strictMono_of_inj D.injective with hm | ha
  · exact hm
  · have hanti := ha (show b < b + 1 by linarith)
    rw [hfix b (fun h => (lt_irrefl b) h.2), hfix (b + 1) (fun h => by linarith [h.2])] at hanti
    linarith

theorem Degree.MorseRearrangement.deriv_pos_of_strictMono_diffeomorph
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) (hm : StrictMono D) (x : ℝ) : 0 < deriv D x := by
  have hd := (D.mdifferentiable (by simp) x).differentiableAt.hasDerivAt
  have hi := (D.symm.mdifferentiable (by simp) (D x)).differentiableAt.hasDerivAt
  have hc := hi.comp x hd
  have heq : D.symm ∘ D = id := funext D.symm_apply_apply
  rw [heq] at hc
  have hh := hc.unique (hasDerivAt_id x)
  have hn : deriv D x ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.mul_zero] at hh
    norm_num at hh
  exact lt_of_le_of_ne hm.monotone.deriv_nonneg (Ne.symm hn)

theorem Degree.MorseRearrangement.exists_increasing_interval_translation {a b x y : ℝ}
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (∀ z, z ∉ Set.Ioo a b → D z = z) ∧
        (D =ᶠ[𝓝 x] fun z => z + (y - x)) ∧ D x = y ∧ StrictMono D ∧ ∀ z, 0 < deriv D z := by
  obtain ⟨D, hfix, hgerm⟩ := exists_supported_interval_translation hx hy
  have hm := strictMono_of_fixed_exterior D hfix
  exact
    ⟨D, hfix, hgerm, translation_germ_apply D hgerm, hm, deriv_pos_of_strictMono_diffeomorph D hm⟩

theorem Degree.MorseRearrangement.exists_increasing_interval_translation_with_exterior_germs
    {a b x y : ℝ} (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (∀ z, z ∉ Set.Ioo a b → D z = z) ∧
        (D =ᶠ[𝓝 x] fun z => z + (y - x)) ∧
          D x = y ∧ StrictMono D ∧ (∀ z, 0 < deriv D z) ∧ ∀ z, z ∉ Set.Ioo a b → D =ᶠ[𝓝 z] id := by
  obtain ⟨a', haa', ha'⟩ := exists_between (lt_min hx.1 hy.1)
  obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt hx.2 hy.2)
  have hx' : x ∈ Set.Ioo a' b' := ⟨ha'.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hb'⟩
  have hy' : y ∈ Set.Ioo a' b' :=
    ⟨ha'.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hb'⟩
  obtain ⟨D, hfix, hgerm, hpoint, hmono, hderiv⟩ := exists_increasing_interval_translation hx' hy'
  have hsub : Set.Icc a' b' ⊆ Set.Ioo a b := fun z hz => ⟨haa'.trans_le hz.1, hz.2.trans_lt hb'b⟩
  have hout (z : ℝ) (hz : z ∉ Set.Ioo a b) : D =ᶠ[𝓝 z] id := by
    have hz' : z ∈ (Set.Icc a' b')ᶜ := fun h => hz (hsub h)
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hz'] with w hw
    exact hfix w (fun h => hw ⟨h.1.le, h.2.le⟩)
  exact ⟨D, fun z hz => (hout z hz).self_of_nhds, hgerm, hpoint, hmono, hderiv, hout⟩

def Degree.MorseRearrangement.blendHeight (θ : ℝ) (P Q : ℝ → ℝ) (s : ℝ) : ℝ :=
  θ * P s + (1 - θ) * Q s

theorem Degree.MorseRearrangement.blendHeight_zero (P Q : ℝ → ℝ) (s : ℝ) :
    blendHeight 0 P Q s = Q s := by simp [blendHeight]

theorem Degree.MorseRearrangement.blendHeight_one (P Q : ℝ → ℝ) (s : ℝ) :
    blendHeight 1 P Q s = P s := by simp [blendHeight]

theorem Degree.MorseRearrangement.blendHeight_fixed {P Q : ℝ → ℝ} {s : ℝ} (hP : P s = s)
    (hQ : Q s = s) (θ : ℝ) : blendHeight θ P Q s = s := by
  rw [blendHeight, hP, hQ]
  ring

theorem Degree.MorseRearrangement.positive_blended_slope {θ a b : ℝ} (hθ : θ ∈ Set.Icc 0 1)
    (ha : 0 < a) (hb : 0 < b) : 0 < θ * a + (1 - θ) * b := by
  by_cases hzero : θ = 0
  · simpa only [hzero, MulZeroClass.zero_mul, sub_zero, one_mul, zero_add] using hb
  · exact
      add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hθ.1 (Ne.symm hzero)) ha)
        (mul_nonneg (sub_nonneg.mpr hθ.2) hb.le)

theorem Degree.MorseRearrangement.hasDerivAt_blended_height {f θ P Q : ℝ → ℝ} {t f' p' q' : ℝ}
    (hf : HasDerivAt f f' t) (hθ : HasDerivAt θ 0 t) (hP : HasDerivAt P p' (f t))
    (hQ : HasDerivAt Q q' (f t)) :
    HasDerivAt (fun s => blendHeight (θ s) P Q (f s)) ((θ t * p' + (1 - θ t) * q') * f') t := by
  convert!
    (hθ.mul (hP.comp t hf)).add (((hasDerivAt_const t (1 : ℝ)).sub hθ).mul (hQ.comp t hf)) using 1
  simp only [Pi.sub_apply]
  ring

def MorseCancel.longitudinalBlendDisplacement {V : Type*} (D : ℝ → ℝ) (β : V → ℝ) (η : ℝ → ℝ)
    (t : ℝ) (p : ℝ × V) : ℝ :=
  η t * β p.2 * (D p.1 - p.1)

def MorseCancel.longitudinalBlend {V : Type*} (D : ℝ → ℝ) (β : V → ℝ) (η : ℝ → ℝ)
    (p : ℝ × (ℝ × V)) : ℝ × V :=
  (p.2.1 + longitudinalBlendDisplacement D β η p.1 p.2, p.2.2)

theorem MorseCancel.longitudinalBlendDisplacement_smooth {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (t : ℝ) : ContDiff ℝ ∞ (longitudinalBlendDisplacement D β η t) :=
  (contDiff_const.mul (hβ.comp contDiff_snd)).mul ((hD.comp contDiff_fst).sub contDiff_fst)

theorem MorseCancel.longitudinalBlend_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hβ : ContDiff ℝ ∞ β)
    (hη : ContDiff ℝ ∞ η) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, ℝ × V) ∞ (longitudinalBlend D β η) := by
  have hs : ContMDiff 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ) ∞ Prod.fst := contDiff_fst.contMDiff
  have hz : ContMDiff 𝓘(ℝ, ℝ × V) 𝓘(ℝ, V) ∞ Prod.snd := contDiff_snd.contMDiff
  have hs' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × (ℝ × V) => p.2.1) :=
    hs.comp contMDiff_snd
  have hz' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, V) ∞ (fun p : ℝ × (ℝ × V) => p.2.2) :=
    hz.comp contMDiff_snd
  exact
    (hs'.add
          (((hη.contMDiff.comp contMDiff_fst).mul (hβ.contMDiff.comp hz')).mul
            ((hD.contMDiff.comp hs').sub hs'))).prodMk_space
      hz'

theorem MorseCancel.longitudinalBlend_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hη : η 0 = 0) (p : ℝ × V) :
    longitudinalBlend D β η (0, p) = p := by
  simp only [longitudinalBlend, longitudinalBlendDisplacement, hη, MulZeroClass.zero_mul,
    add_zero]

theorem MorseCancel.longitudinalBlendDisplacement_zero_outside {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) {l u : ℝ}
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (t : ℝ) (p : ℝ × V) (hp : p ∉ Set.Icc l u ×ˢ tsupport β) :
    longitudinalBlendDisplacement D β η t p = 0 := by
  by_cases hs : p.1 ∈ Set.Icc l u
  · have hb : β p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp ⟨hs, h⟩)
    simp only [longitudinalBlendDisplacement, hb, MulZeroClass.mul_zero, MulZeroClass.zero_mul]
  · have hd := hfix p.1 (fun h => hs ⟨h.1.le, h.2.le⟩)
    simp only [longitudinalBlendDisplacement, hd, sub_self, MulZeroClass.mul_zero]

theorem MorseCancel.longitudinalBlend_fixed_outside {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) {l u : ℝ}
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (t : ℝ) (p : ℝ × V) (hp : p ∉ Set.Icc l u ×ˢ tsupport β) :
    longitudinalBlend D β η (t, p) = p := by
  rw [longitudinalBlend, longitudinalBlendDisplacement_zero_outside η hfix t p hp, add_zero]

theorem MorseCancel.longitudinalBlend_derivative_positive {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (hDpos : ∀ s, 0 < deriv D s) (hβrange : ∀ z, β z ∈ Set.Icc (0 : ℝ) 1)
    (hηrange : ∀ t, η t ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) (p : ℝ × V) :
    0 <
      fderiv ℝ
        (Degree.RegularHeightCoordinates.displacedHeight (longitudinalBlendDisplacement D β η t))
        p (1, 0) := by
  have hu := longitudinalBlendDisplacement_smooth η hD hβ t
  have hscalar :=
    Degree.RegularHeightCoordinates.scalar_derivative
      (Degree.RegularHeightCoordinates.contDiff_displacedHeight hu) p.1 p.2
  have hd :=
    (hasDerivAt_id p.1).add
      (((hD.differentiable (by simp) p.1).hasDerivAt.sub (hasDerivAt_id p.1)).const_mul
        (η t * β p.2))
  have hrate :
    fderiv ℝ
        (Degree.RegularHeightCoordinates.displacedHeight (longitudinalBlendDisplacement D β η t))
        p (1, 0) =
      1 + (η t * β p.2) * (deriv D p.1 - 1) :=
    hscalar.deriv.symm.trans hd.deriv
  rw [hrate]
  have hweight : η t * β p.2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hηrange t).1 (hβrange p.2).1,
      mul_le_one₀ (hηrange t).2 (hβrange p.2).1 (hβrange p.2).2⟩
  have hpos := Degree.MorseRearrangement.positive_blended_slope hweight (hDpos p.1) zero_lt_one
  nlinarith

theorem MorseCancel.longitudinalBlend_slices {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} {l u : ℝ} (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β) (hDpos : ∀ s, 0 < deriv D s)
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (hβrange : ∀ z, β z ∈ Set.Icc (0 : ℝ) 1)
    (hηrange : ∀ t, η t ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    ∃ d : Diffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) (ℝ × V) (ℝ × V) ∞,
      ∀ p, d p = longitudinalBlend D β η (t, p) := by
  have hu := longitudinalBlendDisplacement_smooth η hD hβ t
  have hcompact : HasCompactSupport (longitudinalBlendDisplacement D β η t) :=
    HasCompactSupport.intro (CompactIccSpace.isCompact_Icc.prod hc.isCompact)
      (longitudinalBlendDisplacement_zero_outside η hfix t)
  exact
    ⟨Degree.RegularHeightCoordinates.longitudinalDiffeomorph hu hcompact
        (longitudinalBlend_derivative_positive hD hβ hDpos hβrange hηrange t),
      fun _ => rfl⟩

theorem MorseCancel.expNegInvGlue_hasDerivAt (t : ℝ) :
    HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t

theorem MorseCancel.smoothTransition_deriv_pos {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < deriv Real.smoothTransition t := by
  let a := expNegInvGlue t
  let b := expNegInvGlue (1 - t)
  let a' := t⁻¹ ^ 2 * a
  let b' := (1 - t)⁻¹ ^ 2 * b
  have ha : 0 < a := expNegInvGlue.pos_of_pos ht.1
  have hb : 0 < b := expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2)
  have ha' : 0 < a' := mul_pos (sq_pos_of_ne_zero (inv_ne_zero ht.1.ne')) ha
  have hb' : 0 < b' := mul_pos (sq_pos_of_ne_zero (inv_ne_zero (sub_pos.mpr ht.2).ne')) hb
  have hA : HasDerivAt expNegInvGlue a' t := expNegInvGlue_hasDerivAt t
  have hB : HasDerivAt (fun s : ℝ => expNegInvGlue (1 - s)) (-b') t := by
    convert!
      (expNegInvGlue_hasDerivAt (1 - t)).comp t
        ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) using
      1
    dsimp only [b', b]
    ring
  have hd := hA.div (hA.add hB) (Real.smoothTransition.pos_denom t).ne'
  change HasDerivAt Real.smoothTransition ((a' * (a + b) - a * (a' + -b')) / (a + b) ^ 2) t at hd
  rw [hd.deriv]
  apply div_pos
  · have he : a' * (a + b) - a * (a' + -b') = a' * b + a * b' := by ring
    rw [he]
    exact add_pos (mul_pos ha' hb) (mul_pos ha hb')
  · exact sq_pos_of_pos (add_pos ha hb)

theorem MorseCancel.smoothTransition_strictMonoOn :
    StrictMonoOn Real.smoothTransition (Set.Icc (0 : ℝ) 1) := by
  apply
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) Real.smoothTransition.continuous.continuousOn
  intro t ht
  apply smoothTransition_deriv_pos
  simpa only [interior_Icc] using ht

theorem MorseCancel.exists_unique_smoothTransition_time {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ τ : ℝ,
      τ ∈ Set.Ioo (0 : ℝ) 1 ∧
        Real.smoothTransition τ = c ∧
          0 < deriv Real.smoothTransition τ ∧
            ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.smoothTransition t = c ↔ t = τ := by
  have hc' : c ∈ Set.Icc (Real.smoothTransition 0) (Real.smoothTransition 1) := by
    rw [Real.smoothTransition.zero, Real.smoothTransition.one]
    exact ⟨hc.1.le, hc.2.le⟩
  obtain ⟨τ, hτ, heq⟩ :=
    intermediate_value_Icc zero_le_one Real.smoothTransition.continuous.continuousOn hc'
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, Real.smoothTransition.zero] at heq
    linarith [hc.1]
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, Real.smoothTransition.one] at heq
    linarith [hc.2]
  have hτI : τ ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hτ.1 (Ne.symm hτ0), lt_of_le_of_ne hτ.2 hτ1⟩
  refine ⟨τ, hτI, heq, smoothTransition_deriv_pos hτI, ?_⟩
  intro t ht
  exact ⟨fun h => smoothTransition_strictMonoOn.injOn ht hτ (h.trans heq.symm), fun h => h ▸ heq⟩

structure MorseCancel.LongitudinalTubeMotion {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) where
  profile : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞
  cutoff : V → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_germ : cutoff =ᶠ[𝓝 (0 : V)] fun _ => 1
  cutoff_zero : cutoff 0 = 1
  destination : ℝ
  destination_gt_one : 1 < destination
  profile_zero : profile 0 = destination
  profile_germ : (profile : ℝ → ℝ) =ᶠ[𝓝 (0 : ℝ)] fun s => s + destination
  time : ℝ
  time_mem : time ∈ Set.Ioo (0 : ℝ) 1
  time_value : Real.smoothTransition time * destination = 1
  time_rate : 0 < deriv Real.smoothTransition time * destination
  unique_time : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.smoothTransition t * destination = 1 ↔ t = time
  family : ℝ × M → M
  support : Set M
  compact_support : IsCompact support
  support_subset : support ⊆ Φ.target
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ family
  zero : ∀ y, family (0, y) = y
  slices : ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, d y = family (t, y)
  fixedOutside : ∀ t y, y ∉ support → family (t, y) = y
  model_source :
    ∀ t z, z ∈ Φ.source → longitudinalBlend profile cutoff Real.smoothTransition (t, z) ∈ Φ.source
  formula :
    ∀ t z,
      z ∈ Φ.source →
        family (t, Φ z) = Φ (longitudinalBlend profile cutoff Real.smoothTransition (t, z))

theorem MorseCancel.nonempty_longitudinalTubeMotion {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ V]
    [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞)
    (haxis : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : V)} ⊆ Φ.source) : Nonempty (LongitudinalTubeMotion Φ) := by
  obtain ⟨l, u, r, hl, hu, hr, hbox⟩ := exists_tube_support_box Φ haxis
  let c : ℝ := (1 + u) / 2
  have hc : 1 < c := by dsimp only [c]; linarith
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hcu : c < u := by dsimp only [c]; linarith
  have h0I : (0 : ℝ) ∈ Set.Ioo l u := ⟨hl, zero_lt_one.trans hu⟩
  have hcI : c ∈ Set.Ioo l u := ⟨hl.trans hcpos, hcu⟩
  obtain ⟨D, hDfix, hDgerm, hD0, -, hDpos⟩ :=
    Degree.MorseRearrangement.exists_increasing_interval_translation h0I hcI
  let β : ContDiffBump (0 : V) :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  have hβgerm : (β : V → ℝ) =ᶠ[𝓝 (0 : V)] fun _ => 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : V) β.rIn_pos] with z hz
    exact β.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  have hβrange : ∀ z : V, β z ∈ Set.Icc (0 : ℝ) 1 := fun _ => ⟨β.nonneg, β.le_one⟩
  have hηrange : ∀ t : ℝ, Real.smoothTransition t ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hmodel :=
    longitudinalBlend_smooth D.contMDiff.contDiff β.contDiff
      (Real.smoothTransition.contDiff (n := ⊤))
  have hsource : Set.Icc l u ×ˢ tsupport (β : V → ℝ) ⊆ Φ.source := by
    rw [β.tsupport_eq]
    exact hbox
  obtain ⟨F, K, hK, hKΦ, hF, hF0, hFd, hFfix, hsrc, hformula⟩ :=
    Smale.SupportedDiffeomorph.exists_supported_isotopy_extension Φ hmodel
      (longitudinalBlend_zero Real.smoothTransition.zero)
      (longitudinalBlend_slices D.contMDiff.contDiff β.contDiff β.hasCompactSupport hDpos hDfix
        hβrange hηrange)
      (CompactIccSpace.isCompact_Icc.prod β.hasCompactSupport.isCompact) hsource
      (longitudinalBlend_fixed_outside Real.smoothTransition hDfix)
  have hcInv : 1 / c ∈ Set.Ioo (0 : ℝ) 1 := ⟨one_div_pos.mpr hcpos, (div_lt_one hcpos).mpr hc⟩
  obtain ⟨τ, hτ, hτvalue, hτrate, hτunique⟩ := exists_unique_smoothTransition_time hcInv
  refine
    ⟨{  profile := D
        cutoff := β
        cutoff_smooth := β.contDiff
        cutoff_germ := hβgerm
        cutoff_zero := hβgerm.self_of_nhds
        destination := c
        destination_gt_one := hc
        profile_zero := hD0
        profile_germ := by simpa only [sub_zero] using hDgerm
        time := τ
        time_mem := hτ
        time_value := (eq_div_iff hcpos.ne').mp hτvalue
        time_rate := mul_pos hτrate hcpos
        unique_time := ?_
        family := F
        support := K
        compact_support := hK
        support_subset := hKΦ
        smooth := hF
        zero := hF0
        slices := hFd
        fixedOutside := hFfix
        model_source := hsrc
        formula := hformula }⟩
  intro t ht
  rw [← eq_div_iff hcpos.ne']
  exact hτunique t ht

theorem MorseCancel.LongitudinalTubeMotion.model_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (t : ℝ) :
    MorseCancel.longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, (0, 0)) =
      (Real.smoothTransition t * A.destination, 0) := by
  simp only [MorseCancel.longitudinalBlend, MorseCancel.longitudinalBlendDisplacement,
    A.cutoff_zero, A.profile_zero, mul_one, sub_zero, zero_add]

theorem MorseCancel.LongitudinalTubeMotion.model_germ {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (t : ℝ) :
    MorseCancel.longitudinalBlend A.profile A.cutoff Real.smoothTransition =ᶠ[𝓝 (t, (0, 0))]
      fun p : ℝ × (ℝ × V) => (p.2.1 + Real.smoothTransition p.1 * A.destination, p.2.2) := by
  have hs : Filter.Tendsto (fun p : ℝ × (ℝ × V) => p.2.1) (𝓝 (t, (0, 0))) (𝓝 0) :=
    continuous_fst.continuousAt.comp continuous_snd.continuousAt
  have hz : Filter.Tendsto (fun p : ℝ × (ℝ × V) => p.2.2) (𝓝 (t, (0, 0))) (𝓝 0) :=
    continuous_snd.continuousAt.comp continuous_snd.continuousAt
  filter_upwards [hs.eventually A.profile_germ, hz.eventually A.cutoff_germ] with p hp hβ
  simp only [MorseCancel.longitudinalBlend, MorseCancel.longitudinalBlendDisplacement, hp, hβ,
    mul_one, add_sub_cancel_left]

theorem MorseCancel.LongitudinalTubeMotion.native_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) (t : ℝ) :
    A.family (t, Φ 0) = Φ (Real.smoothTransition t * A.destination, 0) := by
  rw [A.formula t 0 h0]
  exact congrArg Φ (A.model_axis t)

theorem MorseCancel.LongitudinalTubeMotion.native_germ {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) (t : ℝ) :
    (fun p : ℝ × (ℝ × V) => A.family (p.1, Φ p.2)) =ᶠ[𝓝 (t, 0)] fun p =>
      Φ (p.2.1 + Real.smoothTransition p.1 * A.destination, p.2.2) := by
  have hs : ∀ᶠ p : ℝ × (ℝ × V) in 𝓝 (t, 0), p.2 ∈ Φ.source :=
    continuous_snd.continuousAt.eventually (Φ.open_source.mem_nhds h0)
  filter_upwards [A.model_germ t, hs] with p hp hs
  rw [A.formula p.1 p.2 hs, hp]

theorem MorseCancel.LongitudinalTubeMotion.fixed_outside_target {V E H M : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (t : ℝ) (y : M) (hy : y ∉ Φ.target) : A.family (t, y) = y :=
  A.fixedOutside t y (fun h => hy (A.support_subset h))

theorem MorseCancel.LongitudinalTubeMotion.crossing_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancel.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) : A.family (A.time, Φ 0) = Φ (1, 0) := by
  rw [A.native_axis h0, A.time_value]

theorem MorseCancel.LongitudinalTubeMotion.whole_sheet_crossing_iff {U V E H M X Y : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) J (ℝ × (U × V)) M ∞}
    (A : MorseCancel.LongitudinalTubeMotion Φ) {f : X → M} {g : Y → M}
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hdisj : Disjoint (Set.range f) (Set.range g))
    (hrecf : ∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrecg : ∀ z ∈ Φ.source, Φ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) (x₀ : X) (y₀ : Y)
    (hx₀ : Φ 0 = f x₀) (hy₀ : Φ (1, 0) = g y₀) (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : X) (y : Y) :
    A.family (t, f x) = g y ↔ t = A.time ∧ x = x₀ ∧ y = y₀ := by
  constructor
  · intro he
    have htarget : f x ∈ Φ.target := by
      by_contra hn
      have hxy : f x = g y := (A.fixed_outside_target t (f x) hn).symm.trans he
      exact (Set.disjoint_left.mp hdisj) ⟨x, rfl⟩ ⟨y, hxy.symm⟩
    let z := Φ.symm (f x)
    have hz : z ∈ Φ.source := Φ.map_target htarget
    have hzfx : Φ z = f x := Φ.right_inv htarget
    have hfz := (hrecf z hz).mp ⟨x, hzfx.symm⟩
    let w := MorseCancel.longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, z)
    have hw : w ∈ Φ.source := A.model_source t z hz
    have hwgy : Φ w = g y := by
      calc
        Φ w = A.family (t, Φ z) := (A.formula t z hz).symm
        _ = A.family (t, f x) := (congrArg (fun p => A.family (t, p)) hzfx)
        _ = g y := he
    have hgw := (hrecg w hw).mp ⟨y, hwgy.symm⟩
    have hu : z.2.1 = 0 := hgw.2
    have hz0 : z = 0 := Prod.ext hfz.1 (Prod.ext hu hfz.2)
    have hwaxis : w = (Real.smoothTransition t * A.destination, 0) := by
      dsimp only [w]
      rw [hz0]
      exact A.model_axis t
    have htimevalue : Real.smoothTransition t * A.destination = 1 :=
      (congrArg Prod.fst hwaxis).symm.trans hgw.1
    have htτ : t = A.time := (A.unique_time t ht).mp htimevalue
    have hx : x = x₀ := hfi (hzfx.symm.trans ((congrArg Φ hz0).trans hx₀))
    have hwy : Φ w = g y₀ := by
      rw [hwaxis, htimevalue]
      exact hy₀
    exact ⟨htτ, hx, hgi (hwgy.symm.trans hwy)⟩
  · rintro ⟨ht, hx, hy⟩
    rw [ht, hx, hy]
    calc
      A.family (A.time, f x₀) = A.family (A.time, Φ 0) :=
        congrArg (fun p => A.family (A.time, p)) hx₀.symm
      _ = Φ (1, 0) := (A.crossing_axis h0)
      _ = g y₀ := hy₀

theorem MorseCancel.surjective_sheet_coordinate_mfderiv {U W H X : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (P : W →L[ℝ] U) (Q : U →L[ℝ] W) (b : W) {a : X → W} {x : X}
    (ha : MDifferentiableAt I 𝓘(ℝ, W) a x) (hi : Function.Injective (mfderiv I 𝓘(ℝ, W) a x))
    (hgerm : a =ᶠ[𝓝 x] fun y => Q (P (a y)) + b) :
    Function.Surjective (mfderiv I 𝓘(ℝ, U) (P ∘ a) x) := by
  have hP : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, U) P (a x) := P.differentiableAt.mdifferentiableAt
  have hα := hP.comp x ha
  have hQ : HasMFDerivAt 𝓘(ℝ, U) 𝓘(ℝ, W) (fun u => Q u + b) (P (a x)) Q :=
    (Q.hasFDerivAt.add_const b).hasMFDerivAt
  have heq : (mfderiv I 𝓘(ℝ, W) a x : U →L[ℝ] W) = Q.comp (mfderiv I 𝓘(ℝ, U) (P ∘ a) x) :=
    hgerm.mfderiv_eq.trans (hQ.comp x hα.hasMFDerivAt).mfderiv
  let D : U →L[ℝ] U := mfderiv I 𝓘(ℝ, U) (P ∘ a) x
  change Function.Surjective D
  apply (LinearMap.injective_iff_surjective (f := D.toLinearMap)).mp
  intro u v huv
  apply hi
  rw [heq]
  exact congrArg Q huv

theorem MorseCancel.native_coordinate_plane_trace_transverse {U H X : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X] {V H' Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] {α : X → U} {β : Y → V} {x : X} {y : Y} {η : ℝ → ℝ}
    {τ κ : ℝ} (hα : MDifferentiableAt I 𝓘(ℝ, U) α x) (hβ : MDifferentiableAt I' 𝓘(ℝ, V) β y)
    (hαs : Function.Surjective (mfderiv I 𝓘(ℝ, U) α x))
    (hβs : Function.Surjective (mfderiv I' 𝓘(ℝ, V) β y)) (hη : HasDerivAt η κ τ) (hκ : κ ≠ 0) :
    Smale.NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' 𝓘(ℝ, ℝ × (U × V))
      (fun p : ℝ × X => (η p.1, (α p.2, 0))) (fun q : Y => (1, (0, β q))) (τ, x) y := by
  let D : U →L[ℝ] U := mfderiv I 𝓘(ℝ, U) α x
  let E : V →L[ℝ] V := mfderiv I' 𝓘(ℝ, V) β y
  let C : (ℝ × U) →L[ℝ] ℝ :=
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).comp (ContinuousLinearMap.fst ℝ ℝ U)
  let L : (ℝ × U) →L[ℝ] ℝ × (U × V) := C.prod ((D.comp (ContinuousLinearMap.snd ℝ ℝ U)).prod 0)
  let R : V →L[ℝ] ℝ × (U × V) := (0 : V →L[ℝ] ℝ).prod ((0 : V →L[ℝ] U).prod E)
  have htime :=
    hη.hasFDerivAt.hasMFDerivAt.comp (τ, x) (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hcoord := hα.hasMFDerivAt.comp (τ, x) (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hzero : HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) (fun _ : ℝ × X => (0 : V)) (τ, x) 0 :=
    hasMFDerivAt_const _ _
  have hT :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × (U × V)) (fun p : ℝ × X => (η p.1, (α p.2, (0 : V))))
      (τ, x) L := by convert! htime.prodMk (hcoord.prodMk hzero) using 1
  have hone : HasMFDerivAt I' 𝓘(ℝ, ℝ) (fun _ : Y => (1 : ℝ)) y 0 := hasMFDerivAt_const _ _
  have hz : HasMFDerivAt I' 𝓘(ℝ, U) (fun _ : Y => (0 : U)) y 0 := hasMFDerivAt_const _ _
  have hB : HasMFDerivAt I' 𝓘(ℝ, ℝ × (U × V)) (fun q : Y => ((1 : ℝ), ((0 : U), β q))) y R := by
    convert! hone.prodMk (hz.prodMk hβ.hasMFDerivAt) using 1
  intro _
  rw [hT.mfderiv, hB.mfderiv]
  change Function.Surjective (L.coprod R)
  rintro ⟨s, u, v⟩
  obtain ⟨a, ha⟩ := hαs u
  obtain ⟨b, hb⟩ := hβs v
  refine ⟨((s / κ, a), b), ?_⟩
  apply Prod.ext
  · change s / κ * κ + 0 = s
    rw [add_zero, div_mul_cancel₀ s hκ]
  · change (D a + 0, 0 + E b) = (u, v)
    rw [add_zero, zero_add]
    exact Prod.ext ha hb

theorem MorseCancel.LongitudinalTubeMotion.whole_sheet_transverse {U V E HU HV H M X Y : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HV] [TopologicalSpace H] {I : ModelWithCorners ℝ U HU}
    {I' : ModelWithCorners ℝ V HV} {J : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace Y]
    [ChartedSpace HV Y] {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) J (ℝ × (U × V)) M ∞}
    (A : MorseCancel.LongitudinalTubeMotion Φ) {f : X → M} {g : Y → M} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hfi : Function.Injective (mfderiv I J f x)) (hgi : Function.Injective (mfderiv I' J g y))
    (hrecf : ∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrecg : ∀ z ∈ Φ.source, Φ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) (hx : Φ 0 = f x)
    (hy : Φ (1, 0) = g y) (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) :
    Smale.NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' J (fun p : ℝ × X => A.family (p.1, f p.2)) g
      (A.time, x) y := by
  let W := ℝ × (U × V)
  let a : X → W := Φ.symm ∘ f
  let b : Y → W := Φ.symm ∘ g
  let P : W →L[ℝ] U := (ContinuousLinearMap.fst ℝ U V).comp (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let Q : U →L[ℝ] W := (0 : U →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ U).prod (0 : U →L[ℝ] V))
  let R : W →L[ℝ] V := (ContinuousLinearMap.snd ℝ U V).comp (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let S : V →L[ℝ] W := (0 : V →L[ℝ] ℝ).prod ((0 : V →L[ℝ] U).prod (ContinuousLinearMap.id ℝ V))
  have h1 : ((1 : ℝ), (0 : U × V)) ∈ Φ.source := by
    have hh := A.model_source A.time ((0 : ℝ), (0 : U × V)) h0
    rw [A.model_axis, A.time_value] at hh
    exact hh
  have hfx : f x ∈ Φ.target := hx ▸ Φ.map_source h0
  have hgy : g y ∈ Φ.target := hy ▸ Φ.map_source h1
  have ha : MDifferentiableAt I 𝓘(ℝ, W) a x := (Φ.symm.mdifferentiableAt (by simp) hfx).comp x hf
  have hb : MDifferentiableAt I' 𝓘(ℝ, W) b y := (Φ.symm.mdifferentiableAt (by simp) hgy).comp y hg
  have hai : Function.Injective (mfderiv I 𝓘(ℝ, W) a x) := by
    rw [mfderiv_comp x (Φ.symm.mdifferentiableAt (by simp) hfx) hf]
    exact (Smale.PartialChart.bijective_mfderiv Φ.symm hfx).injective.comp hfi
  have hbi : Function.Injective (mfderiv I' 𝓘(ℝ, W) b y) := by
    rw [mfderiv_comp y (Φ.symm.mdifferentiableAt (by simp) hgy) hg]
    exact (Smale.PartialChart.bijective_mfderiv Φ.symm hgy).injective.comp hgi
  have ha0 : a x = 0 := (congrArg Φ.symm hx).symm.trans (Φ.left_inv h0)
  have hb1 : b y = (1, 0) := (congrArg Φ.symm hy).symm.trans (Φ.left_inv h1)
  have hfn : ∀ᶠ q in 𝓝 x, f q ∈ Φ.target :=
    hf.continuousAt.eventually (Φ.open_target.mem_nhds hfx)
  have hgn : ∀ᶠ q in 𝓝 y, g q ∈ Φ.target :=
    hg.continuousAt.eventually (Φ.open_target.mem_nhds hgy)
  have hca : ∀ᶠ q in 𝓝 x, (a q).1 = 0 ∧ (a q).2.2 = 0 := by
    filter_upwards [hfn] with q hq
    exact (hrecf (a q) (Φ.map_target hq)).mp ⟨q, (Φ.right_inv hq).symm⟩
  have hcb : ∀ᶠ q in 𝓝 y, (b q).1 = 1 ∧ (b q).2.1 = 0 := by
    filter_upwards [hgn] with q hq
    exact (hrecg (b q) (Φ.map_target hq)).mp ⟨q, (Φ.right_inv hq).symm⟩
  have hagerm : a =ᶠ[𝓝 x] fun q => Q (P (a q)) + (0 : W) := by
    filter_upwards [hca] with q hq
    change a q = (0, ((a q).2.1, 0)) + (0 : W)
    rw [add_zero]
    exact Prod.ext hq.1 (Prod.ext rfl hq.2)
  have hbgerm : b =ᶠ[𝓝 y] fun q => S (R (b q)) + ((1 : ℝ), (0 : U × V)) := by
    filter_upwards [hcb] with q hq
    change b q = (0, (0, (b q).2.2)) + ((1 : ℝ), (0 : U × V))
    apply Prod.ext
    · change (b q).1 = 0 + 1
      simpa only [zero_add] using hq.1
    · apply Prod.ext
      · change (b q).2.1 = 0 + 0
        simpa only [zero_add] using hq.2
      · change (b q).2.2 = (b q).2.2 + 0
        exact (add_zero _).symm
  let α : X → U := P ∘ a
  let β : Y → V := R ∘ b
  have hα : MDifferentiableAt I 𝓘(ℝ, U) α x := P.differentiableAt.mdifferentiableAt.comp x ha
  have hβ : MDifferentiableAt I' 𝓘(ℝ, V) β y := R.differentiableAt.mdifferentiableAt.comp y hb
  have hαs := MorseCancel.surjective_sheet_coordinate_mfderiv P Q 0 ha hai hagerm
  have hβs := MorseCancel.surjective_sheet_coordinate_mfderiv R S (1, 0) hb hbi hbgerm
  let η : ℝ → ℝ := fun t => Real.smoothTransition t * A.destination
  have hη : HasDerivAt η (deriv Real.smoothTransition A.time * A.destination) A.time :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
          A.time).hasDerivAt.mul_const
      _
  let T : ℝ × X → W := fun p => (η p.1, (α p.2, 0))
  let B : Y → W := fun q => (1, (0, β q))
  have hT : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, W) T (A.time, x) :=
    (hη.differentiableAt.mdifferentiableAt.comp (A.time, x) mdifferentiableAt_fst).prodMk_space
      ((hα.comp (A.time, x) mdifferentiableAt_snd).prodMk_space mdifferentiableAt_const)
  have hB : MDifferentiableAt I' 𝓘(ℝ, W) B y :=
    mdifferentiableAt_const.prodMk_space (mdifferentiableAt_const.prodMk_space hβ)
  have hT0 : T (A.time, x) = (1, 0) := by
    change (η A.time, (P (a x), (0 : V))) = (1, 0)
    rw [ha0, map_zero]
    exact Prod.ext A.time_value rfl
  have hB0 : B y = (1, 0) := by
    change ((1 : ℝ), ((0 : U), R (b y))) = (1, 0)
    rw [hb1]
    rfl
  have hmodel : Smale.NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' 𝓘(ℝ, W) T B (A.time, x) y :=
    MorseCancel.native_coordinate_plane_trace_transverse hα hβ hαs hβs hη A.time_rate.ne'
  have hnative :=
    (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff Φ hT hB
          (hB0.trans hT0.symm) (hT0 ▸ h1)).mp
      hmodel
  have hq :
    Filter.Tendsto (fun p : ℝ × X => (p.1, a p.2)) (𝓝 (A.time, x)) (𝓝 (A.time, (0 : W))) := by
    have hcont : ContinuousAt (fun p : ℝ × X => (p.1, a p.2)) (A.time, x) :=
      continuousAt_fst.prodMk
        (ContinuousAt.comp (g := a) (f := fun p : ℝ × X => p.2) ha.continuousAt continuousAt_snd)
    simpa only [ha0] using hcont.tendsto
  have hFgerm : (fun p : ℝ × X => A.family (p.1, f p.2)) =ᶠ[𝓝 (A.time, x)] (Φ ∘ T) := by
    filter_upwards [hq.eventually (A.native_germ h0 A.time),
      continuous_snd.continuousAt.eventually hfn, continuous_snd.continuousAt.eventually hca] with
      p hmove hp hplane
    have hpoint : Φ (a p.2) = f p.2 := Φ.right_inv hp
    calc
      A.family (p.1, f p.2) = A.family (p.1, Φ (a p.2)) :=
        congrArg (fun z => A.family (p.1, z)) hpoint.symm
      _ = Φ ((a p.2).1 + η p.1, (a p.2).2) := hmove
      _ = (Φ ∘ T) p := by
        apply congrArg Φ
        change ((a p.2).1 + η p.1, (a p.2).2) = (η p.1, ((a p.2).2.1, 0))
        rw [hplane.1, zero_add]
        exact Prod.ext rfl (Prod.ext rfl hplane.2)
  have hGgerm : g =ᶠ[𝓝 y] (Φ ∘ B) := by
    filter_upwards [hgn, hcb] with q hq hplane
    calc
      g q = Φ (b q) := (Φ.right_inv hq).symm
      _ = (Φ ∘ B) q := congrArg Φ (Prod.ext hplane.1 (Prod.ext hplane.2 rfl))
  intro _
  rw [hFgerm.mfderiv_eq, hGgerm.mfderiv_eq]
  exact hnative (congrArg Φ (hB0.trans hT0.symm))

theorem MorseCancel.exists_clean_two_sheet_arc_avoiding {E M X Y Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [IsManifold (𝓡 2) ∞ X] [CompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y]
    [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y] [SecondCountableTopology Y] [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z]
    {f : X → M} {g : Y → M} {b : Z → M} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g) (hfe : Topology.IsEmbedding f)
    (hge : Topology.IsEmbedding g) (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y)) (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b)
    (hbc : IsClosed (Set.range b)) (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hx : f x ∉ Set.range g) (hy : g y ∉ Set.range f) (hbx : f x ∉ Set.range b)
    (hby : g y ∉ Set.range b) (γ : Path (f x) (g y)) :
    ∃ Φ Ψ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
      (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source ∧
        ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Ψ.source ∧
          Φ 0 = f x ∧
            Ψ (1, 0) = g y ∧
              (∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                (∀ z ∈ Ψ.source, Ψ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                  ∃ a : C(ℝ, M),
                    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a ∧
                      (a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ (t, 0)) ∧
                        (a =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0)) ∧
                          Topology.IsClosedEmbedding (fun t : unitInterval => a t) ∧
                            (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t)) ∧
                              (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range f ↔ t = 0) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range g ↔ t = 1) ∧
                                  Set.MapsTo a (Set.Icc (0 : ℝ) 1) (Set.range b)ᶜ := by
  obtain ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦavoid, hΨavoid, hΦrec, hΨrec, -⟩ :=
    exists_clean_two_sheet_arc hf hg hfe hge hfi hgi hdim x y hx hy γ
  let o : C((X ⊕ Y) ⊕ Z, M) :=
    ⟨Sum.elim (Sum.elim f g) b, (hf.continuous.sumElim hg.continuous).sumElim hb.continuous⟩
  have ho : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ o := (hf.sumElim hg).sumElim hb
  have horange : Set.range o = (Set.range f ∪ Set.range g) ∪ Set.range b := by
    ext z
    constructor
    · rintro ⟨(a | c) | d, he⟩
      · exact Or.inl (Or.inl ⟨a, he⟩)
      · exact Or.inl (Or.inr ⟨c, he⟩)
      · exact Or.inr ⟨d, he⟩
    · rintro ((⟨a, he⟩ | ⟨c, he⟩) | ⟨d, he⟩)
      · exact ⟨Sum.inl (Sum.inl a), he⟩
      · exact ⟨Sum.inl (Sum.inr c), he⟩
      · exact ⟨Sum.inr d, he⟩
  have hoclosed : IsClosed (Set.range o) := by
    rw [horange]
    exact
      ((isCompact_range hf.continuous).isClosed.union
            (isCompact_range hg.continuous).isClosed).union
        hbc
  obtain ⟨U, hU, h0U, hUΦ, ha, hia⟩ := chart_axis_curve_properties Φ 0 hΦ0
  obtain ⟨V, hV, h1V, hVΨ, hc, hic⟩ := chart_axis_curve_properties Ψ 1 hΨ1
  have hnear0 :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Φ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∉ Set.range b :=
    (ha.contMDiffAt (hU.mem_nhds h0U)).continuousAt.eventually
      (hbc.isOpen_compl.mem_nhds (by change Φ 0 ∉ Set.range b; rw [hΦx]; exact hbx))
  have hnear1 :
    ∀ᶠ t in 𝓝 (1 : ℝ),
      Ψ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∉ Set.range b :=
    (hc.contMDiffAt (hV.mem_nhds h1V)).continuousAt.eventually
      (hbc.isOpen_compl.mem_nhds (by change Ψ (1, 0) ∉ Set.range b; rw [hΨy]; exact hby))
  have hclean0 :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Φ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 0 := by
    filter_upwards [hU.mem_nhds h0U, hnear0] with t ht hb'
    rw [horange]
    rintro ((h | h) | h)
    · exact ((hΦrec (t, 0) (hUΦ t ht)).mp h).1
    · exact (hΦavoid (Φ.map_source' (hUΦ t ht)) h).elim
    · exact (hb' h).elim
  have hclean1 :
    ∀ᶠ t in 𝓝 (1 : ℝ),
      Ψ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 1 := by
    filter_upwards [hV.mem_nhds h1V, hnear1] with t ht hb'
    rw [horange]
    rintro ((h | h) | h)
    · exact (hΨavoid (Ψ.map_source' (hVΨ t ht)) h).elim
    · exact ((hΨrec (t, 0) (hVΨ t ht)).mp h).1
    · exact (hb' h).elim
  have hends : Φ (0, 0) ≠ Ψ (1, 0) := by
    change Φ 0 ≠ Ψ (1, 0)
    rw [hΦx, hΨy]
    exact fun h => hx ⟨y, h.symm⟩
  obtain ⟨a, ha', hleft, hright, hemb, hi, havoid⟩ :=
    exists_clean_arc_with_local_endpoint_germs ha hc hU hV h0U h1V hia hic (γ.cast hΦx hΨy) hends
      (by omega) o ho hoclosed (by rw [finrank_euclideanSpace_fin, hdim]; norm_num) hclean0
      hclean1
  have ha0 : a 0 = f x := hleft.eq_of_nhds.trans hΦx
  have ha1 : a 1 = g y := hright.eq_of_nhds.trans hΨy
  refine ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦrec, hΨrec, a, ha', hleft, hright, hemb, hi, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · intro h
      by_contra ht0
      have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at h; exact hy h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inl (Or.inl h))
    · intro he
      subst t
      rw [ha0]
      exact Set.mem_range_self x
  · intro t ht
    constructor
    · intro h
      by_contra ht1
      have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at h; exact hx h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inl (Or.inr h))
    · intro he
      subst t
      rw [ha1]
      exact Set.mem_range_self y
  · intro t ht htb
    have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at htb; exact hbx htb
    have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at htb; exact hby htb
    exact
      havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
        (horange.symm ▸ Or.inr htb)

theorem AdaptedWindows.exists_forward_basin_smooth_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∃ r : ℝ,
      0 < r ∧
        (∀ n : ℕ,
            ContMDiffOn 𝓘(ℝ, (S.data p).chart.PositiveCoordinates) 𝓘(ℝ, E) ∞
              (fun v => S.flow (-(n : ℝ)) ((S.data p).chart.splitChart.symm (0, v)))
              (Metric.ball 0 r)) ∧
          {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} =
            ⋃ n : ℕ,
              (fun v => S.flow (-(n : ℝ)) ((S.data p).chart.splitChart.symm (0, v))) ''
                Metric.ball (0 : (S.data p).chart.PositiveCoordinates) r := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ :=
    MorseCancel.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  have htarget (v : c.PositiveCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    (0, v) ∈ c.splitChart.target :=
    hblock
      ⟨Metric.mem_closedBall_self hr.le,
        Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ r)
          (Metric.ball_subset_closedBall hv)⟩
  have hlocal :
    ContMDiffOn 𝓘(ℝ, c.PositiveCoordinates) 𝓘(ℝ, E) ∞ (fun v => c.splitChart.symm (0, v))
      (Metric.ball 0 (r / 2)) :=
    c.splitChart.contMDiffOn_invFun.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
      htarget
  have hpoint (v : c.PositiveCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    Filter.Tendsto (fun t => S.flow t (c.splitChart.symm (0, v))) Filter.atTop (𝓝 p.val) := by
    have ht := htarget v hv
    have hs : c.splitChart.symm (0, v) ∈ c.splitChart.source := c.splitChart.map_target' ht
    have he : c.splitChart (c.splitChart.symm (0, v)) = (0, v) := c.splitChart.right_inv' ht
    apply ((hbasin (c.splitChart.symm (0, v)) hs ?_ ?_).1).mpr
    · rw [he]
    · rw [he]
      simpa using hr
    · rw [he]
      exact (mem_ball_zero_iff.mp hv).trans (half_lt_self hr)
  refine ⟨r / 2, half_pos hr, ?_, ?_⟩
  · intro n
    exact
      (Degree.SmoothODE.nativeFlowTimeDiffeomorph_of_field S.smooth S.flow S.integral
            (-(n : ℝ))).contMDiff.comp_contMDiffOn
        hlocal
  · ext x
    constructor
    · intro hx
      have hlim := hx.comp tendsto_natCast_atTop_atTop
      obtain ⟨n, hs, hn, hp'⟩ :=
        (hlim.eventually
            (MorseCancel.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
      have hnew := (MorseCancel.flow_time_atTop_limit_iff S.flow (n : ℝ) x p.val).mpr hx
      have hz : (c.splitChart (S.flow (n : ℝ) x)).1 = 0 :=
        ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp'.trans (half_lt_self hr))).1).mp hnew
      refine
        Set.mem_iUnion.mpr ⟨n, (c.splitChart (S.flow (n : ℝ) x)).2, mem_ball_zero_iff.mpr hp', ?_⟩
      have he : (0, (c.splitChart (S.flow (n : ℝ) x)).2) = c.splitChart (S.flow (n : ℝ) x) :=
        Prod.ext hz.symm rfl
      change S.flow (-(n : ℝ)) (c.splitChart.symm (0, (c.splitChart (S.flow (n : ℝ) x)).2)) = x
      rw [he]
      have hi : c.splitChart.symm (c.splitChart (S.flow (n : ℝ) x)) = S.flow (n : ℝ) x :=
        c.splitChart.left_inv' hs
      rw [hi, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]
    · intro hx
      obtain ⟨n, v, hv, rfl⟩ := Set.mem_iUnion.mp hx
      exact
        (MorseCancel.flow_time_atTop_limit_iff S.flow (-(n : ℝ)) (c.splitChart.symm (0, v))
              p.val).mpr
          (hpoint v hv)

theorem AdaptedWindows.exists_backward_basin_smooth_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∃ r : ℝ,
      0 < r ∧
        (∀ n : ℕ,
            ContMDiffOn 𝓘(ℝ, (S.data p).chart.NegativeCoordinates) 𝓘(ℝ, E) ∞
              (fun v => S.flow (n : ℝ) ((S.data p).chart.splitChart.symm (v, 0)))
              (Metric.ball 0 r)) ∧
          {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)} =
            ⋃ n : ℕ,
              (fun v => S.flow (n : ℝ) ((S.data p).chart.splitChart.symm (v, 0))) ''
                Metric.ball (0 : (S.data p).chart.NegativeCoordinates) r := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ :=
    MorseCancel.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  have htarget (v : c.NegativeCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    (v, 0) ∈ c.splitChart.target :=
    hblock
      ⟨Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ r)
          (Metric.ball_subset_closedBall hv),
        Metric.mem_closedBall_self hr.le⟩
  have hlocal :
    ContMDiffOn 𝓘(ℝ, c.NegativeCoordinates) 𝓘(ℝ, E) ∞ (fun v => c.splitChart.symm (v, 0))
      (Metric.ball 0 (r / 2)) :=
    c.splitChart.contMDiffOn_invFun.comp (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffOn
      htarget
  have hpoint (v : c.NegativeCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    Filter.Tendsto (fun t => S.flow t (c.splitChart.symm (v, 0))) Filter.atBot (𝓝 p.val) := by
    have ht := htarget v hv
    have hs : c.splitChart.symm (v, 0) ∈ c.splitChart.source := c.splitChart.map_target' ht
    have he : c.splitChart (c.splitChart.symm (v, 0)) = (v, 0) := c.splitChart.right_inv' ht
    apply ((hbasin (c.splitChart.symm (v, 0)) hs ?_ ?_).2).mpr
    · rw [he]
    · rw [he]
      exact (mem_ball_zero_iff.mp hv).trans (half_lt_self hr)
    · rw [he]
      simpa using hr
  refine ⟨r / 2, half_pos hr, ?_, ?_⟩
  · intro n
    exact
      (Degree.SmoothODE.nativeFlowTimeDiffeomorph_of_field S.smooth S.flow S.integral
            (n : ℝ)).contMDiff.comp_contMDiffOn
        hlocal
  · ext x
    constructor
    · intro hx
      have hlim : Filter.Tendsto (fun n : ℕ => S.flow (-(n : ℝ)) x) Filter.atTop (𝓝 p.val) :=
        hx.comp (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      obtain ⟨n, hs, hn, hp'⟩ :=
        (hlim.eventually
            (MorseCancel.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
      have hnew := (MorseCancel.flow_time_atBot_limit_iff S.flow (-(n : ℝ)) x p.val).mpr hx
      have hz : (c.splitChart (S.flow (-(n : ℝ)) x)).2 = 0 :=
        ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp'.trans (half_lt_self hr))).2).mp hnew
      refine
        Set.mem_iUnion.mpr
          ⟨n, (c.splitChart (S.flow (-(n : ℝ)) x)).1, mem_ball_zero_iff.mpr hn, ?_⟩
      have he :
        ((c.splitChart (S.flow (-(n : ℝ)) x)).1, 0) = c.splitChart (S.flow (-(n : ℝ)) x) :=
        Prod.ext rfl hz.symm
      change S.flow (n : ℝ) (c.splitChart.symm ((c.splitChart (S.flow (-(n : ℝ)) x)).1, 0)) = x
      rw [he]
      have hi : c.splitChart.symm (c.splitChart (S.flow (-(n : ℝ)) x)) = S.flow (-(n : ℝ)) x :=
        c.splitChart.left_inv' hs
      rw [hi, ← S.flow.map_add, add_neg_cancel, S.flow.map_zero_apply]
    · intro hx
      obtain ⟨n, v, hv, rfl⟩ := Set.mem_iUnion.mp hx
      exact
        (MorseCancel.flow_time_atBot_limit_iff S.flow (n : ℝ) (c.splitChart.symm (v, 0))
              p.val).mpr
          (hpoint v hv)

theorem MorseCancel.exists_smooth_ball_parametrization {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ} (hd : Module.finrank ℝ V ≤ d) {r : ℝ}
    (hr : 0 < r) :
    ∃ ψ : EuclideanSpace ℝ (Fin d) → V, ContDiff ℝ ∞ ψ ∧ Set.range ψ = Metric.ball 0 r := by
  let W := EuclideanSpace ℝ (Fin (d - Module.finrank ℝ V))
  let L : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (V × W) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by
        simp only [Module.finrank_prod, finrank_euclideanSpace_fin, W]
        omega)
  let π : EuclideanSpace ℝ (Fin d) →L[ℝ] V :=
    (ContinuousLinearMap.fst ℝ V W).comp L.toContinuousLinearMap
  have hπ : Function.Surjective π := by
    intro v
    refine ⟨L.symm (v, 0), ?_⟩
    change (L (L.symm (v, 0))).1 = v
    rw [L.apply_symm_apply]
  let B := OpenPartialHomeomorph.univBall (0 : V) r
  let ψ : EuclideanSpace ℝ (Fin d) → V := B ∘ π
  have hψ : ContDiff ℝ ∞ ψ := OpenPartialHomeomorph.contDiff_univBall.comp π.contDiff
  refine ⟨ψ, hψ, ?_⟩
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    have hm : π z ∈ B.source := by rw [OpenPartialHomeomorph.univBall_source]; trivial
    have hh := B.map_source hm
    rwa [OpenPartialHomeomorph.univBall_target _ hr] at hh
  · intro hv
    have hvt : v ∈ B.target := by rw [OpenPartialHomeomorph.univBall_target _ hr]; exact hv
    obtain ⟨z, hz⟩ := hπ (B.symm v)
    refine ⟨z, ?_⟩
    change B (π z) = v
    rw [hz]
    exact B.right_inv hvt

theorem MorseCancel.exists_global_smooth_image_of_ball {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {d : ℕ} (hd : Module.finrank ℝ V ≤ d) {r : ℝ} (hr : 0 < r) {f : V → M}
    (hf : ContMDiffOn 𝓘(ℝ, V) I ∞ f (Metric.ball 0 r)) :
    ∃ g : EuclideanSpace ℝ (Fin d) → M,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I ∞ g ∧ Set.range g = f '' Metric.ball 0 r := by
  obtain ⟨ψ, hψ, hrange⟩ := exists_smooth_ball_parametrization hd hr
  refine ⟨f ∘ ψ, ?_, ?_⟩
  · intro x
    have hx : ψ x ∈ Metric.ball (0 : V) r := hrange ▸ Set.mem_range_self x
    exact (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)).comp x hψ.contMDiff.contMDiffAt
  · rw [Set.range_comp, hrange]

theorem Degree.FlowCancellation.native_flow_eq_on_positive_halfline {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W) {x : M}
    (hagrees : ∀ t : ℝ, 0 ≤ t → W (G t x) = V (G t x)) : ∀ t : ℝ, 0 ≤ t → G t x = F t x := by
  intro t ht
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [G.map_zero_apply, F.map_zero_apply]
  · have hc : IsMIntegralCurveOn (fun s => G s x) V (Set.Ioo (0 : ℝ) t) := by
      intro s hs
      have hd := hG x s
      rw [hagrees s hs.1.le] at hd
      exact hd.hasMFDerivWithinAt
    have hh :=
      Degree.FlowSuspension.native_flow_segment_endpoints hV F hF ht
        (hG x).continuous.continuousOn hc
    simpa only [sub_zero, G.map_zero_apply] using hh.symm

theorem Degree.FlowCancellation.native_flow_eq_on_negative_halfline {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W) {x : M}
    (hagrees : ∀ t : ℝ, t ≤ 0 → W (G t x) = V (G t x)) : ∀ t : ℝ, t ≤ 0 → G t x = F t x := by
  intro t ht
  rcases ht.lt_or_eq with ht | ht
  · have hc : IsMIntegralCurveOn (fun s => G s x) V (Set.Ioo t (0 : ℝ)) := by
      intro s hs
      have hd := hG x s
      rw [hagrees s hs.2.le] at hd
      exact hd.hasMFDerivWithinAt
    have hh :=
      Degree.FlowSuspension.native_flow_segment_endpoints hV F hF ht
        (hG x).continuous.continuousOn hc
    have he := congrArg (F t) hh
    simpa only [zero_sub, ← F.map_add, add_neg_cancel, F.map_zero_apply, G.map_zero_apply] using
      he
  · subst t
    rw [G.map_zero_apply, F.map_zero_apply]

theorem Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {x p q : X}
    (hp : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 q)) {c : ℝ} (hpc : c < f p)
    (hqc : f q < c) : ∃ t, f (F t x) = c := by
  have htop : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f q)) :=
    hf.continuousAt.tendsto.comp hq
  have hbot : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hp
  obtain ⟨s, hs⟩ := (htop.eventually (eventually_lt_nhds hqc)).exists
  obtain ⟨t, ht⟩ := (hbot.eventually (eventually_gt_nhds hpc)).exists
  exact
    mem_range_of_exists_le_of_exists_ge (hf.comp (F.continuous continuous_id continuous_const))
      ⟨s, hs.le⟩ ⟨t, ht.le⟩

def MorseCancel.forwardHighBasins {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (a : ℝ) : Set M :=
  {x |
    ∃ p : Smale.ManifoldMorse.criticalPoints E f,
      a ≤ f p ∧ Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)}

def MorseCancel.backwardLowBasins {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (a : ℝ) : Set M :=
  {x |
    ∃ p : Smale.ManifoldMorse.criticalPoints E f,
      f p ≤ a ∧ Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)}

theorem MorseCancel.forwardHighBasins_eq_inter {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : forwardHighBasins S a = ⋂ t : ℝ, {x | a ≤ f (S.flow t x)} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hlim⟩ t
    have hmono :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    exact hp.trans (hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t)
  · intro hbound
    obtain ⟨-, -, q, hq, -, hlim, -⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    refine ⟨⟨q, hq⟩, ?_, hlim⟩
    exact
      ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim)
        (Filter.Eventually.of_forall hbound)

theorem MorseCancel.backwardLowBasins_eq_inter {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : backwardLowBasins S a = ⋂ t : ℝ, {x | f (S.flow t x) ≤ a} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hlim⟩ t
    have hmono :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    exact (hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t).trans hp
  · intro hbound
    obtain ⟨p, hp, -, -, hlim, -, -⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    refine ⟨⟨p, hp⟩, ?_, hlim⟩
    exact
      le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim)
        (Filter.Eventually.of_forall hbound)

theorem MorseCancel.isClosed_endpoint_obstruction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : IsClosed (forwardHighBasins S a ∪ backwardLowBasins S a) := by
  rw [forwardHighBasins_eq_inter S hf, backwardLowBasins_eq_inter S hf]
  apply IsClosed.union
  · exact
      isClosed_iInter
        (fun t =>
          isClosed_le continuous_const
            (hf.continuous.comp (S.flow.continuous continuous_const continuous_id)))
  · exact
      isClosed_iInter
        (fun t =>
          isClosed_le (hf.continuous.comp (S.flow.continuous continuous_const continuous_id))
            continuous_const)

theorem MorseCancel.levelBasin_compl_eq_endpoint_obstruction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    (Degree.FlowCancellation.levelBasin S.flow f a)ᶜ =
      forwardHighBasins S a ∪ backwardLowBasins S a := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, q, hq, hback, hforward, -⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    by_cases hqa : a ≤ f q
    · exact Or.inl ⟨⟨q, hq⟩, hqa, hforward⟩
    by_cases hpa : f p ≤ a
    · exact Or.inr ⟨⟨p, hp⟩, hpa, hback⟩
    exact
      False.elim
        (hx
          (Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
            hback hforward (lt_of_not_ge hpa) (lt_of_not_ge hqa)))
  · intro hx hcross
    obtain ⟨t, ht⟩ := hcross
    have hmono :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    rcases hx with ⟨p, hp, hlim⟩ | ⟨p, hp, hlim⟩
    · have hh := hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t
      rw [ht] at hh
      exact hreg p (le_antisymm hh hp) p.property
    · have hh := hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t
      rw [ht] at hh
      exact hreg p (le_antisymm hp hh) p.property

theorem AdaptedWindows.exists_forward_basin_global_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hd : Module.finrank ℝ E - MorseCancel.nativeMorseIndex E f p ≤ d) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → M,
      (∀ n, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g n)) ∧
        {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} =
          ⋃ n, Set.range (g n) := by
  obtain ⟨r, hr, hsmooth, hcover⟩ := S.exists_forward_basin_smooth_images hf p
  have hdim : Module.finrank ℝ (S.data p).chart.PositiveCoordinates ≤ d := by
    have hh := (S.data p).chart.finrank_negative_add_positive
    rw [MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart] at hd
    omega
  choose g hg hrange using
    (fun n => MorseCancel.exists_global_smooth_image_of_ball hdim hr (hsmooth n))
  refine ⟨g, hg, ?_⟩
  rw [hcover]
  exact Set.iUnion_congr (fun n => (hrange n).symm)

theorem AdaptedWindows.exists_backward_basin_global_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hd : MorseCancel.nativeMorseIndex E f p ≤ d) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → M,
      (∀ n, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g n)) ∧
        {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)} =
          ⋃ n, Set.range (g n) := by
  obtain ⟨r, hr, hsmooth, hcover⟩ := S.exists_backward_basin_smooth_images hf p
  have hdim : Module.finrank ℝ (S.data p).chart.NegativeCoordinates ≤ d := by
    rwa [MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart] at hd
  choose g hg hrange using
    (fun n => MorseCancel.exists_global_smooth_image_of_ball hdim hr (hsmooth n))
  refine ⟨g, hg, ?_⟩
  rw [hcover]
  exact Set.iUnion_congr (fun n => (hrange n).symm)

abbrev MorseCancel.EndpointBasinIndex {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (a : ℝ) :=
  ({ p : Smale.ManifoldMorse.criticalPoints E f // a ≤ f p.val } × ℕ) ⊕
    ({ p : Smale.ManifoldMorse.criticalPoints E f // f p.val ≤ a } × ℕ)

theorem MorseCancel.endpointBasinIndex_countable {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (a : ℝ) : Countable (EndpointBasinIndex (E := E) (f := f) a) := by
  let _ := S.finite.fintype
  unfold EndpointBasinIndex
  infer_instance

theorem AdaptedWindows.exists_endpoint_obstruction_global_images {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) {d : ℕ}
    (hhigh :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancel.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ d) :
    ∃ g : MorseCancel.EndpointBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
        MorseCancel.forwardHighBasins S a ∪ MorseCancel.backwardLowBasins S a =
          ⋃ i, Set.range (g i) := by
  choose gF hgF hF using
    (fun p : { p : Smale.ManifoldMorse.criticalPoints E f // a ≤ f p.val } =>
      S.exists_forward_basin_global_images hf p.val (hhigh p.val p.property))
  choose gB hgB hB using
    (fun p : { p : Smale.ManifoldMorse.criticalPoints E f // f p.val ≤ a } =>
      S.exists_backward_basin_global_images hf p.val (hlow p.val p.property))
  let g : MorseCancel.EndpointBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M :=
    Sum.elim (fun i => gF i.1 i.2) (fun i => gB i.1 i.2)
  refine ⟨g, ?_, ?_⟩
  · intro i
    rcases i with ⟨p, n⟩ | ⟨p, n⟩
    · exact hgF p n
    · exact hgB p n
  · ext x
    constructor
    · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
      · have hh : x ∈ ⋃ n, Set.range (gF ⟨p, hp⟩ n) := (hF ⟨p, hp⟩) ▸ hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨Sum.inl (⟨p, hp⟩, n), hn⟩
      · have hh : x ∈ ⋃ n, Set.range (gB ⟨p, hp⟩ n) := (hB ⟨p, hp⟩) ▸ hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨p, hp⟩, n), hn⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rcases i with ⟨p, n⟩ | ⟨p, n⟩
      · have hh : x ∈ {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val.val)} :=
          by
          rw [hF p]
          exact Set.mem_iUnion.mpr ⟨n, hi⟩
        exact Or.inl ⟨p.val, p.property, hh⟩
      · have hh : x ∈ {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val.val)} :=
          by
          rw [hB p]
          exact Set.mem_iUnion.mpr ⟨n, hi⟩
        exact Or.inr ⟨p.val, p.property, hh⟩

theorem MorseCancel.isClosed_backwardLowBasins {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) : IsClosed (backwardLowBasins S a) := by
  rw [backwardLowBasins_eq_inter S hf]
  exact
    isClosed_iInter
      (fun t =>
        isClosed_le (hf.continuous.comp (S.flow.continuous continuous_const continuous_id))
          continuous_const)

abbrev MorseCancel.LowBackwardBasinIndex {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (a : ℝ) :=
  { p : Smale.ManifoldMorse.criticalPoints E f // f p.val ≤ a } × ℕ

theorem MorseCancel.lowBackwardBasinIndex_countable {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (a : ℝ) : Countable (LowBackwardBasinIndex (E := E) (f := f) a) := by
  let _ := S.finite.fintype
  unfold LowBackwardBasinIndex
  infer_instance

theorem AdaptedWindows.exists_low_backward_obstruction_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) {d : ℕ}
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ d) :
    ∃ g : MorseCancel.LowBackwardBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
        MorseCancel.backwardLowBasins S a = ⋃ i, Set.range (g i) := by
  choose g hg hcover using
    (fun p : { p : Smale.ManifoldMorse.criticalPoints E f // f p.val ≤ a } =>
      S.exists_backward_basin_global_images hf p.val (hlow p.val p.property))
  refine ⟨fun i => g i.1 i.2, fun i => hg i.1 i.2, ?_⟩
  ext x
  constructor
  · rintro ⟨p, hp, hx⟩
    have hh : x ∈ ⋃ n, Set.range (g ⟨p, hp⟩ n) := (hcover ⟨p, hp⟩) ▸ hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
    exact Set.mem_iUnion.mpr ⟨(⟨p, hp⟩, n), hn⟩
  · intro hx
    obtain ⟨⟨p, n⟩, hn⟩ := Set.mem_iUnion.mp hx
    have hh : x ∈ {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val.val)} := by
      rw [hcover p]
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    exact ⟨p.val, p.property, hh⟩

theorem MorseCancel.contMDiff_discrete_family {ι V E H M : Type*} [TopologicalSpace ι]
    [DiscreteTopology ι] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] (f : ι → V → M) (hf : ∀ i, ContMDiff 𝓘(ℝ, V) I ∞ (f i)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) ι := ChartedSpace.ofDiscreteTopology
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞ (fun p : ι × V => f p.1 p.2) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) ι := ChartedSpace.ofDiscreteTopology
  change ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞ (fun p : ι × V => f p.1 p.2)
  intro p
  have hg :
    ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞ (fun q : ι × V => f p.1 q.2)
      p :=
    (hf p.1).contMDiffAt.comp p contMDiffAt_snd
  apply hg.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : ι × V in 𝓝 p, q.1 ∈ ({ p.1 } : Set ι) :=
    ((isOpen_discrete ({ p.1 } : Set ι)).preimage continuous_fst).mem_nhds (Set.mem_singleton _)
  filter_upwards [hnear] with q hq
  rw [Set.mem_singleton_iff.mp hq]

theorem MorseCancel.range_discrete_family {ι V M : Type*} [TopologicalSpace ι]
    [DiscreteTopology ι] [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M]
    (f : ι → V → M) : Set.range (fun p : ι × V => f p.1 p.2) = ⋃ i, Set.range (f i) := by
  ext x
  constructor
  · rintro ⟨⟨i, v⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, v, rfl⟩
  · intro hx
    obtain ⟨i, v, hv⟩ := Set.mem_iUnion.mp hx
    exact ⟨(i, v), hv⟩

theorem MorseCancel.joinedIn_sublevel_of_forward_limit {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {x p : X} {a : ℝ} (hx : f x ≤ a)
    (hp : f p < a) (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    JoinedIn {y : X | f y ≤ a} x p := by
  have hU : {y : X | f y < a} ∈ 𝓝 p := (isOpen_lt hf continuous_const).mem_nhds hp
  have hC := pathComponentIn_mem_nhds hU
  obtain ⟨T, hT, hFT⟩ := ((Filter.eventually_ge_atTop (0 : ℝ)).and (hlim.eventually hC)).exists
  have htail : JoinedIn {y : X | f y ≤ a} (F T x) p :=
    (show JoinedIn {y : X | f y < a} p (F T x) from hFT).symm.mono
      (fun y hy => (show f y < a from hy).le)
  have hsegment : JoinedIn {y : X | f y ≤ a} x (F T x) := by
    let γ : Path x (F T x) :=
      { toFun := fun u => F ((u : ℝ) * T) x
        continuous_toFun := F.continuous (continuous_subtype_val.mul_const T) continuous_const
        source' := by simp
        target' := by simp }
    refine ⟨γ, fun u => ?_⟩
    have htime : 0 ≤ (u : ℝ) * T := mul_nonneg u.property.1 hT
    have hh := hmono x htime
    have hh' : f (F ((u : ℝ) * T) x) ≤ f x := by simpa only [F.map_zero_apply] using hh
    exact hh'.trans hx
  exact hsegment.trans htail

theorem MorseCancel.joined_sublevel_of_common_forward_limit {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {a : ℝ} (x y : { z : X // f z ≤ a }) {p : X}
    (hp : f p < a) (hx : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hy : Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) : Joined x y := by
  exact
    ((joinedIn_sublevel_of_forward_limit F hf hmono x.property hp hx).trans
        (joinedIn_sublevel_of_forward_limit F hf hmono y.property hp hy).symm).joined_subtype

theorem MorseCancel.joinedIn_open_forward_basin {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (F : Flow ℝ X) (p : X)
    (hopen : IsOpen {x : X | Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)})
    (hp : Filter.Tendsto (fun t => F t p) Filter.atTop (𝓝 p)) {x : X}
    (hx : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    JoinedIn {y : X | Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)} x p := by
  let B : Set X := {y | Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)}
  have hC := pathComponentIn_mem_nhds (hopen.mem_nhds hp)
  obtain ⟨T, hT⟩ := (hx.eventually hC).exists
  have htail : JoinedIn B (F T x) p := (show JoinedIn B p (F T x) from hT).symm
  let γ : Path x (F T x) :=
    { toFun := fun u => F ((u : ℝ) * T) x
      continuous_toFun := F.continuous (continuous_subtype_val.mul_const T) continuous_const
      source' := by simp
      target' := by simp }
  have hsegment : JoinedIn B x (F T x) := by
    refine ⟨γ, fun u => ?_⟩
    exact (flow_time_atTop_limit_iff F ((u : ℝ) * T) x p).mpr hx
  exact hsegment.trans htail

theorem AdaptedWindows.joinedIn_minimum_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 0) {x y : M}
    (hx : Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val))
    (hy : Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p.val)) :
    JoinedIn {z : M | Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val)} x y := by
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  have hpp : Filter.Tendsto (fun t => S.flow t p.val) Filter.atTop (𝓝 p.val) := by
    have heq : (fun t => S.flow t p.val) = fun _ => p.val :=
      funext
        (fun t =>
          Smale.FlowConstruction.flow_fixed_of_zero (S.smooth.of_le (by simp)) S.flow S.integral
            (S.zero p p.property) t)
    rw [heq]
    exact tendsto_const_nhds
  have hopen := S.isOpen_minimum_forward_basin hf p hp
  exact
    (MorseCancel.joinedIn_open_forward_basin S.flow p.val hopen hpp hx).trans
      (MorseCancel.joinedIn_open_forward_basin S.flow p.val hopen hpp hy).symm

theorem Degree.SmoothODE.scalar_partial_invertible {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {F : P × ℝ → ℝ} {p : P} {t v : ℝ} (hF : ContDiffAt ℝ ∞ F (p, t))
    (htime : HasDerivAt (fun s : ℝ => F (p, s)) v t) (hv : v ≠ 0) :
    ((fderiv ℝ F (p, t)).comp (ContinuousLinearMap.inr ℝ P ℝ)).IsInvertible := by
  have hd :=
    (hF.differentiableAt (by simp)).hasFDerivAt.comp t
      ((hasFDerivAt_const p t).prodMk (hasFDerivAt_id t))
  change
    HasFDerivAt (fun s : ℝ => F (p, s)) ((fderiv ℝ F (p, t)).comp (ContinuousLinearMap.inr ℝ P ℝ))
      t at hd
  have heq := hd.unique htime.hasFDerivAt
  let L : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ v hv).toContinuousLinearEquiv
  refine ⟨L, ?_⟩
  rw [heq]
  apply ContinuousLinearMap.ext
  intro r
  change v * r = r * v
  exact mul_comm v r

theorem Degree.SmoothODE.exists_smooth_scalar_time_germ {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [CompleteSpace P] {F : P × ℝ → ℝ} {p : P} {t c v : ℝ}
    (hF : ContDiffAt ℝ ∞ F (p, t)) (hlevel : F (p, t) = c)
    (htime : HasDerivAt (fun s : ℝ => F (p, s)) v t) (hv : v ≠ 0) :
    ∃ θ : P → ℝ, θ p = t ∧ ContDiffAt ℝ ∞ θ p ∧ ∀ᶠ q in 𝓝 p, F (q, θ q) = c := by
  have hinv := scalar_partial_invertible hF htime hv
  let θ := hF.implicitFunction (by simp) hinv
  refine
    ⟨θ, hF.implicitFunction_apply_self (by simp) hinv,
      hF.contDiffAt_implicitFunction (by simp) hinv, ?_⟩
  filter_upwards [hF.eventually_apply_implicitFunction (by simp) hinv] with q hq
  exact hq.trans hlevel

theorem Degree.FlowCancellation.exists_native_smooth_time_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {H : M × ℝ → ℝ} {p : M} {t c v : ℝ}
    (hH : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H (p, t)) (hlevel : H (p, t) = c)
    (htime : HasDerivAt (fun s : ℝ => H (p, s)) v t) (hv : v ≠ 0) :
    ∃ θ : M → ℝ, θ p = t ∧ ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ p ∧ ∀ᶠ q in 𝓝 p, H (q, θ q) = c := by
  let e := NoExotic.modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) p
  have hp : p ∈ e.source := mem_extChartAt_source p
  have hz : e p ∈ e.target := e.map_source' hp
  have he : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e p :=
    (e.contMDiffOn p hp).contMDiffAt (e.open_source.mem_nhds hp)
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm (e p) :=
    (e.symm.contMDiffOn (e p) hz).contMDiffAt (e.open_target.mem_nhds hz)
  let B (q : E × ℝ) : M × ℝ := (e.symm q.1, q.2)
  let F : E × ℝ → ℝ := H ∘ B
  have hleft : e.symm (e p) = p := e.left_inv' hp
  have hB : ContMDiffAt 𝓘(ℝ, E × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞ B (e p, t) := by
    have hfst : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞ (Prod.fst : E × ℝ → E) (e p, t) :=
      contDiffAt_fst.contMDiffAt
    have hfirst := hi.comp (e p, t) hfst
    exact hfirst.prodMk contDiffAt_snd.contMDiffAt
  have hB0 : B (e p, t) = (p, t) := Prod.ext hleft rfl
  have hH' : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H (B (e p, t)) := by
    rw [hB0]
    exact hH
  have hF : ContDiffAt ℝ ∞ F (e p, t) := (hH'.comp (e p, t) hB).contDiffAt
  have hFtime : (fun s : ℝ => F (e p, s)) = fun s => H (p, s) := by
    funext s
    change H (e.symm (e p), s) = H (p, s)
    rw [hleft]
  have hFt : HasDerivAt (fun s : ℝ => F (e p, s)) v t := by rw [hFtime]; exact htime
  have hFc : F (e p, t) = c := by
    change H (B (e p, t)) = c
    rw [hB0]
    exact hlevel
  obtain ⟨θ, hθ, hsmooth, hroot⟩ := Degree.SmoothODE.exists_smooth_scalar_time_germ hF hFc hFt hv
  refine ⟨θ ∘ e, hθ, hsmooth.contMDiffAt.comp p he, ?_⟩
  filter_upwards [e.open_source.mem_nhds hp, he.continuousAt hroot] with q hq hrootq
  have hqleft : e.symm (e q) = q := e.left_inv' hq
  change H (e.symm (e q), θ (e q)) = c at hrootq
  change H (q, θ (e q)) = c
  rwa [hqleft] at hrootq

theorem Degree.FlowCancellation.smooth_signed_level_time {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsOpen (levelBasin F f c) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (signedLevelTime F f c) (levelBasin F f c) ∧
        ∀ x ∈ levelBasin F f c,
          ∀ s : ℝ, signedLevelTime F f c (F s x) = signedLevelTime F f c x - s := by
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancel.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hH : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : M × ℝ => f (F q.2 q.1)) :=
    hf.comp (Degree.SmoothODE.contMDiff_native_flow hV F hcurve)
  have hgerm (p : M) (hp : p ∈ levelBasin F f c) :
    ∃ θ : M → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ p ∧ ∀ᶠ q in 𝓝 p, f (F (θ q) q) = c := by
    let t := signedLevelTime F f c p
    have hhit : f (F t p) = c := signedLevelTime_hits F f c hp
    obtain ⟨θ, -, hθ, heq⟩ :=
      exists_native_smooth_time_germ hH.contMDiffAt hhit (hder p t) (hboundary (F t p) hhit).ne
    exact ⟨θ, hθ, heq⟩
  have hB : IsOpen (levelBasin F f c) := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    obtain ⟨θ, -, heq⟩ := hgerm p hp
    exact heq.mono (fun q hq => ⟨θ q, hq⟩)
  refine ⟨hB, ?_, ?_⟩
  · intro p hp
    obtain ⟨θ, hθ, heq⟩ := hgerm p hp
    apply ContMDiffAt.contMDiffWithinAt
    apply hθ.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    exact signedLevelTime_eq_of_level F hf.continuous hD hder hboundary hq
  · intro x hx s
    exact signedLevelTime_flow F hf.continuous hD hder hboundary hx s

theorem Degree.FlowCancellation.exists_native_level_flow_cylinder {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {c : ℝ} (hreg : ∀ x, f x = c → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) (z : { x : M // f x = c }) :
    letI := Smale.RegularLevel.chartedSpace hf hreg
    ∃ Φ :
      PartialDiffeomorph (𝓘(ℝ, Smale.RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({ x : M // f x = c } × ℝ) M ∞,
      Φ.source = Set.univ ∧
        Φ.target = levelBasin F f c ∧
          (∀ p, Φ p = F p.2 p.1) ∧ ∀ x ∈ Φ.target, (Φ.symm x).2 = -signedLevelTime F f c x := by
  classical
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let L := { x : M // f x = c }
  let B := levelBasin F f c
  let θ := signedLevelTime F f c
  obtain ⟨hB, hθ, htranslate⟩ := smooth_signed_level_time hf hV F hcurve hboundary
  let r : M → L := fun x => if hx : x ∈ B then ⟨F (θ x) x, signedLevelTime_hits F f c hx⟩ else z
  let φ : L × ℝ → M := fun p => F p.2 p.1
  let ψ : M → L × ℝ := fun x => (r x, -θ x)
  have hflow := Degree.SmoothODE.contMDiff_native_flow hV F hcurve
  have hφ : ContMDiff (𝓘(ℝ, Smale.RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ φ :=
    hflow.comp
      (((Smale.RegularLevel.contMDiff_inclusion hf hreg).comp contMDiff_fst).prodMk contMDiff_snd)
  have hψ : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, Smale.RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) ∞ ψ B := by
    intro x hx
    have hθx := (hθ x hx).contMDiffAt (hB.mem_nhds hx)
    have hr : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ r x := by
      apply (Smale.RegularLevel.contMDiffAt_iff_inclusion hf hreg 𝓘(ℝ, E) r x).mpr
      apply (hflow.contMDiffAt.comp x (contMDiffAt_id.prodMk hθx)).congr_of_eventuallyEq
      filter_upwards [hB.mem_nhds hx] with y hy
      change (r y : M) = F (θ y) y
      have hyB : y ∈ B := hy
      simp only [r, dif_pos hyB]
    exact (hr.prodMk hθx.neg).contMDiffWithinAt
  have hD : Continuous (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) :=
    (MorseCancel.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) :=
    Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hlevel (x : L) : (x : M) ∈ B := ⟨0, by simpa only [F.map_zero_apply] using x.property⟩
  have hφB (p : L × ℝ) : φ p ∈ B := (levelBasin_flow_iff F f c p.2 p.1).mpr (hlevel p.1)
  have hclock (p : L × ℝ) : θ (φ p) = -p.2 := by
    have hh := htranslate p.1 (hlevel p.1) p.2
    rw [signedLevelTime_eq_zero F hf.continuous hD hder hboundary p.1.property, zero_sub] at hh
    exact hh
  have hleft (p : L × ℝ) : ψ (φ p) = p := by
    apply Prod.ext
    · apply Subtype.ext
      change (r (φ p) : M) = p.1
      rw [show r (φ p) = ⟨F (θ (φ p)) (φ p), signedLevelTime_hits F f c (hφB p)⟩ by
          simp only [r, dif_pos (hφB p)] ]
      change F (θ (φ p)) (F p.2 p.1) = p.1
      rw [hclock, ← F.map_add, neg_add_cancel, F.map_zero_apply]
    · change -θ (φ p) = p.2
      rw [hclock, neg_neg]
  have hright (x : M) (hx : x ∈ B) : φ (ψ x) = x := by
    change F (-θ x) (r x) = x
    rw [show r x = ⟨F (θ x) x, signedLevelTime_hits F f c hx⟩ by simp only [r, dif_pos hx] ]
    change F (-θ x) (F (θ x) x) = x
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  let Φ :
    PartialDiffeomorph (𝓘(ℝ, Smale.RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (L × ℝ) M ∞ :=
    { toFun := φ
      invFun := ψ
      source := Set.univ
      target := B
      map_source' := fun p _ => hφB p
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := fun p _ => hleft p
      right_inv' := hright
      open_source := isOpen_univ
      open_target := hB
      contMDiffOn_toFun := hφ.contMDiffOn
      contMDiffOn_invFun := hψ }
  exact ⟨Φ, rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem AdaptedWindows.joinedIn_regular_level_of_endpoint_dimensions {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancel.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) {x y : M} (hxa : f x = a) (hya : f y = a) (γ : Path x y) :
    JoinedIn {z : M | f z = a} x y := by
  let _ := S.finite.fintype
  let K := MorseCancel.EndpointBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := MorseCancel.endpointBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_endpoint_obstruction_global_images hf a hhigh hlow
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun z : K × V => g z.1 z.2) :=
    MorseCancel.contMDiff_discrete_family g hg
  let G : C(K × V, M) := ⟨fun z => g z.1 z.2, hG.continuous⟩
  have hrange : Set.range G = (Degree.FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [MorseCancel.levelBasin_compl_eq_endpoint_obstruction S hf hreg, hcover]
    exact MorseCancel.range_discrete_family g
  have hclosed : IsClosed (Set.range G) := by
    rw [hrange, MorseCancel.levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact MorseCancel.isClosed_endpoint_obstruction S hf a
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : M) (hz : f z = a) : z ∉ Set.range G := by
    rw [hrange, Set.mem_compl_iff, Classical.not_not]
    exact ⟨0, by simpa only [S.flow.map_zero_apply] using hz⟩
  obtain ⟨η, -, havoid⟩ :=
    MorseCancel.exists_smooth_path_avoiding_closed_image γ G hG hclosed hdim' (hnot x hxa)
      (hnot y hya)
  have hcross (t : unitInterval) : η t ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
    have hh := havoid t
    simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using hh
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let xL : { z : M // f z = a } := ⟨x, hxa⟩
  let yL : { z : M // f z = a } := ⟨y, hya⟩
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ :=
    Degree.FlowCancellation.exists_native_level_flow_cylinder hf hreg S.smooth S.flow S.integral
      (fun z hz => S.descent z (hreg z hz)) xL
  have hcont : Continuous (fun t : unitInterval => Φ.symm (η t)) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous η.continuous
      (fun t => htarget.symm ▸ hcross t)
  have hinverse (z : { w : M // f w = a }) : Φ.symm z.val = (z, 0) := by
    have hs : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hs
    rwa [he] at hi
  let ξ : Path x y :=
    { toFun := fun t => (Φ.symm (η t)).1.val
      continuous_toFun := continuous_subtype_val.comp (continuous_fst.comp hcont)
      source' := by
        rw [η.source]
        exact congrArg (fun z : { w : M // f w = a } × ℝ => z.1.val) (hinverse xL)
      target' := by
        rw [η.target]
        exact congrArg (fun z : { w : M // f w = a } × ℝ => z.1.val) (hinverse yL) }
  exact ⟨ξ, fun t => (Φ.symm (η t)).1.property⟩

theorem AdaptedWindows.pathConnectedSpace_regular_level_of_endpoint_dimensions {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [PathConnectedSpace M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancel.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) (z₀ : { z : M // f z = a }) :
    PathConnectedSpace { z : M // f z = a }
    where
  nonempty := ⟨z₀⟩
  joined x
    y :=
    (S.joinedIn_regular_level_of_endpoint_dimensions hf hreg hhigh hlow hdim x.property y.property
        (PathConnectedSpace.somePath x.val y.val)).joined_subtype

theorem AdaptedWindows.pathConnectedSpace_middle_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PathConnectedSpace M]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f p → 3 ≤ MorseCancel.nativeMorseIndex E f p)
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ 3)
    (z₀ : { z : M // f z = a }) : PathConnectedSpace { z : M // f z = a } :=
  S.pathConnectedSpace_regular_level_of_endpoint_dimensions hf hreg
    (fun p hp => by have hh := hhigh p hp; omega) hlow (by omega) z₀

theorem AdaptedWindows.pathConnectedSpace_index_three_upper_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (p : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancel.nativeMorseIndex E f p = 3)
    (z₀ : (S.data p).UpperLevel) : PathConnectedSpace (S.data p).UpperLevel := by
  apply S.pathConnectedSpace_middle_level hf hdim (S.data p).upper_regular (z₀ := z₀)
  · intro r hr
    have hpr : f p < f r := (S.toSurgeryWindows.value_lt_upper p).trans_le hr
    simpa only [hp] using horder p r hpr
  · intro r hr
    rcases lt_trichotomy (f r) (f p) with h | h | h
    · simpa only [hp] using horder r p h
    · have he : r = p := Subtype.ext (S.distinct r.property p.property h)
      rw [he, hp]
    · have hsep := S.separated p r h
      have hlow := S.toSurgeryWindows.lower_lt_value r
      exact ((not_lt_of_ge hr) (hsep.trans hlow)).elim

theorem Degree.MorseRearrangement.native_transverse_dimension_bound {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {f : X → N} {g : Y → N} {x : X} {y : Y}
    (ht : Smale.NativeTransversality.At I I' J f g x y) (hxy : g y = f x) :
    Module.finrank ℝ G ≤ Module.finrank ℝ D + Module.finrank ℝ Z := by
  let L : (D × Z) →L[ℝ] G := by
    exact (mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G)
  have hL : Function.Surjective L := ht hxy
  have hh := LinearMap.finrank_le_finrank_of_surjective (f := L.toLinearMap) hL
  simpa only [Module.finrank_prod] using hh

theorem Degree.MorseRearrangement.disjoint_ranges_of_native_transverse_dimension
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ D H}
    {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] {f : X → N} {g : Y → N}
    (ht : ∀ x y, Smale.NativeTransversality.At I I' J f g x y)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) :
    Disjoint (Set.range f) (Set.range g) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  exact (not_le_of_gt hdim) (native_transverse_dimension_bound (ht x y) (hy.trans hx.symm))

theorem Degree.MorseRearrangement.native_transverse_of_ignored_factor {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] {R H'' W : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [TopologicalSpace H'']
    {I'' : ModelWithCorners ℝ R H''} [TopologicalSpace W] [ChartedSpace H'' W] {f : X → N}
    {g : Y → N} {x : X} {y : Y} (w : W) (hf : MDifferentiableAt I J f x)
    (ht : Smale.NativeTransversality.At (I.prod I'') I' J (f ∘ Prod.fst) g (x, w) y) :
    Smale.NativeTransversality.At I I' J f g x y := by
  intro hxy
  have hsurj := ht hxy
  have hd :
    (mfderiv (I.prod I'') J (f ∘ Prod.fst) (x, w) : (D × R) →L[ℝ] G) =
      (mfderiv I J f x : D →L[ℝ] G).comp (ContinuousLinearMap.fst ℝ D R) := by
    rw [mfderiv_comp (x, w) hf mdifferentiableAt_fst, mfderiv_fst]
    rfl
  change
    Function.Surjective
      ((mfderiv (I.prod I'') J (f ∘ Prod.fst) (x, w) : (D × R) →L[ℝ] G).coprod
        (mfderiv I' J g y : Z →L[ℝ] G)) at hsurj
  rw [hd] at hsurj
  intro v
  obtain ⟨⟨⟨a, b⟩, c⟩, hh⟩ := hsurj v
  exact ⟨(a, c), hh⟩

theorem Smale.ChartMapPerturbation.exists_ambient_transverse_plateau
    {D Z G F H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N]
    [ChartedSpace K N] [T2Space N] [LindelofSpace (X × Y)]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {β : F → ℝ}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ c.target)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        ∃ e : Diffeomorph J J N N ∞,
          (∀ y, e y = Smale.SupportedDiffeomorph.bumpFamily c.symm β (a, y)) ∧
            (∀ y ∉ c.symm '' tsupport β, e y = y) ∧
              Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
                ∀ x,
                  f x ∈ c.source →
                    (β =ᶠ[𝓝 (c (f x))] fun _ => 1) →
                      ∀ y,
                        g y = e (f x) →
                          Function.Surjective
                            ((mfderiv I J (e ∘ f) x : D →L[ℝ] G).coprod
                              (mfderiv I' J g y : Z →L[ℝ] G)) := by
  let U : Set X := f ⁻¹' c.source
  let V : Set Y := g ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have hV : IsOpen V := c.open_source.preimage hg.continuous
  have hcf : ContMDiffOn I 𝓘(ℝ, F) ∞ (c ∘ f) U :=
    c.contMDiffOn_toFun.comp hf.contMDiffOn (fun _ hx => hx)
  have hcg : ContMDiffOn I' 𝓘(ℝ, F) ∞ (c ∘ g) V :=
    c.contMDiffOn_toFun.comp hg.contMDiffOn (fun _ hy => hy)
  have hdense := Smale.TransverseCoordinates.dense_native_translations hU hV hcf hcg hdim
  obtain ⟨δ, hδ, hdiff, -, hsource⟩ :=
    Smale.SupportedDiffeomorph.exists_radius_ambient_bumpFamily c.symm hβ hcompact hsupport
  obtain ⟨η, hη, hisotopy⟩ :=
    Smale.SupportedDiffeomorph.exists_radius_bumpFamily_isotopy c.symm hβ hcompact hsupport
  obtain ⟨a, ha, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε (lt_min hδ hη))
  have hn : ‖a‖ < Min.min ε (Min.min δ η) := by simpa only [dist_zero_left] using hnorm
  have haδ := (lt_min_iff.mp (lt_min_iff.mp hn).2).1
  have haη := (lt_min_iff.mp (lt_min_iff.mp hn).2).2
  obtain ⟨e, he⟩ := hdiff a haδ
  have hsrc := hsource a haδ
  refine ⟨a, (lt_min_iff.mp hn).1, e, he, ?_, hisotopy a haη e he, ?_⟩
  · intro y hy
    rw [he]
    exact Smale.SupportedDiffeomorph.bumpFamily_fixed_outside c.symm β a hy
  · intro x hfx hx y hxy
    have hnew : e (f x) ∈ c.source := by
      rw [he]
      exact Smale.SupportedDiffeomorph.bumpFamily_mem_target c.symm β a hsrc hfx
    have hgy : g y ∈ c.source := hxy ▸ hnew
    have hcfAt := hcf.contMDiffAt (hU.mem_nhds hfx)
    have hevent : c ∘ (e ∘ f) =ᶠ[𝓝 x] fun z => c (f z) + a := by
      filter_upwards [hU.mem_nhds hfx, hx.comp_tendsto hcfAt.continuousAt] with z hz hβz
      change β (c (f z)) = 1 at hβz
      change c (e (f z)) = c (f z) + a
      rw [he]
      have hh := Smale.SupportedDiffeomorph.bumpFamily_coordinates c.symm β a hsrc hz
      change
        c (Smale.SupportedDiffeomorph.bumpFamily c.symm β (a, f z)) =
          c (f z) + β (c (f z)) • a at hh
      exact hh.trans (by rw [hβz, one_smul])
    have hcross : (c ∘ g) y = (c ∘ f) x + a := by
      change c (g y) = c (f x) + a
      rw [hxy]
      exact hevent.eq_of_nhds
    have ht := ha x hfx y hgy hcross
    have hderiv := mfderiv_eq_of_translation_germ (hcfAt.mdifferentiableAt (by simp)) hevent
    apply
      transverse_of_chart c ((e.contMDiff.comp hf).mdifferentiableAt (by simp))
        (hg.mdifferentiableAt (by simp)) hxy hnew
    rw [hderiv]
    exact ht

structure Smale.NativeTransversality.Patch {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] (J : ModelWithCorners ℝ G K) [TopologicalSpace N]
    [ChartedSpace K N] (X : Type*) [TopologicalSpace X] where
  core : Set X
  core_compact : IsCompact core
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  cutoff : G → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ chart.target
  plateau : Set N
  plateau_open : IsOpen plateau
  plateau_source : plateau ⊆ chart.source
  plateau_one : ∀ y ∈ plateau, cutoff =ᶠ[𝓝 (chart y)] fun _ => 1

def Smale.NativeTransversality.Patch.Compatible {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] {X : Type*} [TopologicalSpace X]
    (p : Smale.NativeTransversality.Patch J X (N := N)) (f : X → N) : Prop :=
  Set.MapsTo f p.core p.plateau

theorem Smale.NativeTransversality.exists_patch_at {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] {X : Type*} [TopologicalSpace X] [FiniteDimensional ℝ G] [J.Boundaryless]
    [IsManifold J ∞ N] [CompactSpace X] [T2Space X] {f : X → N} (hf : Continuous f) (x : X) :
    ∃ p : Patch J X (N := N), p.Compatible f ∧ x ∈ interior p.core := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  have hcx : f x ∈ c.source := mem_extChartAt_source _
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source' hcx))
  obtain ⟨β, hβ, hsupport, W, hW, hcenter, -, hone⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed (K := {c (f x)}) (U :=
      Metric.ball (c (f x)) r) isClosed_singleton Metric.isOpen_ball
      (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  have hcompact : HasCompactSupport β :=
    (ProperSpace.isCompact_closedBall (c (f x)) r).of_isClosed_subset (isClosed_tsupport β)
      (hsupport.trans Metric.ball_subset_closedBall)
  let O : Set N := c.source ∩ c ⁻¹' W
  have hO : IsOpen O := c.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_source hW
  have hfx : f x ∈ O := ⟨hcx, hcenter (Set.mem_singleton _)⟩
  obtain ⟨C, hC, -, hxC, hCO⟩ :=
    exists_compact_closed_between (isCompact_singleton (x := x)) (hO.preimage hf)
      (Set.singleton_subset_iff.mpr hfx)
  let p : Patch J X (N := N) :=
    { core := C
      core_compact := hC
      chart := c
      cutoff := β
      cutoff_smooth := hβ
      cutoff_compact := hcompact
      cutoff_support := hsupport.trans hball
      plateau := O
      plateau_open := hO
      plateau_source := Set.inter_subset_left
      plateau_one := by
        intro y hy
        filter_upwards [hW.mem_nhds hy.2] with z hz
        exact hone hz }
  exact ⟨p, hCO, hxC (Set.mem_singleton x)⟩

theorem Smale.NativeTransversality.exists_patch_step {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] (p : ι → Patch J X (N := N)) (i : ι)
    {f : X → N} {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {C : Set X}
    (hC : IsCompact C) (htrans : ∀ x ∈ C, ∀ y, At I I' J f g x y) :
    ∃ e : Diffeomorph J J N N ∞,
      (∀ j, (p j).Compatible (e ∘ f)) ∧
        (∀ x ∈ C ∪ (p i).core, ∀ y, At I I' J (e ∘ f) g x y) ∧
          (∀ y ∉ (p i).chart.symm '' tsupport (p i).cutoff, e y = y) ∧
            Smale.SupportedDiffeomorph.IsotopicToIdentity e := by
  let A : G × X → N := fun q =>
    Smale.SupportedDiffeomorph.bumpFamily (p i).chart.symm (p i).cutoff (q.1, f q.2)
  have hkeep : ∀ᶠ a in 𝓝 (0 : G), ∀ j, (p j).Compatible (fun x => A (a, x)) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.SupportedDiffeomorph.eventually_bumpFamily_maps_compact_into_open (p i).chart.symm
        (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hf.continuous
        (p j).core_compact (p j).plateau_open (hcompatible j)
  obtain ⟨δ, hδ, -, hsmooth, -⟩ :=
    Smale.SupportedDiffeomorph.exists_radius_ambient_bumpFamily (p i).chart.symm
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support
  have hA : ContMDiffOn (𝓘(ℝ, G).prod I) J ∞ A (Metric.ball (0 : G) δ ×ˢ Set.univ) := by
    intro q hq
    have hsmall : ‖q.1‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hq.1
    have hpair :
      ContMDiffAt (𝓘(ℝ, G).prod I) (𝓘(ℝ, G).prod J) ∞ (fun r : G × X => (r.1, f r.2)) q :=
      contMDiffAt_fst.prodMk (hf.comp contMDiff_snd).contMDiffAt
    exact ((hsmooth (q.1, f q.2) hsmall).comp q hpair).contMDiffWithinAt
  have hzero : (fun x => A (0, x)) = f := by
    funext x
    exact Smale.SupportedDiffeomorph.bumpFamily_zero _ _ _
  have hregular :
    ∀ᶠ a in 𝓝 (0 : G), ∀ z ∈ C ×ˢ (Set.univ : Set Y), At I I' J (fun x => A (a, x)) g z.1 z.2 := by
    apply
      eventually_on_compact Metric.isOpen_ball hA hg hdim (hC.prod isCompact_univ)
        (Metric.mem_ball_self hδ)
    intro z hz
    rw [hzero]
    exact htrans z.1 hz.1 z.2
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp (hkeep.and hregular)
  obtain ⟨a, ha, e, he, hfixed, hisotopy, hnew⟩ :=
    Smale.ChartMapPerturbation.exists_ambient_transverse_plateau (p i).chart hf hg
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hdim hε
  have hgood :=
    hsmall
      (show a ∈ Metric.ball (0 : G) ε by simpa only [Metric.mem_ball, dist_zero_right] using ha)
  have heq : (fun x => A (a, x)) = e ∘ f := funext (fun x => (he (f x)).symm)
  refine ⟨e, ?_, ?_, hfixed, hisotopy⟩
  · intro j
    exact heq ▸ hgood.1 j
  · intro x hx y
    rcases hx with hx | hx
    · exact heq ▸ hgood.2 (x, y) ⟨hx, Set.mem_univ y⟩
    · intro hxy
      have hplateau := hcompatible i hx
      exact hnew x ((p i).plateau_source hplateau) ((p i).plateau_one _ hplateau) y hxy

theorem Smale.NativeTransversality.exists_finite_patch_diffeomorph {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] (p : ι → Patch J X (N := N)) {f : X → N}
    {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) (s : Finset ι) :
    ∃ e : Diffeomorph J J N N ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
        (∀ j, (p j).Compatible (e ∘ f)) ∧
          ∀ j ∈ s, ∀ x ∈ (p j).core, ∀ y, At I I' J (e ∘ f) g x y := by
  classical
    induction s using Finset.induction_on with
  |
    empty =>
    refine
      ⟨Diffeomorph.refl J N ∞, Smale.SupportedDiffeomorph.isotopicToIdentity_refl, hcompatible,
        ?_⟩
    intro j hj
    simp at hj
  | @insert i s _ ih =>
    obtain ⟨e₁, hiso₁, hc₁, ht₁⟩ := ih
    let C : Set X := ⋃ j ∈ s, (p j).core
    have hC : IsCompact C := s.isCompact_biUnion (fun j _ => (p j).core_compact)
    have htrans : ∀ x ∈ C, ∀ y, At I I' J (e₁ ∘ f) g x y := by
      intro x hx y
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      exact ht₁ j hj x hxj y
    obtain ⟨e₂, hc₂, ht₂, -, hiso₂⟩ :=
      exists_patch_step p i (e₁.contMDiff.comp hf) hg hc₁ hdim hC htrans
    refine ⟨e₁.trans e₂, hiso₁.trans hiso₂, hc₂, ?_⟩
    intro j hj x hx y
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact ht₂ x (Or.inr hx) y
    · exact ht₂ x (Or.inl (Set.mem_iUnion₂.mpr ⟨j, hjs, hx⟩)) y

theorem Smale.NativeTransversality.exists_ambient_transverse_diffeomorph
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [CompactSpace X] [T2Space X] {f : X → N}
    {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) :
    ∃ e : Diffeomorph J J N N ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧ ∀ x y, At I I' J (e ∘ f) g x y := by
  classical
  choose p hp hx using fun x : X => exists_patch_at (J := J) hf.continuous x
  have hcover : (Set.univ : Set X) ⊆ ⋃ x : X, interior (p x).core := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover (fun x : X => interior (p x).core)
      (fun _ => isOpen_interior) hcover
  obtain ⟨e, hisotopy, -, ht⟩ :=
    exists_finite_patch_diffeomorph (fun i : s => p i.1) hf hg (fun i => hp i.1) hdim Finset.univ
  refine ⟨e, hisotopy, ?_⟩
  intro x y
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ht ⟨i, hi⟩ (Finset.mem_univ _) x (interior_subset hxi) y

theorem Degree.MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) :
    ∃ e : Diffeomorph J J N N ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
        Disjoint (Set.range (e ∘ f)) (Set.range g) := by
  classical
  let d := Module.finrank ℝ G - (Module.finrank ℝ D + Module.finrank ℝ Z)
  let f' : X × Smale.Hemisphere.Sphere d → N := f ∘ Prod.fst
  have hf' : ContMDiff (I.prod (𝓡 d)) J ∞ f' := hf.comp contMDiff_fst
  have hdim' :
    Module.finrank ℝ (D × EuclideanSpace ℝ (Fin d)) + Module.finrank ℝ Z = Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    dsimp [d]
    omega
  obtain ⟨e, he, ht⟩ :=
    Smale.NativeTransversality.exists_ambient_transverse_diffeomorph hf' hg hdim'
  have htrans : ∀ x y, Smale.NativeTransversality.At I I' J (e ∘ f) g x y := by
    intro x y
    let w : Smale.Hemisphere.Sphere d := Smale.Hemisphere.point Bool.true ⟨0, by simp []⟩
    apply
      native_transverse_of_ignored_factor (I'' := 𝓡 d) w
        ((e.contMDiff.comp hf).mdifferentiable (by simp) x)
    exact ht (x, w) y
  exact ⟨e, he, disjoint_ranges_of_native_transverse_dimension htrans hdim⟩

end Mathoverflow1973
