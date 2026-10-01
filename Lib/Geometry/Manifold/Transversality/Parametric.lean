/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Transversality.RegularValues
public import Lib.Geometry.Manifold.Transversality.Transverse
/-!
# Transversality after a generic translation

For smooth maps `f : X → F` and `g : Y → F` into a finite-dimensional vector space with
`dim X + dim Y = dim F`, the translations `a` for which `f` and `g` fail to be transverse along
`g y = f x + a` form a Haar-null set, hence the good translations are dense. This is the
parametric transversality theorem for the family of translations, proved by Sard's theorem applied
to the difference map `(x, y) ↦ g y - f x`.

## Main results

* `TransverseCoordinates.exists_null_exceptional_native_translations`
* `TransverseCoordinates.dense_native_translations`

## References

* [V. Guillemin, A. Pollack, *Differential Topology*][gp74], §2.3 (transversality theorem).
* [M. Hirsch, *Differential Topology*][hirsch76], Ch. 3.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


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
