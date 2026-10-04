/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Transversality.RegularValues
/-!
# Transversality of two maps at a pair of points

The transversality relation `f ⋔ g` at `(x, y)`: whenever `g y = f x`, the coproduct
`d f_x ⊕ d g_y` of the two derivatives is surjective (Guillemin–Pollack, §2.3). It is described in
a chart of the target by the surjectivity of the derivative of the difference
`(x, y) ↦ c (g y) - c (f x)`, it is an open condition in a smooth family of maps, it persists over a
compact set under small changes of the parameter, and it is invariant under a diffeomorphism of the
target.

## Main definitions and results

* `NativeTransversality.At` : the relation `f ⋔ g` at `(x, y)`.
* `NativeTransversality.at_iff_chart_difference`, `NativeTransversality.isOpen_at_family`,
  `NativeTransversality.eventually_on_compact`,
  `TransverseGerms.native_transversality_partial_diffeomorph_iff`.

## References

* [V. Guillemin, A. Pollack, *Differential Topology*][gp74], §2.3.
* [M. Hirsch, *Differential Topology*][hirsch76], Ch. 3.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


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
