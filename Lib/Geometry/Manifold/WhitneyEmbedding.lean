/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Analysis.ODE.SmoothFlow
import Lib.Geometry.Manifold.ChartedSpace.Transport
import Lib.Topology.Homotopy.CylinderHEP
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index

/-!
# The native Euclidean embedding of a compact manifold

Every compact smooth manifold modeled on a finite-dimensional normed space `E` embeds into
`EuclideanSpace ℝ (Fin e.ambientDimension)` with injective differential
(`NativeEuclideanEmbedding.*` — Lee Thm 6.15's Whitney embedding in the native form
used by the source development), with the tangent-space instances
(`tangentSpaceT2`, `tangentSpaceFiniteDimensional`), the tangent/normal decompositions
(`tangentImageEquiv`, `tangentNormalEquiv`, `contMDiff_normalProjection`), and the
partial-diffeomorphism inverse-function lemmas
(`exists_partialDiffeomorph_into_manifold`, `partialDiffeomorphOfInjectiveLocal`,
`exists_partialDiffeomorph_near_compact`).

## Main definitions and results

* `NativeEuclideanEmbedding` : the embedding structure.
* `NativeEuclideanEmbedding.exists_tubularNeighborhood_in_open_of_embedded_closedBall` :
  the tubular neighbourhood of an embedded closed ball (in Collar.lean's sibling block).

## References

* [John M. Lee, *Introduction to Smooth Manifolds*][lee13], Theorem 6.15

## Tags

Whitney embedding, tubular neighbourhood, partial diffeomorphism
-/



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

theorem ManifoldMorse.exists_separated_value_radii {X : Type*} {f : X → ℝ} {K : Set X}
    (hK : K.Finite) (hinj : Set.InjOn f K) :
    ∃ r : K → ℝ, (∀ p, 0 < r p) ∧ ∀ p q : K, f p < f q → f p + (r p) ^ 2 < f q - (r q) ^ 2 := by
  have hex :
    ∀ p : K,
      ∃ ρ > (0 : ℝ), ρ < 1 ∧ ∀ x ∈ K, f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p.val := by
    intro p
    exact exists_isolating_radius hK p.val (fun x hx hfx => hinj hx p.property hfx) zero_lt_one
  choose ρ hρ hρ₁ hisolated using hex
  refine ⟨fun p => ρ p / 2, fun p => half_pos (hρ p), ?_⟩
  intro p q hpq
  have hupper : f p + (ρ p) ^ 2 < f q := by
    apply lt_of_not_ge
    intro h
    have heq := hisolated p q.val q.property ⟨by nlinarith [sq_nonneg (ρ p)], h⟩
    exact (ne_of_lt hpq) (congrArg f heq).symm
  have hlower : f p < f q - (ρ q) ^ 2 := by
    apply lt_of_not_ge
    intro h
    have heq := hisolated q p.val p.property ⟨h, by nlinarith [sq_nonneg (ρ q)]⟩
    exact (ne_of_lt hpq) (congrArg f heq)
  nlinarith

theorem exists_partialDiffeomorph_into_manifold {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : D → M} {U : Set D}
    {x : D} (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ Set.EqOn f Φ Φ.source := by
  let c := modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) (f x)
  have hc : f x ∈ c.source := mem_extChartAt_source (f x)
  let V : Set D := U ∩ f ⁻¹' c.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU c.open_source
  have hxV : x ∈ V := ⟨hx, hc⟩
  have hcf : ContDiffOn ℝ ∞ (c ∘ f) V :=
    (c.contMDiffOn_toFun.comp (hf.mono Set.inter_subset_left) (fun _ hy => hy.2)).contDiffOn
  have hcinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (f x)).IsInvertible :=
    isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x))
  have hderiv : (fderiv ℝ (c ∘ f) x).IsInvertible := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp x (c.mdifferentiableAt (by simp) hc)
        ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact hcinv.comp hinv
  obtain ⟨d, hd, hdV, hdf⟩ := exists_partialDiffeomorph_of_contDiffOn hV hxV hcf hderiv
  have hdx : d x ∈ c.target := by
    rw [hdf]
    exact c.map_source' hc
  refine ⟨d.trans c.symm, ⟨hd, hdx⟩, fun y hy => (hdV hy.1).1, ?_⟩
  intro y hy
  change f y = c.symm (d y)
  rw [hdf]
  exact (c.left_inv' (hdV hy.1).2).symm

theorem isLocalDiffeomorphAt_of_contMDiffOn {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : D → M} {U : Set D}
    {x : D} (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f x := by
  obtain ⟨Φ, hxΦ, -, heq⟩ := exists_partialDiffeomorph_into_manifold hU hx hf hinv
  exact ⟨Φ, hxΦ, heq⟩

theorem exists_partialDiffeomorph_between_manifolds {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {H X : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [I.Boundaryless] [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] {f : X → M} {U : Set X} {x : X} (hU : IsOpen U)
    (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv I 𝓘(ℝ, E) f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ Set.EqOn f Φ Φ.source := by
  let c := modelChartPartialDiffeomorph (I := I) x
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c x ∈ c.target := c.map_source' hxc
  have hleft (y : X) (hy : y ∈ c.source) : c.symm (c y) = y := c.left_inv' hy
  let V : Set D := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hU
  have hcxV : c x ∈ V :=
    ⟨hcx, by
      change c.symm (c x) ∈ U
      rwa [hleft x hxc]⟩
  have hgf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (f ∘ c.symm) V :=
    hf.comp (c.contMDiffOn_invFun.mono Set.inter_subset_left) (fun _ hy => hy.2)
  have hcDiff : c.toOpenPartialHomeomorph.MDifferentiable I 𝓘(ℝ, D) :=
    ⟨c.mdifferentiableOn (by simp), c.symm.mdifferentiableOn (by simp)⟩
  have hci : (mfderiv 𝓘(ℝ, D) I c.symm (c x)).IsInvertible := ⟨hcDiff.symm.mfderiv hcx, rfl⟩
  have hderiv : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) (f ∘ c.symm) (c x)).IsInvertible := by
    have hfx := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hfc : MDifferentiableAt I 𝓘(ℝ, E) f (c.symm (c x)) := by
      simpa only [hleft x hxc] using hfx
    rw [mfderiv_comp (c x) hfc (c.symm.mdifferentiableAt (by simp) hcx), hleft x hxc]
    exact hinv.comp hci
  obtain ⟨d, hd, hdV, heq⟩ := exists_partialDiffeomorph_into_manifold hV hcxV hgf hderiv
  refine ⟨c.trans d, ⟨hxc, hd⟩, ?_, ?_⟩
  · intro y hy
    have hh := (hdV hy.2).2
    change c.symm (c y) ∈ U at hh
    rwa [hleft y hy.1] at hh
  · intro y hy
    have hh := heq hy.2
    change f (c.symm (c y)) = d (c y) at hh
    change f y = d (c y)
    simpa only [hleft y hy.1] using hh

theorem isLocalDiffeomorphAt_between_manifolds {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {H X : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [I.Boundaryless] [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] {f : X → M} {U : Set X} {x : X} (hU : IsOpen U)
    (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv I 𝓘(ℝ, E) f x).IsInvertible) : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ f x := by
  obtain ⟨Φ, hxΦ, -, heq⟩ := exists_partialDiffeomorph_between_manifolds hU hx hf hinv
  exact ⟨Φ, hxΦ, heq⟩

theorem exists_partialDiffeomorph_boundaryless {D E H H' X Y : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ D H}
    {J : ModelWithCorners ℝ E H'} [I.Boundaryless] [J.Boundaryless] [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [IsManifold J ∞ Y] {f : X → Y} {U : Set X} {x : X} (hU : IsOpen U) (hx : x ∈ U)
    (hf : ContMDiffOn I J ∞ f U) (hinv : (mfderiv I J f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph I J X Y ∞, x ∈ Φ.source ∧ Φ.source ⊆ U ∧ Set.EqOn f Φ Φ.source := by
  let c := modelChartPartialDiffeomorph (I := J) (f x)
  have hc : f x ∈ c.source := mem_extChartAt_source (f x)
  let V : Set X := U ∩ f ⁻¹' c.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU c.open_source
  have hxV : x ∈ V := ⟨hx, hc⟩
  have hcf : ContMDiffOn I 𝓘(ℝ, E) ∞ (c ∘ f) V :=
    c.contMDiffOn_toFun.comp (hf.mono Set.inter_subset_left) (fun _ hy => hy.2)
  have hci : (mfderiv J 𝓘(ℝ, E) c (f x)).IsInvertible :=
    isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x))
  have hderiv : (mfderiv I 𝓘(ℝ, E) (c ∘ f) x).IsInvertible := by
    rw [mfderiv_comp x (c.mdifferentiableAt (by simp) hc)
        ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact hci.comp hinv
  obtain ⟨d, hd, hdV, hdf⟩ := exists_partialDiffeomorph_between_manifolds hV hxV hcf hderiv
  have hdx : d x ∈ c.target := by
    have heq : d x = c (f x) := (hdf hd).symm
    rw [heq]
    exact c.map_source' hc
  refine ⟨d.trans c.symm, ⟨hd, hdx⟩, fun y hy => (hdV hy.1).1, ?_⟩
  intro y hy
  have heq : d y = c (f y) := (hdf hy.1).symm
  change f y = c.symm (d y)
  rw [heq]
  exact (c.left_inv' (hdV hy.1).2).symm

theorem isLocalDiffeomorphAt_boundaryless {D E H H' X Y : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ D H}
    {J : ModelWithCorners ℝ E H'} [I.Boundaryless] [J.Boundaryless] [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [IsManifold J ∞ Y] {f : X → Y} {U : Set X} {x : X} (hU : IsOpen U) (hx : x ∈ U)
    (hf : ContMDiffOn I J ∞ f U) (hinv : (mfderiv I J f x).IsInvertible) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  obtain ⟨Φ, hxΦ, -, heq⟩ := exists_partialDiffeomorph_boundaryless hU hx hf hinv
  exact ⟨Φ, hxΦ, heq⟩

def partialDiffeomorphOfInjectiveLocal {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [Nonempty X] [TopologicalSpace Y] [ChartedSpace H' Y] {f : X → Y}
    {U : Set X} (hU : IsOpen U) (hinj : Set.InjOn f U) (hloc : IsLocalDiffeomorphOn I J ∞ f U) :
    PartialDiffeomorph I J X Y ∞ := by
  let p := hinj.toPartialEquiv f U
  have htarget : IsOpen p.target := by
    change IsOpen (f '' U)
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hloc.isLocalHomeomorphOn.map_nhds_eq hx]
    exact Filter.image_mem_map (hU.mem_nhds hx)
  have hinverse : ContMDiffOn J I ∞ p.symm p.target := by
    intro y hy
    have hx : p.symm y ∈ U := p.map_target hy
    obtain ⟨φ, hφx, heq⟩ := hloc ⟨p.symm y, hx⟩
    have hφxy : φ (p.symm y) = y := (heq hφx).symm.trans (p.right_inv hy)
    have hφy : y ∈ φ.target := hφxy ▸ φ.map_source' hφx
    have hφyx : φ.symm y = p.symm y := by
      calc
        φ.symm y = φ.symm (φ (p.symm y)) := congrArg φ.symm hφxy.symm
        _ = p.symm y := φ.left_inv' hφx
    have hg : ContMDiffAt J I ∞ φ.symm y :=
      φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds hφy)
    have hNU : U ∈ 𝓝 (φ.symm y) := by
      rw [hφyx]
      exact hU.mem_nhds hx
    have hfg : p.symm =ᶠ[𝓝 y] φ.symm := by
      filter_upwards [φ.open_target.mem_nhds hφy, hg.continuousAt hNU] with z hz hzU
      have hfz : f (φ.symm z) = z := (heq (φ.map_target' hz)).trans (φ.right_inv' hz)
      exact (congrArg p.symm hfz.symm).trans (p.left_inv hzU)
    exact (hfg.contMDiffAt_iff.mpr hg).contMDiffWithinAt
  exact
    { p with
      open_source := hU
      open_target := htarget
      contMDiffOn_toFun := hloc.contMDiffOn
      contMDiffOn_invFun := hinverse }

theorem exists_partialDiffeomorph_near_compact {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [Nonempty X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    {f : X → Y} {K U : Set X} (hK : IsCompact K) (hinj : Set.InjOn f K)
    (hloc : ∀ x ∈ K, IsLocalDiffeomorphAt I J ∞ f x) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ Φ : PartialDiffeomorph I J X Y ∞, K ⊆ Φ.source ∧ Φ.source ⊆ U ∧ (Φ : X → Y) = f := by
  let R : Set X := {x | IsLocalDiffeomorphAt I J ∞ f x}
  have hR : IsOpen R := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨φ, hx, heq⟩
    exact Filter.mem_of_superset (φ.open_source.mem_nhds hx) (fun y hy => ⟨φ, hy, heq⟩)
  have hlocalinj : ∀ x ∈ K, ∃ V ∈ 𝓝 x, Set.InjOn f V := by
    intro x hx
    obtain ⟨φ, hφ, heq⟩ := hloc x hx
    exact ⟨φ.source, φ.open_source.mem_nhds hφ, heq.injOn_iff.mpr φ.toPartialEquiv.injOn⟩
  obtain ⟨V, hV, hKV, hVi⟩ :=
    hinj.exists_isOpen_superset hK (fun x hx => (hloc x hx).contMDiffAt.continuousAt) hlocalinj
  let W := (V ∩ R) ∩ U
  have hW : IsOpen W := (hV.inter hR).inter hU
  have hKW : K ⊆ W := fun x hx => ⟨⟨hKV hx, hloc x hx⟩, hKU hx⟩
  have hWi : Set.InjOn f W := hVi.mono (Set.inter_subset_left.trans Set.inter_subset_left)
  have hWloc : IsLocalDiffeomorphOn I J ∞ f W := fun x => x.property.1.2
  exact ⟨partialDiffeomorphOfInjectiveLocal hW hWi hWloc, hKW, Set.inter_subset_right, rfl⟩

def CollarHeight.heightChange {X : Type*} (h : X × ℝ → ℝ) (z : X × ℝ) : X × ℝ :=
  (z.1, h z)

theorem CollarHeight.heightChange_zero {X : Type*} {h : X × ℝ → ℝ}
    (hzero : ∀ x, h (x, 0) = 0) (x : X) : heightChange h (x, 0) = (x, 0) :=
  Prod.ext rfl (hzero x)

theorem CollarHeight.contMDiffOn_heightChange {D H X : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X]
    [ChartedSpace H X] {h : X × ℝ → ℝ} {U : Set (X × ℝ)}
    (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ (heightChange h) U :=
  contMDiff_fst.contMDiffOn.prodMk hh

theorem CollarHeight.mfderiv_height_zero {D H X : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X]
    [ChartedSpace H X] {h : X × ℝ → ℝ} {U : Set (X × ℝ)} (hU : IsOpen U)
    (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U) (hzero : ∀ x, h (x, 0) = 0) (x : X)
    (hx : (x, 0) ∈ U) (htime : HasDerivAt (fun t : ℝ => h (x, t)) 1 0) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) h (x, 0) = ContinuousLinearMap.snd ℝ D ℝ := by
  have hbase : (fun y : X => h (y, 0)) = fun _ => 0 := funext hzero
  have ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => h (x, t)) 0 = ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv, htime.hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext
    intro t
    simp only [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, mul_one]
  apply ContinuousLinearMap.ext
  intro v
  rw [mfderiv_prod_eq_add_apply ((hh.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)),
    hbase, mfderiv_const, ht]
  change (0 : ℝ) + v.2 = v.2
  exact zero_add _

theorem CollarHeight.mfderiv_heightChange_zero {D H X : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X]
    [ChartedSpace H X] {h : X × ℝ → ℝ} {U : Set (X × ℝ)} (hU : IsOpen U)
    (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U) (hzero : ∀ x, h (x, 0) = 0) (x : X)
    (hx : (x, 0) ∈ U) (htime : HasDerivAt (fun t : ℝ => h (x, t)) 1 0) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (heightChange h) (x, 0) =
      ContinuousLinearMap.id ℝ (D × ℝ) := by
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (fun z => (z.1, h z)) (x, 0) = _
  rw [mfderiv_prodMk mdifferentiableAt_fst
      ((hh.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)),
    mfderiv_fst, mfderiv_height_zero hU hh hzero x hx htime]
  rfl

theorem CollarHeight.exists_heightChangeChart {D H X : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X]
    [ChartedSpace H X] [CompleteSpace D] [I.Boundaryless] [IsManifold I ∞ X] [T2Space X]
    [CompactSpace X] [Nonempty X] {h : X × ℝ → ℝ} {U : Set (X × ℝ)} (hU : IsOpen U)
    (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U) (hzero : ∀ x, h (x, 0) = 0)
    (hsource : ∀ x, (x, 0) ∈ U) (htime : ∀ x, HasDerivAt (fun t : ℝ => h (x, t)) 1 0) :
    ∃ χ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (X × ℝ) (X × ℝ) ∞,
      (Set.univ : Set X) ×ˢ {(0 : ℝ)} ⊆ χ.source ∧
        χ.source ⊆ U ∧ (χ : X × ℝ → X × ℝ) = heightChange h := by
  let K : Set (X × ℝ) := Set.univ ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hinj : Set.InjOn (heightChange h) K := by
    rintro ⟨x, s⟩ ⟨-, hs⟩ ⟨y, t⟩ ⟨-, ht⟩ hxy
    have hs0 : s = 0 := hs
    have ht0 : t = 0 := ht
    subst s
    subst t
    rw [heightChange_zero hzero x, heightChange_zero hzero y] at hxy
    exact hxy
  have hloc :
    ∀ z ∈ K, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ (heightChange h) z := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    apply isLocalDiffeomorphAt_boundaryless hU (hsource x) (contMDiffOn_heightChange hh)
    rw [mfderiv_heightChange_zero hU hh hzero x (hsource x) (htime x)]
    exact ⟨ContinuousLinearEquiv.refl ℝ (D × ℝ), rfl⟩
  exact
    exists_partialDiffeomorph_near_compact hK hinj hloc hU
      (fun ⟨x, t⟩ hx => by
        have ht : t = 0 := hx.2
        simpa only [ht] using hsource x)

theorem RegularLevel.injective_mfderiv_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    Function.Injective
      (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x) := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let Φ := heightChart hf hreg x
  have hΦ :=
    Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (heightChart_mem_source hf hreg x))
  have hprojection : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Model E) ∞ (fun y : M => (Φ y).2) (x : M) :=
    contDiff_snd.contMDiff.contMDiffAt.comp (x : M) hΦ
  have hi :=
    (mdifferentiable_chart (I := 𝓘(ℝ, Model E)) x).mfderiv_injective
      (mem_chart_source (Model E) x)
  change
    Function.Injective
      (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ((fun y : M => (Φ y).2) ∘ Subtype.val) x) at hi
  rw [mfderiv_comp x (hprojection.mdifferentiableAt (by simp))
      ((RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))] at hi
  exact fun u v huv =>
    hi (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Model E) (fun y : M => (Φ y).2) (x : M)) huv)

theorem RegularLevel.height_derivative_comp_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    (mvfderiv 𝓘(ℝ, E) f (x : M)).comp
        (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x) =
      0 := by
  let _ := chartedSpace hf hreg
  have heq : f ∘ (Subtype.val : { x : M // f x = b } → M) = fun _ => b :=
    funext (fun y => y.property)
  have hc :=
    mfderiv_comp x (hf.mdifferentiableAt (by simp))
      ((RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))
  rw [heq, mfderiv_const] at hc
  exact hc.symm

theorem RegularLevel.range_mfderiv_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x).range =
      (mvfderiv 𝓘(ℝ, E) f (x : M)).ker := by
  let _ := chartedSpace hf hreg
  let A : Model E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  change A.range = L.ker
  have hsub : A.range ≤ L.ker := by
    rintro _ ⟨v, rfl⟩
    change L (A v) = 0
    exact congrArg (fun T => T v) (height_derivative_comp_inclusion hf hreg x)
  have hAi : Function.Injective A := injective_mfderiv_inclusion hf hreg x
  have hL : L ≠ 0 := hreg x x.property
  have hdim := finrank_kernel_add_one hL
  have hAr : Module.finrank ℝ A.range = Module.finrank ℝ E - 1 := by
    rw [LinearMap.finrank_range_of_inj hAi]
    exact finrank_euclideanSpace_fin
  apply Submodule.eq_of_le_of_finrank_eq hsub
  rw [hAr]
  omega

def RegularLevel.transverseTangentMap {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) (x : { x : M // f x = b })
    (v : E) : Model E × ℝ →L[ℝ] E :=
  letI := chartedSpace hf hreg
  (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x).coprod
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

theorem RegularLevel.bijective_transverseTangentMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) (x : { x : M // f x = b })
    (v : E) (hv : mvfderiv 𝓘(ℝ, E) f (x : M) v = 1) :
    Function.Bijective (transverseTangentMap hf hreg x v) := by
  let _ := chartedSpace hf hreg
  let A : Model E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  have hLA (u : Model E) : L (A u) = 0 :=
    congrArg (fun T => T u) (height_derivative_comp_inclusion hf hreg x)
  have hAi : Function.Injective A := injective_mfderiv_inclusion hf hreg x
  change L v = 1 at hv
  constructor
  · intro z w hzw
    change A z.1 + z.2 • v = A w.1 + w.2 • v at hzw
    have ht : z.2 = w.2 := by
      have h := congrArg L hzw
      simpa only [map_add, map_smul, hLA, hv, smul_eq_mul, mul_one, zero_add] using h
    rw [ht] at hzw
    exact Prod.ext (hAi (add_right_cancel hzw)) ht
  · intro w
    have hrem : w - L w • v ∈ L.ker := by
      change L (w - L w • v) = 0
      simp only [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
    have hrange : A.range = L.ker := range_mfderiv_inclusion hf hreg x
    rw [← hrange] at hrem
    obtain ⟨u, hu⟩ := hrem
    change A u = w - L w • v at hu
    refine ⟨(u, L w), ?_⟩
    change A u + L w • v = w
    rw [hu, sub_add_cancel]

theorem RegularLevel.surjective_normal_derivative_of_tangent_lift {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] {n : M → N} (x : { x : M // f x = b })
    (hn : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (x : M)) (R : N →L[ℝ] E)
    (hheight : (mvfderiv 𝓘(ℝ, E) f (x : M)).comp R = 0)
    (hnormal :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (x : M) : E →L[ℝ] N).comp R = ContinuousLinearMap.id ℝ N) :
    letI := chartedSpace hf hreg
    Function.Surjective
      (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, N) (n ∘ (Subtype.val : { x : M // f x = b } → M)) x) := by
  let _ := chartedSpace hf hreg
  let A : Model E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  let B : E →L[ℝ] N := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (x : M)
  change L.comp R = 0 at hheight
  change B.comp R = ContinuousLinearMap.id ℝ N at hnormal
  have hrange : A.range = L.ker := range_mfderiv_inclusion hf hreg x
  rw [mfderiv_comp x hn
      ((RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))]
  change Function.Surjective (B.comp A)
  intro z
  have hker : R z ∈ L.ker := by
    change L (R z) = 0
    exact congrArg (fun T : N →L[ℝ] ℝ => T z) hheight
  rw [← hrange] at hker
  obtain ⟨v, hv⟩ := hker
  change A v = R z at hv
  refine ⟨v, ?_⟩
  change B (A v) = z
  rw [hv]
  exact congrArg (fun T : N →L[ℝ] N => T z) hnormal

structure NativeEuclideanEmbedding (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] where
  ambientDimension : ℕ
  toFun : M → EuclideanSpace ℝ (Fin ambientDimension)
  smooth : ContMDiff 𝓘(ℝ, E) (𝓡 ambientDimension) ∞ toFun
  closedEmbedding : Topology.IsClosedEmbedding toFun
  injective_mfderiv : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) (𝓡 ambientDimension) toFun x)

theorem nonempty_nativeEuclideanEmbedding {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] :
    Nonempty (NativeEuclideanEmbedding E M) := by
  obtain ⟨n, f, hs, hc, hd⟩ := exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)
  exact ⟨⟨n, f, hs, hc, hd⟩⟩

theorem NativeEuclideanEmbedding.injective_mvfderiv {E : Type*} {M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    Function.Injective (mvfderiv 𝓘(ℝ, E) e.toFun x) :=
  (NormedSpace.fromTangentSpace (e.toFun x)).injective.comp (e.injective_mfderiv x)

def NativeEuclideanEmbedding.tangentImage {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (mvfderiv 𝓘(ℝ, E) e.toFun x).range

theorem NativeEuclideanEmbedding.finrank_tangentImage {E : Type*} {M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    Module.finrank ℝ (e.tangentImage x) = Module.finrank ℝ E := by
  exact LinearMap.finrank_range_of_inj (e.injective_mvfderiv x)

noncomputable def realAdjoint {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E)
    where
  toFun A := A.adjoint
  map_add' A B := map_add ContinuousLinearMap.adjoint A B
  map_smul' r A := by simp
  cont := ContinuousLinearMap.adjoint.continuous

noncomputable def gramOperator {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →L[ℝ] F) : E →L[ℝ] E :=
  A.adjoint.comp A

theorem gramOperator_isInvertible {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →L[ℝ] F) (hA : Function.Injective A) :
    (gramOperator A).IsInvertible := by
  have hG : Function.Injective (gramOperator A) := A.adjoint_comp_self_injective_iff.mpr hA
  let g := (LinearEquiv.ofInjectiveEndo (gramOperator A).toLinearMap hG).toContinuousLinearEquiv
  exact ⟨g, by ext v; rfl⟩

noncomputable def gramProjection {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →L[ℝ] F) : F →L[ℝ] F :=
  A.comp ((gramOperator A).inverse.comp A.adjoint)

theorem gramProjection_eq_starProjection {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →L[ℝ] F) (hA : Function.Injective A) :
    gramProjection A = A.range.starProjection := by
  ext v
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨(gramOperator A).inverse (A.adjoint v), rfl⟩
  · rw [A.orthogonal_range]
    change A.adjoint (v - A ((gramOperator A).inverse (A.adjoint v))) = 0
    rw [map_sub]
    change A.adjoint v - gramOperator A ((gramOperator A).inverse (A.adjoint v)) = 0
    rw [(gramOperator_isInvertible A hA).self_apply_inverse, sub_self]

theorem contMDiffAt_gramProjection {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    {A : M → E →L[ℝ] F} {x : M} (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ A x)
    (hinj : Function.Injective (A x)) :
    ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun y ↦ gramProjection (A y)) x := by
  have hadj : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] E) ∞ (fun y ↦ (A y).adjoint) x :=
    (realAdjoint.contDiff.contMDiff.contMDiffAt).comp x hA
  have hgram : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun y ↦ gramOperator (A y)) x := hadj.clm_comp hA
  have hinverse : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun y ↦ (gramOperator (A y)).inverse) x :=
    ContDiffAt.comp_contMDiffAt (f := fun y ↦ gramOperator (A y)) (x := x)
      (gramOperator_isInvertible (A x) hinj).contDiffAt_map_inverse hgram
  exact hA.clm_comp (hinverse.clm_comp hadj)

def NativeEuclideanEmbedding.localDifferential {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : NativeEuclideanEmbedding E M) (x₀ : M) :
    M → E →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  inTangentCoordinates 𝓘(ℝ, E) (𝓡 e.ambientDimension) id e.toFun
    (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun) x₀

theorem NativeEuclideanEmbedding.contMDiffAt_localDifferential {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x₀ : M) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)) ∞
      (e.localDifferential x₀) x₀ :=
  e.smooth.contMDiffAt.mfderiv_const (by simp)

theorem NativeEuclideanEmbedding.localDifferential_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : NativeEuclideanEmbedding E M) (x₀ y : M) :
    e.localDifferential x₀ y =
      (mvfderiv 𝓘(ℝ, E) e.toFun y).comp
        ((FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ y) := by
  simp only [localDifferential, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space]
  rfl

private theorem NativeEuclideanEmbedding.localFiberMap_bijective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    Function.Bijective ((FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ y) := by
  have hy' : y ∈ (FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  rw [← Bundle.Trivialization.symm_continuousLinearEquivAt_eq _ hy']
  exact ContinuousLinearEquiv.bijective _

theorem NativeEuclideanEmbedding.localDifferential_injective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x₀ y : M)
    (hy : y ∈ (chartAt E x₀).source) : Function.Injective (e.localDifferential x₀ y) := by
  rw [e.localDifferential_eq]
  exact (e.injective_mvfderiv y).comp (localFiberMap_bijective x₀ y hy).1

theorem NativeEuclideanEmbedding.localDifferential_range {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) (x₀ y : M)
    (hy : y ∈ (chartAt E x₀).source) : (e.localDifferential x₀ y).range = e.tangentImage y := by
  rw [e.localDifferential_eq]
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearMap.range_eq_top.mpr (localFiberMap_bijective x₀ y hy).2

def NativeEuclideanEmbedding.tangentProjection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  (e.tangentImage x).starProjection

theorem NativeEuclideanEmbedding.contMDiff_tangentProjection {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M) [FiniteDimensional ℝ E] :
    ContMDiff 𝓘(ℝ, E)
      𝓘(ℝ,
        EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
      ∞ e.tangentProjection := by
  let φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  intro x
  let A (y : M) := (e.localDifferential x y).comp φ.toContinuousLinearMap
  have hs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, _ →L[ℝ] _) ∞ A x :=
    (e.contMDiffAt_localDifferential x).clm_comp contMDiffAt_const
  have hi (y : M) (hy : y ∈ (chartAt E x).source) : Function.Injective (A y) :=
    (e.localDifferential_injective x y hy).comp φ.injective
  have hr (y : M) (hy : y ∈ (chartAt E x).source) : (A y).range = e.tangentImage y := by
    calc
      (A y).range = (e.localDifferential x y).range :=
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
      _ = e.tangentImage y := e.localDifferential_range x y hy
  have h := contMDiffAt_gramProjection hs (hi x (mem_chart_source _ _))
  have heq : e.tangentProjection =ᶠ[𝓝 x] (fun y => gramProjection (A y)) := by
    filter_upwards [chart_source_mem_nhds E x] with y hy
    simpa only [tangentProjection, hr y hy] using
      (gramProjection_eq_starProjection _ (hi y hy)).symm
  exact heq.contMDiffAt_iff.mpr h

def NativeEuclideanEmbedding.normalFiber {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (e.tangentImage x)ᗮ

def NativeEuclideanEmbedding.normalProjection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  (e.normalFiber x).starProjection

theorem NativeEuclideanEmbedding.normalProjection_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    e.normalProjection x = 1 - e.tangentProjection x :=
  Submodule.starProjection_orthogonal' (e.tangentImage x)

theorem NativeEuclideanEmbedding.range_normalProjection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    (e.normalProjection x).range = e.normalFiber x :=
  (e.normalFiber x).range_starProjection

theorem NativeEuclideanEmbedding.normalProjection_idempotent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) : IsIdempotentElem (e.normalProjection x) :=
  (e.normalFiber x).isIdempotentElem_starProjection

theorem NativeEuclideanEmbedding.finrank_tangent_add_normal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) (x : M) :
    Module.finrank ℝ E + Module.finrank ℝ (e.normalFiber x) = e.ambientDimension := by
  calc
    Module.finrank ℝ E + Module.finrank ℝ (e.normalFiber x) =
        Module.finrank ℝ (e.tangentImage x) + Module.finrank ℝ (e.tangentImage x)ᗮ :=
      congrArg (fun n => n + Module.finrank ℝ (e.normalFiber x)) (e.finrank_tangentImage x).symm
    _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
      (e.tangentImage x).finrank_add_finrank_orthogonal
    _ = e.ambientDimension := finrank_euclideanSpace_fin

theorem NativeEuclideanEmbedding.tangentSpaceT2 {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (x : M) :
    T2Space (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (T2Space E)

attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2 in
theorem NativeEuclideanEmbedding.tangentSpaceFiniteDimensional {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2
attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2
    NativeEuclideanEmbedding.tangentSpaceFiniteDimensional in
def NativeEuclideanEmbedding.tangentImageEquiv {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) [FiniteDimensional ℝ E] (x : M) :
    TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] e.tangentImage x :=
  (LinearEquiv.ofInjective (mvfderiv 𝓘(ℝ, E) e.toFun x).toLinearMap
      (e.injective_mvfderiv x)).toContinuousLinearEquiv

attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2
attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2
    NativeEuclideanEmbedding.tangentSpaceFiniteDimensional in
def NativeEuclideanEmbedding.tangentNormalEquiv {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) [FiniteDimensional ℝ E] (x : M) :
    (TangentSpace 𝓘(ℝ, E) x × e.normalFiber x) ≃L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  ((LinearEquiv.prodCongr (e.tangentImageEquiv x).toLinearEquiv
          (LinearEquiv.refl ℝ (e.normalFiber x))).trans
      ((e.tangentImage x).prodEquivOfIsCompl (e.normalFiber x)
        (e.tangentImage x).isCompl_orthogonal)).toContinuousLinearEquiv

attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2
attribute [local instance] NativeEuclideanEmbedding.tangentSpaceT2
    NativeEuclideanEmbedding.tangentSpaceFiniteDimensional in
theorem NativeEuclideanEmbedding.contMDiff_normalProjection {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : NativeEuclideanEmbedding E M) [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] :
    ContMDiff 𝓘(ℝ, E)
      𝓘(ℝ,
        EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
      ∞ e.normalProjection := by
  have heq : e.normalProjection = fun x => 1 - e.tangentProjection x :=
    funext e.normalProjection_eq
  rw [heq]
  exact contMDiff_const.sub e.contMDiff_tangentProjection
end Mathoverflow1973
