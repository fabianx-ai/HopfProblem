/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Collar.Tubular
public import Lib.Geometry.Manifold.Collar.RangeTransport

/-!
# Tubular neighbourhoods of an embedded closed ball

Let `f : D → M` be smooth, injective on the closed unit ball of `D` and immersive there, with
`dim D + n = dim M`, `M` compact. Then `f` extends to a diffeomorphism `Φ` from an open
neighbourhood of `closedBall 0 1 × closedBall 0 ε` in `D × ℝⁿ` onto an open subset of `M` with
`Φ (x, 0) = f x`, and the image may be taken inside any given open set containing
`f (closedBall 0 1)`: the tubular neighbourhood theorem for an embedded disc, whose normal
bundle is trivial (Lee, *Introduction to Smooth Manifolds*, Thm 6.24; Hirsch, *Differential
Topology*, Ch. 4, §5).

The construction embeds `M` in Euclidean space, takes the normal space of the disc inside the
tangent space of `M` (`NativeEuclideanEmbedding.diskNormalSpace`), frames it smoothly near the
closed ball (`exists_smooth_normalFrame_near_closedBall`), displaces along the frame
(`DiskFraming.displacement`) and retracts back to `M`
(`NativeEuclideanEmbedding.SmoothRetraction.diskCoordinates`).

## Main results

* `NativeEuclideanEmbedding.SmoothRetraction.exists_diskTubularNeighborhood`
* `exists_tubularNeighborhood_in_open_of_embedded_closedBall`

## References

* [John M. Lee, *Introduction to Smooth Manifolds*][lee13], Thm 6.24

## Tags

tubular neighbourhood, embedded disc, normal frame
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

@[expose] public noncomputable section

/-! ### Orthogonal projections -/

/-- The star projection onto the orthogonal complement. -/
theorem DiskFraming.starProjection_orthogonal_inf_eq_sub {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {U V : Submodule ℝ F} (h : U ≤ V) :
    (Uᗮ ⊓ V).starProjection = V.starProjection - U.starProjection := by
  ext x
  change (Uᗮ ⊓ V).starProjection x = V.starProjection x - U.starProjection x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · refine ⟨?_, V.sub_mem (V.starProjection_apply_mem x) (h (U.starProjection_apply_mem x))⟩
    rw [← U.ker_starProjection]
    change U.starProjection (V.starProjection x - U.starProjection x) = 0
    rw [map_sub]
    have hc : U.starProjection (V.starProjection x) = U.starProjection x :=
      congrArg (fun A : F →L[ℝ] F => A x) (Submodule.starProjection_comp_starProjection_of_le h)
    rw [hc, Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x), sub_self]
  · have h₁ : x - V.starProjection x ∈ (Uᗮ ⊓ V)ᗮ :=
      Submodule.orthogonal_le inf_le_right (V.sub_starProjection_mem_orthogonal x)
    have h₂ : U.starProjection x ∈ (Uᗮ ⊓ V)ᗮ :=
      Submodule.orthogonal_le inf_le_left
        (U.le_orthogonal_orthogonal (U.starProjection_apply_mem x))
    convert (Uᗮ ⊓ V)ᗮ.add_mem h₁ h₂ using 1
    abel

/-! ### The disk normal bundle -/

/-- The tangent image of a disk under the embedding derivative. -/
def NativeEuclideanEmbedding.diskTangentImage {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M) (f : D → M) (x : D) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (fderiv ℝ (e.toFun ∘ f) x).range

/-- The normal space of the disk embedding. -/
def NativeEuclideanEmbedding.diskNormalSpace {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M) (f : D → M) (x : D) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (e.diskTangentImage f x)ᗮ ⊓ e.tangentImage (f x)

/-- The derivative of the composed embedding. -/
theorem NativeEuclideanEmbedding.fderiv_comp_eq {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (x : D) :
    fderiv ℝ (e.toFun ∘ f) x =
      (mvfderiv 𝓘(ℝ, E) e.toFun (f x)).comp (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x) := by
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp x (e.smooth.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  rfl

/-- The disk tangent image is contained in the tangent space. -/
theorem NativeEuclideanEmbedding.diskTangentImage_le {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (x : D) :
    e.diskTangentImage f x ≤ e.tangentImage (f x) := by
  rw [diskTangentImage, e.fderiv_comp_eq hf x]
  exact LinearMap.range_comp_le_range _ _

/-- The composed derivative is injective. -/
theorem NativeEuclideanEmbedding.injective_fderiv_comp {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M)
    {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    Function.Injective (fderiv ℝ (e.toFun ∘ f) x) := by
  rw [e.fderiv_comp_eq hf x]
  exact (e.injective_mvfderiv (f x)).comp hi

/-- The disk tangent and normal ranks sum to the dimension. -/
theorem NativeEuclideanEmbedding.finrank_diskTangent_add_normal {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] (e : NativeEuclideanEmbedding E M)
    {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    Module.finrank ℝ D + Module.finrank ℝ (e.diskNormalSpace f x) = Module.finrank ℝ E := by
  have hd : Module.finrank ℝ (e.diskTangentImage f x) = Module.finrank ℝ D :=
    LinearMap.finrank_range_of_inj (e.injective_fderiv_comp hf hi)
  calc
    Module.finrank ℝ D + Module.finrank ℝ (e.diskNormalSpace f x) =
        Module.finrank ℝ (e.diskTangentImage f x) + Module.finrank ℝ (e.diskNormalSpace f x) :=
      congrArg (fun n => n + Module.finrank ℝ (e.diskNormalSpace f x)) hd.symm
    _ = Module.finrank ℝ (e.tangentImage (f x)) :=
      (Submodule.finrank_add_inf_finrank_orthogonal (e.diskTangentImage_le hf x))
    _ = Module.finrank ℝ E := e.finrank_tangentImage (f x)

/-- The projection onto the disk normal space. -/
def NativeEuclideanEmbedding.diskNormalProjection {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M)
    (f : D → M) (x : D) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.tangentProjection (f x) - gramProjection (fderiv ℝ (e.toFun ∘ f) x)

/-- The disk normal projection computes the orthogonal component. -/
theorem NativeEuclideanEmbedding.diskNormalProjection_eq {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    (e : NativeEuclideanEmbedding E M) {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {x : D} (hi : Function.Injective (fderiv ℝ (e.toFun ∘ f) x)) :
    e.diskNormalProjection f x = (e.diskNormalSpace f x).starProjection := by
  rw [diskNormalProjection, gramProjection_eq_starProjection _ hi]
  exact (DiskFraming.starProjection_orthogonal_inf_eq_sub (e.diskTangentImage_le hf x)).symm

/-- The disk normal projection is smooth. -/
theorem NativeEuclideanEmbedding.contDiffOn_diskNormalProjection {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) :
    ContDiffOn ℝ ∞ (e.diskNormalProjection f)
      {x | Function.Injective (fderiv ℝ (e.toFun ∘ f) x)} := by
  have hs : ContDiff ℝ ∞ (e.toFun ∘ f) := (e.smooth.comp hf).contDiff
  have hd : ContDiff ℝ ∞ (fderiv ℝ (e.toFun ∘ f)) := (contDiff_infty_iff_fderiv.mp hs).2
  have hT : ContDiff ℝ ∞ (fun x => e.tangentProjection (f x)) :=
    (e.contMDiff_tangentProjection.comp hf).contDiff
  intro x hx
  have hp : ContDiffAt ℝ ∞ (e.diskNormalProjection f) x :=
    hT.contDiffAt.sub (contMDiffAt_gramProjection hd.contMDiff.contMDiffAt hx).contDiffAt
  exact hp.contDiffWithinAt

/-- An open domain for the disk normal projection exists. -/
theorem NativeEuclideanEmbedding.exists_open_diskNormalProjection {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D}
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    ∃ U : Set D,
      IsOpen U ∧
        K ⊆ U ∧
          ContDiffOn ℝ ∞ (e.diskNormalProjection f) U ∧
            ∀ x ∈ U, e.diskNormalProjection f x = (e.diskNormalSpace f x).starProjection := by
  have hs : ContDiff ℝ ∞ (e.toFun ∘ f) := (e.smooth.comp hf).contDiff
  have hd : ContDiff ℝ ∞ (fderiv ℝ (e.toFun ∘ f)) := (contDiff_infty_iff_fderiv.mp hs).2
  refine
    ⟨{x | Function.Injective (fderiv ℝ (e.toFun ∘ f) x)},
      ContinuousLinearMap.isOpen_injective.preimage hd.continuous, fun x hx =>
      e.injective_fderiv_comp hf (hi x hx), e.contDiffOn_diskNormalProjection hf, ?_⟩
  exact fun _ hx => e.diskNormalProjection_eq hf hx

/-! ### Normal frames near a closed ball -/

/-- A smooth normal frame exists near a closed ball. -/
theorem NativeEuclideanEmbedding.exists_smooth_normalFrame_near_closedBall {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hi : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) :
    ∃ V : Set D,
      IsOpen V ∧
        Metric.closedBall (0 : D) 1 ⊆ V ∧
          ∃ A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension),
            ContDiffOn ℝ ∞ A V ∧
              ∀ x ∈ V, Function.Injective (A x) ∧ (A x).range = e.diskNormalSpace f x := by
  obtain ⟨U, hU, hKU, hsP, hP⟩ := e.exists_open_diskNormalProjection hf hi
  have hidem : ∀ x ∈ U, IsIdempotentElem (e.diskNormalProjection f x) := by
    intro x hx
    rw [hP x hx]
    exact (e.diskNormalSpace f x).isIdempotentElem_starProjection
  obtain ⟨V, hV, hKV, hVU, A, hA, hAi⟩ :=
    DiskFraming.exists_smooth_frame_on_neighborhood_closedBall hU hKU
      (e.diskNormalProjection f) hidem hsP
  have hz : (0 : D) ∈ Metric.closedBall (0 : D) 1 := Metric.mem_closedBall_self zero_le_one
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
    _ = e.diskNormalSpace f x := by rw [hP x (hVU hx), Submodule.range_starProjection]

/-! ### Disk framings and displacement -/

/-- The splitting of the ambient space into range and normal parts. -/
def DiskFraming.normalSplitEquiv {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : D →L[ℝ] F) (A : Z →L[ℝ] F)
    {V : Submodule ℝ F} (hL : Function.Injective L) (hA : Function.Injective A)
    (hLV : L.range ≤ V) (hAr : A.range = L.rangeᗮ ⊓ V) : (D × Z) ≃L[ℝ] V := by
  let a : D × Z →ₗ[ℝ] F := L.toLinearMap.coprod A.toLinearMap
  have har : a.range = V := by
    rw [LinearMap.range_coprod, hAr]
    exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hLV
  have had : Disjoint L.range A.range := by
    rw [hAr]
    exact L.range.orthogonal_disjoint.mono_right inf_le_left
  have hai : Function.Injective a := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ had,
      LinearMap.ker_eq_bot.mpr hL, LinearMap.ker_eq_bot.mpr hA, Submodule.prod_bot]
  let b : D × Z →ₗ[ℝ] V := a.codRestrict V (fun q => har ▸ LinearMap.mem_range_self a q)
  have hbi : Function.Injective b := fun _ _ h => hai (congrArg Subtype.val h)
  have hbs : Function.Surjective b := by
    intro v
    have hv : (v : F) ∈ a.range := har.symm ▸ v.property
    obtain ⟨q, hq⟩ := hv
    exact ⟨q, Subtype.ext hq⟩
  exact (LinearEquiv.ofBijective b ⟨hbi, hbs⟩).toContinuousLinearEquiv

/-- The tangent-plus-normal splitting of the disk embedding. -/
def NativeEuclideanEmbedding.diskTangentNormalEquiv {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M)
    {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    (hA : Function.Injective A) (hAr : A.range = e.diskNormalSpace f x) :
    (D × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] e.tangentImage (f x) :=
  DiskFraming.normalSplitEquiv (fderiv ℝ (e.toFun ∘ f) x) A (e.injective_fderiv_comp hf hi)
    hA (e.diskTangentImage_le hf x) hAr

/-- The displacement of a framed disk along the normal frame. -/
def DiskFraming.displacement {D Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (H : D → F) (A : D → Z →L[ℝ] F) (p : D × Z) : F :=
  H p.1 + A p.1 p.2

/-- The displacement at zero is the disk point. -/
theorem DiskFraming.displacement_zero {D Z F : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] (H : D → F) (A : D → Z →L[ℝ] F)
    (x : D) : displacement H A (x, 0) = H x := by simp [displacement]

/-- The displacement is smooth. -/
theorem DiskFraming.contDiffOn_displacement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {H : D → F} {A : D → Z →L[ℝ] F} {V : Set D} (hH : ContDiff ℝ ∞ H)
    (hA : ContDiffOn ℝ ∞ A V) : ContDiffOn ℝ ∞ (displacement H A) (V ×ˢ Set.univ) :=
  (hH.comp contDiff_fst).contDiffOn.add
    ((hA.comp contDiffOn_fst (fun _ hp => hp.1)).clm_apply contDiffOn_snd)

/-- The displacement's derivative at zero. -/
theorem DiskFraming.hasFDerivAt_displacement_zero {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {H : D → F} {A : D → Z →L[ℝ] F} {x : D} (hH : ContDiffAt ℝ ∞ H x)
    (hA : ContDiffAt ℝ ∞ A x) :
    HasFDerivAt (displacement H A) ((fderiv ℝ H x).coprod (A x)) (x, 0) := by
  have hfst : HasFDerivAt (Prod.fst : D × Z → D) (ContinuousLinearMap.fst ℝ D Z) (x, 0) :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : D × Z → Z) (ContinuousLinearMap.snd ℝ D Z) (x, 0) :=
    hasFDerivAt_snd
  have h₁ :
    HasFDerivAt (fun p : D × Z => H p.1) ((fderiv ℝ H x).comp (ContinuousLinearMap.fst ℝ D Z))
      (x, 0) :=
    (hH.differentiableAt (by simp)).hasFDerivAt.comp (x, 0) hfst
  have h₂ :
    HasFDerivAt (fun p : D × Z => A p.1) ((fderiv ℝ A x).comp (ContinuousLinearMap.fst ℝ D Z))
      (x, 0) :=
    (hA.differentiableAt (by simp)).hasFDerivAt.comp (x, 0) hfst
  have h := h₁.add (h₂.clm_apply hsnd)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro q
  change fderiv ℝ H x q.1 + (A x q.2 + (fderiv ℝ A x q.1) 0) = fderiv ℝ H x q.1 + A x q.2
  rw [map_zero, add_zero]

/-! ### Disk coordinates of a retraction -/

/-- Disk coordinates of a smooth retraction. -/
def NativeEuclideanEmbedding.SmoothRetraction.diskCoordinates {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)) :
    D × EuclideanSpace ℝ (Fin n) → M :=
  r.toFun ∘ DiskFraming.displacement (e.toFun ∘ f) A

/-- The domain of the disk coordinates. -/
def NativeEuclideanEmbedding.SmoothRetraction.diskCoordinateDomain {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    (V : Set D) : Set (D × EuclideanSpace ℝ (Fin n)) :=
  (V ×ˢ Set.univ) ∩ DiskFraming.displacement (e.toFun ∘ f) A ⁻¹' r.domain

/-- The disk coordinates at zero. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.diskCoordinates_zero {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)) (x : D) :
    r.diskCoordinates f A (x, 0) = f x := by
  rw [diskCoordinates, Function.comp_apply, DiskFraming.displacement_zero]
  exact r.retract (f x)

/-- The disk coordinate domain is open. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.isOpen_diskCoordinateDomain
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {V : Set D}
    (hV : IsOpen V) (hA : ContDiffOn ℝ ∞ A V) : IsOpen (r.diskCoordinateDomain f A V) := by
  have hc :=
    (DiskFraming.contDiffOn_displacement (e.smooth.comp hf).contDiff hA).continuousOn
  exact hc.isOpen_inter_preimage (hV.prod isOpen_univ) r.open_domain

/-- Zero lies in the disk coordinate domain. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.zero_mem_diskCoordinateDomain
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ}
    (f : D → M) (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    {V : Set D} {x : D} (hx : x ∈ V) : (x, 0) ∈ r.diskCoordinateDomain f A V := by
  refine ⟨⟨hx, Set.mem_univ _⟩, ?_⟩
  change DiskFraming.displacement (e.toFun ∘ f) A (x, 0) ∈ r.domain
  rw [DiskFraming.displacement_zero]
  exact r.contains ⟨f x, rfl⟩

/-- The disk coordinates are smooth. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.contMDiffOn_diskCoordinates
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {V : Set D}
    (hA : ContDiffOn ℝ ∞ A V) :
    ContMDiffOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ (r.diskCoordinates f A)
      (r.diskCoordinateDomain f A V) :=
  r.smooth.comp
    ((DiskFraming.contDiffOn_displacement (e.smooth.comp hf).contDiff hA).contMDiffOn.mono
      Set.inter_subset_left)
    (fun _ hp => hp.2)

/-- The disk coordinates' derivative at zero. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.mfderiv_diskCoordinates_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {x : D}
    (hA : ContDiffAt ℝ ∞ A x) :
    mfderiv 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (r.diskCoordinates f A) (x, 0) =
      (mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun (f x))).comp
        ((fderiv ℝ (e.toFun ∘ f) x).coprod (A x)) := by
  have hd :=
    DiskFraming.hasFDerivAt_displacement_zero (e.smooth.comp hf).contDiff.contDiffAt hA
  have hr :
    MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun
      (DiskFraming.displacement (e.toFun ∘ f) A (x, 0)) := by
    rw [DiskFraming.displacement_zero]
    exact
      (r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨f x, rfl⟩))).mdifferentiableAt
        (by simp)
  rw [diskCoordinates, mfderiv_comp (x, 0) hr hd.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, hd.fderiv, DiskFraming.displacement_zero]
  rfl

/-- The disk coordinates' derivative is invertible at zero. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.isInvertible_mfderiv_diskCoordinates_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {n : ℕ} {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {x : D}
    (hA : ContDiffAt ℝ ∞ A x) (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hAi : Function.Injective (A x)) (hAr : (A x).range = e.diskNormalSpace f x) :
    (mfderiv 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (r.diskCoordinates f A)
        (x, 0)).IsInvertible := by
  let L := e.diskTangentNormalEquiv hf hi (A x) hAi hAr
  let T := L.trans (e.tangentImageEquiv (f x)).symm
  refine ⟨T, ?_⟩
  apply ContinuousLinearMap.ext
  intro q
  rw [r.mfderiv_diskCoordinates_zero hf hA]
  apply e.injective_mvfderiv (f x)
  have hleft := congrArg Subtype.val ((e.tangentImageEquiv (f x)).apply_symm_apply (L q))
  exact hleft.trans (r.embedding_derivative_retract (L q).property).symm

/-- The disk coordinates are a local diffeomorphism at zero. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.isLocalDiffeomorphAt_diskCoordinates_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {e : NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) {n : ℕ} {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {V : Set D}
    (hV : IsOpen V) (hA : ContDiffOn ℝ ∞ A V) {x : D} (hx : x ∈ V)
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (hAi : Function.Injective (A x))
    (hAr : (A x).range = e.diskNormalSpace f x) :
    IsLocalDiffeomorphAt 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ (r.diskCoordinates f A)
      (x, 0) :=
  isLocalDiffeomorphAt_of_contMDiffOn (r.isOpen_diskCoordinateDomain hf hV hA)
    (r.zero_mem_diskCoordinateDomain f A hx) (r.contMDiffOn_diskCoordinates hf hA)
    (r.isInvertible_mfderiv_diskCoordinates_zero hf (hA.contDiffAt (hV.mem_nhds hx)) hi hAi hAr)

/-- A disk tubular neighborhood exists. -/
theorem NativeEuclideanEmbedding.SmoothRetraction.exists_diskTubularNeighborhood
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K V : Set D} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)}
    (hA : ContDiffOn ℝ ∞ A V) (hAi : ∀ x ∈ K, Function.Injective (A x))
    (hAr : ∀ x ∈ K, (A x).range = e.diskNormalSpace f x) :
    ∃ Φ :
      PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (D × EuclideanSpace ℝ (Fin n))
        M ∞,
      K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Φ.source ∧
        Φ.source ⊆ r.diskCoordinateDomain f A V ∧
          (Φ : D × EuclideanSpace ℝ (Fin n) → M) = r.diskCoordinates f A := by
  have hzeroInj : Set.InjOn (r.diskCoordinates f A) (K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))}) := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩ ⟨y, w⟩ ⟨hy, hw⟩ hxy
    have hv0 : v = 0 := hv
    have hw0 : w = 0 := hw
    subst v
    subst w
    rw [r.diskCoordinates_zero, r.diskCoordinates_zero] at hxy
    exact Prod.ext (hinj hx hy hxy) rfl
  have hlocal :
    ∀ p ∈ K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))},
      IsLocalDiffeomorphAt 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ (r.diskCoordinates f A)
        p := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    exact
      r.isLocalDiffeomorphAt_diskCoordinates_zero hf hV hA (hKV hx) (hi x hx) (hAi x hx)
        (hAr x hx)
  apply
    exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton) hzeroInj hlocal
      (r.isOpen_diskCoordinateDomain hf hV hA)
  rintro ⟨x, v⟩ ⟨hx, hv⟩
  have hv0 : v = 0 := hv
  subst v
  exact r.zero_mem_diskCoordinateDomain f A (hKV hx)

/-- A tubular neighborhood of an embedded closed ball exists. -/
theorem exists_tubularNeighborhood_in_open_of_embedded_closedBall {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hinj : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hi : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f (Metric.closedBall (0 : D) 1) O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          Metric.closedBall (0 : D) 1 ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            (∀ x ∈ Metric.closedBall (0 : D) 1, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hKV, A, hA, hframe⟩ := e.exists_smooth_normalFrame_near_closedBall hf hi n hcodim
  obtain ⟨Φ, hzero, -, hΦ⟩ :=
    r.exists_diskTubularNeighborhood hf (ProperSpace.isCompact_closedBall 0 1) hV hKV hinj hi hA
      (fun x hx => (hframe x (hKV hx)).1) (fun x hx => (hframe x (hKV hx)).2)
  let W := Φ.source ∩ Φ ⁻¹' O
  have hW : IsOpen W := Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hO
  have hWloc : IsLocalDiffeomorphOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ Φ W := fun p =>
    Φ.isLocalDiffeomorphAt _ _ _ p.property.1
  let Ψ :=
    partialDiffeomorphOfInjectiveLocal hW (Φ.toPartialEquiv.injOn.mono Set.inter_subset_left)
      hWloc
  have hzeroΨ : Metric.closedBall (0 : D) 1 ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    refine ⟨hzero ⟨hx, rfl⟩, ?_⟩
    change Φ (x, 0) ∈ O
    rw [hΦ, r.diskCoordinates_zero]
    exact hfO hx
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset (ProperSpace.isCompact_closedBall 0 1)
      Ψ.open_source hzeroΨ
  refine ⟨ε, hε, Ψ, hprod, ?_, ?_⟩
  · intro x _
    change Φ (x, 0) = f x
    rw [hΦ, r.diskCoordinates_zero]
  · change Φ '' W ⊆ O
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2
