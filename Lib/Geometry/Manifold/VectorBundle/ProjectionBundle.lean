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
import Lib.Geometry.Manifold.WhitneyEmbedding


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

def NoExotic.projectionIntertwiner {R : Type*} [Ring R] (P Q : R) : R :=
  Q * P + (1 - Q) * (1 - P)

theorem NoExotic.projectionIntertwiner_self {R : Type*} [Ring R] (P : R)
    (hP : IsIdempotentElem P) : projectionIntertwiner P P = 1 := by
  unfold projectionIntertwiner
  rw [hP, hP.one_sub]
  simpa only [add_sub_assoc] using add_sub_cancel_left P 1

theorem NoExotic.projectionIntertwiner_intertwines {R : Type*} [Ring R] (P Q : R)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    Q * projectionIntertwiner P Q = projectionIntertwiner P Q * P := by
  calc
    Q * projectionIntertwiner P Q = (Q * Q) * P + (Q * (1 - Q)) * (1 - P) := by
      simp only [projectionIntertwiner, mul_add, mul_assoc]
    _ = Q * P := by rw [hQ, hQ.mul_one_sub_self, MulZeroClass.zero_mul, add_zero]
    _ = Q * (P * P) + (1 - Q) * ((1 - P) * P) := by
      rw [hP, hP.one_sub_mul_self, MulZeroClass.mul_zero, add_zero]
    _ = projectionIntertwiner P Q * P := by simp only [projectionIntertwiner, add_mul, mul_assoc]

theorem NoExotic.projectionIntertwiner_map_range {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (P Q : F →L[ℝ] F) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) :
    Submodule.map (projectionIntertwiner P Q).toLinearMap P.range = Q.range := by
  have hcomm := projectionIntertwiner_intertwines P Q hP hQ
  have hsurj : Function.Surjective (projectionIntertwiner P Q : F →L[ℝ] F) := by
    obtain ⟨r, hr⟩ := hR
    simpa only [← hr, ContinuousLinearEquiv.coe_coe] using r.surjective
  rw [← LinearMap.range_comp]
  have hlin :
    (projectionIntertwiner P Q).toLinearMap.comp P.toLinearMap =
      Q.toLinearMap.comp (projectionIntertwiner P Q).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap hcomm.symm
  rw [hlin]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)

noncomputable def NoExotic.invertibleOperatorEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : F →L[ℝ] F) (hA : A.IsInvertible) : F ≃L[ℝ] F
    where
  toLinearEquiv :=
    { A.toLinearMap with
      invFun := A.inverse
      left_inv := hA.inverse_apply_self
      right_inv := hA.self_apply_inverse }
  continuous_toFun := A.continuous
  continuous_invFun := A.inverse.continuous

noncomputable def NoExotic.projectionRangeEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (P Q : F →L[ℝ] F) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) : P.range ≃L[ℝ] Q.range :=
  (invertibleOperatorEquiv (projectionIntertwiner P Q) hR).ofSubmodules P.range Q.range
    (projectionIntertwiner_map_range P Q hP hQ hR)

theorem NoExotic.projectionRangeEquiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P Q : F →L[ℝ] F) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) (v : P.range) :
    (projectionRangeEquiv P Q hP hQ hR v : F) = projectionIntertwiner P Q v :=
  rfl

theorem NoExotic.projectionRangeEquiv_symm_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (P Q : F →L[ℝ] F) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) (v : Q.range) :
    ((projectionRangeEquiv P Q hP hQ hR).symm v : F) = (projectionIntertwiner P Q).inverse v :=
  rfl

theorem NoExotic.projection_apply_range {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : F →L[ℝ] F) (hP : IsIdempotentElem P) (v : P.range) : P v = v := by
  obtain ⟨w, hw⟩ := v.property
  rw [← hw]
  exact congrArg (fun A : F →L[ℝ] F ↦ A w) hP

def NoExotic.projectionTransportDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*} (P : M → F →L[ℝ] F) (x₀ : M) : Set M :=
  {x | (projectionIntertwiner (P x₀) (P x)).IsInvertible}

theorem NoExotic.contMDiff_projectionIntertwiner {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (hP : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun x ↦ projectionIntertwiner (P x₀) (P x)) :=
  (hP.clm_comp contMDiff_const).add ((contMDiff_const.sub hP).clm_comp contMDiff_const)

theorem NoExotic.isOpen_projectionTransportDomain {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (hP : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    IsOpen (projectionTransportDomain P x₀) := by
  have hi : IsOpen {A : F →L[ℝ] F | A.IsInvertible} := ContinuousLinearEquiv.isOpen
  exact hi.preimage (contMDiff_projectionIntertwiner P hP x₀).continuous

theorem NoExotic.mem_projectionTransportDomain {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {M : Type*} (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
    (x₀ : M) : x₀ ∈ projectionTransportDomain P x₀ := by
  change (projectionIntertwiner (P x₀) (P x₀)).IsInvertible
  rw [projectionIntertwiner_self _ (hP x₀)]
  exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩

theorem NoExotic.contMDiffOn_projectionIntertwiner_inverse {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (hP : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun x ↦ (projectionIntertwiner (P x₀) (P x)).inverse)
      (projectionTransportDomain P x₀) := by
  intro x hx
  have hi := hx.contDiffAt_map_inverse (n := ∞)
  exact
    (ContDiffAt.comp_contMDiffAt (f := fun y ↦ projectionIntertwiner (P x₀) (P y)) (x := x) hi
        (contMDiff_projectionIntertwiner P hP x₀).contMDiffAt).contMDiffWithinAt

noncomputable def NoExotic.ProjectionBundle.toCoordinates {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M) : (P x).range →L[ℝ] K :=
  (q x₀).toContinuousLinearMap.comp
    ((P x₀).rangeRestrict.comp
      ((NoExotic.projectionIntertwiner (P x₀) (P x)).inverse.comp (P x).range.subtypeL))

noncomputable def NoExotic.ProjectionBundle.fromCoordinates {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M) : K →L[ℝ] (P x).range :=
  (P x).rangeRestrict.comp
    ((NoExotic.projectionIntertwiner (P x₀) (P x)).comp
      ((P x₀).range.subtypeL.comp (q x₀).symm.toContinuousLinearMap))

noncomputable def NoExotic.ProjectionBundle.coordinateEquiv {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M)
    (hx : x ∈ NoExotic.projectionTransportDomain P x₀) : (P x).range ≃L[ℝ] K :=
  (NoExotic.projectionRangeEquiv (P x₀) (P x) (hP x₀) (hP x) hx).symm.trans (q x₀)

theorem NoExotic.ProjectionBundle.toCoordinates_eq {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M)
    (hx : x ∈ NoExotic.projectionTransportDomain P x₀) :
    toCoordinates P q x₀ x = (coordinateEquiv P hP q x₀ x hx).toContinuousLinearMap := by
  ext v
  change
    q x₀ ((P x₀).rangeRestrict ((NoExotic.projectionIntertwiner (P x₀) (P x)).inverse v)) =
      q x₀ ((NoExotic.projectionRangeEquiv (P x₀) (P x) (hP x₀) (hP x) hx).symm v)
  congr 1
  apply Subtype.ext
  change P x₀ ((NoExotic.projectionIntertwiner (P x₀) (P x)).inverse v) = _
  rw [← NoExotic.projectionRangeEquiv_symm_apply (P x₀) (P x) (hP x₀) (hP x) hx v]
  exact NoExotic.projection_apply_range (P x₀) (hP x₀) _

theorem NoExotic.ProjectionBundle.fromCoordinates_eq {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M)
    (hx : x ∈ NoExotic.projectionTransportDomain P x₀) :
    fromCoordinates P q x₀ x = (coordinateEquiv P hP q x₀ x hx).symm.toContinuousLinearMap := by
  ext v
  change
    P x (NoExotic.projectionIntertwiner (P x₀) (P x) ((q x₀).symm v)) =
      (NoExotic.projectionRangeEquiv (P x₀) (P x) (hP x₀) (hP x) hx ((q x₀).symm v) : F)
  rw [← NoExotic.projectionRangeEquiv_apply (P x₀) (P x) (hP x₀) (hP x) hx ((q x₀).symm v)]
  exact NoExotic.projection_apply_range (P x) (hP x) _

theorem NoExotic.ProjectionBundle.fromCoordinates_toCoordinates {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*}
    (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K)
    (x₀ x : M) (hx : x ∈ NoExotic.projectionTransportDomain P x₀) (v : (P x).range) :
    fromCoordinates P q x₀ x (toCoordinates P q x₀ x v) = v := by
  rw [toCoordinates_eq P hP q x₀ x hx, fromCoordinates_eq P hP q x₀ x hx]
  exact (coordinateEquiv P hP q x₀ x hx).symm_apply_apply v

theorem NoExotic.ProjectionBundle.toCoordinates_fromCoordinates {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*}
    (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K)
    (x₀ x : M) (hx : x ∈ NoExotic.projectionTransportDomain P x₀) (v : K) :
    toCoordinates P q x₀ x (fromCoordinates P q x₀ x v) = v := by
  rw [toCoordinates_eq P hP q x₀ x hx, fromCoordinates_eq P hP q x₀ x hx]
  exact (coordinateEquiv P hP q x₀ x hx).apply_symm_apply v

noncomputable def NoExotic.ProjectionBundle.ambientFromCoordinates {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*}
    (P : M → F →L[ℝ] F) (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M) : K →L[ℝ] F :=
  (P x).comp
    ((NoExotic.projectionIntertwiner (P x₀) (P x)).comp
      ((P x₀).range.subtypeL.comp (q x₀).symm.toContinuousLinearMap))

theorem NoExotic.ProjectionBundle.contMDiff_ambientFromCoordinates {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K]
    {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M] (P : M → F →L[ℝ] F)
    (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    ContMDiff I 𝓘(ℝ, K →L[ℝ] F) ∞ (ambientFromCoordinates P q x₀) :=
  hs.clm_comp ((NoExotic.contMDiff_projectionIntertwiner P hs x₀).clm_comp contMDiff_const)

noncomputable def NoExotic.ProjectionBundle.pretrivialization {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K] [NormedSpace ℝ K] {B H M : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace M] [ChartedSpace H M] (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
    (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    Bundle.Pretrivialization K (Bundle.TotalSpace.proj (F := K) (E := fun x ↦ (P x).range))
    where
  toFun p := ⟨p.1, toCoordinates P q x₀ p.1 p.2⟩
  invFun p := ⟨p.1, fromCoordinates P q x₀ p.1 p.2⟩
  source := Bundle.TotalSpace.proj ⁻¹' NoExotic.projectionTransportDomain P x₀
  target := NoExotic.projectionTransportDomain P x₀ ×ˢ Set.univ
  map_source' := fun _ h ↦ ⟨h, Set.mem_univ _⟩
  map_target' := fun _ h ↦ h.1
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [Bundle.TotalSpace.mk_inj]
    exact fromCoordinates_toCoordinates P hP q x₀ x hx v
  right_inv' := by
    rintro ⟨x, v⟩ ⟨hx, _⟩
    simp only [Prod.mk_right_inj]
    exact toCoordinates_fromCoordinates P hP q x₀ x hx v
  open_target := (NoExotic.isOpen_projectionTransportDomain P hs x₀).prod isOpen_univ
  baseSet := NoExotic.projectionTransportDomain P x₀
  open_baseSet := NoExotic.isOpen_projectionTransportDomain P hs x₀
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance NoExotic.ProjectionBundle.pretrivialization_isLinear {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K] [NormedSpace ℝ K] {B H M : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace M] [ChartedSpace H M] (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
    (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    (pretrivialization P hP q hs x₀).IsLinear ℝ where
  linear x _ := (toCoordinates P q x₀ x).toLinearMap.isLinear

theorem NoExotic.ProjectionBundle.pretrivialization_symm_apply {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K]
    [NormedSpace ℝ K] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K)
    (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ x : M)
    (hx : x ∈ NoExotic.projectionTransportDomain P x₀) (v : K) :
    (pretrivialization P hP q hs x₀).symm x v = fromCoordinates P q x₀ x v := by
  rw [Bundle.Pretrivialization.symm_apply]
  · rfl
  · exact hx

noncomputable def NoExotic.ProjectionBundle.coordinateChange {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x₁ x : M) : K →L[ℝ] K :=
  (q x₁).toContinuousLinearMap.comp
    ((P x₁).rangeRestrict.comp
      ((NoExotic.projectionIntertwiner (P x₁) (P x)).inverse.comp
        ((P x).comp
          ((NoExotic.projectionIntertwiner (P x₀) (P x)).comp
            ((P x₀).range.subtypeL.comp (q x₀).symm.toContinuousLinearMap)))))

theorem NoExotic.ProjectionBundle.contMDiffOn_coordinateChange {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K]
    [NormedSpace ℝ K] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P)
    (x₀ x₁ : M) :
    ContMDiffOn I 𝓘(ℝ, K →L[ℝ] K) ∞ (coordinateChange P q x₀ x₁)
      (NoExotic.projectionTransportDomain P x₀ ∩ NoExotic.projectionTransportDomain P x₁) := by
  have hi :=
    (NoExotic.contMDiffOn_projectionIntertwiner_inverse P hs x₁).mono
      (Set.inter_subset_right (s := NoExotic.projectionTransportDomain P x₀))
  exact
    contMDiffOn_const.clm_comp
      (contMDiffOn_const.clm_comp
        (hi.clm_comp
          (hs.contMDiffOn.clm_comp
            ((NoExotic.contMDiff_projectionIntertwiner P hs x₀).contMDiffOn.clm_comp
              contMDiffOn_const))))

theorem NoExotic.ProjectionBundle.coordinateChange_apply {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K] [NormedSpace ℝ K] {B H M : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace M] [ChartedSpace H M] (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
    (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ x₁ x : M)
    (hx : x ∈ NoExotic.projectionTransportDomain P x₀ ∩ NoExotic.projectionTransportDomain P x₁)
    (v : K) :
    coordinateChange P q x₀ x₁ x v =
      ((pretrivialization P hP q hs x₁) ⟨x, (pretrivialization P hP q hs x₀).symm x v⟩).2 := by
  rw [pretrivialization_symm_apply P hP q hs x₀ x hx.1]
  rfl

noncomputable def NoExotic.ProjectionBundle.vectorPrebundle {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K] [NormedSpace ℝ K] {B H M : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace M] [ChartedSpace H M] (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
    (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) :
    VectorPrebundle ℝ K (fun x ↦ (P x).range)
    where
  pretrivializationAtlas := Set.range (pretrivialization P hP q hs)
  pretrivialization_linear' := by
    rintro _ ⟨x₀, rfl⟩
    infer_instance
  pretrivializationAt := pretrivialization P hP q hs
  mem_base_pretrivializationAt := NoExotic.mem_projectionTransportDomain P hP
  pretrivialization_mem_atlas x := ⟨x, rfl⟩
  exists_coordChange := by
    rintro _ ⟨x₀, rfl⟩ _ ⟨x₁, rfl⟩
    exact
      ⟨coordinateChange P q x₀ x₁, (contMDiffOn_coordinateChange P q hs x₀ x₁).continuousOn,
        coordinateChange_apply P hP q hs x₀ x₁⟩
  totalSpaceMk_isInducing := by
    intro x
    change Topology.IsInducing (fun v : (P x).range ↦ (x, toCoordinates P q x x v))
    have hx := NoExotic.mem_projectionTransportDomain P hP x
    rw [toCoordinates_eq P hP q x x hx]
    exact
      Topology.isInducing_const_prod.mpr (coordinateEquiv P hP q x x hx).toHomeomorph.isInducing

instance NoExotic.ProjectionBundle.vectorPrebundle_isContMDiff {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K]
    [NormedSpace ℝ K] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K)
    (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) : (vectorPrebundle P hP q hs).IsContMDiff I ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨x₀, rfl⟩ _ ⟨x₁, rfl⟩
    exact
      ⟨coordinateChange P q x₀ x₁, contMDiffOn_coordinateChange P q hs x₀ x₁,
        coordinateChange_apply P hP q hs x₀ x₁⟩
end Mathoverflow1973
