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
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Immersion.Relative
/-!
# Rearrangement of Morse functions and the band-cancellation tail

The rearrangement side of the Morse theory: reordering critical points by
modifying the function in disjoint bands, the regular-height coordinate
system, the band-cancellation tail of the toolbox, the smooth-time germs of
the ODE layer, and the `NativeTransversality.Patch` structures
(Milnor, *Lectures on the h-cobordism theorem*, Thm 4.1 and §5; the
Rearrangement Theorem of the source text).

## Outline

1. `MorseCancellation.linearTransverseChart` and the F-lane band tail: the
   transverse-chart control used by the belt-cancellation step.
2. `RegularHeightCoordinates` and `MorseRearrangement`: the
   rearrangement theorem - critical points can be reordered by an isotopy
   supported away from the attaching spheres.
3. `AdaptedWindows` flow lemmas, `SmoothODE` time germs and
   `FlowCancellation` smooth signed level time.
4. `NativeTransversality.Patch` and the rearrangement stragglers.

## Main definitions and results

* `MorseRearrangement.exists_morse_rearrangement_of_no_connection` -
  the Rearrangement Theorem.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, Thm 4.1, §5.

## Tags

morse-theory, rearrangement, h-cobordism
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

/-! ### Linear transverse chart corrections -/

/-- A chart composed with a linear transverse correction on the `V` factor. -/
def MorseCancellation.linearTransverseChart {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (C : V ≃L[ℝ] V) (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞ :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C).toDiffeomorph.toPartialDiffeomorph.trans Φ

/-- The linear transverse chart fixes the axis. -/
theorem MorseCancellation.linearTransverseChart_axis {V E M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (C : V ≃L[ℝ] V) (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    (t : ℝ) : linearTransverseChart C Φ (t, 0) = Φ (t, 0) := by
  change Φ (t, C 0) = Φ (t, 0)
  rw [map_zero]

/-- Axis points lie in the corrected source exactly in the original. -/
theorem MorseCancellation.linearTransverseChart_axis_source {V E M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (C : V ≃L[ℝ] V) (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    (t : ℝ) : (t, (0 : V)) ∈ (linearTransverseChart C Φ).source ↔ (t, (0 : V)) ∈ Φ.source := by
  change (t, (0 : V)) ∈ Set.univ ∧ (t, C 0) ∈ Φ.source ↔ _
  simp only [Set.mem_univ, map_zero, true_and]

/-- The transverse block of a composite factors out the linear correction. -/
theorem MorseCancellation.transverseBlock_comp_linear {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (C : V ≃L[ℝ] V) (L : (ℝ × V) →L[ℝ] (ℝ × V)) :
    AxisCoordinates.transverseBlock
        (L.comp ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C).toContinuousLinearMap) =
      (AxisCoordinates.transverseBlock L).comp C.toContinuousLinearMap := by
  ext z
  rfl

/-- The transition derivative determinant picks up the transverse block of `C`. -/
theorem MorseCancellation.det_transition_linearTransverseChart {V E M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (C : V ≃L[ℝ] V) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    {t : ℝ} (ht : (t, (0 : V)) ∈ (Φ.trans Ψ.symm).source) :
    (AxisCoordinates.transverseBlock
          (fderiv ℝ (Ψ.symm ∘ linearTransverseChart C Φ) (t, 0))).toLinearMap.det =
      (AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (t, 0))).toLinearMap.det *
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

/-- An invertible linear map has nonzero determinant. -/
theorem MorseCancellation.det_ne_zero_of_isInvertible {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (T : V →L[ℝ] V) (hT : T.IsInvertible) : T.toLinearMap.det ≠ 0 := by
  obtain ⟨e, he⟩ := hT
  rw [← he]
  exact e.toLinearEquiv.isUnit_det'.ne_zero

/-- Endpoint sheets can be given compatibly oriented charts on the arc. -/
theorem MorseCancellation.exists_compatible_sheet_endpoint_orientation {A B E M ι : Type*}
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
        (AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det *
          (AxisCoordinates.transverseBlock
              (fderiv ℝ
                (Ψ.symm ∘ linearTransverseChart ((ContinuousLinearEquiv.refl ℝ A).prodCongr R) Φ₁)
                (q, 0))).toLinearMap.det := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨U₀, -, hp, -, -, -, -, hi₀, -⟩ :=
    AxisCoordinates.exists_native_axis_transition_data Φ₀ Ψ hΦ₀ hΨ₀ haxis₀
  obtain ⟨U₁, -, hq, hs₁, -, -, -, hi₁, -⟩ :=
    AxisCoordinates.exists_native_axis_transition_data Φ₁ Ψ hΦ₁ hΨ₁ haxis₁
  let d₀ :=
    (AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det
  let d₁ :=
    (AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ₁) (q, 0))).toLinearMap.det
  have h₀ : d₀ ≠ 0 := det_ne_zero_of_isInvertible _ (hi₀ p hp)
  have h₁ : d₁ ≠ 0 := det_ne_zero_of_isInvertible _ (hi₁ q hq)
  obtain ⟨R, hR⟩ :=
    SupportedGerms.exists_linearEquiv_with_det basis i (inv_ne_zero (mul_ne_zero h₀ h₁))
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

/-- An embedded arc with injective differential admits a tubular sheet chart. -/
theorem MorseCancellation.exists_sheet_arc_tube {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
    exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero ha
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
    AxisCoordinates.exists_native_axis_chart_with_endpoint_germs
      (Module.finBasis ℝ ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) Ψ Φ₀ Φ₂
      zero_lt_one CompactIccSpace.isCompact_Icc hzero hΨ₀ hΨ₁ hΦ₀ hΦ₂ haxis₀ haxis₂ hsign
  exact
    ⟨R, ε, hε, Φ, hprod, fun t => (haxis t).trans (hΨaxis t), hgl, hgr, fun z hz =>
      hΞO (htarget hz).1⟩

/-- An open tube avoiding a closed set recognizes the sheet away from it. -/
theorem MorseCancellation.exists_open_tube_sheet_recognition {V E H M : Type*} [NormedAddCommGroup V]
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

/-- A tube can be restricted cleanly around a compact axis segment. -/
theorem MorseCancellation.exists_clean_axis_tube_restriction {V E H M : Type*} [NormedAddCommGroup V]
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
  let Ψ := PartialChart.restrictSource Φ (hU.inter hW)
  have hzero : K ×ˢ {(0 : V)} ⊆ Ψ.source := fun z hz => ⟨hKsource hz, hKU hz, hKW hz⟩
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hzero
  exact
    ⟨ε, hε, Ψ, hprod, fun _ => rfl, fun _ hz => hz.1, fun z hz => hSU z hz.2.1, fun z hz =>
      hTW z hz.2.2⟩

/-- A tube around the unit axis contains a coordinate box. -/
theorem MorseCancellation.exists_tube_support_box {V E H M : Type*} [NormedAddCommGroup V]
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
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc
      Φ.open_source hwideAxis
  exact ⟨-a, 1 + b, r, by linarith, by linarith, hr, hprod⟩

/-! ### Regular height coordinates -/

/-- The map `(t, z) ↦ (F(t, z), z)` keeping the transverse coordinate. -/
def RegularHeightCoordinates.heightMap {V : Type*} (F : ℝ × V → ℝ) (p : ℝ × V) : ℝ × V :=
  (F p, p.2)

/-- A linear map on `ℝ × V` splits into scalar and transverse parts. -/
theorem RegularHeightCoordinates.linear_decomposition {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℝ × V →L[ℝ] ℝ) (s : ℝ) (z : V) : L (s, z) = s * L (1, 0) + L (0, z) := by
  have he : (s, z) = s • (1, (0 : V)) + (0, z) := by simp
  rw [he, map_add, map_smul]
  rfl

/-- A height-preserving triangular map with nonzero axis component is bijective. -/
theorem RegularHeightCoordinates.triangular_bijective {V : Type*} [NormedAddCommGroup V]
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

/-- The triangular map as a continuous linear equivalence. -/
def RegularHeightCoordinates.triangularEquiv {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : ℝ × V →L[ℝ] ℝ) (hL : L (1, 0) ≠ 0) :
    (ℝ × V) ≃L[ℝ] (ℝ × V) :=
  (LinearEquiv.ofBijective (L.prod (ContinuousLinearMap.snd ℝ ℝ V)).toLinearMap
      (triangular_bijective L hL)).toContinuousLinearEquiv

/-- The height map is smooth when `F` is. -/
theorem RegularHeightCoordinates.contDiff_heightMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (heightMap F) :=
  hF.prodMk contDiff_snd

/-- The derivative of the height map in block form. -/
theorem RegularHeightCoordinates.fderiv_heightMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) (p : ℝ × V) :
    fderiv ℝ (heightMap F) p = (fderiv ℝ F p).prod (ContinuousLinearMap.snd ℝ ℝ V) :=
  (((hF.differentiable (by simp) p).hasFDerivAt).prodMk
      (ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt).fderiv

/-- The height map is a local diffeomorphism where its time derivative is nonzero. -/
theorem RegularHeightCoordinates.heightMap_localDiffeomorph {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {F : ℝ × V → ℝ}
    (hF : ContDiff ℝ ∞ F) {p : ℝ × V} (hreg : fderiv ℝ F p (1, 0) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ (heightMap F) p := by
  have hinv : (fderiv ℝ (heightMap F) p).IsInvertible := by
    refine ⟨triangularEquiv (fderiv ℝ F p) hreg, ?_⟩
    rw [fderiv_heightMap hF]
    rfl
  obtain ⟨Φ, hp, _, hΦ⟩ :=
    exists_partialDiffeomorph_of_contDiffOn isOpen_univ (Set.mem_univ p)
      (contDiff_heightMap hF).contDiffOn hinv
  exact ⟨Φ, hp, fun _ _ => congrFun hΦ.symm _⟩

/-- The height with a longitudinal displacement added. -/
def RegularHeightCoordinates.displacedHeight {V : Type*} (u : ℝ × V → ℝ) (p : ℝ × V) : ℝ :=
  p.1 + u p

/-- The displaced height is smooth. -/
theorem RegularHeightCoordinates.contDiff_displacedHeight {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (displacedHeight u) :=
  contDiff_fst.add hu

/-- The scalar time derivative of a height function. -/
theorem RegularHeightCoordinates.scalar_derivative {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) (s : ℝ) (z : V) :
    HasDerivAt (fun t : ℝ => F (t, z)) (fderiv ℝ F (s, z) (1, 0)) s :=
  ((hF.differentiable (by simp) (s, z)).hasFDerivAt).comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))

/-- Positive time derivative makes the height map injective. -/
theorem RegularHeightCoordinates.heightMap_injective_of_positive {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hpos : ∀ p, 0 < fderiv ℝ F p (1, 0)) : Function.Injective (heightMap F) := by
  have hmono (z : V) : StrictMono (fun s : ℝ => F (s, z)) :=
    strictMono_of_deriv_pos (fun s => by rw [(scalar_derivative hF s z).deriv]; exact hpos _)
  rintro ⟨s, z⟩ ⟨t, w⟩ he
  have hzw : z = w := congrArg Prod.snd he
  subst w
  have hst : s = t := (hmono z).injective (congrArg Prod.fst he)
  exact Prod.ext hst rfl

/-- Bounded slope makes the height map surjective. -/
theorem RegularHeightCoordinates.heightMap_surjective_of_bounded {V : Type*}
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

/-- Compactly supported displacement keeps the height map surjective. -/
theorem RegularHeightCoordinates.heightMap_surjective_of_compactSupport {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : Function.Surjective (heightMap (displacedHeight u)) := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hu.continuous).isBounded.exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg (u 0)).trans (hC _ ⟨0, rfl⟩)
  exact
    heightMap_surjective_of_bounded hu.continuous C hC0
      (fun p => by simpa only [Real.norm_eq_abs] using hC _ ⟨p, rfl⟩)

/-- The longitudinal displacement as a diffeomorphism of `ℝ × V`. -/
def RegularHeightCoordinates.longitudinalDiffeomorph {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hpos : ∀ p, 0 < fderiv ℝ (displacedHeight u) p (1, 0)) :
    (ℝ × V) ≃ₘ⟮𝓘(ℝ, ℝ × V), 𝓘(ℝ, ℝ × V)⟯ (ℝ × V) := by
  have hs := contDiff_displacedHeight hu
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ (heightMap (displacedHeight u)) :=
    fun p => heightMap_localDiffeomorph hs (hpos p).ne'
  exact
    hloc.diffeomorphOfBijective
      ⟨heightMap_injective_of_positive hs hpos, heightMap_surjective_of_compactSupport hu hc⟩

/-! ### Interval translations -/

/-- A compactly supported translation of the interval. -/
def MorseRearrangement.IntervalTranslation (a b x y : ℝ) : Prop :=
  ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
    (∀ z, z ∉ Set.Ioo a b → D z = z) ∧ D =ᶠ[𝓝 x] fun z => z + (y - x)

/-- The translation germ computes the shifted value. -/
theorem MorseRearrangement.translation_germ_apply (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    {x y : ℝ} (hD : D =ᶠ[𝓝 x] fun z => z + (y - x)) : D x = y := by
  have h := hD.self_of_nhds
  linarith

/-- The identity interval translation. -/
theorem MorseRearrangement.intervalTranslation_refl (a b x : ℝ) :
    IntervalTranslation a b x x := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞, fun _ _ => rfl, Filter.Eventually.of_forall ?_⟩
  intro z
  change z = z + (x - x)
  ring

/-- The inverse of an interval translation. -/
theorem MorseRearrangement.intervalTranslation_symm {a b x y : ℝ}
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

/-- Composition of interval translations. -/
theorem MorseRearrangement.intervalTranslation_trans {a b x y z : ℝ}
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

/-- A local value extends to a supported interval translation. -/
theorem MorseRearrangement.exists_local_interval_translation {a b x : ℝ}
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
    SmallPerturbation.exists_radius_bumpTranslation β.contDiff hcompact
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hnorm : ‖y - x‖ < ε := by simpa only [dist_eq_norm] using hy
  obtain ⟨D, hD, hfix⟩ := hmove (y - x) hnorm
  refine ⟨D, fun z hz => hfix z (fun h => hz (hsupp h)), ?_⟩
  filter_upwards [Metric.ball_mem_nhds x β.rIn_pos] with z hz
  rw [hD, β.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_smul]

/-- An interval translation supported on a compact interval. -/
theorem MorseRearrangement.exists_supported_interval_translation {a b x y : ℝ}
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

/-- A diffeomorphism fixed outside an interval is strictly monotone on it. -/
theorem MorseRearrangement.strictMono_of_fixed_exterior
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) {a b : ℝ} (hfix : ∀ z, z ∉ Set.Ioo a b → D z = z) :
    StrictMono D := by
  rcases D.continuous.strictMono_of_inj D.injective with hm | ha
  · exact hm
  · have hanti := ha (show b < b + 1 by linarith)
    rw [hfix b (fun h => (lt_irrefl b) h.2), hfix (b + 1) (fun h => by linarith [h.2])] at hanti
    linarith

/-- A strictly monotone diffeomorphism has positive derivative. -/
theorem MorseRearrangement.deriv_pos_of_strictMono_diffeomorph
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

/-- An increasing supported translation of the interval. -/
theorem MorseRearrangement.exists_increasing_interval_translation {a b x y : ℝ}
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (∀ z, z ∉ Set.Ioo a b → D z = z) ∧
        (D =ᶠ[𝓝 x] fun z => z + (y - x)) ∧ D x = y ∧ StrictMono D ∧ ∀ z, 0 < deriv D z := by
  obtain ⟨D, hfix, hgerm⟩ := exists_supported_interval_translation hx hy
  have hm := strictMono_of_fixed_exterior D hfix
  exact
    ⟨D, hfix, hgerm, translation_germ_apply D hgerm, hm, deriv_pos_of_strictMono_diffeomorph D hm⟩

/-- An increasing translation with prescribed exterior germs. -/
theorem MorseRearrangement.exists_increasing_interval_translation_with_exterior_germs
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

/-! ### Blending heights -/

/-- The convex blend of two height functions along a cutoff. -/
def MorseRearrangement.blendHeight (θ : ℝ) (P Q : ℝ → ℝ) (s : ℝ) : ℝ :=
  θ * P s + (1 - θ) * Q s

/-- At cutoff zero the blend is the first height. -/
theorem MorseRearrangement.blendHeight_zero (P Q : ℝ → ℝ) (s : ℝ) :
    blendHeight 0 P Q s = Q s := by simp [blendHeight]

/-- At cutoff one the blend is the second height. -/
theorem MorseRearrangement.blendHeight_one (P Q : ℝ → ℝ) (s : ℝ) :
    blendHeight 1 P Q s = P s := by simp [blendHeight]

/-- Where the heights agree the blend is fixed. -/
theorem MorseRearrangement.blendHeight_fixed {P Q : ℝ → ℝ} {s : ℝ} (hP : P s = s)
    (hQ : Q s = s) (θ : ℝ) : blendHeight θ P Q s = s := by
  rw [blendHeight, hP, hQ]
  ring

/-- The blended slope stays positive when both slopes are. -/
theorem MorseRearrangement.positive_blended_slope {θ a b : ℝ} (hθ : θ ∈ Set.Icc 0 1)
    (ha : 0 < a) (hb : 0 < b) : 0 < θ * a + (1 - θ) * b := by
  by_cases hzero : θ = 0
  · simpa only [hzero, MulZeroClass.zero_mul, sub_zero, one_mul, zero_add] using hb
  · exact
      add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hθ.1 (Ne.symm hzero)) ha)
        (mul_nonneg (sub_nonneg.mpr hθ.2) hb.le)

/-- The blended height has the blended derivative. -/
theorem MorseRearrangement.hasDerivAt_blended_height {f θ P Q : ℝ → ℝ} {t f' p' q' : ℝ}
    (hf : HasDerivAt f f' t) (hθ : HasDerivAt θ 0 t) (hP : HasDerivAt P p' (f t))
    (hQ : HasDerivAt Q q' (f t)) :
    HasDerivAt (fun s => blendHeight (θ s) P Q (f s)) ((θ t * p' + (1 - θ t) * q') * f') t := by
  convert!
    (hθ.mul (hP.comp t hf)).add (((hasDerivAt_const t (1 : ℝ)).sub hθ).mul (hQ.comp t hf)) using 1
  simp only [Pi.sub_apply]
  ring

/-! ### Longitudinal blending -/

/-- The longitudinal displacement of a blended height. -/
def MorseCancellation.longitudinalBlendDisplacement {V : Type*} (D : ℝ → ℝ) (β : V → ℝ) (η : ℝ → ℝ)
    (t : ℝ) (p : ℝ × V) : ℝ :=
  η t * β p.2 * (D p.1 - p.1)

/-- The longitudinal blend diffeomorphism of the tube. -/
def MorseCancellation.longitudinalBlend {V : Type*} (D : ℝ → ℝ) (β : V → ℝ) (η : ℝ → ℝ)
    (p : ℝ × (ℝ × V)) : ℝ × V :=
  (p.2.1 + longitudinalBlendDisplacement D β η p.1 p.2, p.2.2)

/-- The blend displacement is smooth. -/
theorem MorseCancellation.longitudinalBlendDisplacement_smooth {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (t : ℝ) : ContDiff ℝ ∞ (longitudinalBlendDisplacement D β η t) :=
  (contDiff_const.mul (hβ.comp contDiff_snd)).mul ((hD.comp contDiff_fst).sub contDiff_fst)

/-- The longitudinal blend is smooth. -/
theorem MorseCancellation.longitudinalBlend_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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

/-- At cutoff zero the blend is the identity. -/
theorem MorseCancellation.longitudinalBlend_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hη : η 0 = 0) (p : ℝ × V) :
    longitudinalBlend D β η (0, p) = p := by
  simp only [longitudinalBlend, longitudinalBlendDisplacement, hη, MulZeroClass.zero_mul,
    add_zero]

/-- The displacement vanishes outside the support. -/
theorem MorseCancellation.longitudinalBlendDisplacement_zero_outside {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) {l u : ℝ}
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (t : ℝ) (p : ℝ × V) (hp : p ∉ Set.Icc l u ×ˢ tsupport β) :
    longitudinalBlendDisplacement D β η t p = 0 := by
  by_cases hs : p.1 ∈ Set.Icc l u
  · have hb : β p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp ⟨hs, h⟩)
    simp only [longitudinalBlendDisplacement, hb, MulZeroClass.mul_zero, MulZeroClass.zero_mul]
  · have hd := hfix p.1 (fun h => hs ⟨h.1.le, h.2.le⟩)
    simp only [longitudinalBlendDisplacement, hd, sub_self, MulZeroClass.mul_zero]

/-- The blend is fixed outside the support. -/
theorem MorseCancellation.longitudinalBlend_fixed_outside {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ) {l u : ℝ}
    (hfix : ∀ s ∉ Set.Ioo l u, D s = s) (t : ℝ) (p : ℝ × V) (hp : p ∉ Set.Icc l u ×ˢ tsupport β) :
    longitudinalBlend D β η (t, p) = p := by
  rw [longitudinalBlend, longitudinalBlendDisplacement_zero_outside η hfix t p hp, add_zero]

/-- The blend has positive longitudinal derivative. -/
theorem MorseCancellation.longitudinalBlend_derivative_positive {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} (hD : ContDiff ℝ ∞ D)
    (hβ : ContDiff ℝ ∞ β) (hDpos : ∀ s, 0 < deriv D s) (hβrange : ∀ z, β z ∈ Set.Icc (0 : ℝ) 1)
    (hηrange : ∀ t, η t ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) (p : ℝ × V) :
    0 <
      fderiv ℝ
        (RegularHeightCoordinates.displacedHeight (longitudinalBlendDisplacement D β η t))
        p (1, 0) := by
  have hu := longitudinalBlendDisplacement_smooth η hD hβ t
  have hscalar :=
    RegularHeightCoordinates.scalar_derivative
      (RegularHeightCoordinates.contDiff_displacedHeight hu) p.1 p.2
  have hd :=
    (hasDerivAt_id p.1).add
      (((hD.differentiable (by simp) p.1).hasDerivAt.sub (hasDerivAt_id p.1)).const_mul
        (η t * β p.2))
  have hrate :
    fderiv ℝ
        (RegularHeightCoordinates.displacedHeight (longitudinalBlendDisplacement D β η t))
        p (1, 0) =
      1 + (η t * β p.2) * (deriv D p.1 - 1) :=
    hscalar.deriv.symm.trans hd.deriv
  rw [hrate]
  have hweight : η t * β p.2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hηrange t).1 (hβrange p.2).1,
      mul_le_one₀ (hηrange t).2 (hβrange p.2).1 (hβrange p.2).2⟩
  have hpos := MorseRearrangement.positive_blended_slope hweight (hDpos p.1) zero_lt_one
  nlinarith

/-- The blend preserves the transverse slices. -/
theorem MorseCancellation.longitudinalBlend_slices {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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
    ⟨RegularHeightCoordinates.longitudinalDiffeomorph hu hcompact
        (longitudinalBlend_derivative_positive hD hβ hDpos hβrange hηrange t),
      fun _ => rfl⟩

/-- The exponential glue `exp(-1/t)` is differentiable. -/
theorem MorseCancellation.expNegInvGlue_hasDerivAt (t : ℝ) :
    HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t

/-- The smooth transition has positive derivative on the interior. -/
theorem MorseCancellation.smoothTransition_deriv_pos {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
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

/-- The smooth transition is strictly monotone on its domain. -/
theorem MorseCancellation.smoothTransition_strictMonoOn :
    StrictMonoOn Real.smoothTransition (Set.Icc (0 : ℝ) 1) := by
  apply
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) Real.smoothTransition.continuous.continuousOn
  intro t ht
  apply smoothTransition_deriv_pos
  simpa only [interior_Icc] using ht

/-- Each level is crossed at a unique transition time. -/
theorem MorseCancellation.exists_unique_smoothTransition_time {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
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

/-! ### Longitudinal tube motions -/

/-- A supported longitudinal motion of a tube preserving its axis and germ data. -/
structure MorseCancellation.LongitudinalTubeMotion {V E H M : Type*} [NormedAddCommGroup V]
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

/-- The trivial longitudinal tube motion exists. -/
theorem MorseCancellation.nonempty_longitudinalTubeMotion {V E H M : Type*} [NormedAddCommGroup V]
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
    MorseRearrangement.exists_increasing_interval_translation h0I hcI
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
    SupportedDiffeomorph.exists_supported_isotopy_extension Φ hmodel
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

/-- The model motion fixes the axis. -/
theorem MorseCancellation.LongitudinalTubeMotion.model_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (t : ℝ) :
    MorseCancellation.longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, (0, 0)) =
      (Real.smoothTransition t * A.destination, 0) := by
  simp only [MorseCancellation.longitudinalBlend, MorseCancellation.longitudinalBlendDisplacement,
    A.cutoff_zero, A.profile_zero, mul_one, sub_zero, zero_add]

/-- The model motion has the prescribed axis germ. -/
theorem MorseCancellation.LongitudinalTubeMotion.model_germ {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (t : ℝ) :
    MorseCancellation.longitudinalBlend A.profile A.cutoff Real.smoothTransition =ᶠ[𝓝 (t, (0, 0))]
      fun p : ℝ × (ℝ × V) => (p.2.1 + Real.smoothTransition p.1 * A.destination, p.2.2) := by
  have hs : Filter.Tendsto (fun p : ℝ × (ℝ × V) => p.2.1) (𝓝 (t, (0, 0))) (𝓝 0) :=
    continuous_fst.continuousAt.comp continuous_snd.continuousAt
  have hz : Filter.Tendsto (fun p : ℝ × (ℝ × V) => p.2.2) (𝓝 (t, (0, 0))) (𝓝 0) :=
    continuous_snd.continuousAt.comp continuous_snd.continuousAt
  filter_upwards [hs.eventually A.profile_germ, hz.eventually A.cutoff_germ] with p hp hβ
  simp only [MorseCancellation.longitudinalBlend, MorseCancellation.longitudinalBlendDisplacement, hp, hβ,
    mul_one, add_sub_cancel_left]

/-- The native motion fixes the chart axis. -/
theorem MorseCancellation.LongitudinalTubeMotion.native_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) (t : ℝ) :
    A.family (t, Φ 0) = Φ (Real.smoothTransition t * A.destination, 0) := by
  rw [A.formula t 0 h0]
  exact congrArg Φ (A.model_axis t)

/-- The native motion has the prescribed axis germ. -/
theorem MorseCancellation.LongitudinalTubeMotion.native_germ {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) (t : ℝ) :
    (fun p : ℝ × (ℝ × V) => A.family (p.1, Φ p.2)) =ᶠ[𝓝 (t, 0)] fun p =>
      Φ (p.2.1 + Real.smoothTransition p.1 * A.destination, p.2.2) := by
  have hs : ∀ᶠ p : ℝ × (ℝ × V) in 𝓝 (t, 0), p.2 ∈ Φ.source :=
    continuous_snd.continuousAt.eventually (Φ.open_source.mem_nhds h0)
  filter_upwards [A.model_germ t, hs] with p hp hs
  rw [A.formula p.1 p.2 hs, hp]

/-- The motion is fixed outside the target tube. -/
theorem MorseCancellation.LongitudinalTubeMotion.fixed_outside_target {V E H M : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (t : ℝ) (y : M) (hy : y ∉ Φ.target) : A.family (t, y) = y :=
  A.fixedOutside t y (fun h => hy (A.support_subset h))

/-- The moved axis point where the sheet crosses. -/
theorem MorseCancellation.LongitudinalTubeMotion.crossing_axis {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞} (A : MorseCancellation.LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) : A.family (A.time, Φ 0) = Φ (1, 0) := by
  rw [A.native_axis h0, A.time_value]

/-- The whole sheet crosses the level exactly at the crossing axis. -/
theorem MorseCancellation.LongitudinalTubeMotion.whole_sheet_crossing_iff {U V E H M X Y : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) J (ℝ × (U × V)) M ∞}
    (A : MorseCancellation.LongitudinalTubeMotion Φ) {f : X → M} {g : Y → M}
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
    let w := MorseCancellation.longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, z)
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

/-- The sheet coordinate derivative is surjective along the axis. -/
theorem MorseCancellation.surjective_sheet_coordinate_mfderiv {U W H X : Type*} [NormedAddCommGroup U]
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

/-- The native coordinate plane traces the sheet transversely. -/
theorem MorseCancellation.native_coordinate_plane_trace_transverse {U H X : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X] {V H' Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] {α : X → U} {β : Y → V} {x : X} {y : Y} {η : ℝ → ℝ}
    {τ κ : ℝ} (hα : MDifferentiableAt I 𝓘(ℝ, U) α x) (hβ : MDifferentiableAt I' 𝓘(ℝ, V) β y)
    (hαs : Function.Surjective (mfderiv I 𝓘(ℝ, U) α x))
    (hβs : Function.Surjective (mfderiv I' 𝓘(ℝ, V) β y)) (hη : HasDerivAt η κ τ) (hκ : κ ≠ 0) :
    NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' 𝓘(ℝ, ℝ × (U × V))
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

/-- The whole moved sheet remains transverse to the level. -/
theorem MorseCancellation.LongitudinalTubeMotion.whole_sheet_transverse {U V E HU HV H M X Y : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HV] [TopologicalSpace H] {I : ModelWithCorners ℝ U HU}
    {I' : ModelWithCorners ℝ V HV} {J : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace Y]
    [ChartedSpace HV Y] {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) J (ℝ × (U × V)) M ∞}
    (A : MorseCancellation.LongitudinalTubeMotion Φ) {f : X → M} {g : Y → M} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hfi : Function.Injective (mfderiv I J f x)) (hgi : Function.Injective (mfderiv I' J g y))
    (hrecf : ∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrecg : ∀ z ∈ Φ.source, Φ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) (hx : Φ 0 = f x)
    (hy : Φ (1, 0) = g y) (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) :
    NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' J (fun p : ℝ × X => A.family (p.1, f p.2)) g
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
    exact (PartialChart.bijective_mfderiv Φ.symm hfx).injective.comp hfi
  have hbi : Function.Injective (mfderiv I' 𝓘(ℝ, W) b y) := by
    rw [mfderiv_comp y (Φ.symm.mdifferentiableAt (by simp) hgy) hg]
    exact (PartialChart.bijective_mfderiv Φ.symm hgy).injective.comp hgi
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
  have hαs := MorseCancellation.surjective_sheet_coordinate_mfderiv P Q 0 ha hai hagerm
  have hβs := MorseCancellation.surjective_sheet_coordinate_mfderiv R S (1, 0) hb hbi hbgerm
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
  have hmodel : NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' 𝓘(ℝ, W) T B (A.time, x) y :=
    MorseCancellation.native_coordinate_plane_trace_transverse hα hβ hαs hβs hη A.time_rate.ne'
  have hnative :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff Φ hT hB
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

/-- Two endpoint sheets admit a clean arc avoiding a closed set. -/
theorem MorseCancellation.exists_clean_two_sheet_arc_avoiding {E M X Y Z : Type*} [NormedAddCommGroup E]
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

/-! ### Basin images of adapted windows -/

/-- Forward basins are covered by countably many smooth ball images. -/
theorem AdaptedWindows.exists_forward_basin_smooth_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) :
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
    MorseCancellation.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
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
      (SmoothODE.nativeFlowTimeDiffeomorph_of_field S.smooth S.flow S.integral
            (-(n : ℝ))).contMDiff.comp_contMDiffOn
        hlocal
  · ext x
    constructor
    · intro hx
      have hlim := hx.comp tendsto_natCast_atTop_atTop
      obtain ⟨n, hs, hn, hp'⟩ :=
        (hlim.eventually
            (MorseCancellation.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
      have hnew := (MorseCancellation.flow_time_atTop_limit_iff S.flow (n : ℝ) x p.val).mpr hx
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
        (MorseCancellation.flow_time_atTop_limit_iff S.flow (-(n : ℝ)) (c.splitChart.symm (0, v))
              p.val).mpr
          (hpoint v hv)

/-- Backward basins are covered by countably many smooth ball images. -/
theorem AdaptedWindows.exists_backward_basin_smooth_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) :
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
    MorseCancellation.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
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
      (SmoothODE.nativeFlowTimeDiffeomorph_of_field S.smooth S.flow S.integral
            (n : ℝ)).contMDiff.comp_contMDiffOn
        hlocal
  · ext x
    constructor
    · intro hx
      have hlim : Filter.Tendsto (fun n : ℕ => S.flow (-(n : ℝ)) x) Filter.atTop (𝓝 p.val) :=
        hx.comp (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      obtain ⟨n, hs, hn, hp'⟩ :=
        (hlim.eventually
            (MorseCancellation.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
      have hnew := (MorseCancellation.flow_time_atBot_limit_iff S.flow (-(n : ℝ)) x p.val).mpr hx
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
        (MorseCancellation.flow_time_atBot_limit_iff S.flow (n : ℝ) (c.splitChart.symm (v, 0))
              p.val).mpr
          (hpoint v hv)

/-- A basis element admits a smooth ball parametrization. -/
theorem MorseCancellation.exists_smooth_ball_parametrization {V : Type*} [NormedAddCommGroup V]
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

/-- A local smooth ball parametrization extends to a global image. -/
theorem MorseCancellation.exists_global_smooth_image_of_ball {V : Type*} [NormedAddCommGroup V]
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

/-- The native flow is the chart flow on the positive half-line. -/
theorem FlowCancellation.native_flow_eq_on_positive_halfline {E M : Type*}
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
      FlowSuspension.native_flow_segment_endpoints hV F hF ht
        (hG x).continuous.continuousOn hc
    simpa only [sub_zero, G.map_zero_apply] using hh.symm

/-- The native flow is the chart flow on the negative half-line. -/
theorem FlowCancellation.native_flow_eq_on_negative_halfline {E M : Type*}
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
      FlowSuspension.native_flow_segment_endpoints hV F hF ht
        (hG x).continuous.continuousOn hc
    have he := congrArg (F t) hh
    simpa only [zero_sub, ← F.map_add, add_neg_cancel, F.map_zero_apply, G.map_zero_apply] using
      he
  · subst t
    rw [G.map_zero_apply, F.map_zero_apply]

/-- A flow line between endpoint limits crosses the intermediate level. -/
theorem FlowCancellation.exists_level_crossing_of_endpoint_limits {X : Type*}
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

/-! ### Endpoint obstructions and basin counts -/

/-- The union of forward basins of high critical points. -/
def MorseCancellation.forwardHighBasins {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (a : ℝ) : Set M :=
  {x |
    ∃ p : ManifoldMorse.criticalPoints E f,
      a ≤ f p ∧ Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)}

/-- The union of backward basins of low critical points. -/
def MorseCancellation.backwardLowBasins {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (a : ℝ) : Set M :=
  {x |
    ∃ p : ManifoldMorse.criticalPoints E f,
      f p ≤ a ∧ Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)}

/-- The high forward basins as an intersection formulation. -/
theorem MorseCancellation.forwardHighBasins_eq_inter {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : forwardHighBasins S a = ⋂ t : ℝ, {x | a ≤ f (S.flow t x)} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hlim⟩ t
    have hmono :=
      FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    exact hp.trans (hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t)
  · intro hbound
    obtain ⟨-, -, q, hq, -, hlim, -⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    refine ⟨⟨q, hq⟩, ?_, hlim⟩
    exact
      ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim)
        (Filter.Eventually.of_forall hbound)

/-- The low backward basins as an intersection formulation. -/
theorem MorseCancellation.backwardLowBasins_eq_inter {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : backwardLowBasins S a = ⋂ t : ℝ, {x | f (S.flow t x) ≤ a} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hlim⟩ t
    have hmono :=
      FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    exact (hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t).trans hp
  · intro hbound
    obtain ⟨p, hp, -, -, hlim, -, -⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    refine ⟨⟨p, hp⟩, ?_, hlim⟩
    exact
      le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim)
        (Filter.Eventually.of_forall hbound)

/-- The endpoint obstruction set is closed. -/
theorem MorseCancellation.isClosed_endpoint_obstruction {E M : Type*} [NormedAddCommGroup E]
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

/-- The level minus the basins is the endpoint obstruction. -/
theorem MorseCancellation.levelBasin_compl_eq_endpoint_obstruction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) :
    (FlowCancellation.levelBasin S.flow f a)ᶜ =
      forwardHighBasins S a ∪ backwardLowBasins S a := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, q, hq, hback, hforward, -⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    by_cases hqa : a ≤ f q
    · exact Or.inl ⟨⟨q, hq⟩, hqa, hforward⟩
    by_cases hpa : f p ≤ a
    · exact Or.inr ⟨⟨p, hp⟩, hpa, hback⟩
    exact
      False.elim
        (hx
          (FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
            hback hforward (lt_of_not_ge hpa) (lt_of_not_ge hqa)))
  · intro hx hcross
    obtain ⟨t, ht⟩ := hcross
    have hmono :=
      FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    rcases hx with ⟨p, hp, hlim⟩ | ⟨p, hp, hlim⟩
    · have hh := hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t
      rw [ht] at hh
      exact hreg p (le_antisymm hh hp) p.property
    · have hh := hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t
      rw [ht] at hh
      exact hreg p (le_antisymm hp hh) p.property

/-- Forward basins are covered by global smooth images. -/
theorem AdaptedWindows.exists_forward_basin_global_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hd : Module.finrank ℝ E - MorseCancellation.nativeMorseIndex E f p ≤ d) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → M,
      (∀ n, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g n)) ∧
        {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} =
          ⋃ n, Set.range (g n) := by
  obtain ⟨r, hr, hsmooth, hcover⟩ := S.exists_forward_basin_smooth_images hf p
  have hdim : Module.finrank ℝ (S.data p).chart.PositiveCoordinates ≤ d := by
    have hh := (S.data p).chart.finrank_negative_add_positive
    rw [MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart] at hd
    omega
  choose g hg hrange using
    (fun n => MorseCancellation.exists_global_smooth_image_of_ball hdim hr (hsmooth n))
  refine ⟨g, hg, ?_⟩
  rw [hcover]
  exact Set.iUnion_congr (fun n => (hrange n).symm)

/-- Backward basins are covered by global smooth images. -/
theorem AdaptedWindows.exists_backward_basin_global_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hd : MorseCancellation.nativeMorseIndex E f p ≤ d) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → M,
      (∀ n, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g n)) ∧
        {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)} =
          ⋃ n, Set.range (g n) := by
  obtain ⟨r, hr, hsmooth, hcover⟩ := S.exists_backward_basin_smooth_images hf p
  have hdim : Module.finrank ℝ (S.data p).chart.NegativeCoordinates ≤ d := by
    rwa [MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart] at hd
  choose g hg hrange using
    (fun n => MorseCancellation.exists_global_smooth_image_of_ball hdim hr (hsmooth n))
  refine ⟨g, hg, ?_⟩
  rw [hcover]
  exact Set.iUnion_congr (fun n => (hrange n).symm)

/-- The index type of endpoint obstruction basins. -/
abbrev MorseCancellation.EndpointBasinIndex {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (a : ℝ) :=
  ({ p : ManifoldMorse.criticalPoints E f // a ≤ f p.val } × ℕ) ⊕
    ({ p : ManifoldMorse.criticalPoints E f // f p.val ≤ a } × ℕ)

/-- There are countably many endpoint obstruction basins. -/
theorem MorseCancellation.endpointBasinIndex_countable {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (a : ℝ) : Countable (EndpointBasinIndex (E := E) (f := f) a) := by
  let _ := S.finite.fintype
  unfold EndpointBasinIndex
  infer_instance

/-- The endpoint obstruction is covered by global smooth images. -/
theorem AdaptedWindows.exists_endpoint_obstruction_global_images {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) {d : ℕ}
    (hhigh :
      ∀ p : ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ d) :
    ∃ g : MorseCancellation.EndpointBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
        MorseCancellation.forwardHighBasins S a ∪ MorseCancellation.backwardLowBasins S a =
          ⋃ i, Set.range (g i) := by
  choose gF hgF hF using
    (fun p : { p : ManifoldMorse.criticalPoints E f // a ≤ f p.val } =>
      S.exists_forward_basin_global_images hf p.val (hhigh p.val p.property))
  choose gB hgB hB using
    (fun p : { p : ManifoldMorse.criticalPoints E f // f p.val ≤ a } =>
      S.exists_backward_basin_global_images hf p.val (hlow p.val p.property))
  let g : MorseCancellation.EndpointBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M :=
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

/-- The low backward basins form a closed set. -/
theorem MorseCancellation.isClosed_backwardLowBasins {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) : IsClosed (backwardLowBasins S a) := by
  rw [backwardLowBasins_eq_inter S hf]
  exact
    isClosed_iInter
      (fun t =>
        isClosed_le (hf.continuous.comp (S.flow.continuous continuous_const continuous_id))
          continuous_const)

/-- The index type of low backward basins. -/
abbrev MorseCancellation.LowBackwardBasinIndex {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (a : ℝ) :=
  { p : ManifoldMorse.criticalPoints E f // f p.val ≤ a } × ℕ

/-- There are countably many low backward basins. -/
theorem MorseCancellation.lowBackwardBasinIndex_countable {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (a : ℝ) : Countable (LowBackwardBasinIndex (E := E) (f := f) a) := by
  let _ := S.finite.fintype
  unfold LowBackwardBasinIndex
  infer_instance

/-- The low backward obstruction is covered by smooth images. -/
theorem AdaptedWindows.exists_low_backward_obstruction_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) {d : ℕ}
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ d) :
    ∃ g : MorseCancellation.LowBackwardBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
        MorseCancellation.backwardLowBasins S a = ⋃ i, Set.range (g i) := by
  choose g hg hcover using
    (fun p : { p : ManifoldMorse.criticalPoints E f // f p.val ≤ a } =>
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

/-! ### Joining in sublevels and basins -/

/-- A discrete family of smooth maps is jointly smooth. -/
theorem MorseCancellation.contMDiff_discrete_family {ι V E H M : Type*} [TopologicalSpace ι]
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

/-- The range of a discrete family is the union of the ranges. -/
theorem MorseCancellation.range_discrete_family {ι V M : Type*} [TopologicalSpace ι]
    [DiscreteTopology ι] [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M]
    (f : ι → V → M) : Set.range (fun p : ι × V => f p.1 p.2) = ⋃ i, Set.range (f i) := by
  ext x
  constructor
  · rintro ⟨⟨i, v⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, v, rfl⟩
  · intro hx
    obtain ⟨i, v, hv⟩ := Set.mem_iUnion.mp hx
    exact ⟨(i, v), hv⟩

/-- A point forward-limiting to a lower point joins it in the sublevel. -/
theorem MorseCancellation.joinedIn_sublevel_of_forward_limit {X : Type*} [TopologicalSpace X]
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

/-- Points with a common forward limit join in the sublevel. -/
theorem MorseCancellation.joined_sublevel_of_common_forward_limit {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {a : ℝ} (x y : { z : X // f z ≤ a }) {p : X}
    (hp : f p < a) (hx : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hy : Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) : Joined x y := by
  exact
    ((joinedIn_sublevel_of_forward_limit F hf hmono x.property hp hx).trans
        (joinedIn_sublevel_of_forward_limit F hf hmono y.property hp hy).symm).joined_subtype

/-- Points in an open forward basin join the limit point in it. -/
theorem MorseCancellation.joinedIn_open_forward_basin {X : Type*} [TopologicalSpace X]
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

/-- A minimum-index critical point's forward basin is joined. -/
theorem AdaptedWindows.joinedIn_minimum_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (hp : MorseCancellation.nativeMorseIndex E f p = 0) {x y : M}
    (hx : Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val))
    (hy : Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p.val)) :
    JoinedIn {z : M | Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val)} x y := by
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  have hpp : Filter.Tendsto (fun t => S.flow t p.val) Filter.atTop (𝓝 p.val) := by
    have heq : (fun t => S.flow t p.val) = fun _ => p.val :=
      funext
        (fun t =>
          FlowConstruction.flow_fixed_of_zero (S.smooth.of_le (by simp)) S.flow S.integral
            (S.zero p p.property) t)
    rw [heq]
    exact tendsto_const_nhds
  have hopen := S.isOpen_minimum_forward_basin hf p hp
  exact
    (MorseCancellation.joinedIn_open_forward_basin S.flow p.val hopen hpp hx).trans
      (MorseCancellation.joinedIn_open_forward_basin S.flow p.val hopen hpp hy).symm

/-! ### Smooth time germs and level cylinders -/

/-- Nonzero time derivative makes the time partial invertible. -/
theorem SmoothODE.scalar_partial_invertible {P : Type*} [NormedAddCommGroup P]
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

/-- A smooth time germ solving `F(q, θ q) = c` near a point of nonzero time derivative. -/
theorem SmoothODE.exists_smooth_scalar_time_germ {P : Type*} [NormedAddCommGroup P]
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

/-- The manifold version: a smooth level-time germ near nonzero time derivative. -/
theorem FlowCancellation.exists_native_smooth_time_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {H : M × ℝ → ℝ} {p : M} {t c v : ℝ}
    (hH : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H (p, t)) (hlevel : H (p, t) = c)
    (htime : HasDerivAt (fun s : ℝ => H (p, s)) v t) (hv : v ≠ 0) :
    ∃ θ : M → ℝ, θ p = t ∧ ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ p ∧ ∀ᶠ q in 𝓝 p, H (q, θ q) = c := by
  let e := modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) p
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
  obtain ⟨θ, hθ, hsmooth, hroot⟩ := SmoothODE.exists_smooth_scalar_time_germ hF hFc hFt hv
  refine ⟨θ ∘ e, hθ, hsmooth.contMDiffAt.comp p he, ?_⟩
  filter_upwards [e.open_source.mem_nhds hp, he.continuousAt hroot] with q hq hrootq
  have hqleft : e.symm (e q) = q := e.left_inv' hq
  change H (e.symm (e q), θ (e q)) = c at hrootq
  change H (q, θ (e q)) = c
  rwa [hqleft] at hrootq

/-- A smooth signed time to reach a regular level along a vector field. -/
theorem FlowCancellation.smooth_signed_level_time {E M : Type*} [NormedAddCommGroup E]
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
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hH : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : M × ℝ => f (F q.2 q.1)) :=
    hf.comp (SmoothODE.contMDiff_native_flow hV F hcurve)
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

/-- A flow cylinder over a regular level along a nonvanishing field. -/
theorem FlowCancellation.exists_native_level_flow_cylinder {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {c : ℝ} (hreg : ∀ x, f x = c → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) (z : { x : M // f x = c }) :
    letI := RegularLevel.chartedSpace hf hreg
    ∃ Φ :
      PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({ x : M // f x = c } × ℝ) M ∞,
      Φ.source = Set.univ ∧
        Φ.target = levelBasin F f c ∧
          (∀ p, Φ p = F p.2 p.1) ∧ ∀ x ∈ Φ.target, (Φ.symm x).2 = -signedLevelTime F f c x := by
  classical
  let _ := RegularLevel.chartedSpace hf hreg
  let L := { x : M // f x = c }
  let B := levelBasin F f c
  let θ := signedLevelTime F f c
  obtain ⟨hB, hθ, htranslate⟩ := smooth_signed_level_time hf hV F hcurve hboundary
  let r : M → L := fun x => if hx : x ∈ B then ⟨F (θ x) x, signedLevelTime_hits F f c hx⟩ else z
  let φ : L × ℝ → M := fun p => F p.2 p.1
  let ψ : M → L × ℝ := fun x => (r x, -θ x)
  have hflow := SmoothODE.contMDiff_native_flow hV F hcurve
  have hφ : ContMDiff (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ φ :=
    hflow.comp
      (((RegularLevel.contMDiff_inclusion hf hreg).comp contMDiff_fst).prodMk contMDiff_snd)
  have hψ : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) ∞ ψ B := by
    intro x hx
    have hθx := (hθ x hx).contMDiffAt (hB.mem_nhds hx)
    have hr : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, RegularLevel.Model E) ∞ r x := by
      apply (RegularLevel.contMDiffAt_iff_inclusion hf hreg 𝓘(ℝ, E) r x).mpr
      apply (hflow.contMDiffAt.comp x (contMDiffAt_id.prodMk hθx)).congr_of_eventuallyEq
      filter_upwards [hB.mem_nhds hx] with y hy
      change (r y : M) = F (θ y) y
      have hyB : y ∈ B := hy
      simp only [r, dif_pos hyB]
    exact (hr.prodMk hθx.neg).contMDiffWithinAt
  have hD : Continuous (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) :=
    (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
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
    PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (L × ℝ) M ∞ :=
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

/-! ### Connectedness of regular levels -/

/-- Endpoint basins join inside the regular level under the dimension bounds. -/
theorem AdaptedWindows.joinedIn_regular_level_of_endpoint_dimensions {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) {x y : M} (hxa : f x = a) (hya : f y = a) (γ : Path x y) :
    JoinedIn {z : M | f z = a} x y := by
  let _ := S.finite.fintype
  let K := MorseCancellation.EndpointBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := MorseCancellation.endpointBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_endpoint_obstruction_global_images hf a hhigh hlow
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun z : K × V => g z.1 z.2) :=
    MorseCancellation.contMDiff_discrete_family g hg
  let G : C(K × V, M) := ⟨fun z => g z.1 z.2, hG.continuous⟩
  have hrange : Set.range G = (FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [MorseCancellation.levelBasin_compl_eq_endpoint_obstruction S hf hreg, hcover]
    exact MorseCancellation.range_discrete_family g
  have hclosed : IsClosed (Set.range G) := by
    rw [hrange, MorseCancellation.levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact MorseCancellation.isClosed_endpoint_obstruction S hf a
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : M) (hz : f z = a) : z ∉ Set.range G := by
    rw [hrange, Set.mem_compl_iff, Classical.not_not]
    exact ⟨0, by simpa only [S.flow.map_zero_apply] using hz⟩
  obtain ⟨η, -, havoid⟩ :=
    MorseCancellation.exists_smooth_path_avoiding_closed_image γ G hG hclosed hdim' (hnot x hxa)
      (hnot y hya)
  have hcross (t : unitInterval) : η t ∈ FlowCancellation.levelBasin S.flow f a := by
    have hh := havoid t
    simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using hh
  let _ := RegularLevel.chartedSpace hf hreg
  let xL : { z : M // f z = a } := ⟨x, hxa⟩
  let yL : { z : M // f z = a } := ⟨y, hya⟩
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf hreg S.smooth S.flow S.integral
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

/-- The regular level is path connected under the endpoint dimension bounds. -/
theorem AdaptedWindows.pathConnectedSpace_regular_level_of_endpoint_dimensions {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [PathConnectedSpace M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) (z₀ : { z : M // f z = a }) :
    PathConnectedSpace { z : M // f z = a }
    where
  nonempty := ⟨z₀⟩
  joined x
    y :=
    (S.joinedIn_regular_level_of_endpoint_dimensions hf hreg hhigh hlow hdim x.property y.property
        (PathConnectedSpace.somePath x.val y.val)).joined_subtype

/-- In dimension six the middle regular level is path connected. -/
theorem AdaptedWindows.pathConnectedSpace_middle_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PathConnectedSpace M]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hhigh :
      ∀ p : ManifoldMorse.criticalPoints E f,
        a ≤ f p → 3 ≤ MorseCancellation.nativeMorseIndex E f p)
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ 3)
    (z₀ : { z : M // f z = a }) : PathConnectedSpace { z : M // f z = a } :=
  S.pathConnectedSpace_regular_level_of_endpoint_dimensions hf hreg
    (fun p hp => by have hh := hhigh p hp; omega) hlow (by omega) z₀

/-- Above index-three critical points the upper level is path connected. -/
theorem AdaptedWindows.pathConnectedSpace_index_three_upper_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    (p : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 3)
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

/-! ### Transversality for rearrangement -/

/-- A dimension bound making a map transverse to an ignored factor. -/
theorem MorseRearrangement.native_transverse_dimension_bound {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {f : X → N} {g : Y → N} {x : X} {y : Y}
    (ht : NativeTransversality.At I I' J f g x y) (hxy : g y = f x) :
    Module.finrank ℝ G ≤ Module.finrank ℝ D + Module.finrank ℝ Z := by
  let L : (D × Z) →L[ℝ] G := by
    exact (mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G)
  have hL : Function.Surjective L := ht hxy
  have hh := LinearMap.finrank_le_finrank_of_surjective (f := L.toLinearMap) hL
  simpa only [Module.finrank_prod] using hh

/-- Under the transverse dimension bound the ranges can be made disjoint. -/
theorem MorseRearrangement.disjoint_ranges_of_native_transverse_dimension
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ D H}
    {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] {f : X → N} {g : Y → N}
    (ht : ∀ x y, NativeTransversality.At I I' J f g x y)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) :
    Disjoint (Set.range f) (Set.range g) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  exact (not_le_of_gt hdim) (native_transverse_dimension_bound (ht x y) (hy.trans hx.symm))

/-- Transversality when the target factor is ignored. -/
theorem MorseRearrangement.native_transverse_of_ignored_factor {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] {R H'' W : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [TopologicalSpace H'']
    {I'' : ModelWithCorners ℝ R H''} [TopologicalSpace W] [ChartedSpace H'' W] {f : X → N}
    {g : Y → N} {x : X} {y : Y} (w : W) (hf : MDifferentiableAt I J f x)
    (ht : NativeTransversality.At (I.prod I'') I' J (f ∘ Prod.fst) g (x, w) y) :
    NativeTransversality.At I I' J f g x y := by
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

/-- A chart map can be perturbed to a transverse plateau. -/
theorem ChartMapPerturbation.exists_ambient_transverse_plateau
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
          (∀ y, e y = SupportedDiffeomorph.bumpFamily c.symm β (a, y)) ∧
            (∀ y ∉ c.symm '' tsupport β, e y = y) ∧
              SupportedDiffeomorph.IsotopicToIdentity e ∧
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
  have hdense := TransverseCoordinates.dense_native_translations hU hV hcf hcg hdim
  obtain ⟨δ, hδ, hdiff, -, hsource⟩ :=
    SupportedDiffeomorph.exists_radius_ambient_bumpFamily c.symm hβ hcompact hsupport
  obtain ⟨η, hη, hisotopy⟩ :=
    SupportedDiffeomorph.exists_radius_bumpFamily_isotopy c.symm hβ hcompact hsupport
  obtain ⟨a, ha, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε (lt_min hδ hη))
  have hn : ‖a‖ < Min.min ε (Min.min δ η) := by simpa only [dist_zero_left] using hnorm
  have haδ := (lt_min_iff.mp (lt_min_iff.mp hn).2).1
  have haη := (lt_min_iff.mp (lt_min_iff.mp hn).2).2
  obtain ⟨e, he⟩ := hdiff a haδ
  have hsrc := hsource a haδ
  refine ⟨a, (lt_min_iff.mp hn).1, e, he, ?_, hisotopy a haη e he, ?_⟩
  · intro y hy
    rw [he]
    exact SupportedDiffeomorph.bumpFamily_fixed_outside c.symm β a hy
  · intro x hfx hx y hxy
    have hnew : e (f x) ∈ c.source := by
      rw [he]
      exact SupportedDiffeomorph.bumpFamily_mem_target c.symm β a hsrc hfx
    have hgy : g y ∈ c.source := hxy ▸ hnew
    have hcfAt := hcf.contMDiffAt (hU.mem_nhds hfx)
    have hevent : c ∘ (e ∘ f) =ᶠ[𝓝 x] fun z => c (f z) + a := by
      filter_upwards [hU.mem_nhds hfx, hx.comp_tendsto hcfAt.continuousAt] with z hz hβz
      change β (c (f z)) = 1 at hβz
      change c (e (f z)) = c (f z) + a
      rw [he]
      have hh := SupportedDiffeomorph.bumpFamily_coordinates c.symm β a hsrc hz
      change
        c (SupportedDiffeomorph.bumpFamily c.symm β (a, f z)) =
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

/-- A compact-core chart patch for local transversality constructions. -/
structure NativeTransversality.Patch {G K N : Type*} [NormedAddCommGroup G]
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

/-- Compatibility of a patch with a map: the chart covers the core. -/
def NativeTransversality.Patch.Compatible {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] {X : Type*} [TopologicalSpace X]
    (p : NativeTransversality.Patch J X (N := N)) (f : X → N) : Prop :=
  Set.MapsTo f p.core p.plateau

/-- Every point of a compact space admits a patch around its image. -/
theorem NativeTransversality.exists_patch_at {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] {X : Type*} [TopologicalSpace X] [FiniteDimensional ℝ G] [J.Boundaryless]
    [IsManifold J ∞ N] [CompactSpace X] [T2Space X] {f : X → N} (hf : Continuous f) (x : X) :
    ∃ p : Patch J X (N := N), p.Compatible f ∧ x ∈ interior p.core := by
  let c := modelChartPartialDiffeomorph (I := J) (f x)
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

/-- One step of the finite transversality patch construction. -/
theorem NativeTransversality.exists_patch_step {D Z G H H' K X Y N : Type*}
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
            SupportedDiffeomorph.IsotopicToIdentity e := by
  let A : G × X → N := fun q =>
    SupportedDiffeomorph.bumpFamily (p i).chart.symm (p i).cutoff (q.1, f q.2)
  have hkeep : ∀ᶠ a in 𝓝 (0 : G), ∀ j, (p j).Compatible (fun x => A (a, x)) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      SupportedDiffeomorph.eventually_bumpFamily_maps_compact_into_open (p i).chart.symm
        (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hf.continuous
        (p j).core_compact (p j).plateau_open (hcompatible j)
  obtain ⟨δ, hδ, -, hsmooth, -⟩ :=
    SupportedDiffeomorph.exists_radius_ambient_bumpFamily (p i).chart.symm
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
    exact SupportedDiffeomorph.bumpFamily_zero _ _ _
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
    ChartMapPerturbation.exists_ambient_transverse_plateau (p i).chart hf hg
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

/-- Finitely many patches give a transverse diffeomorphism. -/
theorem NativeTransversality.exists_finite_patch_diffeomorph {D Z G H H' K X Y N : Type*}
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
      SupportedDiffeomorph.IsotopicToIdentity e ∧
        (∀ j, (p j).Compatible (e ∘ f)) ∧
          ∀ j ∈ s, ∀ x ∈ (p j).core, ∀ y, At I I' J (e ∘ f) g x y := by
  classical
    induction s using Finset.induction_on with
  |
    empty =>
    refine
      ⟨Diffeomorph.refl J N ∞, SupportedDiffeomorph.isotopicToIdentity_refl, hcompatible,
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

/-- An ambient diffeomorphism making the map transverse. -/
theorem NativeTransversality.exists_ambient_transverse_diffeomorph
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
      SupportedDiffeomorph.IsotopicToIdentity e ∧ ∀ x y, At I I' J (e ∘ f) g x y := by
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

/-- Under the dimension bound an ambient diffeomorphism makes the ranges disjoint. -/
theorem MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension
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
      SupportedDiffeomorph.IsotopicToIdentity e ∧
        Disjoint (Set.range (e ∘ f)) (Set.range g) := by
  classical
  let d := Module.finrank ℝ G - (Module.finrank ℝ D + Module.finrank ℝ Z)
  let f' : X × Hemisphere.Sphere d → N := f ∘ Prod.fst
  have hf' : ContMDiff (I.prod (𝓡 d)) J ∞ f' := hf.comp contMDiff_fst
  have hdim' :
    Module.finrank ℝ (D × EuclideanSpace ℝ (Fin d)) + Module.finrank ℝ Z = Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    dsimp [d]
    omega
  obtain ⟨e, he, ht⟩ :=
    NativeTransversality.exists_ambient_transverse_diffeomorph hf' hg hdim'
  have htrans : ∀ x y, NativeTransversality.At I I' J (e ∘ f) g x y := by
    intro x y
    let w : Hemisphere.Sphere d := Hemisphere.point Bool.true ⟨0, by simp []⟩
    apply
      native_transverse_of_ignored_factor (I'' := 𝓡 d) w
        ((e.contMDiff.comp hf).mdifferentiable (by simp) x)
    exact ht (x, w) y
  exact ⟨e, he, disjoint_ranges_of_native_transverse_dimension htrans hdim⟩

end Mathoverflow1973
