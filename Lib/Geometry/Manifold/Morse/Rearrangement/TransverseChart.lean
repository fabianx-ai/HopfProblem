/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.Immersion.Relative.FrameField
public import Lib.Geometry.Manifold.LocalDiffeomorph
/-!
# Linear transverse corrections of tube charts

A tube chart `Φ : ℝ × V → M` around an arc `t ↦ Φ (t, 0)` can be composed with a linear
automorphism `C` of the transverse factor `V` (`MorseCancellation.linearTransverseChart`).
The axis is unchanged (`linearTransverseChart_axis`), and the determinant of the transverse
block of a transition derivative `fderiv (Ψ.symm ∘ Φ) (t, 0)` is multiplied by `det C`
(`det_transition_linearTransverseChart`). Choosing `C` with prescribed determinant makes the
transverse orientations at the two ends of an arc agree
(`exists_compatible_sheet_endpoint_orientation`).

The second half restricts a tube chart to a neighbourhood of a compact axis segment `K` on
which two closed sets `S`, `T` met by the axis only at `p`, `q` are recognised as the coordinate
slices `{t = p} × N`, `{t = q} × P` (`exists_open_tube_sheet_recognition`,
`exists_clean_axis_tube_restriction`), and finds a coordinate box `Icc l u ×ˢ closedBall 0 r`
inside a tube around the unit axis segment (`exists_tube_support_box`).

This is the chart bookkeeping of the Whitney trick: an arc joining two intersection points is
thickened to a tube in which both sheets are coordinate planes
(cf. Milnor, *Lectures on the h-cobordism theorem*, §6).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Linear transverse chart corrections -/

/-- A chart composed with a linear transverse correction on the `V` factor. -/
def MorseCancellation.linearTransverseChart {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (C : V ≃L[ℝ] V) (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞ :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C).toDiffeomorph.toPartialDiffeomorph'.trans Φ

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

/-! ### Clean tube restrictions -/

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
