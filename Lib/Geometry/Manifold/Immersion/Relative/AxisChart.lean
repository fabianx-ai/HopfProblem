/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Immersion.Relative.FrameField
public import Lib.Geometry.Manifold.Immersion.Relative.Arc

/-!
# Axis charts with prescribed endpoint germs

The invertible endomorphisms of a finite-dimensional space `D` of dimension at least `2` form two
path components, distinguished by the sign of the determinant
(`LinearFramePaths.operatorComponent`, `LinearFramePaths.joined_operatorComponent`), so two germs
of smooth families of invertible endomorphisms at `0` and `1` with determinants of the same sign
extend to a single smooth family of invertible endomorphisms
(`LinearFramePaths.exists_smooth_invertible_frame_join`). Applied to the transverse parts of sheared
blocks this gives `AxisCoordinates.exists_smooth_sheared_frame_join` and
`AxisCoordinates.exists_smooth_sheared_frame_join_at`. Combined with the sheared tubular charts of
`Lib.Geometry.Manifold.Immersion.Relative.FrameField` this yields
`AxisCoordinates.exists_native_axis_chart_with_endpoint_germs`: given a chart `Ψ` along a compact piece
of the axis `ℝ × {0}` and two charts `Φ₀`, `Φ₁` agreeing with `Ψ` along the axis near `p` and `q`,
with transverse determinants of the same sign, there is a chart with the same axis as `Ψ` which
agrees with `Φ₀` near `(p, 0)` and with `Φ₁` near `(q, 0)`. This is how the clean charts at the two
ends of a Whitney arc are joined into one chart along the arc.

## References

* Milnor, *Lectures on the h-cobordism theorem*, §6.
* cf. Hirsch, *Differential Topology*, Ch. 4.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- The linear isomorphism between endomorphisms of `D` and `ι × ι` matrices given by a basis. -/
def LinearFramePaths.matrixCoordinates {D ι : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ D) : (D →L[ℝ] D) ≃L[ℝ] Matrix ι ι ℝ :=
  (LinearMap.toContinuousLinearMap.symm.trans (LinearMap.toMatrix b b)).toContinuousLinearEquiv

/-- The determinant of the matrix of an endomorphism is its determinant. -/
theorem LinearFramePaths.det_matrixCoordinates {D ι : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ D)
    (A : D →L[ℝ] D) : Matrix.det (matrixCoordinates b A) = A.toLinearMap.det :=
  LinearMap.det_toMatrix b A.toLinearMap

/-- The open set of endomorphisms of `D` whose determinant has the sign of `σ`; for `σ ≠ 0` these
are the two connected components of the invertible endomorphisms. -/
def LinearFramePaths.operatorComponent {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (σ : ℝ) : TopologicalSpace.Opens (D →L[ℝ] D) :=
  ⟨{A | 0 < σ * A.toLinearMap.det},
    isOpen_lt continuous_const (continuous_const.mul ContinuousLinearMap.continuous_det)⟩

/-- Two invertible endomorphisms with determinants of the same sign are joined by a path: `GL(D)`
has two connected components. -/
theorem LinearFramePaths.joined_operatorComponent {D ι : Type*} [NormedAddCommGroup D]
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

/-- Two germs of smooth families of endomorphisms at `0` and `1`, invertible and with determinants
of the same sign, extend to a single smooth family of invertible endomorphisms with those germs. -/
theorem LinearFramePaths.exists_smooth_invertible_frame_join {D ι : Type*}
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
    exists_smooth_open_curve_with_endpoint_germs S ha hb hU hV h0U h1V ha0 hb1 γ
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

/-- Two germs of sheared frames at `0` and `1`, whose transverse parts have determinants of the same
sign, extend to a single smooth family of invertible sheared blocks with those germs. -/
theorem AxisCoordinates.exists_smooth_sheared_frame_join {V ι : Type*}
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
              (∀ s, (FrameField.shearedBlock (A s) (T s)).IsInvertible) ∧
                (A =ᶠ[𝓝 (0 : ℝ)] A₀) ∧
                  (A =ᶠ[𝓝 (1 : ℝ)] A₁) ∧ (T =ᶠ[𝓝 (0 : ℝ)] T₀) ∧ (T =ᶠ[𝓝 (1 : ℝ)] T₁) := by
  let S : TopologicalSpace.Opens (V →L[ℝ] ℝ) := ⟨Set.univ, isOpen_univ⟩
  let γ : Path (⟨A₀ 0, Set.mem_univ _⟩ : S) ⟨A₁ 1, Set.mem_univ _⟩ :=
    { toFun := fun t => ⟨(1 - (t : ℝ)) • A₀ 0 + (t : ℝ) • A₁ 1, Set.mem_univ _⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
  obtain ⟨A, hA, -, ha₀, ha₁⟩ :=
    exists_smooth_open_curve_with_endpoint_germs S hA₀ hA₁ hU₀ hU₁ h0 h1 (Set.mem_univ _)
      (Set.mem_univ _) γ
  obtain ⟨T, hT, hi, -, ht₀, ht₁⟩ :=
    LinearFramePaths.exists_smooth_invertible_frame_join basis hT₀ hT₁ hU₀ hU₁ h0 h1 hsign
  have hTi (s : ℝ) : (T s).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (T s).toLinearMap (hi s)).toContinuousLinearEquiv, rfl⟩
  exact
    ⟨A, T, hA, hT, hTi, fun s => FrameField.isInvertible_shearedBlock (A s) (T s) (hTi s),
      ha₀, ha₁, ht₀, ht₁⟩

/-- The previous statement at two arbitrary parameters `p < q` in place of `0` and `1`. -/
theorem AxisCoordinates.exists_smooth_sheared_frame_join_at {V ι : Type*}
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
              (∀ s, (FrameField.shearedBlock (A s) (T s)).IsInvertible) ∧
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


/-- Axis chart with prescribed endpoint germs: given a chart `Ψ` along a compact piece of the axis
and two charts `Φ₀`, `Φ₁` agreeing with it along the axis near `p` and `q`, with transverse
determinants of the same sign, there is a chart `Φ` with the same axis as `Ψ` that agrees with
`Φ₀` near `(p, 0)` and with `Φ₁` near `(q, 0)`. -/
theorem AxisCoordinates.exists_native_axis_chart_with_endpoint_germs {V E M ι : Type*}
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
  let H := FrameField.shearedMap A T
  have hH : ContDiff ℝ ∞ H :=
    (contDiff_fst.add ((hA.comp contDiff_fst).clm_apply contDiff_snd)).prodMk
      ((hT.comp contDiff_fst).clm_apply contDiff_snd)
  have hHd (s : ℝ) : fderiv ℝ H (s, (0 : V)) = FrameField.shearedBlock (A s) (T s) :=
    (FrameField.hasFDerivAt_shearedMap_zero (hA.differentiable (by simp) s)
        (hT.differentiable (by simp) s)).fderiv
  have hv₀ : (fun s : ℝ => R₀ (s, (0 : V))) =ᶠ[𝓝 p] (fun s => H (s, 0)) := by
    filter_upwards [hU₀.mem_nhds h0U] with s hs
    exact (hx₀ s hs).trans (FrameField.shearedMap_zero A T s).symm
  have hv₁ : (fun s : ℝ => R₁ (s, (0 : V))) =ᶠ[𝓝 q] (fun s => H (s, 0)) := by
    filter_upwards [hU₁.mem_nhds h1U] with s hs
    exact (hx₁ s hs).trans (FrameField.shearedMap_zero A T s).symm
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
    (hvG s).trans (FrameField.shearedMap_zero A T s)
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
      isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ _)
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
    exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton) hGi hGl
      (Ψ.open_source.preimage hG.continuous) hGO
  let Φ := χ.trans Ψ
  have hΦzero : K ×ˢ {(0 : V)} ⊆ Φ.source := by
    intro p hp
    refine ⟨hχzero hp, ?_⟩
    change χ p ∈ Ψ.source
    rw [hχ]
    exact hχsub (hχzero hp)
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset hK Φ.open_source hΦzero
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
