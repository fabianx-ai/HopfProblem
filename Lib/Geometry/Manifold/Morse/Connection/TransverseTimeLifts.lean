/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection.Suspension

/-!
# Transversality of flow sheets through transverse level maps

Two maps `α : X → L`, `β : Y → L` into a regular level `L = {f = c}` that are transverse at a
common point spread out along the flow to sheets `(x, s) ↦ F s (α x)` and `(y, t) ↦ F t (β y)`
in `M`, and these are transverse as well:

* `timeLiftLinear L α`, `surjective_time_lift_coprod`, `native_time_lift_derivative`: the
  derivative of `(x, s) ↦ (f x, s + v x)` and the surjectivity of the lifted coproduct;
* `native_transversality_time_lifts`, `native_transverse_sheets_of_level_maps`,
  `native_transverse_basin_tubes_of_level_maps`: transversality of the lifted sheets, together
  with the basins of their points;
* `native_vertical_cylinder_flow`, `native_corrected_cylinder_tails`: in a vertical flow-box
  chart `Φ` on `U × ℝ` the flow is `F t (Φ (z, s)) = Φ (z, s + t)`, and a corrected chart
  agreeing with `Φ` below height `0` and with `Φ ∘ (D × id)` above height `1` has flows agreeing
  with the old ones on the two tails.

cf. Milnor, *Lectures on the h-cobordism theorem*, §5 (the descending and ascending manifolds
of two critical points meet transversally iff their traces on a level between them do).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Transverse time lifts -/

/-- The linear time lift of a transverse vector. -/
def TransverseGerms.timeLiftLinear {A Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : A →L[ℝ] Z) (α : A →L[ℝ] ℝ) :
    (A × ℝ) →L[ℝ] (Z × ℝ) :=
  (L.comp (ContinuousLinearMap.fst ℝ A ℝ)).prod
    (ContinuousLinearMap.snd ℝ A ℝ + α.comp (ContinuousLinearMap.fst ℝ A ℝ))

/-- The time lift coproduct is surjective. -/
theorem TransverseGerms.surjective_time_lift_coprod {A B Z : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] (L : A →L[ℝ] Z) (R : B →L[ℝ] Z) (α : A →L[ℝ] ℝ) (β : B →L[ℝ] ℝ)
    (h : Function.Surjective (L.coprod R)) :
    Function.Surjective ((timeLiftLinear L α).coprod (timeLiftLinear R β)) := by
  rintro ⟨z, t⟩
  obtain ⟨⟨a, b⟩, hab⟩ := h z
  refine ⟨((a, t - α a - β b), (b, 0)), ?_⟩
  apply Prod.ext
  · exact hab
  · change (t - α a - β b + α a) + (0 + β b) = t
    ring

/-- The native time lift's derivative. -/
theorem TransverseGerms.native_time_lift_derivative {A Z : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {HA HZ X N : Type*}
    [TopologicalSpace HA] [TopologicalSpace HZ] {I : ModelWithCorners ℝ A HA}
    {J : ModelWithCorners ℝ Z HZ} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace N]
    [ChartedSpace HZ N] {f : X → N} {v : X → ℝ} {x : X} (s : ℝ) (hf : MDifferentiableAt I J f x)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x) :
    (mfderiv (I.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (fun p : X × ℝ => (f p.1, p.2 + v p.1)) (x, s) :
        (A × ℝ) →L[ℝ] (Z × ℝ)) =
      timeLiftLinear (A := A) (Z := Z) (mfderiv I J f x) (mvfderiv I v x) := by
  have hn := hf.hasMFDerivAt.comp (x, s) (hasMFDerivAt_fst (I := I) (I' := 𝓘(ℝ, ℝ)) (x, s))
  have hp := hv.hasMFDerivAt.comp (x, s) (hasMFDerivAt_fst (I := I) (I' := 𝓘(ℝ, ℝ)) (x, s))
  have ht := (hasMFDerivAt_snd (I := I) (I' := 𝓘(ℝ, ℝ)) (x, s)).add hp
  exact (hn.prodMk ht).mfderiv

/-- Native transversality from time lifts. -/
theorem TransverseGerms.native_transversality_time_lifts {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {HA HB HZ X Y N : Type*} [TopologicalSpace HA]
    [TopologicalSpace HB] [TopologicalSpace HZ] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} {J : ModelWithCorners ℝ Z HZ} [TopologicalSpace X]
    [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y] [TopologicalSpace N]
    [ChartedSpace HZ N] {f : X → N} {g : Y → N} {v : X → ℝ} {w : Y → ℝ} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x) (hw : MDifferentiableAt I' 𝓘(ℝ, ℝ) w y)
    (hxy : g y = f x) (htrans : NativeTransversality.At I I' J f g x y) (s t : ℝ) :
    NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ))
      (fun p : X × ℝ => (f p.1, p.2 + v p.1)) (fun p : Y × ℝ => (g p.1, p.2 + w p.1)) (x, s)
      (y, t) := by
  intro _
  rw [native_time_lift_derivative s hf hv, native_time_lift_derivative t hg hw]
  exact surjective_time_lift_coprod _ _ _ _ (htrans hxy)

/-- Native transverse sheets from level maps. -/
theorem TransverseGerms.native_transverse_sheets_of_level_maps
    {A B Z E HA HB HZ HE X Y N M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HA] [TopologicalSpace HB]
    [TopologicalSpace HZ] [TopologicalSpace HE] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} {J : ModelWithCorners ℝ Z HZ} {J' : ModelWithCorners ℝ E HE}
    [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
    [TopologicalSpace N] [ChartedSpace HZ N] [TopologicalSpace M] [ChartedSpace HE M]
    (C : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) J' (N × ℝ) M ∞) {f : X → N} {g : Y → N} {v : X → ℝ}
    {w : Y → ℝ} {x : X} {y : Y} (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x) (hw : MDifferentiableAt I' 𝓘(ℝ, ℝ) w y)
    (hxy : g y = f x) (htrans : NativeTransversality.At I I' J f g x y) {s t : ℝ}
    (hphase : t + w y = s + v x) (hsource : (f x, s + v x) ∈ C.source) :
    NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ)) J'
      (fun p : X × ℝ => C (f p.1, p.2 + v p.1)) (fun p : Y × ℝ => C (g p.1, p.2 + w p.1)) (x, s)
      (y, t) := by
  let F : X × ℝ → N × ℝ := fun p => (f p.1, p.2 + v p.1)
  let G : Y × ℝ → N × ℝ := fun p => (g p.1, p.2 + w p.1)
  have hF : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) F (x, s) :=
    (hf.comp (x, s) mdifferentiableAt_fst).prodMk
      (mdifferentiableAt_snd.add (hv.comp (x, s) mdifferentiableAt_fst))
  have hG : MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) G (y, t) :=
    (hg.comp (y, t) mdifferentiableAt_fst).prodMk
      (mdifferentiableAt_snd.add (hw.comp (y, t) mdifferentiableAt_fst))
  have hcross : G (y, t) = F (x, s) := Prod.ext hxy hphase
  exact
    (native_transversality_partial_diffeomorph_iff C hF hG hcross hsource).mp
      (native_transversality_time_lifts hf hg hv hw hxy htrans s t)

/-- Native transverse basin tubes from level maps. -/
theorem FlowSuspension.native_transverse_basin_tubes_of_level_maps {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {A B HA HB X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ z, f z = c → z ∉ ManifoldMorse.criticalPoints E f)
    {V : (z : M) → TangentSpace 𝓘(ℝ, E) z}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ z, IsMIntegralCurve (fun t => F t z) V)
    (hboundary : ∀ z, f z = c → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) {p q : M} :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ (α : X → { z : M // f z = c }) (β : Y → { z : M // f z = c }) (x : X) (y : Y),
      MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
        MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y →
          β y = α x →
            NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
              (∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => F t (α u)) Filter.atBot (𝓝 q)) →
                (∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => F t (β u)) Filter.atTop (𝓝 p)) →
                  let S : X × ℝ → M := fun w => F w.2 (α w.1)
                  let T : Y × ℝ → M := fun w => F w.2 (β w.1)
                  MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) S (x, 0) ∧
                    MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) T (y, 0) ∧
                      S (x, 0) = (α x : M) ∧
                        T (y, 0) = (α x : M) ∧
                          (∀ᶠ u in 𝓝 (x, (0 : ℝ)),
                              Filter.Tendsto (fun t => F t (S u)) Filter.atBot (𝓝 q)) ∧
                            (∀ᶠ u in 𝓝 (y, (0 : ℝ)),
                                Filter.Tendsto (fun t => F t (T u)) Filter.atTop (𝓝 p)) ∧
                              NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ))
                                𝓘(ℝ, E) S T (x, 0) (y, 0) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  intro α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain ⟨C, hsource, -, hformula, -⟩ :=
    exists_native_level_flow_cylinder_with_field hf hreg hV F hF hboundary (α x)
  have hxC : (α x, (0 : ℝ)) ∈ C.source := by rw [hsource]; exact Set.mem_univ _
  have hyC : (β y, (0 : ℝ)) ∈ C.source := by rw [hsource]; exact Set.mem_univ _
  have hS : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (fun w : X × ℝ => C (α w.1, w.2)) (x, 0) :=
    (C.mdifferentiableAt (by simp) hxC).comp (x, 0)
      ((hα.comp (x, 0) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd)
  have hT :
    MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (fun w : Y × ℝ => C (β w.1, w.2)) (y, 0) :=
    (C.mdifferentiableAt (by simp) hyC).comp (y, 0)
      ((hβ.comp (y, 0) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd)
  have ht :=
    TransverseGerms.native_transverse_sheets_of_level_maps C hα hβ (v := fun _ : X =>
      (0 : ℝ)) (w := fun _ : Y => (0 : ℝ)) mdifferentiableAt_const mdifferentiableAt_const hcross
      htrans (s := 0) (t := 0) rfl (by simpa only [add_zero] using hxC)
  refine ⟨?_, ?_, F.map_zero_apply _, ?_, ?_, ?_, ?_⟩
  · simpa only [hformula] using hS
  · simpa only [hformula] using hT
  · change F 0 (β y) = (α x : M)
    rw [F.map_zero_apply, hcross]
  · filter_upwards [continuous_fst.continuousAt hαbasin] with u hu
    exact (MorseCancellation.flow_time_atBot_limit_iff F u.2 (α u.1) q).mpr hu
  · filter_upwards [continuous_fst.continuousAt hβbasin] with u hu
    exact (MorseCancellation.flow_time_atTop_limit_iff F u.2 (β u.1) p).mpr hu
  · simpa only [add_zero, hformula] using ht

/-- The native vertical cylinder flow. -/
theorem FlowSuspension.native_vertical_cylinder_flow {Z E M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (z : Z) (hz : z ∈ U)
    (s t : ℝ) : F t (Φ (z, s)) = Φ (z, s + t) := by
  let γ : ℝ → M := fun t => Φ (z, s + t)
  have hγ : IsMIntegralCurve γ V := by
    intro t
    have hstay : (z, s + t) ∈ Φ.source := by rw [hsource]; exact ⟨hz, Set.mem_univ _⟩
    have hcoord : HasDerivAt (fun r : ℝ => (z, s + r)) (0, 1) t :=
      (hasDerivAt_const t z).prodMk ((hasDerivAt_id t).const_add s)
    have hd :=
      FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm (fun _ : Z × ℝ => (0, 1))
        hcoord hstay
    change
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) (γ t))) at hd
    rw [← hmodel (γ t) (Φ.map_source' hstay)] at hd
    exact hd
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hF (Φ (z, s))) hγ (t₀ := 0)
      (by simp only [γ, F.map_zero_apply, add_zero])
  exact congrFun heq t

/-- The corrected cylinder tails. -/
theorem FlowSuspension.native_corrected_cylinder_tails {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    (Φ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hΦsource : Φ.source = U ×ˢ Set.univ) (hΩsource : Ω.source = U ×ˢ Set.univ)
    {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hΦmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (hΩmodel :
      ∀ x ∈ Ω.target,
        W x = FlowConstruction.partialChartField Ω.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W) (D : Z → Z) (hDU : Set.MapsTo D U U)
    (hleft : ∀ p, p.2 ≤ 0 → Ω p = Φ p) (hright : ∀ p, 1 ≤ p.2 → Ω p = Φ (D p.1, p.2)) :
    (∀ z ∈ U, ∀ t : ℝ, t ≤ 0 → G t (Φ (z, 0)) = F t (Φ (z, 0))) ∧
      (∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → G t (Ω (z, 1)) = F t (Ω (z, 1))) := by
  constructor
  · intro z hz t ht
    rw [← hleft (z, 0) le_rfl, native_vertical_cylinder_flow Ω hΩsource hW hΩmodel G hG z hz 0 t,
      zero_add, hleft (z, t) ht, hleft (z, 0) le_rfl,
      native_vertical_cylinder_flow Φ hΦsource hV hΦmodel F hF z hz 0 t, zero_add]
  · intro z hz t ht
    rw [native_vertical_cylinder_flow Ω hΩsource hW hΩmodel G hG z hz 1 t,
      hright (z, 1 + t) (by dsimp; linarith), hright (z, 1) le_rfl,
      native_vertical_cylinder_flow Φ hΦsource hV hΦmodel F hF (D z) (hDU hz) 1 t]

end
