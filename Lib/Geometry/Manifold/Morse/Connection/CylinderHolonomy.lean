/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection.CubicEndpoints
import Lib.Geometry.Manifold.Morse.Connection.Suspension
import Lib.Geometry.Manifold.Morse.Connection.TransverseBlocks
import Lib.Geometry.Manifold.Morse.Connection.TransverseTimeLifts

/-!
# Holonomy corrections of a flow cylinder

Let `Φ` be a vertical flow-box chart of a descent field `V` on `U × ℝ` with
`f (Φ (z, t)) = c - t` for `t ∈ (0, 1)`.

* `exists_native_vertical_field_replacement`, `mvfderiv_native_height_field`,
  `flow_preserves_base_region`, `exists_native_suspension_chart`: replacing the model field
  `(0, 1)` inside a compact part of the chart by a field of height component `1`.
* `exists_full_cylinder_holonomy`: a supported relative isotopy `D` of the base `U` is realised
  by a new field `V'`, equal to `V` outside a compact subset of the band `c - 1 < f < c`, whose
  flow `G` satisfies `G 1 (Φ (x, 0)) = Φ (D x, 1)`, together with a new vertical chart `Ω`
  agreeing with `Φ` below height `0` and with `Φ ∘ (D × id)` above height `1`.
* `exists_native_block_holonomy`: with `D` chosen by `TransverseGerms.exists_cylinder_block_correction`,
  so that the stable and unstable sheets `Q`, `P` become linear blocks `(L₁, L₂)` in the
  corrected chart, keeping the connection unique on the level;
* `corrected_cylinder_unique_connection`: the corrected flow still has a unique connecting
  orbit from `q` to `p`;
* `cylinder_phase_basin_coordinates`, `cylinder_outgoing_basin_labels`,
  `cylinder_incoming_basin_labels`: basins read off along the cylinder through labelled sheets.

cf. Milnor, *Lectures on the h-cobordism theorem*, §4 and §5 (an isotopy of a level surface
is realised by altering the gradient-like field between two levels).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### The cancelled descent field -/

/-- A native vertical field replacement exists. -/
theorem FlowSuspension.exists_native_vertical_field_replacement {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [TopologicalSpace M] [ChartedSpace B M] [T2Space M]
    [IsManifold 𝓘(ℝ, B) ∞ M] (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    {W : (E × ℝ) → E × ℝ} (hW : ContDiff ℝ ∞ W) (hWheight : ∀ p, (W p).2 = 1) {K : Set (E × ℝ)}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ p ∉ K, W p = (0, 1)) :
    ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, B) x,
      ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
        (∀ x ∈ Φ.target, V' x = FlowConstruction.partialChartField Φ.symm W x) ∧
          (∀ x, V' x = 0 ↔ V x = 0) ∧ ∀ x ∉ Φ '' K, ∀ᶠ y in 𝓝 x, V' y = V y := by
  let Wn := FlowConstruction.partialChartField Φ.symm W
  have hWn :
    ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, Wn x⟩ : TangentBundle 𝓘(ℝ, B) M))
      Φ.target :=
    FlowConstruction.contMDiffOn_partialChartField Φ.symm hW
  have hreg (x : M) (hx : x ∈ Φ.target) : Wn x ≠ 0 := by
    intro hz
    have hWzero := (MorseCancellation.partialChartField_zero_iff Φ W hx).mp hz
    have hh := congrArg Prod.snd hWzero
    rw [hWheight] at hh
    exact one_ne_zero hh
  have hregV (x : M) (hx : x ∈ Φ.target) : V x ≠ 0 := by
    rw [hmodel x hx]
    intro hz
    have hh := (MorseCancellation.partialChartField_zero_iff Φ (fun _ : E × ℝ => (0, 1)) hx).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hkeep (x : M) (hx : x ∈ Φ.target) (hnot : x ∉ Φ '' K) : Wn x = V x := by
    have hz : Φ.symm x ∉ K := fun h => hnot ⟨Φ.symm x, h, Φ.right_inv' hx⟩
    rw [hmodel x hx]
    change FlowConstruction.partialChartField Φ.symm W x = _
    unfold FlowConstruction.partialChartField
    rw [VectorField.mpullback_apply, VectorField.mpullback_apply, hfix _ hz]
  obtain ⟨V', hV', hnew, hzeros, hgerm⟩ :=
    LocalFieldReplacement.exists_smooth_field_replacement Φ V Wn hV hWn hK hKΦ hkeep hreg
  refine ⟨V', hV', hnew, ?_, hgerm⟩
  intro x
  exact (hzeros x).trans ⟨And.left, fun hx => ⟨hx, fun ht => hregV x ht hx⟩⟩

/-- The native height field's derivative. -/
theorem FlowSuspension.mvfderiv_native_height_field {E B M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace M]
    [ChartedSpace B M] (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {b : ℝ} (hheight : ∀ p ∈ Φ.source, f (Φ p) = b - p.2)
    (W : (E × ℝ) → E × ℝ) {x : M} (hx : x ∈ Φ.target) :
    mvfderiv 𝓘(ℝ, B) f x (FlowConstruction.partialChartField Φ.symm W x) =
      -(W (Φ.symm x)).2 := by
  let q := Φ.symm x
  have hq : q ∈ Φ.source := Φ.map_target' hx
  have heq : (f ∘ Φ) =ᶠ[𝓝 q] (fun p : E × ℝ => b - p.2) := by
    filter_upwards [Φ.open_source.mem_nhds hq] with p hp
    exact hheight p hp
  have hd : fderiv ℝ (f ∘ Φ) q = fderiv ℝ (fun p : E × ℝ => b - p.2) q := heq.fderiv_eq
  rw [FlowConstruction.mvfderiv_partialChartField hf Φ.symm W hx]
  change fderiv ℝ (f ∘ Φ) q (W q) = -(W q).2
  rw [hd]
  have hh := (hasFDerivAt_const (𝕜 := ℝ) b q).sub (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have hh' :
    fderiv ℝ (fun p : E × ℝ => b - p.2) q =
      (0 : (E × ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.snd ℝ E ℝ :=
    hh.fderiv
  rw [hh']
  simp

/-! ### Cylinder holonomy -/

/-- The flow preserves the base region. -/
theorem FlowSuspension.flow_preserves_base_region {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : Flow ℝ (E × ℝ)) {K U : Set E} (hKU : K ⊆ U)
    (hfix : ∀ x ∉ K, ∀ s t : ℝ, F t (x, s) = (x, s + t)) {p : E × ℝ} (hp : p.1 ∈ U) (t : ℝ) :
    (F t p).1 ∈ U := by
  by_contra hout
  have hnotK : (F t p).1 ∉ K := fun h => hout (hKU h)
  have hh := hfix (F t p).1 hnotK (F t p).2 (-t)
  change F (-t) (F t p) = ((F t p).1, (F t p).2 + -t) at hh
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply] at hh
  have he := congrArg (fun z : E × ℝ => z.1) hh
  change p.1 = (F t p).1 at he
  exact hout (he ▸ hp)

/-- A native suspension chart exists. -/
theorem FlowSuspension.exists_native_suspension_chart {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞) {U : Set E}
    (hsource : Φ.source = U ×ˢ Set.univ) {D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞} {K : Set E}
    (hKU : K ⊆ U) {W : (E × ℝ) → E × ℝ} {F : Flow ℝ (E × ℝ)} (C : SuspensionCoordinates D K W F)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hmodel : ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) :
    ∃ Ω : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
      Ω.source = Φ.source ∧
        Ω.target = Φ.target ∧
          (∀ p, Ω p = Φ (C.chart p)) ∧
            (∀ y ∈ Ω.target,
                V y =
                  FlowConstruction.partialChartField Ω.symm (fun _ : E × ℝ => (0, 1)) y) ∧
              (∀ p, p.2 ≤ 0 → Ω p = Φ p) ∧ (∀ p, 1 ≤ p.2 → Ω p = Φ (D p.1, p.2)) := by
  let Ω := C.chart.toPartialDiffeomorph.trans Φ
  have hΩsource : Ω.source = Φ.source := by
    ext p
    change (p ∈ (Set.univ : Set (E × ℝ)) ∧ C.chart p ∈ Φ.source) ↔ p ∈ Φ.source
    rw [hsource]
    simp only [Set.mem_univ, true_and, Set.mem_prod, and_true, C.base_iff U hKU]
  have hΩtarget : Ω.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ (Set.univ : Set (E × ℝ))) ↔ y ∈ Φ.target
    simp only [Set.mem_univ, and_true]
  have hpush (p : E × ℝ) (_ : p ∈ C.chart.toPartialDiffeomorph.source) :
    fderiv ℝ C.chart.toPartialDiffeomorph p (0, 1) = W (C.chart p) := by
    calc
      fderiv ℝ C.chart.toPartialDiffeomorph p (0, 1) = suspensionField C.chart (C.chart p) := by
        simp only [suspensionField, C.chart.symm_apply_apply]
        rfl
      _ = W (C.chart p) := (congrArg (fun w => w (C.chart p)) C.field_eq).symm
  refine ⟨Ω, hΩsource, hΩtarget, fun _ => rfl, ?_, ?_, ?_⟩
  · intro y hy
    have hyt : y ∈ Φ.target := hΩtarget ▸ hy
    rw [hmodel y hyt]
    exact
      (MorseCancellation.partialChartField_of_model_conjugacy C.chart.toPartialDiffeomorph Φ
          (fun _ : E × ℝ => (0, 1)) W hpush hy).symm
  · intro p hp
    change Φ (C.chart p) = Φ p
    rw [C.lower p hp]
  · intro p hp
    change Φ (C.chart p) = Φ (D p.1, p.2)
    rw [C.upper p hp]

/-- A full cylinder holonomy exists. -/
theorem FlowSuspension.exists_full_cylinder_holonomy {E B M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M]
    [T2Space M] [CompactSpace M] (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    {U : Set E} (hsource : Φ.source = U ×ˢ Set.univ) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hheight : ∀ p ∈ Φ.source, p.2 ∈ Set.Ioo (0 : ℝ) 1 → f (Φ p) = c - p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) V)
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {K S : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (I : SupportedDiffeomorph.SupportedRelativeIsotopy D K S) :
    ∃ (N : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, B) x) (G : Flow ℝ M),
      IsCompact N ∧
        N ⊆ Φ.target ∩ f ⁻¹' Set.Ioo (c - 1) c ∧
          ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
              (∀ x, V' x = 0 ↔ V x = 0) ∧
                (∀ x, mvfderiv 𝓘(ℝ, B) f x (V x) < 0 → mvfderiv 𝓘(ℝ, B) f x (V' x) < 0) ∧
                  (∀ x ∉ N, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                    (∀ x ∈ Φ.target, ∀ t, G t x ∈ Φ.target) ∧
                      (∀ x ∉ Φ.target, ∀ t, G t x = H t x) ∧
                        (∀ x ∈ U, G 1 (Φ (x, 0)) = Φ (D x, 1)) ∧
                          (∀ x ∈ U ∩ S, ∀ s t : ℝ, G t (Φ (x, s)) = Φ (x, s + t)) ∧
                            ∃ Ω : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
                              Ω.source = U ×ˢ Set.univ ∧
                                Ω.target = Φ.target ∧
                                  (∀ y ∈ Ω.target,
                                      V' y =
                                        FlowConstruction.partialChartField Ω.symm
                                          (fun _ : E × ℝ => (0, 1)) y) ∧
                                    (∀ p, p.2 ≤ 0 → Ω p = Φ p) ∧
                                      (∀ p, 1 ≤ p.2 → Ω p = Φ (D p.1, p.2)) ∧
                                        (∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0))) ∧
                                          (∀ z ∈ U, ∃ w ∈ U, Ω (z, 1) = Φ (w, 1)) ∧
                                            (∀ z ∈ U,
                                                ∀ t : ℝ,
                                                  t ≤ 0 → G t (Φ (z, 0)) = H t (Φ (z, 0))) ∧
                                              (∀ z ∈ U,
                                                ∀ t : ℝ,
                                                  0 ≤ t → G t (Ω (z, 1)) = H t (Ω (z, 1))) := by
  obtain ⟨W, F, hW, hWheight, -, hsupp, hF, hFend, -, hFoutside, hFfixed, ⟨Cdata⟩⟩ :=
    exists_compact_isotopy_suspension D hK I
  let C : Set (E × ℝ) := K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)
  have hC : IsCompact C := hK.prod CompactIccSpace.isCompact_Icc
  have hCsource : C ⊆ Φ.source := by
    rw [hsource]
    exact fun p hp => ⟨hKU hp.1, Set.mem_univ _⟩
  have hWfix (p : E × ℝ) (hp : p ∉ C) : W p = (0, 1) := by
    have hn : p ∉ tsupport (fun z : E × ℝ => W z - (0, 1)) := fun h => hp (hsupp h)
    have hh := image_eq_zero_of_notMem_tsupport hn
    exact sub_eq_zero.mp hh
  obtain ⟨V', hV', hnew, hzeros, hgerm⟩ :=
    exists_native_vertical_field_replacement Φ V hV hmodel hW hWheight hC hCsource hWfix
  let N := Φ '' C
  have hN : IsCompact N :=
    hC.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hslab (p : E × ℝ) (hp : p ∈ C) : p.2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp.2.1, hp.2.2]
  have hNsub : N ⊆ Φ.target ∩ f ⁻¹' Set.Ioo (c - 1) c := by
    rintro y ⟨p, hp, rfl⟩
    refine ⟨Φ.map_source' (hCsource hp), ?_⟩
    change f (Φ p) ∈ Set.Ioo (c - 1) c
    rw [hheight p (hCsource hp) (hslab p hp)]
    constructor <;> linarith [(hslab p hp).1, (hslab p hp).2]
  let R :=
    PartialChart.restrictSource Φ
      (isOpen_univ.prod (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)))
  have hRheight (p : E × ℝ) (hp : p ∈ R.source) : f (R p) = c - p.2 := hheight p hp.1 hp.2.2
  have hnegN (y : M) (hy : y ∈ N) : mvfderiv 𝓘(ℝ, B) f y (V' y) = -1 := by
    rcases hy with ⟨p, hp, rfl⟩
    have hpR : p ∈ R.source := ⟨hCsource hp, Set.mem_univ _, hslab p hp⟩
    rw [hnew (Φ p) (Φ.map_source' (hCsource hp))]
    change mvfderiv 𝓘(ℝ, B) f (R p) (FlowConstruction.partialChartField R.symm W (R p)) = -1
    rw [mvfderiv_native_height_field R hf hRheight W (R.map_source' hpR), hWheight]
  have hV'₁ := hV'.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let G := FlowConstruction.compactFlow hV'₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) V' :=
    FlowConstruction.isMIntegralCurve_compactFlow hV'₁ x
  have hstay (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : F t p ∈ Φ.source := by
    rw [hsource] at hp ⊢
    exact ⟨flow_preserves_base_region F hKU hFoutside hp.1 t, Set.mem_univ _⟩
  have hfull (p : E × ℝ) (hp : p ∈ Φ.source) (t : ℝ) : G t (Φ p) = Φ (F t p) :=
    native_chart_flow_all_time Φ hV'₁ G hG F W hF hnew (hstay p hp) t
  have hinv := native_chart_target_invariant Φ hV'₁ G hG F W hF hnew hstay
  have hcomp := flow_complement_invariant G hinv
  obtain ⟨Ω, hΩsource, hΩtarget, hΩmap, hΩfield, hΩlower, hΩupper⟩ :=
    exists_native_suspension_chart Φ hsource hKU Cdata V' hnew
  have hΩflow (z : E) (hz : z ∈ U) (t : ℝ) : Ω (z, t) = G t (Φ (z, 0)) := by
    have h0 : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hz, Set.mem_univ _⟩
    have hC0 : Cdata.chart (z, (0 : ℝ)) = (z, 0) := Cdata.lower _ le_rfl
    have hFt : F t (z, 0) = Cdata.chart (z, t) := by
      calc
        F t (z, 0) = suspensionFlow Cdata.chart t (z, 0) :=
          congrArg (fun A : Flow ℝ (E × ℝ) => A t (z, 0)) Cdata.flow_eq
        _ = suspensionFlow Cdata.chart t (Cdata.chart (z, 0)) :=
          (congrArg (suspensionFlow Cdata.chart t) hC0.symm)
        _ = Cdata.chart (z, 0 + t) := (suspensionFlow_chart Cdata.chart t (z, 0))
        _ = Cdata.chart (z, t) := by rw [zero_add]
    rw [hΩmap]
    exact ((hfull (z, 0) h0 t).trans (congrArg Φ hFt)).symm
  have hDU : Set.MapsTo D U U :=
    SupportedDiffeomorph.mapsTo_of_fixed_outside D.toEquiv
      (fun z hz => I.endpoint_fixed_outside z (fun h => hz (hKU h)))
  have hΩsection (z : E) (hz : z ∈ U) : ∃ w ∈ U, Ω (z, 1) = Φ (w, 1) :=
    ⟨D z, hDU hz, hΩupper (z, 1) le_rfl⟩
  obtain ⟨hleftTail, hrightTail⟩ :=
    native_corrected_cylinder_tails Φ Ω hsource (hΩsource.trans hsource) (hV.of_le (by simp)) hV'₁
      hmodel hΩfield H G hH hG D hDU hΩlower hΩupper
  refine
    ⟨N, V', G, hN, hNsub, hV', hG, hzeros, ?_, hgerm, hinv, ?_, ?_, ?_, Ω, hΩsource.trans hsource,
      hΩtarget, hΩfield, hΩlower, hΩupper, hΩflow, hΩsection, hleftTail, hrightTail⟩
  · intro x hx
    by_cases hn : x ∈ N
    · rw [hnegN x hn]
      norm_num
    · rw [(hgerm x hn).self_of_nhds]
      exact hx
  · intro x hx t
    have hagree (s : ℝ) : V' (G s x) = V (G s x) :=
      (hgerm (G s x) (fun h => hcomp x hx s (hNsub h).1)).self_of_nhds
    rcases le_total 0 t with ht | ht
    · exact
        FlowCancellation.native_flow_eq_on_positive_halfline (hV.of_le (by simp)) H G hH hG
          (fun s _ => hagree s) t ht
    · exact
        FlowCancellation.native_flow_eq_on_negative_halfline (hV.of_le (by simp)) H G hH hG
          (fun s _ => hagree s) t ht
  · intro x hx
    have hp : (x, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; exact ⟨hx, Set.mem_univ _⟩
    rw [hfull _ hp, hFend]
  · intro x hx s t
    have hp : (x, s) ∈ Φ.source := by rw [hsource]; exact ⟨hx.1, Set.mem_univ _⟩
    rw [hfull _ hp, hFfixed x hx.2 s t]

attribute [local instance 100] Classical.propDecidable in
/-- A native block holonomy exists. -/
theorem FlowSuspension.exists_native_block_holonomy {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hsource : Φ.source = U ×ˢ Set.univ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hheight : ∀ p ∈ Φ.source, p.2 ∈ Set.Ioo (0 : ℝ) 1 → f (Φ p) = c - p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0) (hQzero : Q 0 = 0) (hPzero : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source) (hQU : Q.target ⊆ U)
    (hPU : P.target ⊆ U) (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (htrans :
      NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun x : A => H (x, 0))
        (fun y : B => (0, y)) 0 0)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ H.source → ((H (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (L₁ : A ≃L[ℝ] A) (L₂ : B ≃L[ℝ] B) (N : Set M) (W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G :
      Flow ℝ M) (Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞),
      IsCompact N ∧
        N ⊆ Φ.target ∩ f ⁻¹' Set.Ioo (c - 1) c ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
              (∀ x, W x = 0 ↔ V x = 0) ∧
                (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (W x) < 0) ∧
                  (∀ x ∉ N, ∀ᶠ y in 𝓝 x, W y = V y) ∧
                    (∀ x ∉ Φ.target, ∀ t, G t x = F t x) ∧
                      Ω.source = U ×ˢ Set.univ ∧
                        Ω.target = Φ.target ∧
                          (∀ y ∈ Ω.target,
                              W y =
                                FlowConstruction.partialChartField Ω.symm
                                  (fun _ : Z × ℝ => (0, 1)) y) ∧
                            (∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0))) ∧
                              (∀ p, p.2 ≤ 0 → Ω p = Φ p) ∧
                                (∀ s t : ℝ, G t (Φ (0, s)) = Φ (0, s + t)) ∧
                                  (∀ z ∈ U, ∃ w ∈ U, Ω (z, 1) = Φ (w, 1)) ∧
                                    (∀ z ∈ U, ∀ t : ℝ, t ≤ 0 → G t (Φ (z, 0)) = F t (Φ (z, 0))) ∧
                                      (∀ z ∈ U,
                                          ∀ t : ℝ, 0 ≤ t → G t (Ω (z, 1)) = F t (Ω (z, 1))) ∧
                                        (∀ x : A,
                                            (x, (0 : B)) ∈ H.source →
                                              ∀ y ∈ H.target,
                                                y.1 = 0 →
                                                  Ω (Q (x, 0), 1) = Φ (P y, 1) → x = 0 ∧ y = 0) ∧
                                          ∀ᶠ z in 𝓝 (0 : A × B),
                                            ∀ t : ℝ,
                                              1 ≤ t → Ω (Q z, t) = Φ (P (L₁ z.1, L₂ z.2), t) := by
  obtain ⟨L₁, L₂, D, K, hK, hKU, ⟨I⟩, hD0, hDP, huniq, hgerm⟩ :=
    TransverseGerms.exists_cylinder_block_correction Q P H h0 hH0 hQzero hPzero hHs hHt
      hdiagram htrans hunique
  have hKU' : K ⊆ U := fun z hz => hQU (hKU hz).1
  have h0U : (0 : Z) ∈ U := by
    have hh := hQU (Q.map_source' (hHs h0))
    rwa [hQzero] at hh
  obtain
    ⟨N, W, G, hN, hNsub, hW, hG, hzero, hdesc, hgerms, _, hout, _, haxis, Ω, hΩsource, hΩtarget,
      hΩfield, hΩlower, hΩupper, hΩflow, hΩsection, hleftTail, hrightTail⟩ :=
    exists_full_cylinder_holonomy Φ hsource hf hheight V hV hmodel F hF D hK hKU' I
  refine
    ⟨L₁, L₂, N, W, G, Ω, hN, hNsub, hW, hG, hzero, hdesc, hgerms, hout, hΩsource, hΩtarget,
      hΩfield, hΩflow, hΩlower, haxis 0 ⟨h0U, rfl⟩, hΩsection, hleftTail, hrightTail, ?_, ?_⟩
  · intro x hx y hy hy0 heq
    have hw : D (Q (x, 0)) ∈ P.target := hDP (x, 0) hx
    have hs₁ : (D (Q (x, 0)), (1 : ℝ)) ∈ Φ.source := by
      rw [hsource]
      exact ⟨hPU hw, Set.mem_univ _⟩
    have hs₂ : (P y, (1 : ℝ)) ∈ Φ.source := by
      rw [hsource]
      exact ⟨hPU (P.map_source' (hHt hy)), Set.mem_univ _⟩
    rw [hΩupper _ le_rfl] at heq
    have hlabel : D (Q (x, 0)) = P y :=
      congrArg Prod.fst (Φ.toOpenPartialHomeomorph.injOn hs₁ hs₂ heq)
    have hinv : P.symm (D (Q (x, 0))) = y := by
      rw [hlabel]
      exact P.left_inv' (hHt hy)
    have hx0 : x = 0 := (huniq x hx).mp (by rw [hinv]; exact hy0)
    refine ⟨hx0, ?_⟩
    have hP0 : (0 : A × B) ∈ P.source := by
      have hh := hHt (H.map_source' h0)
      rwa [hH0] at hh
    have hPy : P y = 0 := by
      rw [← hlabel, hx0]
      change D (Q (0 : A × B)) = 0
      rw [hQzero, hD0]
    exact P.toOpenPartialHomeomorph.injOn (hHt hy) hP0 (hPy.trans hPzero.symm)
  · filter_upwards [hgerm] with z hz
    intro t ht
    rw [hΩupper _ ht, hz]

/-- The corrected cylinder's unique connection. -/
theorem FlowSuspension.corrected_cylinder_unique_connection {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (Φ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z} (h0U : (0 : Z) ∈ U)
    (hΦsource : Φ.source = U ×ˢ Set.univ) (hΩsource : Ω.source = U ×ˢ Set.univ)
    (hΩtarget : Ω.target = Φ.target) (F G : Flow ℝ M)
    (hΦflow : ∀ z ∈ U, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0)))
    (hΩflow : ∀ z ∈ U, ∀ t : ℝ, Ω (z, t) = G t (Φ (z, 0)))
    (hΩsection : ∀ z ∈ U, ∃ w ∈ U, Ω (z, 1) = Φ (w, 1))
    (hleft : ∀ z ∈ U, ∀ t : ℝ, t ≤ 0 → G t (Φ (z, 0)) = F t (Φ (z, 0)))
    (hright : ∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → G t (Ω (z, 1)) = F t (Ω (z, 1)))
    (hout : ∀ x ∉ Φ.target, ∀ t, G t x = F t x) (Q P : (A × B) → Z) (hQ0 : Q 0 = 0)
    (S T : Set (A × B)) {p q : M}
    (hleftBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 0))) Filter.atBot (𝓝 q) ↔
          ∃ x : A, (x, (0 : B)) ∈ S ∧ Q (x, 0) = z)
    (hrightBasin :
      ∀ z ∈ U,
        Filter.Tendsto (fun t => F t (Φ (z, 1))) Filter.atTop (𝓝 p) ↔ ∃ y ∈ T, y.1 = 0 ∧ P y = z)
    (hsection :
      ∀ x : A, (x, (0 : B)) ∈ S → ∀ y ∈ T, y.1 = 0 → Ω (Q (x, 0), 1) = Φ (P y, 1) → x = 0 ∧ y = 0)
    (hold :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t (Φ (0, 0)) = x) :
    ∀ x,
      Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q) →
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p) → ∃ t, G t (Φ (0, 0)) = x := by
  intro x hbot htop
  by_cases hx : x ∈ Φ.target
  · have hxΩ : x ∈ Ω.target := hΩtarget.symm ▸ hx
    let w := Ω.symm x
    have hw : w ∈ Ω.source := Ω.map_target' hxΩ
    have hwU : w.1 ∈ U := by rw [hΩsource] at hw; exact hw.1
    have hpoint : x = G w.2 (Φ (w.1, 0)) := by
      calc
        x = Ω w := (Ω.right_inv' hxΩ).symm
        _ = G w.2 (Φ (w.1, 0)) := hΩflow w.1 hwU w.2
    have hbot0 : Filter.Tendsto (fun t => G t (Φ (w.1, 0))) Filter.atBot (𝓝 q) := by
      apply (MorseCancellation.flow_time_atBot_limit_iff G w.2 (Φ (w.1, 0)) q).mp
      rwa [← hpoint]
    have htop0 : Filter.Tendsto (fun t => G t (Φ (w.1, 0))) Filter.atTop (𝓝 p) := by
      apply (MorseCancellation.flow_time_atTop_limit_iff G w.2 (Φ (w.1, 0)) p).mp
      rwa [← hpoint]
    have htop1 : Filter.Tendsto (fun t => G t (Ω (w.1, 1))) Filter.atTop (𝓝 p) := by
      rw [hΩflow w.1 hwU 1]
      exact (MorseCancellation.flow_time_atTop_limit_iff G 1 (Φ (w.1, 0)) p).mpr htop0
    have hbotF : Filter.Tendsto (fun t => F t (Φ (w.1, 0))) Filter.atBot (𝓝 q) := by
      apply hbot0.congr'
      filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with t ht
      exact hleft w.1 hwU t ht
    have htopF : Filter.Tendsto (fun t => F t (Ω (w.1, 1))) Filter.atTop (𝓝 p) := by
      apply htop1.congr'
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact hright w.1 hwU t ht
    obtain ⟨a, ha, hQa⟩ := (hleftBasin w.1 hwU).mp hbotF
    obtain ⟨v, hv, hΩv⟩ := hΩsection w.1 hwU
    rw [hΩv] at htopF
    obtain ⟨y, hy, hy0, hPy⟩ := (hrightBasin v hv).mp htopF
    have hcross : Ω (Q (a, 0), 1) = Φ (P y, 1) := by rw [hQa, hPy]; exact hΩv
    have ha0 := (hsection a ha y hy hy0 hcross).1
    have hw0 : w.1 = 0 := by
      rw [← hQa, ha0]
      exact hQ0
    refine ⟨w.2, ?_⟩
    rw [hpoint, hw0]
  · have hbotF : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) :=
      hbot.congr' (Filter.Eventually.of_forall (hout x hx))
    have htopF : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) :=
      htop.congr' (Filter.Eventually.of_forall (hout x hx))
    obtain ⟨t, ht⟩ := hold x hbotF htopF
    have hsource : (0, t) ∈ Φ.source := by rw [hΦsource]; exact ⟨h0U, Set.mem_univ _⟩
    have hxt : x ∈ Φ.target := by
      rw [← ht, ← hΦflow 0 h0U t]
      exact Φ.map_source' hsource
    exact (hx hxt).elim

/-! ### Cylinder basin labels -/

/-- The cylinder phase basin coordinates. -/
theorem FlowSuspension.cylinder_phase_basin_coordinates {E Z M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [TopologicalSpace M] (F : Flow ℝ M) (Φ : Z × ℝ → M)
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (hflow : ∀ z ∈ Q.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0))) (Ξ : E → M) (v : E → ℝ)
    (hphase : ∀ u ∈ Q.source, Ξ u = Φ (Q u, v u)) (Basin : M → Prop)
    (hshift : ∀ t x, Basin (F t x) ↔ Basin x) (R : E → Prop)
    (hbasin : ∀ u ∈ Q.source, Basin (Ξ u) ↔ R u) :
    ∀ z ∈ Q.target, ∀ b : ℝ, Basin (Φ (z, b)) ↔ R (Q.symm z) := by
  intro z hz b
  have hu := Q.map_target' hz
  have hi : Q (Q.symm z) = z := Q.right_inv' hz
  have hphase' : Ξ (Q.symm z) = F (v (Q.symm z)) (Φ (z, 0)) := by
    rw [hphase (Q.symm z) hu, hi, hflow z hz]
  have hend : Basin (Ξ (Q.symm z)) ↔ Basin (Φ (z, 0)) := by
    rw [hphase']
    exact hshift _ _
  have hslice : Basin (Φ (z, b)) ↔ Basin (Φ (z, 0)) := by
    rw [hflow z hz b]
    exact hshift _ _
  exact hslice.trans (hend.symm.trans (hbasin _ hu))

/-- The cylinder's outgoing basin labels. -/
theorem FlowSuspension.cylinder_outgoing_basin_labels {Z M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace M] {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (F : Flow ℝ M) (Φ : Z × ℝ → M)
    (Q : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (hflow : ∀ z ∈ Q.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0))) (Ξ : (A × B) → M)
    (v : (A × B) → ℝ) (hphase : ∀ u ∈ Q.source, Ξ u = Φ (Q u, v u)) {q : M}
    (hbasin : ∀ u ∈ Q.source, Filter.Tendsto (fun t => F t (Ξ u)) Filter.atBot (𝓝 q) ↔ u.2 = 0) :
    ∀ z ∈ Q.target,
      ∀ b : ℝ,
        Filter.Tendsto (fun t => F t (Φ (z, b))) Filter.atBot (𝓝 q) ↔
          ∃ x : A, (x, (0 : B)) ∈ Q.source ∧ Q (x, 0) = z := by
  have hcoord :=
    cylinder_phase_basin_coordinates F Φ Q hflow Ξ v hphase
      (fun x => Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q))
      (fun t x => MorseCancellation.flow_time_atBot_limit_iff F t x q) (fun u : A × B => u.2 = 0) hbasin
  intro z hz b
  rw [hcoord z hz b]
  constructor
  · intro hu
    have hpair : Q.symm z = ((Q.symm z).1, (0 : B)) := Prod.ext rfl hu
    refine ⟨(Q.symm z).1, hpair ▸ Q.map_target' hz, ?_⟩
    rw [← hpair]
    exact Q.right_inv' hz
  · rintro ⟨x, hx, hQx⟩
    have hi : Q.symm (Q (x, (0 : B))) = (x, 0) := Q.left_inv' hx
    rw [← hQx, hi]

/-- The cylinder's incoming basin labels. -/
theorem FlowSuspension.cylinder_incoming_basin_labels {Z M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace M] {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (F : Flow ℝ M) (Φ : Z × ℝ → M)
    (P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (hflow : ∀ z ∈ P.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0))) (Ξ : (A × B) → M)
    (v : (A × B) → ℝ) (hphase : ∀ u ∈ P.source, Ξ u = Φ (P u, v u)) {p : M}
    (hbasin : ∀ u ∈ P.source, Filter.Tendsto (fun t => F t (Ξ u)) Filter.atTop (𝓝 p) ↔ u.1 = 0) :
    ∀ z ∈ P.target,
      ∀ b : ℝ,
        Filter.Tendsto (fun t => F t (Φ (z, b))) Filter.atTop (𝓝 p) ↔
          ∃ y ∈ P.source, y.1 = 0 ∧ P y = z := by
  have hcoord :=
    cylinder_phase_basin_coordinates F Φ P hflow Ξ v hphase
      (fun x => Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
      (fun t x => MorseCancellation.flow_time_atTop_limit_iff F t x p) (fun u : A × B => u.1 = 0) hbasin
  intro z hz b
  rw [hcoord z hz b]
  constructor
  · intro hu
    exact ⟨P.symm z, P.map_target' hz, hu, P.right_inv' hz⟩
  · rintro ⟨y, hy, hy0, hPy⟩
    have hi : P.symm (P y) = y := P.left_inv' hy
    rw [← hPy, hi]
    exact hy0

end
