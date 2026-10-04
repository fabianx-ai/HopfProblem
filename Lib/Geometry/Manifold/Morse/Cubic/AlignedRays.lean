/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar.DiskTubular
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.Cubic.Model
public import Lib.Geometry.Manifold.Morse.Cubic.DescentField
public import Lib.Geometry.Manifold.Morse.Cubic.SplitCoordinates
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Orbits converging to a critical point, in Morse coordinates and on the cubic axis

For a field `V` with flow `F` that is the descent field of a signed Morse chart `c` near `p`:
an orbit is given by the linear model flow in the chart as long as it stays where `V` is the model
(`MorseCancellation.eventually_morse_coordinate_flow`, `flow_formula_of_local_shifts`,
`morse_coordinates_of_actual_trajectory`); an orbit converging to `p` as `t → ∞` eventually lies
in the plane `z₋ = 0`, one converging as `t → -∞` in the plane `z₊ = 0`
(`exists_incoming_morse_tail`, `exists_outgoing_morse_tail`).  If the chart is aligned with a cubic
model chart `Φ` so that this ray is the image of the model axis
(`descentFlow_outgoing_aligned_ray`, `descentFlow_incoming_aligned_ray`,
`cubic_axis_of_aligned_morse_ray`), the tail of the orbit lies on the axis `Φ (s, 0)`, `|s| < a`
(`incoming_tail_on_cubic_axis`, `outgoing_tail_on_cubic_axis`), and such a chart exists for every
non-constant orbit converging to `p` (`exists_actual_incoming_cubic_endpoint`,
`exists_actual_outgoing_cubic_endpoint`).  Cf. Milnor, *Lectures on the h-cobordism theorem*, §5.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The descent flow of an outgoing aligned ray. -/
theorem MorseCancellation.descentFlow_outgoing_aligned_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (L : Model m ≃L[ℝ] (N × P)) {r : ℝ}
    {v : N} (hL : L (r, 0) = (v, 0)) (t : ℝ) :
    MorseHandle.descentFlow t (L (r, 0)) = L (r * Real.exp t, 0) := by
  have he : (r * Real.exp t, (0 : Fin m → ℝ)) = Real.exp t • (r, 0) := by
    apply Prod.ext
    · change r * Real.exp t = Real.exp t * r
      ring
    · simp
  rw [he, L.map_smul, hL]
  change (Real.exp t • v, Real.exp (-t) • (0 : P)) = (Real.exp t • v, Real.exp t • (0 : P))
  simp

/-- The descent flow of an incoming aligned ray. -/
theorem MorseCancellation.descentFlow_incoming_aligned_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (L : Model m ≃L[ℝ] (N × P)) {r : ℝ}
    {v : P} (hL : L (-r, 0) = (0, v)) (t : ℝ) :
    MorseHandle.descentFlow t (L (-r, 0)) = L (-r * Real.exp (-t), 0) := by
  have he : (-r * Real.exp (-t), (0 : Fin m → ℝ)) = Real.exp (-t) • (-r, 0) := by
    apply Prod.ext
    · change -r * Real.exp (-t) = Real.exp (-t) * -r
      ring
    · simp
  rw [he, L.map_smul, hL]
  change (Real.exp t • (0 : N), Real.exp (-t) • v) = (Real.exp (-t) • (0 : N), Real.exp (-t) • v)
  simp

/-- An aligned Morse ray lies on the cubic axis. -/
theorem MorseCancellation.cubic_axis_of_aligned_morse_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (C : M → N × P)
    (L : Model m ≃L[ℝ] (N × P)) {a : ℝ} {e : ℝ} (he : e ^ 2 = 1)
    (hcoord :
      ∀ p ∈ Φ.source, p.1 ∈ endpointFieldDomain a e ∧ C (Φ p) = L (endpointFieldProduct a e p))
    {x : M} (hx : x ∈ Φ.target) {r : ℝ} (hr : 0 < -e * r) (hCx : C x = L (r, 0)) :
    ∃ s ∈ Set.Ioo (-a) a,
      (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = x ∧ endpointFieldCoordinate a e s = r := by
  let p := Φ.symm x
  have hp : p ∈ Φ.source := Φ.map_target' hx
  have hpx : Φ p = x := Φ.right_inv' hx
  obtain ⟨hdom, hCp⟩ := hcoord p hp
  rw [hpx, hCx] at hCp
  have hlin : endpointFieldProduct a e p = (r, 0) := L.injective hCp.symm
  have hscalar : endpointFieldCoordinate a e p.1 = r := congrArg Prod.fst hlin
  have hzero : p.2 = 0 := congrArg Prod.snd hlin
  have haxis : p = (p.1, 0) := Prod.ext rfl hzero
  have hdir : 0 < -e * endpointFieldCoordinate a e p.1 := hscalar.symm ▸ hr
  refine ⟨p.1, endpointFieldCoordinate_mem_open_axis he hdom hdir, ?_, ?_, hscalar⟩
  · exact haxis ▸ hp
  · exact (congrArg Φ haxis).symm.trans hpx

/-- The flow formula from local shifts. -/
theorem MorseCancellation.flow_formula_of_local_shifts {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (γ : ℝ → X) {S : Set ℝ} (hS : IsPreconnected S)
    (hlocal : ∀ t ∈ S, ∀ᶠ s in 𝓝 t, γ s = F (s - t) (γ t)) {t₀ t : ℝ} (h₀ : t₀ ∈ S) (ht : t ∈ S) :
    γ t = F (t - t₀) (γ t₀) := by
  let β : S → X := fun u => F (-u.1) (γ u.1)
  have hc : IsLocallyConstant β := by
    apply (IsLocallyConstant.iff_eventually_eq β).mpr
    intro u
    filter_upwards [continuousAt_subtype_val.eventually (hlocal u.1 u.2)] with v hv
    change F (-v.1) (γ v.1) = F (-u.1) (γ u.1)
    rw [hv, ← F.map_add]
    congr 1
    ring
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hb : β ⟨t, ht⟩ = β ⟨t₀, h₀⟩ :=
    hc.apply_eq_of_isPreconnected PreconnectedSpace.isPreconnected_univ (Set.mem_univ _)
      (Set.mem_univ _)
  have hh := congrArg (F t) hb
  change F t (F (-t) (γ t)) = F t (F (-t₀) (γ t₀)) at hh
  simpa only [← F.map_add, add_neg_cancel, F.map_zero_apply, ← sub_eq_add_neg] using hh

attribute [local instance 100] Classical.propDecidable in
/-- The flow eventually follows the Morse coordinate formula. -/
theorem MorseCancellation.eventually_morse_coordinate_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M) (t : ℝ)
    (ht : F t x ∈ c.splitChart.source) (heq : ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y) :
    ∀ᶠ s in 𝓝 t,
      c.splitChart (F s x) = MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  have hlocal :
    ∀ᶠ u in 𝓝 (0 : ℝ),
      F u (F t x) = c.splitChart.symm (MorseHandle.descentFlow u (c.splitChart (F t x))) :=
    c.eventually_flow_eq_descentModel hV F hF ht heq
  have htime : Filter.Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s - t) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto t
  have hmodel :
    Continuous (fun u : ℝ => MorseHandle.descentFlow u (c.splitChart (F t x))) :=
    MorseHandle.descentFlow.continuous continuous_id continuous_const
  have htarget :
    ∀ᶠ u in 𝓝 (0 : ℝ),
      MorseHandle.descentFlow u (c.splitChart (F t x)) ∈ c.splitChart.target := by
    have hnhds : ∀ᶠ y in 𝓝 (c.splitChart (F t x)), y ∈ c.splitChart.target :=
      c.splitChart.open_target.mem_nhds (c.splitChart.map_source' ht)
    have hm0 :
      Filter.Tendsto (fun u : ℝ => MorseHandle.descentFlow u (c.splitChart (F t x))) (𝓝 0)
        (𝓝 (c.splitChart (F t x))) := by simpa only [Flow.map_zero_apply] using hmodel.tendsto 0
    exact hm0.eventually hnhds
  filter_upwards [htime.eventually hlocal, htime.eventually htarget] with s hs hst
  rw [← F.map_add, sub_add_cancel] at hs
  have hh := congrArg c.splitChart hs
  exact hh.trans (c.splitChart.right_inv' hst)

attribute [local instance 100] Classical.propDecidable in
/-- The Morse coordinates of an actual trajectory. -/
theorem MorseCancellation.morse_coordinates_of_actual_trajectory {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M) {S : Set ℝ}
    (hS : IsPreconnected S) (htarget : ∀ t ∈ S, F t x ∈ c.splitChart.source)
    (heq : ∀ t ∈ S, ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y) {t₀ t : ℝ} (h₀ : t₀ ∈ S)
    (ht : t ∈ S) :
    c.splitChart (F t x) = MorseHandle.descentFlow (t - t₀) (c.splitChart (F t₀ x)) :=
  flow_formula_of_local_shifts MorseHandle.descentFlow (fun s => c.splitChart (F s x)) hS
    (fun s hs => eventually_morse_coordinate_flow c hV F hF x s (htarget s hs) (heq s hs)) h₀ ht

attribute [local instance 100] Classical.propDecidable in
/-- Tail data of a Morse endpoint orbit. -/
theorem MorseCancellation.morse_endpoint_tail_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (F : Flow ℝ M) (x : M) {l : Filter ℝ}
    (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 p)) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    Filter.Tendsto (fun t => c.splitChart (F t x)) l (𝓝 0) ∧
      ∀ᶠ t in l, F t x ∈ c.splitChart.source ∧ ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y := by
  have hc := c.splitChart.toOpenPartialHomeomorph.continuousAt c.splitChart_mem_source
  have hcoord : Filter.Tendsto (fun t => c.splitChart (F t x)) l (𝓝 0) := by
    have hh : Filter.Tendsto (fun t => c.splitChart (F t x)) l (𝓝 (c.splitChart p)) :=
      hc.tendsto.comp hlim
    simpa only [c.splitChart_center] using hh
  have hsource : ∀ᶠ y in 𝓝 p, y ∈ c.splitChart.source :=
    c.splitChart.open_source.mem_nhds c.splitChart_mem_source
  have hgerm : ∀ᶠ y in 𝓝 p, ∀ᶠ z in 𝓝 y, V z = c.descentField z :=
    eventually_eventually_nhds.mpr heq
  exact ⟨hcoord, hlim.eventually (hsource.and hgerm)⟩

attribute [local instance 100] Classical.propDecidable in
/-- An incoming Morse tail exists. -/
theorem MorseCancellation.exists_incoming_morse_tail {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ T : ℝ,
      (∀ t ≥ T, F t x ∈ c.splitChart.source) ∧
        (∀ t ≥ T, (c.splitChart (F t x)).1 = 0) ∧
          ∀ t ≥ T,
            ∀ s ≥ T,
              c.splitChart (F s x) =
                MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  obtain ⟨hcoord, htail⟩ := morse_endpoint_tail_data c F x hlim heq
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp htail
  have hformula (t : ℝ) (ht : T ≤ t) (s : ℝ) (hs : T ≤ s) :
    c.splitChart (F s x) = MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) :=
    morse_coordinates_of_actual_trajectory c hV F hF x isPreconnected_Ici
      (fun u hu => (hT u hu).1) (fun u hu => (hT u hu).2) ht hs
  refine ⟨T, fun t ht => (hT t ht).1, ?_, hformula⟩
  intro t ht
  have hnorm : Filter.Tendsto (fun s => ‖(c.splitChart (F s x)).1‖) Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, Prod.fst_zero, norm_zero] using
      (continuous_fst.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  have hbound : ∀ᶠ s in Filter.atTop, ‖(c.splitChart (F t x)).1‖ ≤ ‖(c.splitChart (F s x)).1‖ := by
    filter_upwards [Filter.eventually_ge_atTop T, Filter.eventually_ge_atTop t] with s hs hst
    rw [hformula t ht s hs]
    exact MorseHandle.norm_fst_le_descentFlow (sub_nonneg.mpr hst) _
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hbound) (norm_nonneg _))

attribute [local instance 100] Classical.propDecidable in
/-- An outgoing Morse tail exists. -/
theorem MorseCancellation.exists_outgoing_morse_tail {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ T : ℝ,
      (∀ t ≤ T, F t x ∈ c.splitChart.source) ∧
        (∀ t ≤ T, (c.splitChart (F t x)).2 = 0) ∧
          ∀ t ≤ T,
            ∀ s ≤ T,
              c.splitChart (F s x) =
                MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  obtain ⟨hcoord, htail⟩ := morse_endpoint_tail_data c F x hlim heq
  obtain ⟨T, hT⟩ := Filter.eventually_atBot.mp htail
  have hformula (t : ℝ) (ht : t ≤ T) (s : ℝ) (hs : s ≤ T) :
    c.splitChart (F s x) = MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) :=
    morse_coordinates_of_actual_trajectory c hV F hF x isPreconnected_Iic
      (fun u hu => (hT u hu).1) (fun u hu => (hT u hu).2) ht hs
  refine ⟨T, fun t ht => (hT t ht).1, ?_, hformula⟩
  intro t ht
  have hnorm : Filter.Tendsto (fun s => ‖(c.splitChart (F s x)).2‖) Filter.atBot (𝓝 0) := by
    simpa only [Function.comp_def, Prod.snd_zero, norm_zero] using
      (continuous_snd.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  have hbound : ∀ᶠ s in Filter.atBot, ‖(c.splitChart (F t x)).2‖ ≤ ‖(c.splitChart (F s x)).2‖ := by
    filter_upwards [Filter.eventually_le_atBot T, Filter.eventually_le_atBot t] with s hs hst
    rw [hformula t ht s hs, MorseHandle.norm_descentFlow_snd]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr (by linarith))
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hbound) (norm_nonneg _))

attribute [local instance 100] Classical.propDecidable in
/-- The incoming tail lies on the cubic axis. -/
theorem MorseCancellation.incoming_tail_on_cubic_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hcenter : (1 / 2, (0 : Fin m → ℝ)) ∈ Φ.source) (hvalue : Φ (1 / 2, 0) = p)
    (hcoord :
      ∀ q ∈ Φ.source,
        q.1 ∈ endpointFieldDomain (1 / 2) 1 ∧
          c.splitChart (Φ q) = L (endpointFieldProduct (1 / 2) 1 q))
    (F : Flow ℝ M) (x : M) (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) {T r : ℝ}
    (hr : 0 < r) {v : c.PositiveCoordinates} (hL : L (-r, 0) = (0, v))
    (hbase : c.splitChart (F T x) = (0, v))
    (hmodel :
      ∀ t ≥ T,
        c.splitChart (F t x) = MorseHandle.descentFlow (t - T) (c.splitChart (F T x))) :
    ∀ᶠ t in Filter.atTop,
      ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  have hp : p ∈ Φ.target := hvalue ▸ Φ.map_source' hcenter
  have htarget : ∀ᶠ t in Filter.atTop, F t x ∈ Φ.target :=
    hlim.eventually (Φ.open_target.mem_nhds hp)
  filter_upwards [htarget, Filter.eventually_ge_atTop T] with t ht hT
  have hline : c.splitChart (F t x) = L (-r * Real.exp (-(t - T)), 0) := by
    rw [hmodel t hT, hbase, ← hL]
    exact descentFlow_incoming_aligned_ray L hL (t - T)
  have hdir : 0 < -(1 : ℝ) * (-r * Real.exp (-(t - T))) := by nlinarith [Real.exp_pos (-(t - T))]
  obtain ⟨s, hs, hsource, hpoint, _⟩ :=
    cubic_axis_of_aligned_morse_ray Φ c.splitChart L (by norm_num : (1 : ℝ) ^ 2 = 1) hcoord ht
      hdir hline
  exact ⟨s, hs, hsource, hpoint⟩

attribute [local instance 100] Classical.propDecidable in
/-- The outgoing tail lies on the cubic axis. -/
theorem MorseCancellation.outgoing_tail_on_cubic_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hcenter : (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source) (hvalue : Φ (-(1 / 2 : ℝ), 0) = p)
    (hcoord :
      ∀ q ∈ Φ.source,
        q.1 ∈ endpointFieldDomain (1 / 2) (-1) ∧
          c.splitChart (Φ q) = L (endpointFieldProduct (1 / 2) (-1) q))
    (F : Flow ℝ M) (x : M) (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) {T r : ℝ}
    (hr : 0 < r) {v : c.NegativeCoordinates} (hL : L (r, 0) = (v, 0))
    (hbase : c.splitChart (F T x) = (v, 0))
    (hmodel :
      ∀ t ≤ T,
        c.splitChart (F t x) = MorseHandle.descentFlow (t - T) (c.splitChart (F T x))) :
    ∀ᶠ t in Filter.atBot,
      ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  have hp : p ∈ Φ.target := hvalue ▸ Φ.map_source' hcenter
  have htarget : ∀ᶠ t in Filter.atBot, F t x ∈ Φ.target :=
    hlim.eventually (Φ.open_target.mem_nhds hp)
  filter_upwards [htarget, Filter.eventually_le_atBot T] with t ht hT
  have hline : c.splitChart (F t x) = L (r * Real.exp (t - T), 0) := by
    rw [hmodel t hT, hbase, ← hL]
    exact descentFlow_outgoing_aligned_ray L hL (t - T)
  have hdir : 0 < -(-1 : ℝ) * (r * Real.exp (t - T)) := by
    simpa using mul_pos hr (Real.exp_pos (t - T))
  obtain ⟨s, hs, hsource, hpoint, _⟩ :=
    cubic_axis_of_aligned_morse_ray Φ c.splitChart L (by norm_num : (-1 : ℝ) ^ 2 = 1) hcoord ht
      hdir hline
  exact ⟨s, hs, hsource, hpoint⟩

attribute [local instance 100] Classical.propDecidable in
/-- The Morse coordinates are nonzero on a nonstationary orbit. -/
theorem MorseCancellation.morse_coordinates_nonzero_on_nonstationary_orbit {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hxp : x ≠ p)
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) {t : ℝ} (ht : F t x ∈ c.splitChart.source) :
    c.splitChart (F t x) ≠ 0 := by
  have heqp : V p = c.descentField p :=
    mem_of_mem_nhds (x := p) (s := {y : M | V y = c.descentField y}) heq
  have hVp : V p = 0 := heqp.trans c.descentField_center
  have hfixed := FlowConstruction.flow_fixed_of_zero hV F hF hVp
  intro hz
  have hpoint : F t x = p :=
    c.splitChart.toOpenPartialHomeomorph.injOn ht c.splitChart_mem_source
      (hz.trans c.splitChart_center.symm)
  have hh := congrArg (F (-t)) hpoint
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply, hfixed] at hh
  exact hxp hh

attribute [local instance 100] Classical.propDecidable in
/-- An actual incoming cubic endpoint exists. -/
theorem MorseCancellation.exists_actual_incoming_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = 1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hxp : x ≠ p)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (Option.some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (1 / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (1 / 2, 0) = p ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (∀ᶠ t in Filter.atTop,
                  ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
                    (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) ∧
                ∃ L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates),
                  (∀ z, L (endpointLinearField σ (1 / 2) 1 z) = MorseHandle.descent (L z)) ∧
                    ∀ z ∈ Φ.source, c.splitChart (Φ z) = L (endpointFieldProduct (1 / 2) 1 z) := by
  let σ := fun i : Fin m => c.weights (ρ (Option.some i))
  obtain ⟨T, hsource, hzero, hformula⟩ := exists_incoming_morse_tail c hV F hF x hlim heq
  let v := (c.splitChart (F T x)).2
  have hbase : c.splitChart (F T x) = (0, v) := Prod.ext (hzero T le_rfl) rfl
  have hv : v ≠ 0 := by
    intro hv
    exact
      morse_coordinates_nonzero_on_nonstationary_orbit c hV F hF hxp heq (hsource T le_rfl)
        (hbase.trans (Prod.ext rfl hv))
  obtain ⟨r, L, hr, hLray, hL⟩ := exists_selected_incoming_axis c ρ he hv
  have hL' : ∀ q, L (endpointLinearField σ (1 / 2) 1 q) = MorseHandle.descent (L q) := by
    simpa only [he] using hL
  obtain ⟨Φ, hc, hval, hsub, hfield, hcoord⟩ :=
    exists_controlled_morse_field_endpoint c σ (by norm_num : (1 : ℝ) ^ 2 = 1) L hL' V heq
  refine ⟨Φ, hc, hval, hsub, hfield, ?_, L, hL', ?_⟩
  · exact
      incoming_tail_on_cubic_axis c Φ L hc hval hcoord F x hlim hr hLray hbase (hformula T le_rfl)
  · exact fun z hz => (hcoord z hz).2

attribute [local instance 100] Classical.propDecidable in
/-- An actual outgoing cubic endpoint exists. -/
theorem MorseCancellation.exists_actual_outgoing_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = -1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hxp : x ≠ p)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (Option.some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (-(1 / 2 : ℝ), 0) = p ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (∀ᶠ t in Filter.atBot,
                  ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
                    (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) ∧
                ∃ L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates),
                  (∀ z,
                      L (endpointLinearField σ (1 / 2) (-1) z) =
                        MorseHandle.descent (L z)) ∧
                    ∀ z ∈ Φ.source,
                      c.splitChart (Φ z) = L (endpointFieldProduct (1 / 2) (-1) z) := by
  let σ := fun i : Fin m => c.weights (ρ (Option.some i))
  obtain ⟨T, hsource, hzero, hformula⟩ := exists_outgoing_morse_tail c hV F hF x hlim heq
  let v := (c.splitChart (F T x)).1
  have hbase : c.splitChart (F T x) = (v, 0) := Prod.ext rfl (hzero T le_rfl)
  have hv : v ≠ 0 := by
    intro hv
    exact
      morse_coordinates_nonzero_on_nonstationary_orbit c hV F hF hxp heq (hsource T le_rfl)
        (hbase.trans (Prod.ext hv rfl))
  obtain ⟨r, L, hr, hLray, hL⟩ := exists_selected_outgoing_axis c ρ he hv
  have hL' : ∀ q, L (endpointLinearField σ (1 / 2) (-1) q) = MorseHandle.descent (L q) := by
    simpa only [he] using hL
  obtain ⟨Φ, hc, hval, hsub, hfield, hcoord⟩ :=
    exists_controlled_morse_field_endpoint c σ (by norm_num : (-1 : ℝ) ^ 2 = 1) L hL' V heq
  have hc' : (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source := by convert! hc using 1; norm_num
  have hval' : Φ (-(1 / 2 : ℝ), 0) = p := by convert! hval using 1; norm_num
  refine ⟨Φ, hc', hval', hsub, hfield, ?_, L, hL', ?_⟩
  · exact
      outgoing_tail_on_cubic_axis c Φ L hc' hval' hcoord F x hlim hr hLray hbase
        (hformula T le_rfl)
  · exact fun z hz => (hcoord z hz).2
