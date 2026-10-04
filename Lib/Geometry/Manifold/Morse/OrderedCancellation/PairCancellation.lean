/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Cancellation.LevelIsotopy
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.Rearrangement.LevelConnectedness
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Morse.OrderedCancellation.ValueExchange

/-!
# Cancelling a pair of critical points joined by a single flow line

The first cancellation theorem (Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4):
two critical points `p`, `q` of consecutive indices `λ`, `λ + 1` joined by exactly one
trajectory of a gradient-like field, transverse along that trajectory, can be removed together,
by a Morse function which agrees with the old one outside a band around the two critical values
(`MorseCancellation.cancel_transverse_pair_after_flow_preserving_descent`, and the index `0`/`1`
case `cancel_unique_zero_one_connection`, where transversality is automatic because the forward
basin of a minimum is open, `isOpen_forward_basin_of_native_index_zero`).  The auxiliary
statements count connections through a regular level (`unit_level_count_of_circle_placement`,
`no_other_connections_of_two_level_endpoints`), transport transverse sheets and isotopies through
a diffeomorphism (`exists_transverse_sheet_of_circle_placement`, `isotopicToIdentity_conj`), and
push a compact family off the critical set into the basin of a level
(`exists_embedded_avoidance_into_level_basin`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- For a gradient-like flow `F` of `f` modelled near a critical point `p` of index `0` by the
signed Morse chart `c`, the forward basin `{x | F t x → p as t → ∞}` is open. -/
theorem MorseCancellation.isOpen_forward_basin_of_native_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodel : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    (hindex : Module.finrank ℝ c.NegativeCoordinates = 0) :
    IsOpen {x : M | Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)} := by
  let : Subsingleton c.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ c.NegativeCoordinates).mp hindex
  obtain ⟨r, hr, -, hbasin⟩ :=
    exists_descending_morse_basin_block c hf (hV.of_le (by simp)) F hF hzero hdesc hmodel
  have hnear : ∀ᶠ y in 𝓝 p, Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p) := by
    filter_upwards [morse_coordinate_neighborhood c hr hr] with y hy
    exact ((hbasin y hy.1 hy.2.1 hy.2.2).1).mpr (Subsingleton.elim _ _)
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨t, ht⟩ := (hx.eventually (eventually_eventually_nhds.mpr hnear)).exists
  have hc : Continuous (fun y => F t y) := F.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (flow_time_atTop_limit_iff F t y p).mp hy

attribute [local instance 100] Classical.propDecidable in
/-- Cancellation of an index-`0`/index-`1` pair.  Let `p`, `q` be critical points of `f` of
indices `0` and `1`, `f p < f q`, the only critical points with values in `[l, u]`, and let the
gradient-like flow `F` of `V` (modelled by the charts `cp`, `cq`) have the point `z` on a flow
line from `q` to `p` through which every such flow line passes.  Then there is a Morse function
`g` with two critical points fewer (exactly `p` and `q` removed) which agrees with `f` near every
point with `f x ∉ (l, u)`. -/
theorem MorseCancellation.cancel_unique_zero_one_connection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p q z : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hindexp : nativeMorseIndex E f p = 0)
    (hindexq : nativeMorseIndex E f q = 1)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {l u : ℝ} (hl : l < f p)
    (hu : f q < u)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc l u → x = p ∨ x = q)
    (hp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t z = x)
    (heqp : ∀ᶠ x in 𝓝 p, V x = cp.descentField x) (heqq : ∀ᶠ x in 𝓝 q, V x = cq.descentField x) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo l u → g =ᶠ[𝓝 x] f := by
  have hp0 : Module.finrank ℝ cp.NegativeCoordinates = 0 :=
    (nativeMorseIndex_eq_chart cp).symm.trans hindexp
  have hq1 : Module.finrank ℝ cq.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart cq).symm.trans hindexq
  have hdim : Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1 := by
    have h := cq.finrank_negative_add_positive
    omega
  have hindex :
    Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1 := by
    have h :
      Module.finrank ℝ cq.NegativeCoordinates = Module.finrank ℝ cp.NegativeCoordinates + 1 := by
      omega
    simpa only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      MorseHandle.NegativeSpace, finrank_euclideanSpace] using h
  have hbasin : ∀ᶠ x in 𝓝 z, Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) :=
    (isOpen_forward_basin_of_native_index_zero cp hf hV F hF hzero hdesc heqp hp0).mem_nhds hp
  have htrans :
    NativeTransversality.At 𝓘(ℝ, E) 𝓘(ℝ, E) 𝓘(ℝ, E) (fun _ : M => z) (fun x : M => x) z z :=
    by
    intro _ w
    refine ⟨(0, w), ?_⟩
    change
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun _ : M => z) z 0 +
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x : M => x) z w =
        w
    rw [map_zero, zero_add]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id z w = w
    rw [mfderiv_id]
    rfl
  exact
    cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hindex V hV hzero hdesc F
      hF hinj hpc hqc hpq hl hu hpair hp hq hunique heqp heqq (S := fun _ : M => z) (T :=
      fun x : M => x) mdifferentiableAt_const mdifferentiableAt_id rfl rfl
      (Filter.Eventually.of_forall (fun _ => hq)) hbasin htrans

/-- Let `P` be a diffeomorphism of `N`, `γ`, `δ : X → N` with `P ∘ γ = δ` and `γ` differentiable
at `x`, and `β : Y → N` differentiable at `y` and transverse to `δ` at `(x, y)` with `β y = δ x`.
Then `β' := P⁻¹ ∘ β` is differentiable at `y`, meets `γ` at `β' y = γ x`, is transverse to `γ`
there, and satisfies `P ∘ β' = β`. -/
theorem MorseCancellation.exists_transverse_sheet_of_circle_placement {A B E HA HB H X Y N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace HA] {I : ModelWithCorners ℝ A HA}
    [TopologicalSpace X] [ChartedSpace HA X] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HB] {I' : ModelWithCorners ℝ B HB} [TopologicalSpace Y] [ChartedSpace HB Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace N] [ChartedSpace H N] (P : Diffeomorph J J N N ∞) {γ δ : X → N} {β : Y → N}
    {x : X} {y : Y} (hγ : MDifferentiableAt I J γ x) (hβ : MDifferentiableAt I' J β y)
    (hplace : ∀ z, P (γ z) = δ z) (hcross : β y = δ x)
    (htrans : NativeTransversality.At I I' J δ β x y) :
    ∃ β' : Y → N,
      MDifferentiableAt I' J β' y ∧
        β' y = γ x ∧ NativeTransversality.At I I' J γ β' x y ∧ ∀ z, P (β' z) = β z := by
  let β' := P.symm ∘ β
  have hβ' : MDifferentiableAt I' J β' y :=
    (P.symm.contMDiff.mdifferentiableAt (by simp)).comp y hβ
  have hcross' : β' y = γ x := by
    apply P.injective
    change P (P.symm (β y)) = P (γ x)
    rw [P.apply_symm_apply, hcross, hplace]
  have hforward (z : Y) : P (β' z) = β z := P.apply_symm_apply (β z)
  refine ⟨β', hβ', hcross', ?_, hforward⟩
  apply
    (TransverseGerms.native_transversality_partial_diffeomorph_iff P.toPartialDiffeomorph
        hγ hβ' hcross' (Set.mem_univ _)).mpr
  have hγeq : P.toPartialDiffeomorph ∘ γ = δ := funext hplace
  have hβeq : P.toPartialDiffeomorph ∘ β' = β := funext hforward
  rw [hγeq, hβeq]
  exact htrans

/-- General position into the basin of a regular level.  Let `S : AdaptedWindows E f`, `a` a
regular value, all critical points above `a` of coindex `≤ d` and below `a` of index `≤ d`, and
`f₀ : C(A, M)` smooth with `2 dim A < dim M` and `dim A + d < dim M`, embedded on the compact
`K`, and with `f₀ (L ∩ C)` in the basin of the level `a`.  Then `f₀` is homotopic relative to the
closed set `C` to a smooth `g`, embedded on `K`, with `g x = g y → f₀ x = f₀ y`, whose values on
`L` and on the points already in the basin lie in the basin of the level `a`. -/
theorem MorseCancellation.exists_embedded_avoidance_into_level_basin {E M A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ d)
    (f₀ : C(A, M)) (hf₀ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ f₀)
    (hself : 2 * Module.finrank ℝ A < Module.finrank ℝ E)
    (hobstacle : Module.finrank ℝ A + d < Module.finrank ℝ E) {K L C : Set A} (hK : IsCompact K)
    (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f₀ K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f₀ x))
    (hfixed : ∀ x ∈ L ∩ C, f₀ x ∈ FlowCancellation.levelBasin S.flow f a) :
    ∃ g : C(A, M),
      ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ g ∧
        f₀.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) g x)) ∧
              (∀ x y, g x = g y → f₀ x = f₀ y) ∧
                ∀ x,
                  (f₀ x ∈ FlowCancellation.levelBasin S.flow f a ∨ x ∈ L) →
                    g x ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let J := EndpointBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable J := endpointBasinIndex_countable S a
  let _ : DiscreteTopology J := inferInstance
  let _ : ChartedSpace Z J := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ J := IsManifold.of_discreteTopology ∞
  obtain ⟨b, hb, hcover⟩ := S.exists_endpoint_obstruction_global_images hf a hhigh hlow
  have hs : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun p : J × V => b p.1 p.2) :=
    contMDiff_discrete_family b hb
  let B : C(J × V, M) := ⟨fun p => b p.1 p.2, hs.continuous⟩
  have hrange : Set.range B = (FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [levelBasin_compl_eq_endpoint_obstruction S hf hreg, hcover]
    exact range_discrete_family b
  have hclosed : IsClosed (Set.range B) := by
    rw [hrange, levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact isClosed_endpoint_obstruction S hf a
  have hdim : Module.finrank ℝ A + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hobstacle
  have hfixed' : ∀ x ∈ L ∩ C, f₀ x ∉ Set.range B := by
    intro x hx
    rw [hrange, Set.mem_compl_iff, Classical.not_not]
    exact hfixed x hx
  obtain ⟨g, hg, hhom, hemb, hder, hnoNew, havoid⟩ :=
    ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_range f₀ B hf₀ hs
      hclosed hself hdim hK hL hC hinj hderiv hfixed'
  refine ⟨g, hg, hhom, hemb, hder, hnoNew, ?_⟩
  intro x hx
  have hx' : f₀ x ∉ Set.range B ∨ x ∈ L := by
    simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using hx
  simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using havoid x hx'

/-- Conjugating a diffeomorphism `d : M → M` isotopic to the identity by a diffeomorphism
`e : M → N` gives `e ∘ d ∘ e⁻¹ : N → N` isotopic to the identity. -/
theorem MorseCancellation.isotopicToIdentity_conj {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
    (e : Diffeomorph I J M N ∞) {d : Diffeomorph I I M M ∞}
    (hd : SupportedDiffeomorph.IsotopicToIdentity d) :
    SupportedDiffeomorph.IsotopicToIdentity ((e.symm.trans d).trans e) := by
  obtain ⟨A, hA, hA0, hA1, hslices⟩ := hd
  refine
    ⟨(fun p => e (A (p.1, e.symm p.2))),
      e.contMDiff.comp (hA.comp (contMDiff_fst.prodMk (e.symm.contMDiff.comp contMDiff_snd))), ?_,
      ?_, ?_⟩
  · intro y
    change e (A (0, e.symm y)) = y
    rw [hA0, e.apply_symm_apply]
  · intro y
    change e (A (1, e.symm y)) = e (d (e.symm y))
    rw [hA1]
  · intro t
    obtain ⟨dₜ, hdₜ⟩ := hslices t
    refine ⟨(e.symm.trans dₜ).trans e, ?_⟩
    intro y
    change e (A (t, e.symm y)) = e (dₜ (e.symm y))
    rw [hdₜ]

/-- Let `P` be a bijection of the level `f = a` and `δ : X → {f = a}` with `x` in the backward
basin of `p` iff `P x ∈ range δ`, and let `δ z` flow forward to `q` iff `z = z₀`.  Then exactly
one point `x` of the level flows backward to `p` with `P x` flowing forward to `q`. -/
theorem MorseCancellation.unit_level_count_of_circle_placement {M X : Type*} [TopologicalSpace M]
    (F : Flow ℝ M) {f : M → ℝ} {a : ℝ} {p q : M} (P : { y : M // f y = a } ≃ { y : M // f y = a })
    (δ : X → { y : M // f y = a }) (z₀ : X)
    (hplacement : ∀ x, Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ↔ P x ∈ Set.range δ)
    (hsingle : ∀ z, Filter.Tendsto (fun t => F t (δ z).val) Filter.atTop (𝓝 q) ↔ z = z₀) :
    {x : { y : M // f y = a } |
          Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ∧
            Filter.Tendsto (fun t => F t (P x).val) Filter.atTop (𝓝 q)}.ncard =
      1 := by
  have heq :
    {x : { y : M // f y = a } |
        Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t => F t (P x).val) Filter.atTop (𝓝 q)} =
      {P.symm (δ z₀)} := by
    ext x
    constructor
    · rintro ⟨hx, hforward⟩
      obtain ⟨z, hz⟩ := (hplacement x).mp hx
      have hz0 : z = z₀ := (hsingle z).mp (hz.symm ▸ hforward)
      apply Set.mem_singleton_iff.mpr
      apply P.injective
      rw [P.apply_symm_apply, ← hz, hz0]
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      refine ⟨(hplacement _).mpr ⟨z₀, (P.apply_symm_apply _).symm⟩, ?_⟩
      rw [P.apply_symm_apply]
      exact (hsingle z₀).mpr rfl
  rw [heq]
  exact Set.ncard_singleton _

/-- Let `F` be a flow along which the continuous function `f` is antitone, `f` injective on `C`,
`p q r ∈ C`, `a < f p` with every `f j < f p` (`j ∈ C`) below `a`, and suppose every point of
the level `f = a` flowing backward to `p` flows forward to `q` or to `r`.  Then no point flows
backward to `p` and forward to a `j ∈ C` different from `p`, `q`, `r`. -/
theorem MorseCancellation.no_other_connections_of_two_level_endpoints {M : Type*} [TopologicalSpace M]
    [T2Space M] (F : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {C : Set M} (hinj : Set.InjOn f C)
    (p q r : C) {a : ℝ} (hpa : a < f p) (hgap : ∀ j : C, f j < f p → f j < a)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hends :
      ∀ x : { y : M // f y = a },
        Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p.val) →
          Filter.Tendsto (fun t => F t x.val) Filter.atTop (𝓝 q.val) ∨
            Filter.Tendsto (fun t => F t x.val) Filter.atTop (𝓝 r.val)) :
    ∀ j : C,
      j ≠ p →
        j ≠ q →
          j ≠ r →
            ∀ x,
              ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val)) := by
  intro j hjp hjq hjr x hx
  have hforwardHeight := hf.continuousAt.tendsto.comp hx.2
  have hbackwardHeight := hf.continuousAt.tendsto.comp hx.1
  have hle : f j ≤ f p :=
    (hmono x).le_of_tendsto hforwardHeight 0 |>.trans ((hmono x).ge_of_tendsto hbackwardHeight 0)
  have hlt : f j < f p :=
    lt_of_le_of_ne hle (fun h => hjp (Subtype.ext (hinj j.property p.property h)))
  obtain ⟨t, ht⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits F hf hx.1 hx.2 hpa
      (hgap j hlt)
  let z : { y : M // f y = a } := ⟨F t x, ht⟩
  have hzb : Filter.Tendsto (fun s => F s z.val) Filter.atBot (𝓝 p.val) :=
    (flow_time_atBot_limit_iff F t x p.val).mpr hx.1
  have hzf : Filter.Tendsto (fun s => F s z.val) Filter.atTop (𝓝 j.val) :=
    (flow_time_atTop_limit_iff F t x j.val).mpr hx.2
  rcases hends z hzb with hq | hr
  · exact hjq (Subtype.ext (tendsto_nhds_unique hzf hq))
  · exact hjr (Subtype.ext (tendsto_nhds_unique hzf hr))

/-- Milnor, h-cobordism Theorem 5.4 (first cancellation theorem).  Let `f` be a Morse function with
distinct critical values on a compact connected manifold of dimension `m + 1`, `V` a
gradient-like field with flow `F` modelled by signed Morse charts, `r`, `p`, `q` critical points
with `f r < f p < f q` and `index q = index p + 1`, no flow line from `q` to a critical point
other than `p`, `q`, `r`, and `z` a point on a flow line from `q` to `p` through which every such
line passes, with the descending sheet `α` of `q` and the ascending sheet `β` of `p` transverse at
`z`.  Then there is a Morse function `g` with distinct critical values, whose critical points are
those of `f` except `p` and `q`, with the same indices at the remaining ones. -/
theorem MorseCancellation.cancel_transverse_pair_after_flow_preserving_descent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} {m : ℕ} {A B HA HB X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace HA] [TopologicalSpace HB]
    {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X]
    [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hdim : Module.finrank ℝ E = m + 1) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        ∃ c : ManifoldMorse.SignedMorseChart (E := E) f x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : ManifoldMorse.criticalPoints E f) (hrp : f r < f p) (hpq : f p < f q)
    (hindex : nativeMorseIndex E f q = nativeMorseIndex E f p + 1)
    (hnoconnection :
      ∀ j : ManifoldMorse.criticalPoints E f,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val)))
    {z : M} (hzp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p.val))
    (hzq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q.val))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p.val) → ∃ t, F t z = x)
    {α : X → M} {β : Y → M} {x : X} {y : Y} (hα : MDifferentiableAt I 𝓘(ℝ, E) α x)
    (hβ : MDifferentiableAt I' 𝓘(ℝ, E) β y) (hα0 : α x = z) (hβ0 : β y = z)
    (hαbasin : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => F t (α u)) Filter.atBot (𝓝 q.val))
    (hβbasin : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => F t (β u)) Filter.atTop (𝓝 p.val))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) α β x y) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
            (ManifoldMorse.criticalPoints E g).ncard + 2 =
                (ManifoldMorse.criticalPoints E f).ncard ∧
              (∀ w,
                  w ∈ ManifoldMorse.criticalPoints E g ↔
                    w ∈ ManifoldMorse.criticalPoints E f ∧ w ≠ p.val ∧ w ≠ q.val) ∧
                ∀ w ∈ ManifoldMorse.criticalPoints E g,
                  nativeMorseIndex E g w = nativeMorseIndex E f w := by
  obtain ⟨h, hh, hmh, hcrit, hinjh, -, -, hpqh, hconsecutive, hdesch, hmodelsh, hindices⟩ :=
    exists_flow_preserving_consecutive_pair hf hm hinj hV F hF hzero hdesc hmodels p r q hrp hpq
      hnoconnection
  have hpcrit : p.val ∈ ManifoldMorse.criticalPoints E h := hcrit.symm ▸ p.property
  have hqcrit : q.val ∈ ManifoldMorse.criticalPoints E h := hcrit.symm ▸ q.property
  obtain ⟨cp, hcp⟩ := hmodelsh p.val hpcrit
  obtain ⟨cq, hcq⟩ := hmodelsh q.val hqcrit
  have hidx :
    Module.finrank ℝ cq.NegativeCoordinates = Module.finrank ℝ cp.NegativeCoordinates + 1 := by
    rw [← nativeMorseIndex_eq_chart cq, ← nativeMorseIndex_eq_chart cp, hindices q.val q.property,
      hindices p.val p.property]
    exact hindex
  have hcard :
    Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1 := by
    simpa only [ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      MorseHandle.NegativeSpace, finrank_euclideanSpace] using hidx
  obtain ⟨W⟩ := ManifoldMorse.nonempty_surgeryWindows hh hmh hinjh
  let ph : ManifoldMorse.criticalPoints E h := ⟨p.val, hpcrit⟩
  let qh : ManifoldMorse.criticalPoints E h := ⟨q.val, hqcrit⟩
  have hconsecutiveh : ∀ s : ManifoldMorse.criticalPoints E h, ¬(h ph < h s ∧ h s < h qh) :=
    by
    intro s hs
    exact hconsecutive ⟨s.val, hcrit ▸ s.property⟩ hs
  have hpair := surgery_pair_band_isolation W ph qh hconsecutiveh
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior⟩ :=
    cancel_unique_connection_of_transverse_basin_sheets cp cq hh hmh hdim hcard V hV
      (fun w hw => hzero w (hcrit ▸ hw)) hdesch F hF hinjh hpcrit hqcrit hpqh
      (W.lower_lt_value ph) (W.value_lt_upper qh) hpair hzp hzq hunique hcp hcq hα hβ hα0 hβ0
      hαbasin hβbasin htrans
  have hkeep := surviving_critical_germs_of_pair_band hpair hcritg hexterior
  have hinjg :=
    distinct_critical_values_of_surviving_germs hinjh (fun w hw => ((hcritg w).mp hw).1) hkeep
  rw [hcrit] at hcount
  refine ⟨g, hg, hmg, hinjg, hcount, ?_, ?_⟩
  · intro w
    rw [hcritg w, hcrit]
  · intro w hw
    exact
      (nativeMorseIndex_congr_germ (hkeep w hw)).trans (hindices w (hcrit ▸ ((hcritg w).mp hw).1))

end
