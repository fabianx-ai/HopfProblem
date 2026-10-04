/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Cancellation.ConnectionData
import Lib.Geometry.Manifold.Morse.Cancellation.BasinSheets

/-!
# The first cancellation theorem

`MorseCancellation.cancel_of_transverse_level_isotopy` is the First Cancellation
Theorem (Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4): let `f`
be a Morse function on a compact manifold of dimension `m + 1` with a descending
field `V` and flow `F`, `p` and `q` critical points of index `k` and `k + 1`
with `f p < f q` and no other critical value in `[l, u]`, and `c` a regular
value strictly between `f p` and `f q` with no critical value in `[a, b] ∋ c`.
If a diffeomorphism `D` of the level `{f = c}` isotopic to the identity carries
the unstable sphere of `q` to a set meeting the stable sphere of `p` in exactly
one point, transversally (as witnessed by maps `α`, `β` into the two spheres),
then there is a Morse function `g` equal to `f` off `f ⁻¹' (Ioo l u)` whose
critical set is that of `f` minus `{p, q}`.

The proof realises the level isotopy by a new descending field, then applies
`cancel_unique_connection_of_transverse_basin_sheets`: a unique connecting
orbit whose stable and unstable sheets are transverse produces cancellation
data (`Morse.Cancellation.ConnectionData`) which is cancelled through
`Morse.Cancellation.BasinSheets`.

## Main results

* `MorseCancellation.cancel_unique_connection_of_transverse_basin_sheets`
* `MorseCancellation.cancel_of_transverse_level_isotopy`

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, Theorem 5.4.

## Tags

morse-theory, cancellation, h-cobordism
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### The cancellation theorem -/

attribute [local instance 100] Classical.propDecidable in
/-- A unique connection with transverse basin sheets cancels. -/
theorem MorseCancellation.cancel_unique_connection_of_transverse_basin_sheets {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {A B HA HB X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] {f : M → ℝ} {p q z : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc c d → x = p ∨ x = q)
    (hp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t z = x)
    (heqp : ∀ᶠ x in 𝓝 p, V x = cp.descentField x) (heqq : ∀ᶠ x in 𝓝 q, V x = cq.descentField x)
    {S : X → M} {T : Y → M} {x : X} {y : Y} (hS : MDifferentiableAt I 𝓘(ℝ, E) S x)
    (hT : MDifferentiableAt I' 𝓘(ℝ, E) T y) (hS0 : S x = z) (hT0 : T y = z)
    (hSbasin : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => F t (S u)) Filter.atBot (𝓝 q))
    (hTbasin : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => F t (T u)) Filter.atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) S T x y) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          (ManifoldMorse.criticalPoints E g).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ ManifoldMorse.criticalPoints E g ↔
                  x ∈ ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨D, -, hgeometry, t₀, ht₀⟩ :=
    exists_native_connection_cancellation_data cp cq hf hdim hindex V hV hzero hdesc F hF hpc hqc
      hpq hc hd hpair hp hq hunique heqp heqq
  let τ := SmoothODE.nativeFlowTimeDiffeomorph_of_field hV F hF t₀
  have hτ (u : M) : τ u = F t₀ u := rfl
  have hS' : MDifferentiableAt I 𝓘(ℝ, E) (τ ∘ S) x :=
    (τ.contMDiff.mdifferentiableAt (by simp)).comp x hS
  have hT' : MDifferentiableAt I' 𝓘(ℝ, E) (τ ∘ T) y :=
    (τ.contMDiff.mdifferentiableAt (by simp)).comp y hT
  have hS0' : (τ ∘ S) x = D.A 0 := by rw [Function.comp_apply, hτ, hS0, ht₀]
  have hT0' : (τ ∘ T) y = D.A 0 := by rw [Function.comp_apply, hτ, hT0, ht₀]
  have hSb : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => D.flow t ((τ ∘ S) u)) Filter.atBot (𝓝 q) := by
    filter_upwards [hSbasin] with u hu
    apply ((hgeometry ((τ ∘ S) u)).2.2 q).mpr
    exact (flow_time_atBot_limit_iff F t₀ (S u) q).mpr hu
  have hTb : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => D.flow t ((τ ∘ T) u)) Filter.atTop (𝓝 p) := by
    filter_upwards [hTbasin] with u hu
    apply ((hgeometry ((τ ∘ T) u)).2.1 p).mpr
    exact (flow_time_atTop_limit_iff F t₀ (T u) p).mpr hu
  have ht : NativeTransversality.At I I' 𝓘(ℝ, E) (τ ∘ S) (τ ∘ T) x y :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff τ.toPartialDiffeomorph
          hS hT (hT0.trans hS0.symm) (Set.mem_univ _)).mp
      htrans
  exact
    D.cancel_of_transverse_basin_sheets hS' hT' hS0' hT0' hSb hTb ht hf hm hinj hpc hqc hpq hc hd
      hpair

attribute [local instance 100] Classical.propDecidable in
/-- The cancellation theorem: a unique transverse connection can be cancelled by a level isotopy. -/
theorem MorseCancellation.cancel_of_transverse_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {A B HA HB X Y : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] {f : M → ℝ} {p q : M}
    (cp : ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (z : M) → TangentSpace 𝓘(ℝ, E) z)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ z ∈ ManifoldMorse.criticalPoints E f, V z = 0)
    (hdesc : ∀ z, z ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0)
    (F : Flow ℝ M) (hF : ∀ z, IsMIntegralCurve (fun t => F t z) V)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ ManifoldMorse.criticalPoints E f) {l u a b c : ℝ} (hl : l < f p)
    (hu : f q < u)
    (hpair : ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (ha : a < c) (hb : c < b) (hpc' : f p < c) (hqc' : c < f q)
    (hband : ∀ z, f z ∈ Set.Icc a b → z ∉ ManifoldMorse.criticalPoints E f)
    (hreg : ∀ z, f z = c → z ∉ ManifoldMorse.criticalPoints E f)
    (heqp : ∀ᶠ z in 𝓝 p, V z = cp.descentField z) (heqq : ∀ᶠ z in 𝓝 q, V z = cq.descentField z) :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ D :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        { z : M // f z = c } { z : M // f z = c } ∞,
      SupportedDiffeomorph.IsotopicToIdentity D →
        {z : { w : M // f w = c } |
                Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
                  Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)}.ncard =
            1 →
          ∀ (α : X → { z : M // f z = c }) (β : Y → { z : M // f z = c }) (x : X) (y : Y),
            MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
              MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y →
                β y = α x →
                  NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
                    (∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => F t (α z)) Filter.atBot (𝓝 q)) →
                      (∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => F t (D (β z))) Filter.atTop (𝓝 p)) →
                        ∃ g : M → ℝ,
                          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                            ManifoldMorse.IsMorse E g ∧
                              (ManifoldMorse.criticalPoints E g).ncard + 2 =
                                  (ManifoldMorse.criticalPoints E f).ncard ∧
                                (∀ z,
                                    z ∈ ManifoldMorse.criticalPoints E g ↔
                                      z ∈ ManifoldMorse.criticalPoints E f ∧
                                        z ≠ p ∧ z ≠ q) ∧
                                  ∀ z, f z ∉ Set.Ioo l u → g =ᶠ[𝓝 z] f := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  intro D hD hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain
    ⟨r, C, W, V', H, G, -, -, -, -, -, -, hgeometry, hV', hG, hzeros, hneg, hgerms, -, hend, -,
      hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf hV hdesc F hF ha hb
      hband hreg (α x) D hD
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy F H G Subtype.val D
      (fun z => (hgeometry z).2.1) (fun z => (hgeometry z).2.2) hend hleft hright
  have hαb : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => G t (α z)) Filter.atBot (𝓝 q) := by
    filter_upwards [hαbasin] with z hz
    exact (hback (α z) q).mpr hz
  have hβb : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => G t (β z)) Filter.atTop (𝓝 p) := by
    filter_upwards [hβbasin] with z hz
    exact (hforward (β z) p).mpr hz
  obtain ⟨z₀, hz₀⟩ := Set.ncard_eq_one.mp hcount
  have hαq : Filter.Tendsto (fun t => F t (α x)) Filter.atBot (𝓝 q) := hαbasin.self_of_nhds
  have hαp : Filter.Tendsto (fun t => F t (D (α x))) Filter.atTop (𝓝 p) := by
    rw [← hcross]
    exact hβbasin.self_of_nhds
  have hαeq : α x = z₀ := by
    have hh :
      α x ∈
        {z : { w : M // f w = c } |
          Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)} :=
      ⟨hαq, hαp⟩
    rw [hz₀] at hh
    exact Set.mem_singleton_iff.mp hh
  have huniq (z : { w : M // f w = c }) (hzq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hzp : Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)) : z = α x := by
    have hh :
      z ∈
        {z : { w : M // f w = c } |
          Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)} :=
      ⟨hzq, hzp⟩
    rw [hz₀] at hh
    exact (Set.mem_singleton_iff.mp hh).trans hαeq.symm
  obtain ⟨hqG, hpG, huniqueG⟩ :=
    FlowSuspension.unique_connection_of_level_basin_intersection F G hf.continuous hqc'
      hpc' D (fun z => hback z q) (fun z => hforward z p) (α x) hαq hαp huniq
  obtain ⟨hS, hT, hS0, hT0, hSb, hTb, ht⟩ :=
    FlowSuspension.native_transverse_basin_tubes_of_level_maps hf hreg hV' G hG
      (fun z hz => hneg z (hreg z hz)) α β x y hα hβ hcross htrans hαb hβb
  have hgermp : ∀ᶠ z in 𝓝 p, V' z = cp.descentField z := by
    filter_upwards [hgerms p hpc, heqp] with z hz hz'
    exact hz.trans hz'
  have hgermq : ∀ᶠ z in 𝓝 q, V' z = cq.descentField z := by
    filter_upwards [hgerms q hqc, heqq] with z hz hz'
    exact hz.trans hz'
  exact
    cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hindex V' hV'
      (fun z hz => (hzeros z).mpr (hzero z hz)) hneg G hG hinj hpc hqc (hpc'.trans hqc') hl hu
      hpair hpG hqG huniqueG hgermp hgermq hS hT hS0 hT0 hSb hTb ht

end
