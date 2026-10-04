/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Combinatorics.IndexDisorder
import Lib.Geometry.Manifold.Morse.Cubic
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.OrderedCancellation.PrescribedFlow

/-!
# Exchanging the critical values of two consecutive critical points

The rearrangement step of Milnor, *Lectures on the h-cobordism theorem*, Theorem 4.1: if two
critical points `p < q` of a Morse function are consecutive in value and no flow line of a
gradient-like field runs from `q` down to `p`, the critical values can be exchanged by a new Morse
function with the same critical points, the same indices and the same gradient-like field
(`MorseCancellation.exists_flow_preserving_value_exchange`).  Iterating the exchange makes any
two given critical points consecutive while keeping the flow
(`exists_flow_preserving_consecutive_pair`).  The measure that decreases along the iteration is
the *index disorder* `MorseCancellation.nativeIndexDisorder` (the number of value-ordered pairs
with inverted indices), cf. `Lib.Combinatorics.IndexDisorder`.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- If `f` is injective on `S`, `p q ∈ S`, and `g` is obtained from `f` by exchanging the values at
`p` and `q` (`g p = f q`, `g q = f p`, `g x = f x` for the other points of `S`), then `g` is
injective on `S`. -/
theorem MorseCancellation.injOn_of_exchanged_values {X Y : Type*} {f g : X → Y} {S : Set X} {p q : X}
    (hinj : Set.InjOn f S) (hp : p ∈ S) (hq : q ∈ S) (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ S, x ≠ p → x ≠ q → g x = f x) : Set.InjOn g S := by
  classical
  have hform (x : X) (hx : x ∈ S) : g x = f (Equiv.swap p q x) := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hgq
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hothers x hx hxp hxq
  have hmaps : Set.MapsTo (Equiv.swap p q) S S := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hq
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hp
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hx
  intro x hx y hy hxy
  apply (Equiv.swap p q).injective
  apply hinj (hmaps hx) (hmaps hy)
  rw [← hform x hx, ← hform y hy]
  exact hxy

/-- If `g` and `f` have the same critical points and the same `nativeMorseIndex` at each of them,
then `nativeMorseCount E g k = nativeMorseCount E f k` for every `k`. -/
theorem MorseCancellation.nativeMorseCount_eq_of_preserved_indices {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hindex :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x)
    (k : ℕ) : nativeMorseCount E g k = nativeMorseCount E f k := by
  have heq :
    {x : M | x ∈ ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g x = k} =
      {x : M | x ∈ ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = k} := by
    ext x
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [hcrit]
    by_cases hx : x ∈ ManifoldMorse.criticalPoints E f
    · rw [hindex x hx]
    · simp only [hx, false_and]
  exact congrArg Set.ncard heq

/-- Let `S : AdaptedWindows E f` and let `g` be a Morse function with the same critical points
as `f` which exchanges the values of the critical points `p`, `q` and agrees with `f` near every
other critical point.  Then `g` has distinct critical values and admits an `AdaptedWindows E g`. -/
theorem MorseCancellation.adapted_surgery_system_after_value_exchange {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M} [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (S : AdaptedWindows E f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : ManifoldMorse.IsMorse E g) (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hq : q ∈ ManifoldMorse.criticalPoints E f)
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ ManifoldMorse.criticalPoints E f, x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) :
    Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧ Nonempty (AdaptedWindows E g) := by
  have hinj : Set.InjOn g (ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      injOn_of_exchanged_values S.distinct hp hq hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  exact ⟨hinj, nonempty_adaptedSurgeryWindows hg hmg hinj⟩

/-- Milnor, h-cobordism Theorem 4.1 (one exchange).  Let `f` be a Morse function with distinct
critical values on a compact connected manifold, `V` a gradient-like field with flow `F` modelled
by signed Morse charts near the critical points, and `p`, `q` critical points with `f p < f q`,
no critical value strictly between, and no flow line from `q` to `p`.  Then there is a Morse
function `g` with the same critical points, distinct critical values, `g p = f q`, `g q = f p`,
`g = f` near the other critical points, for which `V` is still gradient-like and modelled by
signed Morse charts, with the same indices and the same index counts. -/
theorem MorseCancellation.exists_flow_preserving_value_exchange {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        ∃ c : ManifoldMorse.SignedMorseChart (E := E) f x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hnoconnection :
      ∀ x,
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p.val))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        ManifoldMorse.IsMorse E g ∧
          ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f ∧
            Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
              g p = f q ∧
                g q = f p ∧
                  (∀ x ∈ ManifoldMorse.criticalPoints E f,
                      x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f) ∧
                    (∀ x,
                        x ∉ ManifoldMorse.criticalPoints E g →
                          mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
                      (∀ x ∈ ManifoldMorse.criticalPoints E g,
                          ∃ c : ManifoldMorse.SignedMorseChart (E := E) g x,
                            ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                        (∀ x ∈ ManifoldMorse.criticalPoints E f,
                            nativeMorseIndex E g x = nativeMorseIndex E f x) ∧
                          ∀ k, nativeMorseCount E g k = nativeMorseCount E f k := by
  obtain ⟨S⟩ := ManifoldMorse.nonempty_surgeryWindows hf hm hinj
  obtain ⟨cp, hcp⟩ := hmodels p p.property
  obtain ⟨cq, hcq⟩ := hmodels q q.property
  have hp : f p ∈ Set.Ioo (S.lower p) (S.upper q) :=
    ⟨S.lower_lt_value p, hpq.trans (S.value_lt_upper q)⟩
  have hq : f q ∈ Set.Ioo (S.lower p) (S.upper q) :=
    ⟨(S.lower_lt_value p).trans hpq, S.value_lt_upper q⟩
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, -, hpgerm, hqgerm, hothers, hindices⟩ :=
    MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm hV F hF hzero
      hdesc hinj cp cq hcp hcq hp hq hpq hq hp (surgery_pair_band_isolation S p q hconsecutive)
      hnoconnection
  have hinjg : Set.InjOn g (ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      injOn_of_exchanged_values hinj p.property q.property hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  have hnewmodels :
    ∀ x ∈ ManifoldMorse.criticalPoints E g,
      ∃ c : ManifoldMorse.SignedMorseChart (E := E) g x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    rw [hcrit] at hx
    by_cases hxp : x = p.val
    · subst x
      obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field cp hpgerm
      exact ⟨c, hc ▸ hcp⟩
    by_cases hxq : x = q.val
    · subst x
      obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field cq hqgerm
      exact ⟨c, hc ▸ hcq⟩
    obtain ⟨c, hc⟩ := hmodels x hx
    obtain ⟨d, hd⟩ := exists_signed_morse_chart_of_germ_preserving_field c (hothers x hx hxp hxq)
    exact ⟨d, hd ▸ hc⟩
  exact
    ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, (fun x hx => hdescent x (hcrit ▸ hx)),
      hnewmodels, hindices, nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

/-- Iterated exchange.  Under the hypotheses of `exists_flow_preserving_value_exchange` for the
field `V` and critical points `r`, `p`, `q` with `f₀ r < f₀ p < f₀ q` such that no flow line runs
from `q` to a critical point other than `p`, `q`, `r`, there is a Morse function `f` with the same
critical points and indices, distinct critical values, `f p = f₀ p`, `f r = f₀ r`, `f p < f q`,
no critical value strictly between `f p` and `f q`, for which `V` is gradient-like and modelled by
signed Morse charts. -/
theorem MorseCancellation.exists_flow_preserving_consecutive_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f₀ : M → ℝ}
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : ManifoldMorse.IsMorse E f₀)
    (hinj₀ : Set.InjOn f₀ (ManifoldMorse.criticalPoints E f₀))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f₀, V x = 0)
    (hdesc₀ : ∀ x, x ∉ ManifoldMorse.criticalPoints E f₀ → mvfderiv 𝓘(ℝ, E) f₀ x (V x) < 0)
    (hmodels₀ :
      ∀ x ∈ ManifoldMorse.criticalPoints E f₀,
        ∃ c : ManifoldMorse.SignedMorseChart (E := E) f₀ x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : ManifoldMorse.criticalPoints E f₀) (hrp : f₀ r < f₀ p) (hpq : f₀ p < f₀ q)
    (hnoconnection :
      ∀ j : ManifoldMorse.criticalPoints E f₀,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val))) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ManifoldMorse.criticalPoints E f = ManifoldMorse.criticalPoints E f₀ ∧
            Set.InjOn f (ManifoldMorse.criticalPoints E f) ∧
              f p = f₀ p ∧
                f r = f₀ r ∧
                  f p < f q ∧
                    (∀ z : ManifoldMorse.criticalPoints E f₀, ¬(f p < f z ∧ f z < f q)) ∧
                      (∀ x,
                          x ∉ ManifoldMorse.criticalPoints E f →
                            mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                        (∀ x ∈ ManifoldMorse.criticalPoints E f,
                            ∃ c : ManifoldMorse.SignedMorseChart (E := E) f x,
                              ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                          ∀ x ∈ ManifoldMorse.criticalPoints E f₀,
                            nativeMorseIndex E f x = nativeMorseIndex E f₀ x := by
  classical
  let _ := (ManifoldMorse.finite_criticalPoints hf₀ hm₀).fintype
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ManifoldMorse.criticalPoints E f = ManifoldMorse.criticalPoints E f₀ ∧
            Set.InjOn f (ManifoldMorse.criticalPoints E f) ∧
              f p = f₀ p ∧
                f r = f₀ r ∧
                  f p < f q ∧
                    (∀ x,
                        x ∉ ManifoldMorse.criticalPoints E f →
                          mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                      (∀ x ∈ ManifoldMorse.criticalPoints E f,
                          ∃ c : ManifoldMorse.SignedMorseChart (E := E) f x,
                            ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                        (∀ x ∈ ManifoldMorse.criticalPoints E f₀,
                            nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
                          IndexDisorder.beforeValueRank
                              (fun x : ManifoldMorse.criticalPoints E f₀ => f x) q =
                            n
  have hex : ∃ n, P n :=
    ⟨IndexDisorder.beforeValueRank
        (fun x : ManifoldMorse.criticalPoints E f₀ => f₀ x) q,
      f₀, hf₀, hm₀, rfl, hinj₀, rfl, rfl, hpq, hdesc₀, hmodels₀, fun _ _ => rfl, rfl⟩
  obtain ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hdesc, hmodels, hindices, hrank⟩ :=
    Nat.find_spec hex
  have hconsecutive : ∀ z : ManifoldMorse.criticalPoints E f₀, ¬(f p < f z ∧ f z < f q) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨z, hpz, hzq, hbefore⟩ :=
      IndexDisorder.exists_consecutive_below_of_intermediate (h :=
        fun x : ManifoldMorse.criticalPoints E f₀ => f x) (p := p) (q := q) hnot
    have hzp : z.val ≠ p.val := fun h => (ne_of_lt hpz) (congrArg f h).symm
    have hzq' : z.val ≠ q.val := fun h => (ne_of_lt hzq) (congrArg f h)
    have hzr : z.val ≠ r.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      exact (not_lt_of_gt hpz) (by simpa only [h] using hrp')
    let zf : ManifoldMorse.criticalPoints E f := ⟨z.val, by rw [hcrit]; exact z.property⟩
    let qf : ManifoldMorse.criticalPoints E f := ⟨q.val, by rw [hcrit]; exact q.property⟩
    have hbeforef : ∀ s : ManifoldMorse.criticalPoints E f, ¬(f zf < f s ∧ f s < f qf) := by
      intro s hs
      exact hbefore ⟨s.val, by rw [← hcrit]; exact s.property⟩ hs
    obtain ⟨g, hg, hmg, hcritg, hinjg, hgz, hgq, hothers, hdescg, hmodelsg, hindicesg, -⟩ :=
      exists_flow_preserving_value_exchange hf hm hinj hV F hF (fun x hx => hzero x (hcrit ▸ hx))
        hdesc hmodels zf qf hzq hbeforef
        (hnoconnection z (fun h => hzq' (congrArg Subtype.val h))
          (fun h => hzp (congrArg Subtype.val h)) (fun h => hzr (congrArg Subtype.val h)))
    have hpcrit : p.val ∈ ManifoldMorse.criticalPoints E f := by
      rw [hcrit]
      exact p.property
    have hrcrit : r.val ∈ ManifoldMorse.criticalPoints E f := by
      rw [hcrit]
      exact r.property
    have hpq' : p.val ≠ q.val := fun h => (ne_of_lt hfpq) (congrArg f h)
    have hrq' : r.val ≠ q.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      have hlt : f r < f q := hrp'.trans hfpq
      exact (ne_of_lt hlt) (congrArg f h)
    have hgp : g p = f p := (hothers p hpcrit hzp.symm hpq').self_of_nhds
    have hgr : g r = f r := (hothers r hrcrit hzr.symm hrq').self_of_nhds
    have hidxg₀ (x : M) (hx : x ∈ ManifoldMorse.criticalPoints E f₀) :
      nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
    have hdecrease :
      IndexDisorder.beforeValueRank
          (fun x : ManifoldMorse.criticalPoints E f₀ => g x) q <
        IndexDisorder.beforeValueRank
          (fun x : ManifoldMorse.criticalPoints E f₀ => f x) q := by
      apply
        IndexDisorder.beforeValueRank_exchange_lt (h :=
          fun x : ManifoldMorse.criticalPoints E f₀ => f x) (g :=
          fun x : ManifoldMorse.criticalPoints E f₀ => g x) (p := z) (q := q)
          (fun x y h =>
            Subtype.ext
              (hinj (by rw [hcrit]; exact x.property) (by rw [hcrit]; exact y.property) h))
          hzq hbefore hgz hgq
      intro x hxz hxq
      exact
        (hothers x (by rw [hcrit]; exact x.property) (fun h => hxz (Subtype.ext h))
            (fun h => hxq (Subtype.ext h))).self_of_nhds
    have hminimal :=
      Nat.find_min' hex
        ⟨g, hg, hmg, hcritg.trans hcrit, hinjg, hgp.trans hfp, hgr.trans hfr,
          (by rw [hgp, hgq]; exact hpz), hdescg, hmodelsg, hidxg₀, rfl⟩
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hconsecutive, hdesc, hmodels, hindices⟩

attribute [local instance 100] Classical.propDecidable in
/-- The index disorder of a Morse function `f`: `IndexDisorder.finiteIndexDisorder` of the
critical values and `nativeMorseIndex` on the (finite) set of critical points, and `0` when
that set is infinite. -/
def MorseCancellation.nativeIndexDisorder (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) : ℕ :=
  if hfinite : (ManifoldMorse.criticalPoints E f).Finite then
    let _ := hfinite.fintype
    IndexDisorder.finiteIndexDisorder
      (fun x : ManifoldMorse.criticalPoints E f => f x)
      (fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x)
  else 0

/-- When the critical set of `f` is finite, `nativeIndexDisorder E f` is
`IndexDisorder.finiteIndexDisorder (f ∘ val) (nativeMorseIndex E f ∘ val)` on it. -/
theorem MorseCancellation.nativeIndexDisorder_eq_of_finite {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite) :
    letI := hfinite.fintype
    nativeIndexDisorder E f =
      IndexDisorder.finiteIndexDisorder
        (fun x : ManifoldMorse.criticalPoints E f => f x)
        (fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) := by
  classical simp only [nativeIndexDisorder, dif_pos hfinite]

/-- If `g` has the same (finite) critical set as `f` and the same indices, then
`nativeIndexDisorder E g` is the index disorder of the values of `g` against the indices of `f`,
computed on the critical set of `f`. -/
theorem MorseCancellation.nativeIndexDisorder_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hindex :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    letI := hfinite.fintype
    nativeIndexDisorder E g =
      IndexDisorder.finiteIndexDisorder
        (fun x : ManifoldMorse.criticalPoints E f => g x)
        (fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) := by
  classical
  let _ := hfinite.fintype
  have hgfinite : (ManifoldMorse.criticalPoints E g).Finite := hcrit.symm ▸ hfinite
  let _ := hgfinite.fintype
  let e : ManifoldMorse.criticalPoints E f ≃ ManifoldMorse.criticalPoints E g :=
    Equiv.setCongr hcrit.symm
  rw [nativeIndexDisorder_eq_of_finite hgfinite]
  rw [←
    IndexDisorder.finiteIndexDisorder_comp_equiv
      (fun x : ManifoldMorse.criticalPoints E g => g x)
      (fun x : ManifoldMorse.criticalPoints E g => nativeMorseIndex E g x) e]
  have hw :
    ((fun x : ManifoldMorse.criticalPoints E g => nativeMorseIndex E g x) ∘ e) =
      fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x := by
    funext x
    exact hindex x x.property
  rw [hw]
  rfl

/-- Exchanging the values of two consecutive critical points `p`, `q` (`f p < f q`, no critical
value between) with `index q < index p`, keeping the other values and all indices, strictly
decreases the index disorder: `nativeIndexDisorder E g < nativeIndexDisorder E f`. -/
theorem MorseCancellation.nativeIndexDisorder_exchange_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hindexlt : nativeMorseIndex E f q < nativeMorseIndex E f p)
    (hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ ManifoldMorse.criticalPoints E f, x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f)
    (hindex :
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    nativeIndexDisorder E g < nativeIndexDisorder E f := by
  classical
  let _ : DecidableEq (ManifoldMorse.criticalPoints E f) := fun a b =>
    Classical.propDecidable (a = b)
  let _ := hfinite.fintype
  have hform :
    (fun x : ManifoldMorse.criticalPoints E f => g x) =
      (fun x : ManifoldMorse.criticalPoints E f => f x) ∘ Equiv.swap p q := by
    funext x
    by_cases hxp : x = p
    · subst x
      simpa only [Function.comp_apply, Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Function.comp_apply, Equiv.swap_apply_right] using hgq
    have hh :=
      (hothers x x.property (fun h => hxp (Subtype.ext h))
          (fun h => hxq (Subtype.ext h))).self_of_nhds
    simpa only [Function.comp_apply, Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hh
  rw [nativeIndexDisorder_transport hfinite hcrit hindex,
    nativeIndexDisorder_eq_of_finite hfinite, hform]
  have hi : Function.Injective (fun x : ManifoldMorse.criticalPoints E f => f x) :=
    fun x y h => Subtype.ext (hinj x.property y.property h)
  exact
    IndexDisorder.finiteIndexDisorder_swap_lt (h :=
      fun x : ManifoldMorse.criticalPoints E f => f x) hi
      (fun x : ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) (p := p) (q := q)
      hpq hconsecutive hindexlt

end
