/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Cancellation.CriticalGerms
import Lib.Geometry.Manifold.Morse.CubicFlow
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.RegularLevel

/-!
# What the birth of a critical pair preserves below the birth level

When a Morse function `g` differs from `f` only above a level `l` and has at most two new critical
points `p`, `q` (a *birth*, cf. Milnor, *Lectures on the h-cobordism theorem*, §8, Lemma 8.2), the
sublevel sets below `l` are unchanged: `g` and `f` have the same level set at every `a < l`
(`MorseCancellation.birth_preserves_lower_levels`), that level is regular for `g`
(`regular_level_of_retained_critical_germs`) and diffeomorphic to the level of `f`
(`equalLevelDiffeomorph`), index bounds below `a` persist (`birth_preserves_lower_index_bound`),
and a unique minimum stays unique (`birth_preserves_unique_index_zero`).  The bound
`superlevel_bound_of_critical_bound` is the minimum-principle argument behind these statements.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- Minimum principle.  Let `f` be continuous and `g` smooth on a compact manifold, `g = l` on the
level `f = l`, and `l ≤ g` at every critical point of `g` in `{l ≤ f}`.  Then `l ≤ g` on all of
`{l ≤ f}`. -/
theorem MorseCancellation.superlevel_bound_of_critical_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l : ℝ} (hboundary : ∀ y, f y = l → g y = l)
    (hcritical : ∀ y ∈ ManifoldMorse.criticalPoints E g, l ≤ f y → l ≤ g y) :
    ∀ x, l ≤ f x → l ≤ g x := by
  intro x hx
  have hK : IsCompact {y : M | l ≤ f y} := (isClosed_le continuous_const hf).isCompact
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hg.continuous.continuousOn
  have hgp : l ≤ g p := by
    by_cases hlt : l < f p
    · have hlocal : IsLocalMin g p := by
        filter_upwards [(isOpen_lt continuous_const hf).mem_nhds hlt] with y hy
        exact hmin hy.le
      exact hcritical p (ManifoldMorse.mem_criticalPoints_of_localMin hg hlocal) hp
    · have heq : f p = l := le_antisymm (le_of_not_gt hlt) hp
      exact (hboundary p heq).ge
  exact hgp.trans (hmin hx)

/-- Let `g` agree with `f` near every point outside `U ⊆ {l < f}` and near every critical point of
`f`, let every critical point of `g` be a critical point of `f` or one of `p`, `q` with
`l ≤ g p`, `l ≤ g q`.  Then for every `a < l`: `g y = a ↔ f y = a`, and `g = f` near every `y`
with `f y ≤ a`. -/
theorem MorseCancellation.birth_preserves_lower_levels {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l : ℝ} {U : Set M} {p q : M} (hU : U ⊆ {y : M | l < f y})
    (hexterior : ∀ y, y ∉ U → g =ᶠ[𝓝 y] f)
    (hkeep : ∀ y ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f)
    (hcrit :
      ∀ y ∈ ManifoldMorse.criticalPoints E g,
        y ∈ ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q)
    (hp : l ≤ g p) (hq : l ≤ g q) {a : ℝ} (ha : a < l) :
    (∀ y, g y = a ↔ f y = a) ∧ (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) := by
  have hout (y : M) (hy : f y ≤ l) : y ∉ U := fun h => (hU h).not_ge hy
  have hbound : ∀ y, l ≤ f y → l ≤ g y := by
    apply superlevel_bound_of_critical_bound hf hg
    · intro y hy
      exact (hexterior y (hout y hy.le)).self_of_nhds.trans hy
    · intro y hy hfy
      rcases hcrit y hy with hold | rfl | rfl
      · rw [(hkeep y hold).self_of_nhds]
        exact hfy
      · exact hp
      · exact hq
  refine ⟨?_, fun y hy => hexterior y (hout y (hy.trans ha.le))⟩
  intro y
  constructor
  · intro hgy
    have hfy : f y ≤ l := by
      by_contra h
      have hh := hbound y (le_of_not_ge h)
      rw [hgy] at hh
      exact ha.not_ge hh
    exact ((hexterior y (hout y hfy)).self_of_nhds).symm.trans hgy
  · intro hfy
    exact (hexterior y (hout y (hfy ▸ ha.le))).self_of_nhds.trans hfy

/-- If `f` and `g` are smooth, `a` is a regular value of both and `{g = a} = {f = a}` pointwise,
the identity is a diffeomorphism `{f = a} ≃ {g = a}` for the regular-level charted structures. -/
def MorseCancellation.equalLevelDiffeomorph {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f g : M → ℝ} {a : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hfr : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a) :
    let _ := RegularLevel.chartedSpace hf hfr
    let _ := RegularLevel.chartedSpace hg hgr
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      { y : M // f y = a } { y : M // g y = a } ∞ := by
  let _ := RegularLevel.chartedSpace hf hfr
  let _ := RegularLevel.chartedSpace hg hgr
  let F : { y : M // f y = a } → { y : M // g y = a } := fun y => ⟨y, (heq y).mpr y.property⟩
  let G : { y : M // g y = a } → { y : M // f y = a } := fun y => ⟨y, (heq y).mp y.property⟩
  exact
    { toFun := F
      invFun := G
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      contMDiff_toFun :=
        (RegularLevel.contMDiff_iff_inclusion hg hgr 𝓘(ℝ, RegularLevel.Model E) F).mpr
          (RegularLevel.contMDiff_inclusion hf hfr)
      contMDiff_invFun :=
        (RegularLevel.contMDiff_iff_inclusion hf hfr 𝓘(ℝ, RegularLevel.Model E) G).mpr
          (RegularLevel.contMDiff_inclusion hg hgr) }

/-- If `a` is regular for `f`, every critical point of `g` is a critical point of `f` (near which
`g = f`) or one of `p`, `q` with `a < g p`, `a < g q`, then `a` is regular for `g`. -/
theorem MorseCancellation.regular_level_of_retained_critical_germs {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f g : M → ℝ} {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {p q : M}
    (hcrit :
      ∀ y ∈ ManifoldMorse.criticalPoints E g,
        y ∈ ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q)
    (hkeep : ∀ y ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) (hp : a < g p)
    (hq : a < g q) : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g := by
  intro y hy hcy
  rcases hcrit y hcy with hold | rfl | rfl
  · exact hfr y (((hkeep y hold).self_of_nhds).symm.trans hy) hold
  · exact hp.ne' hy
  · exact hq.ne' hy

/-- If every critical point of `g` is a critical point of `f` (near which `g = f`) or one of `p`,
`q` with `a < g p`, `a < g q`, and every critical point of `f` with value `≤ a` has index `≤ k`,
then every critical point of `g` with value `≤ a` has index `≤ k`. -/
theorem MorseCancellation.birth_preserves_lower_index_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {a : ℝ}
    {k : ℕ}
    (hcrit :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        z ∈ ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f) (hp : a < g p)
    (hq : a < g q)
    (hlow : ∀ z : ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ k) :
    ∀ z : ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ k := by
  intro z hz
  rcases hcrit z.val z.property with hold | hzp | hzq
  · rw [nativeMorseIndex_congr_germ (hkeep z.val hold)]
    apply hlow ⟨z.val, hold⟩
    rwa [← (hkeep z.val hold).self_of_nhds]
  · exact False.elim (hp.not_ge (hzp ▸ hz))
  · exact False.elim (hq.not_ge (hzq ▸ hz))

/-- If every critical point of `g` is a critical point of `f` (near which `g = f`) or one of `p`,
`q`, `a` is regular for `f`, `f` has no critical value in `(a, b)`, `g p < b` and `g p < g q`,
then every critical value of `g` below `g p` is below `a`. -/
theorem MorseCancellation.birth_first_new_value_gap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {a b : ℝ}
    (hcrit :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        z ∈ ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hreg : ∀ z, f z = a → z ∉ ManifoldMorse.criticalPoints E f)
    (hband : ∀ z, f z ∈ Set.Ioo a b → z ∉ ManifoldMorse.criticalPoints E f) (hp : g p < b)
    (hpq : g p < g q) : ∀ z : ManifoldMorse.criticalPoints E g, g z < g p → g z < a := by
  intro z hz
  rcases hcrit z.val z.property with hold | hzp | hzq
  · have hzb : g z < b := hz.trans hp
    have heq := (hkeep z.val hold).self_of_nhds
    by_contra hnot
    have haz : a ≤ f z := by rw [← heq]; exact le_of_not_gt hnot
    have hne : a ≠ f z := fun h => hreg z.val h.symm hold
    exact hband z.val ⟨lt_of_le_of_ne haz hne, by rwa [← heq]⟩ hold
  · exact False.elim ((hzp ▸ hz : g p < g p).false)
  · exact False.elim (hpq.not_gt (hzq ▸ hz))

/-- If every critical point of `g` is a critical point of `f` (near which `g = f`) or one of `p`,
`q`, neither of which has index `0` for `g`, and `m` is the only index-`0` critical point of `f`,
then `m` is the only index-`0` critical point of `g`. -/
theorem MorseCancellation.birth_preserves_unique_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (m : ManifoldMorse.criticalPoints E f)
    (hcrit :
      ∀ z ∈ ManifoldMorse.criticalPoints E g,
        z ∈ ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hp : nativeMorseIndex E g p ≠ 0) (hq : nativeMorseIndex E g q ≠ 0)
    (hunique : ∀ z : ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m) :
    ∀ z ∈ ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = m.val := by
  intro z hz hi
  rcases hcrit z hz with hold | rfl | rfl
  · have hiold : nativeMorseIndex E f z = 0 :=
      (nativeMorseIndex_congr_germ (hkeep z hold)).symm.trans hi
    exact congrArg Subtype.val (hunique ⟨z, hold⟩ hiold)
  · exact False.elim (hp hi)
  · exact False.elim (hq hi)

end
