/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Flow.Compact
public import Lib.Geometry.Manifold.Flow.HeightTranslating
public import Lib.AlgebraicTopology.SingularHomology.LocalDegree
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.Sphere
/-!
# Sublevel sets of Morse functions

  Sublevel sets of Morse functions: the topology of `{x | f x <= c}` changes only
  when `c` crosses a critical value, and then by attachment of a handle of the
  critical point index (Hatcher, Algebraic Topology, Corollary 3.15 / Morse
  Theory, Section 3).
-/



open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### The punctured ball model -/

/-- The open ball of radius `R` with the origin removed. -/
abbrev PuncturedBall.Space (E : Type*) [NormedAddCommGroup E] (R : ℝ) :=
  { x : E // x ≠ 0 ∧ ‖x‖ < R }

/-- The inclusion of the radius-`R` punctured ball into the punctured space. -/
def PuncturedBall.toPunctured {E : Type*} [NormedAddCommGroup E] (R : ℝ) :
    C(Space E R, PuncturedRadial.Space E) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The sphere of radius `r` inside the punctured ball. -/
def PuncturedBall.fromSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) : C(Metric.sphere (0 : E) 1, Space E R) :=
  ⟨fun u =>
    ⟨r • (u : E), smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u),
      by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property,
        mul_one]
      exact hrR⟩,
    (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

/-- The convex blend of a punctured-ball point with the radius-`r` sphere. -/
def PuncturedBall.blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ)
    (r : ℝ) (q : (unitInterval) × Space E R) : E :=
  PuncturedRadial.blendVector r (q.1, toPunctured R q.2)

/-- The blend vector is continuous. -/
theorem PuncturedBall.continuous_blendVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : ℝ) (r : ℝ) : Continuous (blendVector (E := E) R r) :=
  (PuncturedRadial.continuous_blendVector r).comp
    (continuous_fst.prodMk ((toPunctured R).continuous.comp continuous_snd))

/-- The blend norm interpolates between `‖x‖` and `r`. -/
theorem PuncturedBall.norm_blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (r : ℝ) (hr : 0 < r) (t : (unitInterval)) (x : Space E R) :
    ‖blendVector R r (t, x)‖ = (1 - (t : ℝ)) * ‖x.val‖ + (t : ℝ) * r := by
  have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property.1
  have hscale : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * (r / ‖x.val‖) :=
    add_nonneg (sub_nonneg.mpr t.property.2) (mul_nonneg t.property.1 (div_nonneg hr.le hn.le))
  change ‖((1 - (t : ℝ)) + (t : ℝ) * (r / ‖x.val‖)) • x.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale, add_mul, mul_assoc,
    div_mul_cancel₀ _ hn.ne']

/-- The blend stays inside the ball of radius `R`. -/
theorem PuncturedBall.norm_blendVector_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : ℝ) (r : ℝ) (hr : 0 < r) (hrR : r < R) (t : (unitInterval))
    (x : Space E R) : ‖blendVector R r (t, x)‖ < R := by
  rw [norm_blendVector R r hr]
  exact
    (convex_Iio (𝕜 := ℝ) R) x.property.2 hrR (sub_nonneg.mpr t.property.2) t.property.1
      (sub_add_cancel 1 (t : ℝ))

/-! ### Transporting exactness -/

/-- Exactness transports across linear equivalences of all three terms. -/
theorem HomologyTransport.exact_of_equivalences {R A B C A' B' C' : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B'] [AddCommGroup C']
    [Module R C'] (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C') (f : A →ₗ[R] B)
    (g : B →ₗ[R] C) (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C') (hf : ∀ a, f' (eA a) = eB (f a))
    (hg : ∀ b, g' (eB b) = eC (g b)) (hexact : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range f' = LinearMap.ker g' := by
  ext b'
  constructor
  · rintro ⟨a', rfl⟩
    obtain ⟨a, rfl⟩ := eA.surjective a'
    have hfa : g (f a) = 0 := by
      have hmem : f a ∈ LinearMap.range f := ⟨a, rfl⟩
      rw [hexact] at hmem
      exact hmem
    change g' (f' (eA a)) = 0
    rw [hf, hg, hfa, map_zero]
  · intro hb'
    obtain ⟨b, rfl⟩ := eB.surjective b'
    have hgb : g b = 0 := eC.injective ((hg b).symm.trans (hb'.trans (map_zero eC).symm))
    have hb : b ∈ LinearMap.range f := by
      rw [hexact]
      exact hgb
    obtain ⟨a, ha⟩ := hb
    exact ⟨eA a, (hf a).trans (congrArg eB ha)⟩

/-! ### Critical points of smooth functions -/

/-- A local minimum of a smooth function is a critical point. -/
theorem ManifoldMorse.mem_criticalPoints_of_localMin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmin : IsLocalMin f p) :
    p ∈ criticalPoints E f := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hp : p ∈ e.source := mem_chart_source E p
  apply (mem_criticalPoints_iff hf he hp).mpr
  have hmin' : IsLocalMin f (e.symm (e p)) := by rw [e.left_inv hp]; exact hmin
  exact (hmin'.comp_continuous (e.continuousAt_symm (e.map_source hp))).fderiv_eq_zero

/-- A local maximum of a smooth function is a critical point. -/
theorem ManifoldMorse.mem_criticalPoints_of_localMax {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmax : IsLocalMax f p) :
    p ∈ criticalPoints E f := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hp : p ∈ e.source := mem_chart_source E p
  apply (mem_criticalPoints_iff hf he hp).mpr
  have hmax' : IsLocalMax f (e.symm (e p)) := by rw [e.left_inv hp]; exact hmax
  exact (hmax'.comp_continuous (e.continuousAt_symm (e.map_source hp))).fderiv_eq_zero

/-- With only two critical points they are the unique global minimum and maximum. -/
theorem ManifoldMorse.unique_extrema_of_two_critical_values {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {p q : M} (hpq : f p < f q) (hcrit : ∀ x ∈ criticalPoints E f, x = p ∨ x = q) :
    (∀ x, f x ≤ f p → x = p) ∧ (∀ x, f q ≤ f x → x = q) := by
  obtain ⟨u, _, hmin⟩ :=
    isCompact_univ.exists_isMinOn ⟨p, Set.mem_univ p⟩ hf.continuous.continuousOn
  obtain ⟨v, _, hmax⟩ :=
    isCompact_univ.exists_isMaxOn ⟨q, Set.mem_univ q⟩ hf.continuous.continuousOn
  have humin : IsLocalMin f u := Filter.Eventually.of_forall (fun x => hmin (Set.mem_univ x))
  have hvmax : IsLocalMax f v := Filter.Eventually.of_forall (fun x => hmax (Set.mem_univ x))
  have hup : u = p := by
    rcases hcrit u (mem_criticalPoints_of_localMin hf humin) with h | h
    · exact h
    · have hle : f u ≤ f p := hmin (Set.mem_univ p)
      rw [h] at hle
      exact False.elim (not_le_of_gt hpq hle)
  have hvq : v = q := by
    rcases hcrit v (mem_criticalPoints_of_localMax hf hvmax) with h | h
    · have hle : f q ≤ f v := hmax (Set.mem_univ q)
      rw [h] at hle
      exact False.elim (not_le_of_gt hpq hle)
    · exact h
  have hglobalMin (x : M) : f p ≤ f x := by rw [← hup]; exact hmin (Set.mem_univ x)
  have hglobalMax (x : M) : f x ≤ f q := by rw [← hvq]; exact hmax (Set.mem_univ x)
  constructor
  · intro x hx
    have hlocal : IsLocalMin f x := Filter.Eventually.of_forall (fun y => hx.trans (hglobalMin y))
    rcases hcrit x (mem_criticalPoints_of_localMin hf hlocal) with h | h
    · exact h
    · rw [h] at hx
      exact False.elim (not_le_of_gt hpq hx)
  · intro x hx
    have hlocal : IsLocalMax f x := Filter.Eventually.of_forall (fun y => (hglobalMax y).trans hx)
    rcases hcrit x (mem_criticalPoints_of_localMax hf hlocal) with h | h
    · rw [h] at hx
      exact False.elim (not_le_of_gt hpq hx)
    · exact h

/-- A small sublevel of a unique minimum fits in any neighborhood. -/
theorem exists_small_sublevel_subset {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : X → ℝ} (hf : Continuous f) {p : X} (hunique : ∀ x, f x ≤ f p → x = p) {U : Set X}
    (hU : IsOpen U) (hpU : p ∈ U) : ∃ ε > (0 : ℝ), {x | f x ≤ f p + ε} ⊆ U := by
  by_cases hne : Uᶜ.Nonempty
  · obtain ⟨q, hq, hmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn hne hf.continuousOn
    have hgap : f p < f q := by
      by_contra! h
      exact hq (hunique q h ▸ hpU)
    refine ⟨(f q - f p) / 2, half_pos (sub_pos.mpr hgap), ?_⟩
    intro x hx
    by_contra hxU
    have hqx : f q ≤ f x := hmin hxU
    change f x ≤ f p + (f q - f p) / 2 at hx
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x _
    by_contra hx
    exact hne ⟨x, hx⟩
