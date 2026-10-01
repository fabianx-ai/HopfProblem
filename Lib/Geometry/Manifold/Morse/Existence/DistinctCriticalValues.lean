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
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.Morse.HandleAttachment
public import Lib.Geometry.Manifold.Flow.HeightTranslating
public import Lib.Geometry.Manifold.Morse.Existence.RegularLocus

/-!
# Morse functions with distinct critical values

On a compact smooth manifold modelled on a finite-dimensional space, every Morse function can be
perturbed, by adding `a • ψ` for a bump function `ψ` that is locally constant at the critical
points, into a Morse function with the same critical points and pairwise distinct critical
values. Combined with the existence of Morse functions (`ManifoldMorse.exists_morse_function`)
this gives a Morse function with finitely many critical points, all on distinct levels
(Milnor, *Lectures on the h-cobordism theorem*, Theorem 2.7).

## Main results

* `ManifoldMorse.constantPerturb`: the perturbation `x ↦ f x + a * ψ x`.
* `ManifoldMorse.exists_separating_critical_value`: move one critical value off all others.
* `ManifoldMorse.exists_distinct_critical_values`
* `ManifoldMorse.exists_morse_function_with_distinct_critical_values`

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], Theorem 2.7

## Tags

Morse function, critical value, perturbation
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Constant perturbations -/

/-- The perturbation of a function by a constant shift. -/
def ManifoldMorse.constantPerturb {M : Type*} (f ψ : M → ℝ) (a : ℝ) (x : M) : ℝ :=
  f x + a * ψ x

/-- The constant perturbation is smooth. -/
theorem ManifoldMorse.contMDiff_constantPerturb {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ψ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry (constantPerturb f ψ)) :=
  (hf.comp contMDiff_snd).add (contMDiff_fst.smul (hψ.comp contMDiff_snd))

/-- A locally constant perturbation does not change the derivative. -/
theorem ManifoldMorse.mfderiv_constantPerturb_of_locally_constant {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} {b : ℝ} (hψ : ψ =ᶠ[𝓝 x] fun _ => b) (a : ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (constantPerturb f ψ a) x = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x := by
  have heq : constantPerturb f ψ a =ᶠ[𝓝 x] (fun y => f y + a * b) := by
    filter_upwards [hψ] with y hy
    simp only [constantPerturb, hy]
  rw [heq.mfderiv_eq]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f + fun _ => a * b) x = _
  rw [mfderiv_add (hf.mdifferentiableAt (by simp)) mdifferentiableAt_const, mfderiv_const]
  exact add_zero _

/-- Small constant perturbations preserve the Morse critical points. -/
theorem ManifoldMorse.eventually_constantPerturb_morse_criticalPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ψ)
    (hconstant : ∀ p ∈ criticalPoints E f, ∃ b : ℝ, ψ =ᶠ[𝓝 p] fun _ => b) :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      IsMorse E (constantPerturb f ψ a) ∧
        criticalPoints E (constantPerturb f ψ a) = criticalPoints E f := by
  have hfamily := contMDiff_constantPerturb hf hψ
  have hzero : constantPerturb f ψ 0 = f := by funext x; simp [constantPerturb]
  have hm₀ : IsMorseOn E (constantPerturb f ψ 0) Set.univ := by
    rw [hzero]
    exact fun x _ => hm x
  have hmor := (isOpen_isMorseOn hfamily isCompact_univ).mem_nhds hm₀
  let U := ⋃ b : ℝ, interior {x : M | ψ x = b}
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_interior)
  have hcover : criticalPoints E (constantPerturb f ψ 0) ⊆ U := by
    rw [hzero]
    intro p hp
    obtain ⟨b, hb⟩ := hconstant p hp
    exact Set.mem_iUnion.mpr ⟨b, mem_interior_iff_mem_nhds.mpr hb⟩
  have hfixed :
    ∀ a x,
      x ∈ U →
        (x ∈ criticalPoints E (constantPerturb f ψ a) ↔
          x ∈ criticalPoints E (constantPerturb f ψ 0)) := by
    intro a x hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    have hlocal : ψ =ᶠ[𝓝 x] fun _ => b := mem_interior_iff_mem_nhds.mp hb
    rw [hzero]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (constantPerturb f ψ a) x = 0 ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
    rw [mfderiv_constantPerturb_of_locally_constant hf hlocal a]
    rfl
  have hcrit := eventually_criticalPoints_eq hfamily 0 hU hcover hfixed
  rw [hzero] at hcrit
  filter_upwards [hmor, hcrit] with a ha hc
  exact ⟨fun x => ha x (Set.mem_univ x), hc⟩

/-- Critical values can be separated: between any two critical levels there is a regular level, the running hypothesis of the Morse-handle induction (Milnor, Morse Theory, Section 3). -/
theorem ManifoldMorse.exists_separating_critical_value {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) (p : M) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        IsMorse E g ∧
          criticalPoints E g = criticalPoints E f ∧
            (∀ x ∈ criticalPoints E f, x ≠ p → g x = f x) ∧
              ∀ x ∈ criticalPoints E f, g x = g p → x = p := by
  classical
  let K := criticalPoints E f
  have hK : K.Finite := finite_criticalPoints hf hm
  have hclosed : IsClosed (K \ { p }) := (hK.subset Set.sdiff_subset).isClosed
  have hp : p ∈ (K \ { p })ᶜ := by simp
  obtain ⟨ψ, _, hψsub⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p).mem_iff.mp
      (hclosed.isOpen_compl.mem_nhds hp)
  have hψone : (ψ : M → ℝ) =ᶠ[𝓝 p] fun _ => 1 := ψ.eventuallyEq_one
  have hψzero (x : M) (hx : x ∈ K) (hxp : x ≠ p) : (ψ : M → ℝ) =ᶠ[𝓝 x] fun _ => 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h
    exact hψsub h ⟨hx, by simpa only [Set.mem_singleton_iff] using hxp⟩
  have hconstant : ∀ x ∈ criticalPoints E f, ∃ b : ℝ, (ψ : M → ℝ) =ᶠ[𝓝 x] fun _ => b := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      exact ⟨1, hψone⟩
    · exact ⟨0, hψzero x hx hxp⟩
  have hstable := eventually_constantPerturb_morse_criticalPoints hf hm ψ.contMDiff hconstant
  let T : Set ℝ := (fun x => f x - f p) '' (K \ { p })
  have hT : T.Finite := (hK.subset Set.sdiff_subset).image _
  have hdense : Dense Tᶜ := by
    have heq : (Set.univ : Set ℝ) \ T = Tᶜ := by
      ext a
      exact and_iff_right (Set.mem_univ a)
    rw [← heq]
    exact dense_univ.sdiff_finite hT
  obtain ⟨U, hUstable, hU, hzeroU⟩ := _root_.mem_nhds_iff.mp hstable
  obtain ⟨a, haT, haU⟩ := hdense.exists_mem_open hU ⟨0, hzeroU⟩
  let g := constantPerturb f ψ a
  have hvalues (x : M) (hx : x ∈ K) (hxp : x ≠ p) : g x = f x := by
    have hxzero : ψ x = 0 := (hψzero x hx hxp).eq_of_nhds
    simp only [g, constantPerturb, hxzero, MulZeroClass.mul_zero, add_zero]
  have hpvalue : g p = f p + a := by
    have hpone : ψ p = 1 := hψone.eq_of_nhds
    simp only [g, constantPerturb, hpone, mul_one]
  refine
    ⟨g, (contMDiff_constantPerturb hf ψ.contMDiff).comp (contMDiff_const.prodMk contMDiff_id),
      (hUstable haU).1, (hUstable haU).2, hvalues, ?_⟩
  intro x hx heq
  by_contra hxp
  have hax : f x - f p = a := by rw [hvalues x hx hxp, hpvalue] at heq; linarith
  exact haT ⟨x, ⟨hx, by simpa only [Set.mem_singleton_iff] using hxp⟩, hax⟩

/-- Critical values can be made pairwise distinct by an arbitrarily small perturbation (Milnor, h-cobordism Theorem 2.5). -/
theorem ManifoldMorse.exists_distinct_critical_values {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        IsMorse E g ∧
          criticalPoints E g = criticalPoints E f ∧ Set.InjOn g (criticalPoints E g) := by
  classical
  let K := criticalPoints E f
  have hK : K.Finite := finite_criticalPoints hf hm
  have hfinite :
    ∀ s : Finset M,
      (s : Set M) ⊆ K →
        ∃ g : M → ℝ,
          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
            IsMorse E g ∧ criticalPoints E g = K ∧ Set.InjOn g (s : Set M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨f, hf, hm, rfl, by simp⟩
    | @insert p s hps ih =>
      intro hsK
      have hsK' : (s : Set M) ⊆ K := fun x hx => hsK (Finset.mem_insert_of_mem hx)
      obtain ⟨g, hg, hmg, hcrit, hinj⟩ := ih hsK'
      obtain ⟨g', hg', hmg', hcrit', hfixed, hunique⟩ := exists_separating_critical_value hg hmg p
      have hK' : criticalPoints E g' = K := hcrit'.trans hcrit
      refine ⟨g', hg', hmg', hK', ?_⟩
      intro x hx y hy heq
      have hxcrit : x ∈ criticalPoints E g := hcrit ▸ hsK hx
      have hycrit : y ∈ criticalPoints E g := hcrit ▸ hsK hy
      by_cases hxp : x = p
      · subst x
        exact (hunique y hycrit heq.symm).symm
      by_cases hyp : y = p
      · subst y
        exact hunique x hxcrit heq
      have hxs : x ∈ (s : Set M) := (Finset.mem_insert.mp hx).resolve_left hxp
      have hys : y ∈ (s : Set M) := (Finset.mem_insert.mp hy).resolve_left hyp
      apply hinj hxs hys
      rw [← hfixed x hxcrit hxp, ← hfixed y hycrit hyp]
      exact heq
  obtain ⟨g, hg, hmg, hcrit, hinj⟩ := hfinite hK.toFinset (by simp)
  refine ⟨g, hg, hmg, hcrit, ?_⟩
  rw [hcrit]
  simpa only [hK.coe_toFinset] using hinj

/-- A Morse function with all critical values distinct exists on every compact smooth manifold - the form used throughout the handle induction (Milnor, h-cobordism Theorem 2.5; Hatcher, Algebraic Topology, Section 0). -/
theorem ManifoldMorse.exists_morse_function_with_distinct_critical_values (E : Type*)
    (M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        IsMorse E f ∧ (criticalPoints E f).Finite ∧ Set.InjOn f (criticalPoints E f) := by
  obtain ⟨f, hf, hm⟩ := exists_morse_function E M
  obtain ⟨g, hg, hmg, _, hinj⟩ := exists_distinct_critical_values hf hm
  exact ⟨g, hg, hmg, finite_criticalPoints hg hmg, hinj⟩
