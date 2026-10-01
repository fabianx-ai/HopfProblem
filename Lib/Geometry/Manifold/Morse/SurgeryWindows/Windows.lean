/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.SurgeryData
public import Lib.Geometry.Manifold.WhitneyEmbedding

/-!
# Surgery windows of a Morse function

For a Morse function with finitely many critical points and pairwise distinct critical values,
`ManifoldMorse.SurgeryWindows E f` chooses surgery data at every critical point whose level
windows `[f p - ρ², f p + ρ²]` isolate `p` and are pairwise separated; they exist on a compact
manifold (`ManifoldMorse.nonempty_surgeryWindows`), and consecutive windows are related by a band
diffeomorphism (`ManifoldMorse.SurgeryWindows.exists_bandBridge`). `AdaptedWindows E f` adds a
smooth gradient-like field with its flow that agrees with the model descent field of each
chart near the handle (Milnor, *Lectures on the h-cobordism theorem*, §3–4).

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, §3-4.
* [milnor63] J. Milnor, *Morse Theory*, §3.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- A pair of surgery windows around a critical point, with lower and upper levels. -/
structure ManifoldMorse.SurgeryWindows (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) where
  /-- `f` has finitely many critical points. -/
  finite : (criticalPoints E f).Finite
  /-- Distinct critical points have distinct critical values. -/
  distinct : Set.InjOn f (criticalPoints E f)
  /-- The surgery data at each critical point. -/
  data : ∀ p : criticalPoints E f, MorseSurgeryData E f p.val
  /-- No critical point other than `p` has its value in the window `[f p - ρ ^ 2, f p + ρ ^ 2]`. -/
  isolated :
    ∀ (p : criticalPoints E f) (x : M),
      x ∈ criticalPoints E f →
        f x ∈ Set.Icc (f p - (data p).radius ^ 2) (f p + (data p).radius ^ 2) → x = p.val
  /-- If `f p < f q`, the window of `p` lies strictly below the window of `q`. -/
  separated :
    ∀ p q : criticalPoints E f, f p < f q → f p + (data p).radius ^ 2 < f q - (data q).radius ^ 2

/-- The lower level of the surgery windows. -/
def ManifoldMorse.SurgeryWindows.lower {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p : ManifoldMorse.criticalPoints E f) :
    ℝ :=
  f p - (S.data p).radius ^ 2

/-- The upper level of the surgery windows. -/
def ManifoldMorse.SurgeryWindows.upper {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p : ManifoldMorse.criticalPoints E f) :
    ℝ :=
  f p + (S.data p).radius ^ 2

/-- The lower level lies below the critical value. -/
theorem ManifoldMorse.SurgeryWindows.lower_lt_value {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p : ManifoldMorse.criticalPoints E f) :
    S.lower p < f p := by
  dsimp [ManifoldMorse.SurgeryWindows.lower]
  nlinarith [(S.data p).radius_pos]

/-- The critical value lies below the upper level. -/
theorem ManifoldMorse.SurgeryWindows.value_lt_upper {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p : ManifoldMorse.criticalPoints E f) :
    f p < S.upper p := by
  dsimp [ManifoldMorse.SurgeryWindows.upper]
  nlinarith [(S.data p).radius_pos]

/-- The upper window lies below the lower bound. -/
theorem ManifoldMorse.SurgeryWindows.upper_lt_lower {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p q : ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) : S.upper p < S.lower q :=
  S.separated p q hpq

/-- The band between the levels is regular. -/
theorem ManifoldMorse.SurgeryWindows.regular_between {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p q : ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    ∀ x, f x ∈ Set.Icc (S.upper p) (S.lower q) → x ∉ ManifoldMorse.criticalPoints E f := by
  intro x hx hcrit
  exact
    hconsecutive ⟨x, hcrit⟩
      ⟨(S.value_lt_upper p).trans_le hx.1, hx.2.trans_lt (S.lower_lt_value q)⟩

attribute [local instance 100] Classical.propDecidable in
/-- A band bridge between the windows exists. -/
theorem ManifoldMorse.SurgeryWindows.exists_bandBridge {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    letI := RegularLevel.chartedSpace hf (S.data p).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ b :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data p).UpperLevel (S.data q).LowerLevel ∞,
        D '' {x : M | f x ≤ S.upper p} = {x : M | f x ≤ S.lower q} ∧
          ∀ x : (S.data p).UpperLevel, (b x : M) = D x :=
  (S.data p).exists_smoothBandBridge (S.data q) hf (S.upper_lt_lower p q hpq).le
    (S.regular_between p q hconsecutive)

attribute [local instance 100] Classical.propDecidable in
/-- Surgery windows exist around a Morse critical point. -/
theorem ManifoldMorse.nonempty_surgeryWindows {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hinj : Set.InjOn f (criticalPoints E f)) :
    Nonempty (SurgeryWindows E f) := by
  obtain ⟨r, hr, hgap⟩ := exists_separated_value_radii (finite_criticalPoints hf hm) hinj
  have hex :
    ∀ p : criticalPoints E f,
      ∃ d : MorseSurgeryData E f p.val,
        d.radius < r p ∧
          ∀ x ∈ criticalPoints E f,
            f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val := by
    intro p
    exact
      exists_morseSurgeryData_lt hf hm p.property (fun x hx hfx => hinj hx p.property hfx) (hr p)
  choose d hd hisolated using hex
  refine
    ⟨{  finite := finite_criticalPoints hf hm
        distinct := hinj
        data := d
        isolated := hisolated
        separated := ?_ }⟩
  intro p q hpq
  have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hd p)) (add_pos (hr p) (d p).radius_pos)
    nlinarith
  have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hd q)) (add_pos (hr q) (d q).radius_pos)
    nlinarith
  linarith [hgap p q hpq]

attribute [local instance 100] Classical.propDecidable in
/-- Surgery windows adapted to a descent field. -/
structure AdaptedWindows (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (f : M → ℝ) extends
    ManifoldMorse.SurgeryWindows E f where
  field : (x : M) → TangentSpace 𝓘(ℝ, E) x
  flow : Flow ℝ M
  smooth :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, field x⟩ : TangentBundle 𝓘(ℝ, E) M))
  integral : ∀ x, IsMIntegralCurve (fun t => flow t x) field
  zero : ∀ x ∈ ManifoldMorse.criticalPoints E f, field x = 0
  descent : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (field x) < 0
  model_germ :
    ∀ (p : ManifoldMorse.criticalPoints E f) z,
      z ∈
          Metric.closedBall (0 : (data p).chart.NegativeCoordinates) (2 * (data p).radius) ×ˢ
            Metric.closedBall (0 : (data p).chart.PositiveCoordinates) (2 * (data p).radius) →
        ∀ᶠ y in 𝓝 ((data p).chart.splitChart.symm z), field y = (data p).chart.descentField y
