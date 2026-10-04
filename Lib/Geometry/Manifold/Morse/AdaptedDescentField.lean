/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Morse.CriticalPoints
public import Lib.Geometry.Manifold.Morse.DescentField
public import Lib.Geometry.Manifold.Morse.SignedMorseChart
public import Lib.Geometry.Manifold.Morse.SplitChart

/-!
# Descent fields adapted to Morse charts

In the split chart of a signed Morse chart, the model field `(u, v) ↦ (u, -v)`
(`MorseHandle.descent`) pulls back to `ManifoldMorse.SignedMorseChart.descentField`, which
vanishes at the critical point and satisfies
`df(descentField) = -2 (‖u‖² + ‖v‖²) < 0` elsewhere. On a compact manifold with a Morse function
these local fields glue to a global smooth descent field equal to the model field near every
critical point (`ManifoldMorse.exists_adaptedDescentField`), with the model field prescribed on
given disjoint closed patches (`MorseCancellation.exists_prescribed_morse_patch_field`): the
existence of gradient-like vector fields (Milnor, *Lectures on the h-cobordism theorem*,
Lemma 3.2 and §3).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- The descent field `−∇f` in split Morse coordinates. -/
def ManifoldMorse.SignedMorseChart.descentField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) : (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  FlowConstruction.partialChartField c.splitChart MorseHandle.descent

attribute [local instance 100] Classical.propDecidable in
/-- The descent field is smooth on the chart domain. -/
theorem ManifoldMorse.SignedMorseChart.contMDiffOn_descentField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) [CompleteSpace E]
    [IsManifold 𝓘(ℝ, E) ∞ M] :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, c.descentField x⟩ : TangentBundle 𝓘(ℝ, E) M)) c.splitChart.source :=
  FlowConstruction.contMDiffOn_partialChartField c.splitChart
    MorseHandle.contDiff_descent

attribute [local instance 100] Classical.propDecidable in
/-- The descent field vanishes at the critical point. -/
@[simp]
theorem ManifoldMorse.SignedMorseChart.descentField_center {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) : c.descentField p = 0 := by
  have hzero : MorseHandle.descent (c.splitChart p) = 0 := by
    rw [c.splitChart_center]
    simp [MorseHandle.descent]
  unfold descentField FlowConstruction.partialChartField
  rw [VectorField.mpullback_apply, hzero, map_zero, map_zero]

attribute [local instance 100] Classical.propDecidable in
/-- The descent field strictly decreases the function. -/
theorem ManifoldMorse.SignedMorseChart.mvfderiv_descentField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : x ∈ c.splitChart.source) :
    mvfderiv 𝓘(ℝ, E) f x (c.descentField x) =
      -2 * (‖(c.splitChart x).1‖ ^ 2 + ‖(c.splitChart x).2‖ ^ 2) := by
  rw [descentField, FlowConstruction.mvfderiv_partialChartField hf c.splitChart _ hx]
  have hcoord :
    (f ∘ c.splitChart.symm) =ᶠ[𝓝 (c.splitChart x)]
      (fun z => f p + MorseHandle.quadratic z) := by
    filter_upwards [c.splitChart.open_target.mem_nhds
        (c.splitChart.toOpenPartialHomeomorph.map_source hx)] with
      z hz
    change f (c.splitChart.symm z) = f p + (-‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
    rw [c.splitChart_inverse_equation hz]
    ring
  rw [hcoord.fderiv_eq, fderiv_const_add]
  exact MorseHandle.fderiv_quadratic_descent _

attribute [local instance 100] Classical.propDecidable in
/-- The descent field's derivative is negative off the critical point. -/
theorem ManifoldMorse.SignedMorseChart.mvfderiv_descentField_neg {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : x ∈ c.splitChart.source) (hxp : x ≠ p) :
    mvfderiv 𝓘(ℝ, E) f x (c.descentField x) < 0 := by
  have hcoord : c.splitChart x ≠ 0 := by
    intro h
    apply hxp
    exact
      c.splitChart.toOpenPartialHomeomorph.injOn hx c.splitChart_mem_source
        (h.trans c.splitChart_center.symm)
  rw [c.mvfderiv_descentField hf hx]
  simpa only [MorseHandle.fderiv_quadratic_descent] using
    MorseHandle.fderiv_quadratic_descent_neg hcoord

/-- An adapted descent field exists near a Morse critical point. -/
theorem ManifoldMorse.exists_adaptedDescentField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ criticalPoints E f, V x = 0) ∧
          (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
            ∀ p ∈ criticalPoints E f,
              ∃ c : SignedMorseChart (E := E) f p, ∀ᶠ x in 𝓝 p, V x = c.descentField x := by
  classical
  let S := criticalPoints E f
  have hS : S.Finite := finite_criticalPoints hf hm
  let : Fintype S := hS.fintype
  let c (p : S) : SignedMorseChart (E := E) f (p : M) :=
    Classical.choice (nonempty_signedMorseChart hf hm p.1 p.2)
  obtain ⟨U₀, hU₀, hdisj₀⟩ := hS.t2_separation
  let U (p : S) : Set M := U₀ p ∩ (c p).splitChart.source
  have hU (p : S) : IsOpen (U p) := (hU₀ p).2.inter (c p).splitChart.open_source
  have hpU (p : S) : (p : M) ∈ U p := ⟨(hU₀ p).1, (c p).splitChart_mem_source⟩
  have hdisj : Pairwise (fun p q : S => Disjoint (U p) (U q)) := by
    intro p q hpq
    exact
      (hdisj₀ p.2 q.2 (fun h => hpq (Subtype.ext h))).mono Set.inter_subset_left
        Set.inter_subset_left
  choose K hKnhds hKclosed hKU using
    (fun p : S => exists_mem_nhds_isClosed_subset ((hU p).mem_nhds (hpU p)))
  have hcover : criticalPoints E f ⊆ ⋃ p : S, K p := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, mem_of_mem_nhds (hKnhds ⟨p, hp⟩)⟩
  have hVloc (p : S) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, (c p).descentField x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U p) :=
    (c p).contMDiffOn_descentField.mono Set.inter_subset_right
  have hdesc (p : S) (x : M) (hx : x ∈ U p) (hreg : x ∉ criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) f x ((c p).descentField x) < 0 :=
    (c p).mvfderiv_descentField_neg hf hx.2 (fun h => hreg (h.symm ▸ p.2))
  obtain ⟨V, hV, hstrict, hmatch⟩ :=
    FlowConstruction.exists_gluedDescentField hf U K hU hKclosed hKU hdisj hcover
      (fun p => (c p).descentField) hVloc hdesc
  refine ⟨V, hV, ?_, hstrict, ?_⟩
  · intro p hp
    rw [hmatch ⟨p, hp⟩ p (mem_of_mem_nhds (hKnhds ⟨p, hp⟩))]
    exact (c ⟨p, hp⟩).descentField_center
  · intro p hp
    refine ⟨c ⟨p, hp⟩, ?_⟩
    filter_upwards [hKnhds ⟨p, hp⟩] with x hx
    exact hmatch ⟨p, hp⟩ x hx

/-- A descent field vanishing at a critical point is prescribed. -/
theorem MorseCancellation.morse_descentField_zero_at_critical {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ c.splitChart.source) (hcrit : x ∈ ManifoldMorse.criticalPoints E f) :
    c.descentField x = 0 := by
  by_cases hxp : x = p
  · subst x
    exact c.descentField_center
  · have hneg := c.mvfderiv_descentField_neg hf hx hxp
    have hc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0 := hcrit
    have hz : mvfderiv 𝓘(ℝ, E) f x (c.descentField x) = 0 := by
      unfold mvfderiv
      rw [hc]
      rfl
    rw [hz] at hneg
    exact False.elim (lt_irrefl (0 : ℝ) hneg)

/-- A prescribed Morse patch field exists near a critical point. -/
theorem MorseCancellation.exists_prescribed_morse_patch_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f) {ι : Type*}
    [Finite ι] (p : ι → M) (hp : ∀ i, p i ∈ ManifoldMorse.criticalPoints E f)
    (c : ∀ i, ManifoldMorse.SignedMorseChart (E := E) f (p i)) (K : ι → Set M)
    (hK : ∀ i, IsClosed (K i)) (hKchart : ∀ i, K i ⊆ (c i).splitChart.source)
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
          (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
            ∀ i x, x ∈ K i → V x = (c i).descentField x := by
  obtain ⟨V₀, hV₀, hzero₀, hdesc₀, -⟩ := ManifoldMorse.exists_adaptedDescentField hf hm
  apply
    exists_closed_patch_descent_field V₀ hV₀ hzero₀ hdesc₀ K (fun i => (c i).splitChart.source) hK
      (fun i => (c i).splitChart.open_source) hKchart hdisj (fun i => (c i).descentField)
      (fun i => (c i).contMDiffOn_descentField)
  · exact fun i x hx hc => morse_descentField_zero_at_critical (c i) hf hx hc
  · intro i x hx hreg
    exact (c i).mvfderiv_descentField_neg hf hx (fun h => hreg (h.symm ▸ hp i))
