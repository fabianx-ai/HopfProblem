/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.WhitneyEmbedding

/-!
# Adapted windows with a prescribed gradient-like flow

A gradient-like vector field `V` for a Morse function `f` on a compact manifold which agrees near
every critical point with the descent field of a signed Morse chart determines an
`AdaptedWindows E f` package whose field and flow are `V` and its flow
(`MorseCancellation.exists_adapted_windows_with_prescribed_flow`), with surgery radii below any
prescribed bound (`exists_adapted_windows_with_prescribed_flow_lt`).  The construction is local:
`exists_morseSurgeryData_of_field_germ_lt` builds the surgery datum at one critical point.
A signed Morse chart survives replacing `f` by a function with the same germ, or the germ
shifted by a constant (`exists_signed_morse_chart_of_germ_preserving_field`,
`exists_signed_morse_chart_of_shift_germ_preserving_field`).
Cf. Milnor, *Lectures on the h-cobordism theorem*, §3 (gradient-like vector fields).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- Let `f` be smooth on a compact manifold with finitely many critical points, `V` a smooth
vector field with flow `F` vanishing exactly at the critical points and strictly decreasing `f`
elsewhere, `c` a signed Morse chart at `p` with `V = c.descentField` near `p`, and `p` the only
critical point at its value.  Then for every `ε > 0` there is a Morse surgery datum `d` at `p`
with chart `c`, radius `< ε`, no other critical value in `[f p - r², f p + r²]`, and
`V = c.descentField` near the whole model block of radius `2r`. -/
theorem MorseCancellation.exists_morseSurgeryData_of_field_germ_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hunique : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x = f p → x = p)
    (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ManifoldMorse.MorseSurgeryData E f p,
      d.radius < ε ∧
        d.chart = c ∧
          (∀ x ∈ ManifoldMorse.criticalPoints E f,
              f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p) ∧
            ∀ z,
              z ∈
                  Metric.closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
                    Metric.closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) →
                ∀ᶠ x in 𝓝 (d.chart.splitChart.symm z), V x = d.chart.descentField x := by
  obtain ⟨ρ, hρ, hρε, W, hW, -, heqW, hblockW, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock_lt hfinite hunique V heq hε
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hmodel :
    ∀ z,
      z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) →
        ∀ᶠ x in 𝓝 (c.splitChart.symm z), V x = c.descentField x := by
    intro z hz
    filter_upwards [hW.mem_nhds (hblockW hz).2] with x hx
    exact heqW x hx
  have hagreement :
    ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    exact hmodel _ (MorseHandle.modelMap_mem_product hρ z)
  obtain ⟨e, hfront, hfixed, horbit⟩ :=
    c.exists_attachingUnionHomeomorph_with_level_and_orbits hf hV hzero hdesc F hF ρ hρ hblock
      hagreement hband
  have hregular (b : ℝ) (hb : b ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p) (x : M)
    (hx : f x = b) : x ∉ ManifoldMorse.criticalPoints E f := by
    intro hcrit
    exact hne (hx.symm.trans (congrArg f (hband x hcrit (hx ▸ hb))))
  have hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f :=
    hregular _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f :=
    hregular _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f p - ρ ^ 2 := by
    intro x hx t ht
    have hh :=
      FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp)) F hF hzero hdesc
        (hlower x hx) ht
    simpa only [F.map_zero_apply, hx] using hh
  have hlevel :=
    FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F
      (FlowConstruction.antitone_flow_height hf F hF hzero hdesc) hbottom
  have horbits :=
    c.followsModelBoundaryOrbits_of_flow (hV.of_le (by simp)) F hF ρ hρ hblock (e := e) (horbit :=
      horbit) hmodel
  exact
    ⟨{  radius := ρ
        radius_pos := hρ
        chart := c
        block := hblock
        attachmentHomeomorph := e
        attachment_frontier := hfront
        attachment_fixed := hfixed
        attachment_model_orbits := horbits
        surgery := c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e hfront
        oldExterior_eq := fun _ => rfl
        newExterior_eq := fun _ => rfl
        oldPiece_eq := fun _ => rfl
        newPiece_eq := fun _ => rfl
        belt_eq := c.beltSphere_eq_beltCoreMap hf.continuous ρ hρ hblock hlevel e hfront hfixed
        lower_regular := hlower
        upper_regular := hupper }, hρε, rfl, hband, hmodel⟩

attribute [local instance 100] Classical.propDecidable in
/-- Let `f` be a Morse function with distinct critical values on a compact manifold and `V` a
smooth vector field with flow `F` that vanishes exactly at the critical points, strictly
decreases `f` elsewhere, and agrees near each critical point `p` with the descent field of a
given signed Morse chart `c p`.  Then there is an `AdaptedWindows E f` package `S` with
`S.field = V`, `S.flow = F` and `(S.data p).chart = c p` for every `p`. -/
theorem MorseCancellation.exists_adapted_windows_with_prescribed_flow {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (c :
      ∀ p : ManifoldMorse.criticalPoints E f,
        ManifoldMorse.SignedMorseChart (E := E) f p.val)
    (hmodel :
      ∀ p : ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 p.val, V x = (c p).descentField x) :
    ∃ S : AdaptedWindows E f, S.field = V ∧ S.flow = F ∧ ∀ p, (S.data p).chart = c p := by
  have hfinite := ManifoldMorse.finite_criticalPoints hf hm
  obtain ⟨r, hr, hgap⟩ := ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex (p : ManifoldMorse.criticalPoints E f) :=
    exists_morseSurgeryData_of_field_germ_lt hf hfinite hV F hF hzero hdesc (c p)
      (fun x hx hfx => hinj hx p.property hfx) (hmodel p) (hr p)
  choose d hd hchart hisolated hgerm using hex
  have hseparated (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + (d p).radius ^ 2 < f q - (d q).radius ^ 2 := by
    have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hd p)) (add_pos (hr p) (d p).radius_pos)]
    have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hd q)) (add_pos (hr q) (d q).radius_pos)]
    linarith [hgap p q hpq]
  exact
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := hseparated
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hgerm }, rfl, rfl, hchart⟩

attribute [local instance 100] Classical.propDecidable in
/-- `exists_adapted_windows_with_prescribed_flow` with the surgery radii below a prescribed bound:
given `ε p > 0` for every critical point, the package also satisfies `(S.data p).radius < ε p`. -/
theorem MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f))
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (c :
      ∀ p : ManifoldMorse.criticalPoints E f,
        ManifoldMorse.SignedMorseChart (E := E) f p.val)
    (hmodel :
      ∀ p : ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 p.val, V x = (c p).descentField x)
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    ∃ S : AdaptedWindows E f,
      S.field = V ∧ S.flow = F ∧ (∀ p, (S.data p).chart = c p) ∧ ∀ p, (S.data p).radius < ε p := by
  have hfinite := ManifoldMorse.finite_criticalPoints hf hm
  obtain ⟨r, hr, hgap⟩ := ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex (p : ManifoldMorse.criticalPoints E f) :=
    exists_morseSurgeryData_of_field_germ_lt hf hfinite hV F hF hzero hdesc (c p)
      (fun x hx hfx => hinj hx p.property hfx) (hmodel p) (lt_min (hr p) (hε p))
  choose d hd hchart hisolated hgerm using hex
  have hdr (p : ManifoldMorse.criticalPoints E f) : (d p).radius < r p :=
    (hd p).trans_le (min_le_left _ _)
  have hde (p : ManifoldMorse.criticalPoints E f) : (d p).radius < ε p :=
    (hd p).trans_le (min_le_right _ _)
  have hseparated (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + (d p).radius ^ 2 < f q - (d q).radius ^ 2 := by
    have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hdr p)) (add_pos (hr p) (d p).radius_pos)]
    have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hdr q)) (add_pos (hr q) (d q).radius_pos)]
    linarith [hgap p q hpq]
  exact
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := hseparated
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hgerm }, rfl, rfl, hchart, hde⟩

/-- If `g = f` on a neighbourhood of `p` and `c` is a signed Morse chart of `f` at `p`, then `g`
has a signed Morse chart at `p` with the same descent field as `c`. -/
theorem MorseCancellation.exists_signed_morse_chart_of_germ_preserving_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hgerm : g =ᶠ[𝓝 p] f) :
    ∃ d : ManifoldMorse.SignedMorseChart (E := E) g p, d.descentField = c.descentField := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgerm
  let d : ManifoldMorse.SignedMorseChart (E := E) g p :=
    { weights := c.weights
      signs := c.signs
      chart := PartialChart.restrictSource c.chart hU
      mem_source := ⟨c.mem_source, hpU⟩
      center := c.center
      equation := by
        intro x hx
        have hxs : x ∈ c.chart.source ∩ U := hx
        have hxeq : g x = f x := hUsub hxs.2
        change g x = g p + ∑ i, c.weights i * (c.chart x i) ^ 2
        rw [hxeq, hgerm.self_of_nhds]
        exact c.equation x hxs.1
      inverse_equation := by
        intro z hz
        have hzs : z ∈ c.chart.target ∩ c.chart.symm ⁻¹' U := hz
        have hzeq : g (c.chart.symm z) = f (c.chart.symm z) := hUsub hzs.2
        change g (c.chart.symm z) = g p + ∑ i, c.weights i * z i ^ 2
        rw [hzeq, hgerm.self_of_nhds]
        exact c.inverse_equation z hzs.1 }
  exact ⟨d, rfl⟩

/-- If `g = f + k` on a neighbourhood of `p` for a constant `k` and `c` is a signed Morse chart of
`f` at `p`, then `g` has a signed Morse chart at `p` with the same descent field as `c`. -/
theorem MorseCancellation.exists_signed_morse_chart_of_shift_germ_preserving_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    ∃ d : ManifoldMorse.SignedMorseChart (E := E) g p, d.descentField = c.descentField := by
  obtain ⟨d, hd⟩ :=
    exists_signed_morse_chart_of_germ_preserving_field (shiftedSignedMorseChart c k) hgerm
  exact ⟨d, hd⟩

end
