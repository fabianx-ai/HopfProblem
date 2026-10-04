/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.ImageComplement
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.NewInterior
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.OpenHomotopyExtension
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.ZeroAvoidanceCutoff
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.RegularLevel

/-!
# Loops after a surgery

Simple connectivity across a surgery whose attaching sphere has positive dimension, stated with
"every loop `S¹ → X` is homotopic to a constant". For a surgery boundary pair with attaching
sphere of dimension `n` and level of dimension `> n + 2`:

* the complement of the belt sphere in the new level inherits the property from the old level
  (`SurgeryBoundaryPair.beltComplement_circle_nullhomotopies_of_sphere_dimension`; general
  position, `Lib.Geometry.Manifold.Morse.SurgeryWindows.ImageComplement`);
* every loop in the new level can be homotoped off the belt sphere when the belt has
  codimension `> 1` (`SurgeryBoundaryPair.exists_belt_avoiding_circle`), so the new level
  inherits the property (`SurgeryBoundaryPair.newBoundary_circle_nullhomotopies`).

The `ManifoldMorse.SignedMorseChart` versions specialise to the surgery of a level of a Morse
function at a critical point. Cf. Milnor, *Lectures on the h-cobordism theorem*, §3 (surgery).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

/-- If every loop in the old level `X` is nullhomotopic, the attaching sphere is a smooth `n`-sphere
  and `2 + n < dim X`, every loop in the new complement is nullhomotopic. -/
theorem SurgeryBoundaryPair.beltComplement_circle_nullhomotopies_of_sphere_dimension
    {F R X Y G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X] {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)]
    (d : SurgeryBoundaryPair N F R X Y) (hattach : ContMDiff (𝓡 n) J ∞ d.attachingSphere)
    (hdim : 2 + n < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  have hold :
    ∀ f : C(Hemisphere.Sphere 1, d.OldComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
    apply ImageComplement.circle_nullhomotopies d.attachingSphere hattach _ hnull
    simpa only [finrank_euclideanSpace_fin] using hdim
  intro f
  let e := d.complementHomeomorph
  let forward : C(d.OldComplement, d.NewComplement) := ⟨e, e.continuous⟩
  let backward : C(d.NewComplement, d.OldComplement) := ⟨e.symm, e.symm.continuous⟩
  let f₀ : C(Hemisphere.Sphere 1, d.OldComplement) := backward.comp f
  obtain ⟨c, hc⟩ := hold f₀
  have heq : forward.comp f₀ = f := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (f x)
  have hout : (forward.comp f₀).Homotopic (ContinuousMap.const _ (e c)) :=
    (ContinuousMap.Homotopic.refl forward).comp hc
  exact ⟨e c, heq ▸ hout⟩

/-- The case `n = 1` (`finrank N = 2`, `3 < dim X`) of
  `beltComplement_circle_nullhomotopies_of_sphere_dimension`. -/
theorem SurgeryBoundaryPair.beltComplement_circle_nullhomotopies_of_finrank_two
    {F R X Y G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X] {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] [Fact (Module.finrank ℝ N = 1 + 1)]
    (d : SurgeryBoundaryPair N F R X Y) (hattach : ContMDiff (𝓡 1) J ∞ d.attachingSphere)
    (hdim : 3 < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) :=
  d.beltComplement_circle_nullhomotopies_of_sphere_dimension 1 hattach hdim hnull

attribute [local instance 100] Classical.propDecidable in
/-- If the old piece of `d` is the chart's norm handle map, the attaching sphere of `d` is the
  chart's attaching core map. -/
theorem ManifoldMorse.SignedMorseChart.attachingSphere_eq_attachingCoreMap {E M R Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (d :
      SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (PuncturedHandle.sphereToBall z.1, z.2)) :
    d.attachingSphere = c.attachingCoreMap ρ hρ hblock := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change (d.oldPiece (u, PuncturedHandle.ballZero) : M) = _
  rw [hpiece]
  rfl

attribute [local instance 100] Classical.propDecidable in
/-- The surgery attaching sphere map is smooth. -/
theorem ManifoldMorse.SignedMorseChart.contMDiff_surgeryAttachingSphere {E M R Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f)
    (d :
      SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (PuncturedHandle.sphereToBall z.1, z.2)) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.attachingSphere := by
  let _ := RegularLevel.chartedSpace hf hreg
  rw [c.attachingSphere_eq_attachingCoreMap ρ hρ hblock d hpiece]
  exact c.contMDiff_attachingCoreMap n hf ρ hρ hblock hreg

attribute [local instance 100] Classical.propDecidable in
/-- For a surgery of index 2 (`finrank c.NegativeCoordinates = 2`, `4 < dim E`) on a regular level
  in which every loop is nullhomotopic, every loop in the new complement is nullhomotopic. -/
theorem ManifoldMorse.SignedMorseChart.surgery_beltComplement_circle_nullhomotopies
    {E M R Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f)
    (d :
      SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (PuncturedHandle.sphereToBall z.1, z.2))
    (hindex : Module.finrank ℝ c.NegativeCoordinates = 2) (hdim : 4 < Module.finrank ℝ E)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = f p - ρ ^ 2 }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let _ : Fact (Module.finrank ℝ c.NegativeCoordinates = 1 + 1) := ⟨hindex⟩
  have hattach := c.contMDiff_surgeryAttachingSphere 1 hf ρ hρ hblock hreg d hpiece
  apply d.beltComplement_circle_nullhomotopies_of_finrank_two hattach _ hnull
  rw [finrank_euclideanSpace_fin]
  omega

/-- If `1 < finrank N`, every loop in `Y` is homotopic to a loop that misses the belt sphere. -/
theorem SurgeryBoundaryPair.exists_belt_avoiding_circle {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup P]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) (hdim : 1 < Module.finrank ℝ N)
    (g : C(Hemisphere.Sphere 1, Y)) :
    ∃ g' : C(Hemisphere.Sphere 1, Y),
      (∀ x, g' x ∉ Set.range d.beltSphere) ∧ g.Homotopic g' := by
  let U : TopologicalSpace.Opens (Hemisphere.Sphere 1) :=
    ⟨g ⁻¹' d.NewInterior, d.isOpen_newInterior.preimage g.continuous⟩
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let e := d.newInteriorHomeomorph
  let coord : C(U, PuncturedHandle.OpenUnitBall N × PuncturedHandle.UnitSphere P) :=
    ⟨fun x => e.symm ⟨g x, x.property⟩,
      e.symm.continuous.comp ((g.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  let normal : C(U, N) := ⟨fun x => (coord x).1, continuous_subtype_val.comp coord.continuous.fst⟩
  have hparam (x : U) : d.newPiece (⟨(coord x).1, (coord x).1.property.le⟩, (coord x).2) = g x :=
    congrArg (fun y : d.NewInterior => (y : Y)) (e.apply_symm_apply ⟨g x, x.property⟩)
  obtain ⟨q, hq, G, hclose⟩ :=
    exists_nonzero_homotopy_small (I := 𝓡 1) normal (1 / 8) (by norm_num)
      (by simpa only [finrank_euclideanSpace_fin] using hdim)
  have hnorm (t) (x : U) : ‖G (t, x)‖ < 1 := by
    by_cases hx : 1 / 4 ≤ ‖normal x‖
    · rw [G.eq_fst t
          (show x ∈ {x | 2 * (1 / 8 : ℝ) ≤ ‖normal x‖} from
            by
            change 2 * (1 / 8 : ℝ) ≤ ‖normal x‖
            linarith)]
      exact (coord x).1.property
    · have hdist : ‖G (t, x) - normal x‖ < 1 / 8 := by simpa only [dist_eq_norm] using hclose t x
      have hbound := norm_add_le (G (t, x) - normal x) (normal x)
      rw [sub_add_cancel] at hbound
      linarith
  let H : C(unitInterval × U, Y) :=
    ⟨fun z => (e (⟨G z, hnorm z.1 z.2⟩, (coord z.2).2) : Y),
      continuous_subtype_val.comp
        (e.continuous.comp
          ((G.continuous.subtype_mk _).prodMk (coord.continuous.snd.comp continuous_snd)))⟩
  have hreturn (t) (x : U) (hx : G (t, x) = normal x) : H (t, x) = g x := by
    have hu : (⟨G (t, x), hnorm t x⟩ : PuncturedHandle.OpenUnitBall N) = (coord x).1 :=
      Subtype.ext hx
    change (e (⟨G (t, x), _⟩, (coord x).2) : Y) = _
    rw [hu]
    exact hparam x
  have hzero (x : U) : H (0, x) = g x := hreturn 0 x (G.apply_zero x)
  let K₀ : Set Y :=
    d.newPiece ''
      {p : PuncturedHandle.UnitBall N × PuncturedHandle.UnitSphere P |
        ‖(p.1 : N)‖ ≤ 1 / 2}
  have hK₀ : IsClosed K₀ :=
    d.newPiece_closed.isClosedMap _
      (isClosed_le (continuous_subtype_val.comp continuous_fst).norm continuous_const)
  have hK₀U : K₀ ⊆ d.NewInterior := by
    rintro _ ⟨p, hp, rfl⟩
    apply (d.newPiece_mem_newInterior_iff p).mpr
    exact hp.trans_lt (by norm_num)
  let K : Set (Hemisphere.Sphere 1) := g ⁻¹' K₀
  have hK : IsClosed K := hK₀.preimage g.continuous
  have hKU : K ⊆ U := fun _ hx => hK₀U hx
  have hfixed (t) (x : U) (hx : (x : Hemisphere.Sphere 1) ∉ K) : H (t, x) = g x := by
    have hlarge : 1 / 2 < ‖normal x‖ := by
      by_contra! hh
      apply hx
      exact ⟨(⟨(coord x).1, (coord x).1.property.le⟩, (coord x).2), hh, hparam x⟩
    have hsafe : x ∈ {x | 2 * (1 / 8 : ℝ) ≤ ‖normal x‖} := by
      change 2 * (1 / 8 : ℝ) ≤ ‖normal x‖
      linarith
    exact hreturn t x (G.eq_fst t hsafe)
  obtain ⟨g', G', hlocal, houtside⟩ :=
    OpenHomotopyExtension.exists_extended_homotopy U g H hK hKU hzero hfixed
  refine ⟨g', ?_, ⟨G'⟩⟩
  intro x hxB
  by_cases hx : x ∈ U
  · have heq : g' x = H (1, ⟨x, hx⟩) := (G'.apply_one x).symm.trans (hlocal 1 ⟨x, hx⟩)
    rw [heq] at hxB
    have hzero' : G (1, ⟨x, hx⟩) = 0 := (d.newInteriorHomeomorph_mem_belt_iff _).mp hxB
    rw [G.apply_one] at hzero'
    exact hq ⟨x, hx⟩ hzero'
  · have heq : g' x = g x := (G'.apply_one x).symm.trans (houtside 1 x (fun h => hx (hKU h)))
    rw [heq] at hxB
    obtain ⟨v, hv⟩ := hxB
    apply hx
    change g x ∈ d.NewInterior
    rw [← hv]
    exact d.beltSphere_mem_newInterior v

/-- If `1 < finrank N` and every loop in the new complement is nullhomotopic, every loop in `Y` is
  nullhomotopic. -/
theorem SurgeryBoundaryPair.circle_nullhomotopies_of_beltComplement {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup P]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) (hdim : 1 < Module.finrank ℝ N)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, d.NewComplement),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, Y), ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  intro g
  obtain ⟨g', havoid, hgg'⟩ := d.exists_belt_avoiding_circle hdim g
  let g₀ : C(Hemisphere.Sphere 1, d.NewComplement) :=
    ⟨fun x => ⟨g' x, havoid x⟩, g'.continuous.subtype_mk _⟩
  let inc : C(d.NewComplement, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨q, hq⟩ := hnull g₀
  have hh : (inc.comp g₀).Homotopic (ContinuousMap.const _ (q : Y)) :=
    (ContinuousMap.Homotopic.refl inc).comp hq
  exact ⟨q, hgg'.trans hh⟩

/-- If every loop in the old level `X` is nullhomotopic, the attaching sphere is a smooth
  `n`-sphere, `0 < n` and `2 + n < dim X`, every loop in the new level `Y` is nullhomotopic. -/
theorem SurgeryBoundaryPair.newBoundary_circle_nullhomotopies {N F R X Y G H : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace R]
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X]
    (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)] (hn : 0 < n)
    (d : SurgeryBoundaryPair N F R X Y) (hattach : ContMDiff (𝓡 n) J ∞ d.attachingSphere)
    (hdim : 2 + n < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, Y), ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  have hnormal : 1 < Module.finrank ℝ N := by
    rw [show Module.finrank ℝ N = n + 1 from Fact.out]
    omega
  exact
    d.circle_nullhomotopies_of_beltComplement hnormal
      (d.beltComplement_circle_nullhomotopies_of_sphere_dimension n hattach hdim hnull)

attribute [local instance 100] Classical.propDecidable in
/-- For a surgery of index `n + 1` with `0 < n` and `3 + n < dim E` on a regular level in which
  every loop is nullhomotopic, every loop in the new level `Y` is nullhomotopic. -/
theorem ManifoldMorse.SignedMorseChart.surgery_newBoundary_circle_nullhomotopies
    {E M R Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (hn : 0 < n)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f)
    (d :
      SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (PuncturedHandle.sphereToBall z.1, z.2))
    (hdim : 3 + n < Module.finrank ℝ E)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = f p - ρ ^ 2 }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, Y), ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  have hattach := c.contMDiff_surgeryAttachingSphere n hf ρ hρ hblock hreg d hpiece
  apply d.newBoundary_circle_nullhomotopies n hn hattach _ hnull
  rw [finrank_euclideanSpace_fin]
  omega

