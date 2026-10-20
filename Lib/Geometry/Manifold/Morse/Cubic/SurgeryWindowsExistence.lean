/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.Windows
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Existence of adapted surgery windows

A Morse function `f` on a compact Hausdorff manifold whose critical values are pairwise distinct
admits an `AdaptedWindows E f` package (`MorseCancellation.nonempty_adaptedSurgeryWindows`): Morse
surgery data of small radius around every critical point, with pairwise disjoint value windows, and a
complete gradient-like field which is the model descent field in every surgery block.  This is the
existence of a gradient-like vector field adapted to Morse charts, cf. Milnor, *Lectures on the
h-cobordism theorem*, §3.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- A smooth Morse function `f` on a compact Hausdorff manifold modelled on a finite-dimensional
space which is injective on its critical points admits adapted surgery windows: `Nonempty
(AdaptedWindows E f)`. -/
theorem MorseCancellation.nonempty_adaptedSurgeryWindows {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) :
    Nonempty (AdaptedWindows E f) := by
  have hfinite := ManifoldMorse.finite_criticalPoints hf hm
  let : Finite (ManifoldMorse.criticalPoints E f) := hfinite.to_subtype
  obtain ⟨r, hr, hgap⟩ := ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex :
    ∀ p : ManifoldMorse.criticalPoints E f,
      ∃ d : ManifoldMorse.MorseSurgeryData E f p.val,
        d.radius < r p / 3 ∧
          ∀ x ∈ ManifoldMorse.criticalPoints E f,
            f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val := by
    intro p
    exact
      ManifoldMorse.exists_morseSurgeryData_lt hf hm p.property
        (fun x hx hfx => hinj hx p.property hfx) (div_pos (hr p) (by norm_num))
  choose d hd hisolated using hex
  have hsq (p : ManifoldMorse.criticalPoints E f) : 9 * (d p).radius ^ 2 < (r p) ^ 2 := by
    have hsmall : 3 * (d p).radius < r p := by linarith [hd p]
    have hsum : 0 < r p + 3 * (d p).radius :=
      add_pos (hr p) (mul_pos (by norm_num) (d p).radius_pos)
    nlinarith [mul_pos (sub_pos.mpr hsmall) hsum]
  have hwide (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + 9 * (d p).radius ^ 2 < f q - 9 * (d q).radius ^ 2 := by
    linarith [hgap p q hpq, hsq p, hsq q]
  have hintervals :
    Pairwise
      (fun p q : ManifoldMorse.criticalPoints E f =>
        Disjoint (Set.Icc (f p - 9 * (d p).radius ^ 2) (f p + 9 * (d p).radius ^ 2))
          (Set.Icc (f q - 9 * (d q).radius ^ 2) (f q + 9 * (d q).radius ^ 2))) := by
    intro p q hpq
    have hne : f p ≠ f q := fun h => hpq (Subtype.ext (hinj p.property q.property h))
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · linarith [hwide p q hlt, hx.2, hy.1]
    · linarith [hwide q p hgt, hy.2, hx.1]
  obtain ⟨V, F, hV, hF, hzero, hdesc, hmodel⟩ :=
    exists_disjoint_surgery_block_field hf hm
      (fun p : ManifoldMorse.criticalPoints E f => p.val) (fun p => p.property)
      (fun p => (d p).chart) (fun p => (d p).radius) (fun p => (d p).radius_pos)
      (fun p => (d p).block) hintervals
  refine
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := ?_
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hmodel }⟩
  intro p q hpq
  nlinarith [hwide p q hpq, sq_nonneg (d p).radius, sq_nonneg (d q).radius]
