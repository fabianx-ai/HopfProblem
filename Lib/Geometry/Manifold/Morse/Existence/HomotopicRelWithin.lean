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

/-!
# Homotopies relative to a subset that stay in a target set

`HomotopicRelWithin f g C K O` says that `f` and `g` are homotopic relative to `C` by a homotopy
that maps `K` into `O` at all times. It refines Mathlib's `ContinuousMap.HomotopicRel` by this
`MapsTo` constraint, which is what local smoothing in charts needs, and has the expected
reflexivity, transitivity and monotonicity properties.

## Main definitions and results

* `HomotopicRelWithin`, `HomotopicRelWithin.refl`, `HomotopicRelWithin.trans`,
  `HomotopicRelWithin.mono`, `HomotopicRelWithin.homotopicRel`

## Tags

homotopy, relative homotopy
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Homotopy relative to a subset -/

/-- Two maps are homotopic relative to a subset within a target. -/
def HomotopicRelWithin {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (C K : Set X) (O : Set Y) : Prop :=
  ∃ F : f.HomotopyRel g C, ∀ t : unitInterval, Set.MapsTo (fun x => F (t, x)) K O

/-- Relative homotopy is reflexive. -/
theorem HomotopicRelWithin.refl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} {O : Set Y} (f : C(X, Y)) (C : Set X) (hmaps : Set.MapsTo f K O) :
    HomotopicRelWithin f f C K O :=
  ⟨ContinuousMap.HomotopyRel.refl f C, fun _ => hmaps⟩

/-- A relative homotopy within the target is a relative homotopy. -/
theorem HomotopicRelWithin.homotopicRel {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} {C K : Set X} {O : Set Y}
    (H : HomotopicRelWithin f g C K O) : f.HomotopicRel g C := by
  obtain ⟨F, _⟩ := H
  exact ⟨F⟩

/-- The right map lands in the target. -/
theorem HomotopicRelWithin.mapsTo_right {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} {C K : Set X} {O : Set Y}
    (H : HomotopicRelWithin f g C K O) : Set.MapsTo g K O := by
  obtain ⟨F, hF⟩ := H
  intro x hx
  exact (congrArg (fun y => y ∈ O) (F.map_one_left x)).mp (hF 1 hx)

/-- Relative homotopy is transitive. -/
theorem HomotopicRelWithin.trans {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g h : C(X, Y)} {C K : Set X} {O : Set Y} (H : HomotopicRelWithin f g C K O)
    (G : HomotopicRelWithin g h C K O) : HomotopicRelWithin f h C K O := by
  obtain ⟨F, hF⟩ := H
  obtain ⟨G, hG⟩ := G
  refine ⟨ContinuousMap.HomotopyRel.trans F G, ?_⟩
  intro t x hx
  change (F.toHomotopy.trans G.toHomotopy) (t, x) ∈ O
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hF _ hx
  · exact hG _ hx

/-- Relative homotopy is monotone in the fixed set. -/
theorem HomotopicRelWithin.mono {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} {C K : Set X} {O : Set Y} (H : HomotopicRelWithin f g C K O)
    {D L : Set X} {P : Set Y} (hDC : D ⊆ C) (hLK : L ⊆ K) (hOP : O ⊆ P) :
    HomotopicRelWithin f g D L P := by
  obtain ⟨F, hF⟩ := H
  exact
    ⟨{ toHomotopy := F.toHomotopy, prop' := fun t x hx => F.eq_fst t (hDC hx) }, fun t x hx =>
      hOP (hF t (hLK hx))⟩
