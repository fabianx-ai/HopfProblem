/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib.Topology.Homotopy.HomotopyGroup
/-!
# Postcomposition of generalized loops

A continuous map `f : C(X, Y)` sends a based loop `p : GenLoop N X x` to the based loop
`mapGenLoop f x p : GenLoop N Y (f x)`; this preserves the constant loop, homotopy, and the
concatenation `GenLoop.transAt`, so it induces the map `f_* : π_n(X, x) → π_n(Y, f x)` on
homotopy groups (Hatcher, §4.1).

## Main definitions

* `Hurewicz.DegreeTwo.mapGenLoop`, with `mapGenLoop_const`, `mapGenLoop_homotopic`,
  `mapGenLoop_transAt`.
-/

open Set Function Topology

noncomputable section

/-! ### Postcomposition of generalized loops -/

/-- Postcomposition of a generalized loop by a continuous map `f`. -/
def Hurewicz.DegreeTwo.mapGenLoop {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : C(GenLoop N X x, GenLoop N Y (f x))
    where
  toFun p := ⟨f.comp p.val, fun t ht => congrArg f (p.property t ht)⟩
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _

/-- `(mapGenLoop f x p).val = f.comp p.val`. -/
@[simp]
theorem Hurewicz.DegreeTwo.mapGenLoop_val {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop N X x) : (mapGenLoop f x p).val = f.comp p.val :=
  rfl

/-- `mapGenLoop` sends the constant loop to the constant loop. -/
@[simp]
theorem Hurewicz.DegreeTwo.mapGenLoop_const {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : mapGenLoop (N := N) f x GenLoop.const = GenLoop.const :=
  rfl

/-- `mapGenLoop` preserves loop homotopy. -/
theorem Hurewicz.DegreeTwo.mapGenLoop_homotopic {N X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (mapGenLoop f x p) (mapGenLoop f x q) :=
  h.comp_continuousMap f

/-- `mapGenLoop` commutes with `transAt` concatenation. -/
@[simp]
theorem Hurewicz.DegreeTwo.mapGenLoop_transAt {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq N] (f : C(X, Y)) (x : X) (i : N) (p q : GenLoop N X x) :
    mapGenLoop f x (GenLoop.transAt i p q) =
      GenLoop.transAt i (mapGenLoop f x p) (mapGenLoop f x q) := by
  apply GenLoop.ext
  intro t
  change f (if (t i : ℝ) ≤ 1 / 2 then _ else _) = if (t i : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> rfl
