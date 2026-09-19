/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Explicit based contraction in a convex set

A loop in a convex subset of a real normed space contracts to its basepoint
by the affine interpolation `(1 - u) • p(t) + u • z`. Convexity keeps the
interpolation in the subset, and continuity of the ambient affine homotopy
lifts to the subspace topology. At homotopy times zero and one the formula
gives the original loop and the constant loop. Both path endpoints remain
at the same basepoint throughout, since interpolating the basepoint with
itself is constant. No completeness or finite-dimensionality is required.
-/

@[expose] public section
universe u
open scoped unitInterval
namespace Convex

/-- Contract a loop in a convex set by affine interpolation to its basepoint,
keeping both endpoints fixed. Convexity supplies range membership, the ambient
affine homotopy supplies continuity, and the path endpoint identities make
the interpolation constant at both endpoints. -/
noncomputable def basedLoopContraction
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : _root_.Convex ℝ S) {z : S} (p : Path z z) :
    p.Homotopy (Path.refl z) := by
  let f : C(unitInterval, E) :=
    ⟨fun t => (p t : E), continuous_subtype_val.comp p.continuous⟩
  let A := ContinuousMap.Homotopy.affine f (ContinuousMap.const unitInterval (z : E))
  have hr (q : unitInterval × unitInterval) : A q ∈ S :=
    hS.lineMap_mem (p q.2).property z.property q.1.property
  refine
    { toFun := fun q => ⟨A q, hr q⟩
      continuous_toFun := A.continuous.subtype_mk hr
      map_zero_left := fun t => Subtype.ext (A.map_zero_left t)
      map_one_left := fun t => Subtype.ext (A.map_one_left t)
      prop' := ?_ }
  intro s t ht
  apply Subtype.ext
  change AffineMap.lineMap (p t : E) (z : E) (s : ℝ) = (p t : E)
  rcases ht with rfl | rfl <;> simp

/-- The contraction evaluates to the specified convex combination as an
underlying vector. This follows from the affine line-map evaluation formula. -/
theorem basedLoopContraction_apply
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : _root_.Convex ℝ S) {z : S} (p : Path z z)
    (u t : unitInterval) :
    ((basedLoopContraction hS p (u, t) : S) : E) =
      (1 - (u : ℝ)) • (p t : E) + (u : ℝ) • (z : E) := by
  change AffineMap.lineMap (p t : E) (z : E) (u : ℝ) = _
  exact AffineMap.lineMap_apply_module _ _ _

end Convex
