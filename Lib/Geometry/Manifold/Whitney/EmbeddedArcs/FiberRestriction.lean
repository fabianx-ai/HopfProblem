/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib

/-!
# Restricting a fibre-preserving map to a subfibre

For continuous linear maps of fibres `i : U →L[ℝ] V` and `r : V →L[ℝ] U` with `r ∘ i = id`, the
induced inclusion `FiberRestriction.embed i : X × U →L[ℝ] X × V` and projection
`FiberRestriction.project r` satisfy `project r ∘ embed i = id`, and `embed i ∘ project r` is the
identity on points whose fibre coordinate lies in the range of `i`. A diffeomorphism of `X × V` preserving the fibre coordinate restricts to the subfibre
(`FiberRestriction.restrict`).

## Tags

product, fibre, restriction
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

/-- The inclusion `X × U → X × V` induced by a map of fibres. -/
def FiberRestriction.embed {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : U →L[ℝ] V) : (X × U) →L[ℝ] (X × V) :=
  (ContinuousLinearMap.id ℝ X).prodMap i

/-- The projection `X × V → X × U` induced by a map of fibres. -/
def FiberRestriction.project {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : V →L[ℝ] U) : (X × V) →L[ℝ] (X × U) :=
  (ContinuousLinearMap.id ℝ X).prodMap r

/-- Projecting after embedding is the identity when the fibre maps compose to the identity. -/
theorem FiberRestriction.project_embed {X U V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i)
    (z : X × U) : project r (embed i z) = z :=
  Prod.ext rfl (hi z.2)

/-- Embedding after projecting is the identity on points whose fibre coordinate is in the image of
the fibre inclusion. -/
theorem FiberRestriction.embed_project_of_normal {X U V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i) {z : X × V}
    {w : X × U} (hz : z.2 = i w.2) : embed i (project r z) = z := by
  apply Prod.ext
  · rfl
  · change i (r z.2) = z.2
    rw [hz, hi]

/-- The restriction to a subfibre of a diffeomorphism of `X × V` that preserves the fibre
coordinate. -/
def FiberRestriction.restrict {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i)
    (d : Diffeomorph 𝓘(ℝ, X × V) 𝓘(ℝ, X × V) (X × V) (X × V) ∞) (hnormal : ∀ z, (d z).2 = z.2) :
    Diffeomorph 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) (X × U) (X × U) ∞
    where
  toEquiv :=
    { toFun := fun z => project r (d (embed i z))
      invFun := fun z => project r (d.symm (embed i z))
      left_inv := by
        intro z
        have hfix := embed_project_of_normal i r hi (w := z) (hnormal (embed i z))
        change project r (d.symm (embed i (project r (d (embed i z))))) = z
        rw [hfix, d.symm_apply_apply, project_embed i r hi]
      right_inv := by
        intro z
        have hnormalInv : (d.symm (embed i z)).2 = i z.2 := by
          have he := hnormal (d.symm (embed i z))
          rw [d.apply_symm_apply] at he
          exact he.symm
        have hfix := embed_project_of_normal i r hi (w := z) hnormalInv
        change project r (d (embed i (project r (d.symm (embed i z))))) = z
        rw [hfix, d.apply_symm_apply, project_embed i r hi] }
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) ∞ (fun z => project r (d (embed i z)))
    exact (project r).contDiff.contMDiff.comp (d.contMDiff.comp (embed i).contDiff.contMDiff)
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) ∞ (fun z => project r (d.symm (embed i z)))
    exact (project r).contDiff.contMDiff.comp (d.symm.contMDiff.comp (embed i).contDiff.contMDiff)

end
