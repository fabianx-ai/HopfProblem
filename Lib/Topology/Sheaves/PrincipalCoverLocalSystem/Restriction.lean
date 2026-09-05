/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.OpenRestriction
public import Lib.Topology.Sheaves.PrincipalCoverLocalSystem.Trivialization

/-!
# Restricting principal-cover local systems to open subspaces

The inverse image of an open subspace under a principal cover is again a principal cover.  This
file packages its deck action and projection before comparing its associated local system with
literal open restriction of the original sheaf.
-/

@[expose] public section

noncomputable section

open CategoryTheory Filter Opposite Set TopologicalSpace Topology

namespace PrincipalCoverLocalSystem

variable {G E X : Type}
  [Group G] [TopologicalSpace E] [TopologicalSpace X]
  [MulAction G E]

/-- The inherited deck action on the inverse image of an open subspace. -/
@[instance_reducible]
def restrictedMulAction (p : E → X) (hp : IsQuotientCoveringMap p G) (U : Opens X) :
    MulAction G (LiftedOpen p U) where
  smul g e := liftedAction p hp U g e
  one_smul e := Subtype.ext (one_smul G e.1)
  mul_smul g h e := Subtype.ext (mul_smul g h e.1)

/-- The principal cover restricted over an open subspace. -/
def restrictedProjection (p : E → X) (U : Opens X) : LiftedOpen p U → U :=
  fun e ↦ ⟨p e.1, e.2⟩

omit [TopologicalSpace E] in
@[simp]
theorem restrictedProjection_apply (p : E → X) (U : Opens X) (e : LiftedOpen p U) :
    (restrictedProjection p U e : X) = p e.1 :=
  rfl

/-- `LiftedOpen` is the ordinary inverse-image subtype, with only its membership proof
repackaged. -/
def liftedOpenPreimageHomeomorph (p : E → X) (U : Opens X) :
    LiftedOpen p U ≃ₜ p ⁻¹' (U : Set X) where
  toFun e := ⟨e.1, e.2⟩
  invFun e := ⟨e.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- Restricting a principal cover to the inverse image of an open subspace preserves the
principal-cover structure. -/
theorem restrictedProjection_isQuotientCoveringMap (p : E → X)
    (hp : IsQuotientCoveringMap p G) (U : Opens X) :
    let _ := restrictedMulAction p hp U
    IsQuotientCoveringMap (restrictedProjection p U) G := by
  let _ := restrictedMulAction p hp U
  refine
    { toIsQuotientMap := ?_
      continuous_const_smul := ?_
      apply_eq_iff_mem_orbit := ?_
      disjoint := ?_ }
  · let h := liftedOpenPreimageHomeomorph p U
    have hcomp :
        (U : Set X).restrictPreimage p ∘ h = restrictedProjection p U := by
      funext e
      rfl
    rw [← hcomp]
    exact (hp.toIsQuotientMap.restrictPreimage_isOpen U.isOpen).comp h.isQuotientMap
  · intro g
    exact ((hp.continuous_const_smul g).comp continuous_subtype_val).subtype_mk _
  · intro e₁ e₂
    change (⟨p e₁.1, e₁.2⟩ : U) = ⟨p e₂.1, e₂.2⟩ ↔
      e₁ ∈ MulAction.orbit G e₂
    rw [Subtype.ext_iff]
    rw [hp.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, Subtype.ext hg⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  · intro e
    obtain ⟨D, hD, hdisj⟩ := hp.disjoint e.1
    let V : Set (LiftedOpen p U) := Subtype.val ⁻¹' D
    have hV : V ∈ nhds e := continuousAt_subtype_val hD
    refine ⟨V, hV, ?_⟩
    intro g hnonempty
    apply hdisj g
    obtain ⟨z, ⟨y, hyV, hgy⟩, hzV⟩ := hnonempty
    refine ⟨z.1, ⟨y.1, hyV, ?_⟩, hzV⟩
    exact congrArg Subtype.val hgy

end PrincipalCoverLocalSystem
