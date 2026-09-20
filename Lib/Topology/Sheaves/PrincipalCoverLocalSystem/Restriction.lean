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

/-! ## Lifted opens and equivariant sections -/

/-- The canonical point of `U` below a point lifted over the direct image of an open of `U`. -/
def restrictedBasePoint (p : E → X) (U : Opens X) (V : Opens U)
    (e : LiftedOpen p ((TopCat.Sheaf.OpenRestriction.openImage
      (X := TopCat.of X) U).obj V)) : U :=
  ⟨p e.1, TopCat.Sheaf.OpenRestriction.openImage_obj_le
    (X := TopCat.of X) U V e.2⟩

omit [TopologicalSpace E] in
theorem restrictedBasePoint_mem (p : E → X) (U : Opens X) (V : Opens U)
    (e : LiftedOpen p ((TopCat.Sheaf.OpenRestriction.openImage
      (X := TopCat.of X) U).obj V)) :
    restrictedBasePoint p U V e ∈ V := by
  obtain ⟨x, hx, hxe⟩ := e.2
  have h : x = restrictedBasePoint p U V e := Subtype.ext hxe
  exact h ▸ hx

/-- A lifted open for the restricted cover is canonically the lifted direct-image open for the
ambient cover. -/
def restrictionLiftedOpenHomeomorph (p : E → X) (U : Opens X) (V : Opens U) :
    LiftedOpen (restrictedProjection p U) V ≃ₜ
      LiftedOpen p ((TopCat.Sheaf.OpenRestriction.openImage
        (X := TopCat.of X) U).obj V) where
  toFun e :=
    ⟨e.1.1, ⟨restrictedProjection p U e.1, e.2, rfl⟩⟩
  invFun e :=
    ⟨⟨e.1, (restrictedBasePoint p U V e).2⟩, restrictedBasePoint_mem p U V e⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The lifted-open homeomorphism intertwines the restricted and ambient deck actions. -/
theorem restrictionLiftedOpenHomeomorph_liftedAction
    (p : E → X) (hp : IsQuotientCoveringMap p G) (U : Opens X) (V : Opens U)
    (g : G) (e : LiftedOpen (restrictedProjection p U) V) :
    let _ := restrictedMulAction p hp U
    let hpU := restrictedProjection_isQuotientCoveringMap p hp U
    restrictionLiftedOpenHomeomorph p U V
        (liftedAction (restrictedProjection p U) hpU V g e) =
      liftedAction p hp ((TopCat.Sheaf.OpenRestriction.openImage
        (X := TopCat.of X) U).obj V) g
        (restrictionLiftedOpenHomeomorph p U V e) := by
  let _ := restrictedMulAction p hp U
  let hpU := restrictedProjection_isQuotientCoveringMap p hp U
  apply Subtype.ext
  rfl

omit [Group G] [MulAction G E] in
/-- The value of a section over `U` lies in the inverse image of `U`. -/
theorem restrictedCoverSection_mem (p : E → X) (U : Opens X) (s : C(U, E))
    (hs : ∀ x, p (s x) = x.1) (x : U) : p (s x) ∈ U := by
  rw [hs x]
  exact x.2

omit [Group G] [MulAction G E] in
/-- A section of the ambient cover over `U`, regarded as a section of the restricted cover. -/
def restrictedCoverSection (p : E → X) (U : Opens X) (s : C(U, E))
    (hs : ∀ x, p (s x) = x.1) : C(U, LiftedOpen p U) where
  toFun x := ⟨s x, restrictedCoverSection_mem p U s hs x⟩
  continuous_toFun := s.continuous.subtype_mk
    (restrictedCoverSection_mem p U s hs)

omit [Group G] [MulAction G E] in
@[simp]
theorem restrictedProjection_restrictedCoverSection (p : E → X) (U : Opens X)
    (s : C(U, E)) (hs : ∀ x, p (s x) = x.1) (x : U) :
    restrictedProjection p U (restrictedCoverSection p U s hs x) = x := by
  apply Subtype.ext
  exact hs x

variable {E' X' M : Type} [TopologicalSpace E'] [TopologicalSpace X'] [MulAction G E']
  [AddCommGroup M] [DistribMulAction G M]

/-- An equivariant homeomorphism of lifted opens transports equivariant locally constant
sections. -/
def equivariantSectionsEquivOfHomeomorph (p : E → X) (hp : IsQuotientCoveringMap p G)
    (U : Opens X) (q : E' → X') (hq : IsQuotientCoveringMap q G) (V : Opens X')
    (e : LiftedOpen p U ≃ₜ LiftedOpen q V)
    (he : ∀ (g : G) (z : LiftedOpen p U),
      e (liftedAction p hp U g z) = liftedAction q hq V g (e z)) :
    equivariantSections (M := M) p hp U ≃+
      equivariantSections (M := M) q hq V where
  toFun a :=
    ⟨LocallyConstant.comap ⟨e.symm, e.symm.continuous⟩ a.1, by
      intro g z
      change a.1 (e.symm (liftedAction q hq V g z)) = g • a.1 (e.symm z)
      have hinv : e.symm (liftedAction q hq V g z) =
          liftedAction p hp U g (e.symm z) := by
        apply e.injective
        rw [e.apply_symm_apply, he, e.apply_symm_apply]
      rw [hinv, a.2]⟩
  invFun a :=
    ⟨LocallyConstant.comap ⟨e, e.continuous⟩ a.1, by
      intro g z
      change a.1 (e (liftedAction p hp U g z)) = g • a.1 (e z)
      rw [he, a.2]⟩
  left_inv a := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro z
    exact congrArg a.1 (e.symm_apply_apply z)
  right_inv a := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro z
    exact congrArg a.1 (e.apply_symm_apply z)
  map_add' a b := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro z
    rfl

/-- Sections of the local system of the restricted cover are the literal restrictions of
ambient local-system sections. -/
def restrictionSectionsEquiv (p : E → X) (hp : IsQuotientCoveringMap p G)
    (U : Opens X) (V : Opens U) :
    let _ := restrictedMulAction p hp U
    let hpU := restrictedProjection_isQuotientCoveringMap p hp U
    equivariantSections (M := M) (restrictedProjection p U) hpU V ≃+
      equivariantSections (M := M) p hp
        ((TopCat.Sheaf.OpenRestriction.openImage (X := TopCat.of X) U).obj V) := by
  let _ := restrictedMulAction p hp U
  let hpU := restrictedProjection_isQuotientCoveringMap p hp U
  exact equivariantSectionsEquivOfHomeomorph
    (M := M) (restrictedProjection p U) hpU V p hp
      ((TopCat.Sheaf.OpenRestriction.openImage (X := TopCat.of X) U).obj V)
      (restrictionLiftedOpenHomeomorph p U V)
      (restrictionLiftedOpenHomeomorph_liftedAction p hp U V)

/-! ## Restriction of the associated sheaf -/

/-- The local system associated to the principal cover restricted over `U`. -/
def restrictedSheaf (p : E → X) (hp : IsQuotientCoveringMap p G) (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of U) := by
  let _ := restrictedMulAction p hp U
  exact sheaf (M := M) (restrictedProjection p U)
    (restrictedProjection_isQuotientCoveringMap p hp U)

set_option backward.isDefEq.respectTransparency false in
/-- The associated-sheaf construction commutes with restriction to an open subspace. -/
def restrictionPresheafIso (p : E → X) (hp : IsQuotientCoveringMap p G) (U : Opens X) :
    (restrictedSheaf (M := M) p hp U).presheaf ≅
      ((TopCat.Sheaf.OpenRestriction.restriction (X := TopCat.of X) U).obj
        (sheaf (M := M) p hp)).presheaf := by
  let _ := restrictedMulAction p hp U
  let hpU := restrictedProjection_isQuotientCoveringMap p hp U
  change presheaf (M := M) (restrictedProjection p U) hpU ≅
    (TopCat.Sheaf.OpenRestriction.openImage (X := TopCat.of X) U).op ⋙
      presheaf (M := M) p hp
  exact NatIso.ofComponents
    (fun V ↦ (restrictionSectionsEquiv (M := M) p hp U V.unop).toAddCommGrpIso)
    (fun {V W} i ↦ by
      ext a
      apply Subtype.ext
      apply LocallyConstant.ext
      intro e
      rfl)

/-- Literal open restriction of a principal-cover local system is the local system of the
restricted principal cover. -/
def restrictionSheafIso (p : E → X) (hp : IsQuotientCoveringMap p G) (U : Opens X) :
    restrictedSheaf (M := M) p hp U ≅
      (TopCat.Sheaf.OpenRestriction.restriction (X := TopCat.of X) U).obj
        (sheaf (M := M) p hp) :=
  ObjectProperty.isoMk _ (restrictionPresheafIso (M := M) p hp U)

/-- A continuous section over an open subspace identifies literal restriction of the associated
local system with the native constant sheaf on that subspace. -/
def constantSheafRestrictionIsoOfSection (p : E → X)
    (hp : IsQuotientCoveringMap p G) (U : Opens X) (s : C(U, E))
    (hs : ∀ x, p (s x) = x.1) :
    TopCat.ConstantSheaf.sheaf (TopCat.of U) (AddCommGrpCat.of M) ≅
      (TopCat.Sheaf.OpenRestriction.restriction (X := TopCat.of X) U).obj
        (sheaf (M := M) p hp) := by
  let _ := restrictedMulAction p hp U
  let hpU := restrictedProjection_isQuotientCoveringMap p hp U
  let sU := restrictedCoverSection p U s hs
  exact constantSheafIsoOfSection (M := M) (restrictedProjection p U) hpU sU
      (restrictedProjection_restrictedCoverSection p U s hs) ≪≫
    restrictionSheafIso (M := M) p hp U

end PrincipalCoverLocalSystem
