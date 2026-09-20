/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.ConstantPushforward
public import Lib.Topology.Sheaves.PrincipalCoverLocalSystem.Comparison

/-!
# Trivializing a principal-cover local system along a section

A continuous section of a principal covering chooses an origin in every fibre.  The unique deck
transformation from that origin to a lifted point is locally constant, and hence transports
locally constant coefficient values to equivariant locally constant sections.  This identifies
the associated local system with the native constant sheaf on the base.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Set TopologicalSpace Topology

namespace PrincipalCoverLocalSystem

variable {G E X M : Type}
  [Group G] [TopologicalSpace E] [TopologicalSpace X]
  [MulAction G E] [AddCommGroup M] [DistribMulAction G M]

/-- The unique deck element carrying the chosen section value to a point in its fibre. -/
def sectionCoordinate (p : E → X) (hp : IsQuotientCoveringMap p G)
    (s : C(X, E)) (hs : ∀ x, p (s x) = x) (e : E) : G :=
  hp.fiberEquivGroup
    (⟨s (p e), hs (p e)⟩ : p ⁻¹' {p e})
    (⟨e, rfl⟩ : p ⁻¹' {p e})

@[simp]
theorem sectionCoordinate_smul_section (p : E → X) (hp : IsQuotientCoveringMap p G)
    (s : C(X, E)) (hs : ∀ x, p (s x) = x) (e : E) :
    sectionCoordinate p hp s hs e • s (p e) = e :=
  hp.fiberEquivGroup_smul_self
    (⟨s (p e), hs (p e)⟩ : p ⁻¹' {p e})

@[simp]
theorem sectionCoordinate_smul (p : E → X) (hp : IsQuotientCoveringMap p G)
    (s : C(X, E)) (hs : ∀ x, p (s x) = x) (g : G) (e : E) :
    sectionCoordinate p hp s hs (g • e) = g * sectionCoordinate p hp s hs e := by
  apply (hp.fiberEquivGroup_eq_iff _ _ _).mpr
  simp only [hp.map_smul, mul_smul, sectionCoordinate_smul_section]

/-- The deck coordinate supplied by a continuous section is locally constant on the total
space of the cover. -/
theorem sectionCoordinate_isLocallyConstant (p : E → X)
    (hp : IsQuotientCoveringMap p G) (s : C(X, E)) (hs : ∀ x, p (s x) = x) :
    IsLocallyConstant (sectionCoordinate p hp s hs) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro e₀
  obtain ⟨D, hD, hdisj⟩ := hp.disjoint e₀
  let O : Set E := interior D
  have hO : IsOpen O := isOpen_interior
  have he₀O : e₀ ∈ O := mem_interior_iff_mem_nhds.mpr hD
  let g₀ : G := sectionCoordinate p hp s hs e₀
  let q : E → E := fun e ↦ g₀ • s (p e)
  have hq : Continuous q :=
    (hp.continuous_const_smul g₀).comp (s.continuous.comp hp.continuous)
  let V : Set E := O ∩ q ⁻¹' O
  refine ⟨V, hO.inter (hO.preimage hq), ⟨he₀O, ?_⟩, ?_⟩
  · change g₀ • s (p e₀) ∈ O
    rw [show g₀ = sectionCoordinate p hp s hs e₀ from rfl,
      sectionCoordinate_smul_section]
    exact he₀O
  · intro e heV
    let h : G := sectionCoordinate p hp s hs e
    let c : E := g₀ • s (p e)
    have hcO : c ∈ O := heV.2
    have heO : e ∈ O := heV.1
    have hnonempty : (((h * g₀⁻¹) • ·) '' D ∩ D).Nonempty := by
      refine ⟨e, ⟨c, interior_subset hcO, ?_⟩, interior_subset heO⟩
      change (h * g₀⁻¹) • (g₀ • s (p e)) = e
      rw [mul_smul, inv_smul_smul]
      exact sectionCoordinate_smul_section p hp s hs e
    have hh : h * g₀⁻¹ = 1 := hdisj (h * g₀⁻¹) hnonempty
    exact (mul_inv_eq_one.mp hh).trans rfl

set_option maxHeartbeats 1000000 in
/-- Stalkwise descent data identifying the constant sheaf with the local system trivialized by
the chosen section. -/
def constantComparisonData (p : E → X) (hp : IsQuotientCoveringMap p G)
    (s : C(X, E)) (hs : ∀ x, p (s x) = x) :
    StalkComparisonData (M := M) p hp
      (TopCat.ConstantSheaf.sheaf (TopCat.of X) (AddCommGrpCat.of M)) where
  stalkMap e :=
    (TopCat.ConstantSheaf.stalkIso (TopCat.of X) (AddCommGrpCat.of M) (p e)).hom ≫
      AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom M (sectionCoordinate p hp s hs e))
  section_isLocallyConstant U a := by
    change IsLocallyConstant fun e : LiftedOpen p U ↦
      sectionCoordinate p hp s hs e.1 •
        TopCat.ConstantSheaf.sectionValue (X := TopCat.of X)
          (A := AddCommGrpCat.of M) U a ⟨p e.1, e.2⟩
    have hcoordinate : IsLocallyConstant fun e : LiftedOpen p U ↦
        sectionCoordinate p hp s hs e.1 :=
      (sectionCoordinate_isLocallyConstant p hp s hs).comp_continuous continuous_subtype_val
    have hvalue : IsLocallyConstant fun e : LiftedOpen p U ↦
        TopCat.ConstantSheaf.sectionValue (X := TopCat.of X)
          (A := AddCommGrpCat.of M) U a ⟨p e.1, e.2⟩ :=
      (TopCat.ConstantSheaf.sectionValue_isLocallyConstant
        (X := TopCat.of X) (A := AddCommGrpCat.of M) U a).comp_continuous
        ((hp.continuous.comp continuous_subtype_val).subtype_mk _)
    exact hcoordinate.comp₂ hvalue (fun g m ↦ g • m)
  section_equivariant U a g e := by
    change sectionCoordinate p hp s hs (g • e.1) •
        TopCat.ConstantSheaf.sectionValue (X := TopCat.of X)
          (A := AddCommGrpCat.of M) U a
          ⟨p (g • e.1), by simpa only [hp.map_smul] using e.2⟩ =
      g • (sectionCoordinate p hp s hs e.1 •
        TopCat.ConstantSheaf.sectionValue (X := TopCat.of X)
          (A := AddCommGrpCat.of M) U a ⟨p e.1, e.2⟩)
    rw [sectionCoordinate_smul, mul_smul]
    apply congrArg (fun m : M ↦ g • (sectionCoordinate p hp s hs e.1 • m))
    apply congrArg (TopCat.ConstantSheaf.sectionValue
      (X := TopCat.of X) (A := AddCommGrpCat.of M) U a)
    apply Subtype.ext
    exact hp.map_smul g

/-- The constant-sheaf morphism determined by a section of the principal cover. -/
def constantSheafHomOfSection (p : E → X) (hp : IsQuotientCoveringMap p G)
    (s : C(X, E)) (hs : ∀ x, p (s x) = x) :
    TopCat.ConstantSheaf.sheaf (TopCat.of X) (AddCommGrpCat.of M) ⟶
      sheaf (M := M) p hp :=
  (constantComparisonData (M := M) p hp s hs).hom

theorem constantComparisonData_stalkMap_isIso (p : E → X)
    (hp : IsQuotientCoveringMap p G) (s : C(X, E)) (hs : ∀ x, p (s x) = x)
    (e : E) : IsIso ((constantComparisonData (M := M) p hp s hs).stalkMap e) := by
  let actionHom : AddCommGrpCat.of M ⟶ AddCommGrpCat.of M :=
    AddCommGrpCat.ofHom
      (DistribSMul.toAddMonoidHom M (sectionCoordinate p hp s hs e))
  let actionIso : IsIso actionHom := (ConcreteCategory.isIso_iff_bijective actionHom).mpr
    (DistribMulAction.toAddEquiv M (sectionCoordinate p hp s hs e)).bijective
  change IsIso
    ((TopCat.ConstantSheaf.stalkIso (TopCat.of X) (AddCommGrpCat.of M) (p e)).hom ≫
      actionHom)
  exact IsIso.comp_isIso' inferInstance actionIso

/-- A section of the principal cover makes its associated local system a constant sheaf. -/
theorem constantSheafHomOfSection_isIso (p : E → X)
    (hp : IsQuotientCoveringMap p G) (s : C(X, E)) (hs : ∀ x, p (s x) = x) :
    IsIso (constantSheafHomOfSection (M := M) p hp s hs) := by
  let _ : ∀ e : E, IsIso ((constantComparisonData (M := M) p hp s hs).stalkMap e) :=
    fun e ↦ constantComparisonData_stalkMap_isIso p hp s hs e
  exact (constantComparisonData (M := M) p hp s hs).hom_isIso

/-- The constant-sheaf isomorphism determined by a section of the principal cover. -/
def constantSheafIsoOfSection (p : E → X) (hp : IsQuotientCoveringMap p G)
    (s : C(X, E)) (hs : ∀ x, p (s x) = x) :
    TopCat.ConstantSheaf.sheaf (TopCat.of X) (AddCommGrpCat.of M) ≅
      sheaf (M := M) p hp := by
  letI := constantSheafHomOfSection_isIso (M := M) p hp s hs
  exact asIso (constantSheafHomOfSection (M := M) p hp s hs)

end PrincipalCoverLocalSystem
