/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.OpenRestriction.Cohomology
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# High-degree vanishing from a Mayer--Vietoris square

The long exact Mayer--Vietoris sequence shows that degree `n + 1` on the union vanishes if
degree `n` on the intersection and degree `n + 1` on both covering pieces vanish.  This file
packages that exact argument first for an arbitrary site-theoretic Mayer--Vietoris square and
then for ordinary Ext-defined cohomology on open subspaces.

The second form uses the canonical exact-open-restriction comparison, so its hypotheses and
conclusion are stated directly in terms of sheaf cohomology on the four topological spaces.

Reference: Bredon, *Sheaf Theory*, II.13 (the Mayer--Vietoris sequence in sheaf cohomology).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.GrothendieckTopology.MayerVietorisSquare

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

/-- If degree `n` vanishes on the intersection and degree `n + 1` vanishes on both pieces,
then degree `n + 1` vanishes on the union. -/
theorem cohomology_succ_subsingleton (n : ℕ)
    [Subsingleton (F.H' n S.X₁)]
    [Subsingleton (F.H' (n + 1) S.X₂)]
    [Subsingleton (F.H' (n + 1) S.X₃)] :
    Subsingleton (F.H' (n + 1) S.X₄) := by
  apply subsingleton_of_forall_eq 0
  intro x
  have hx : S.toBiprod F (n + 1) x = 0 := by
    let e := (AddCommGrpCat.biprodIsoProd
      (F.H' (n + 1) S.X₂) (F.H' (n + 1) S.X₃)).addCommGroupIsoToAddEquiv
    exact e.toEquiv.subsingleton_congr.mpr inferInstance |>.elim _ _
  have hexact := (S.sequence_exact F n (n + 1) rfl).exact 2 (by decide)
  rw [ShortComplex.ab_exact_iff] at hexact
  let y := (hexact x hx).choose
  have hy := (hexact x hx).choose_spec
  change ((F.H' n S.X₁ : AddCommGrpCat.{w}) : Type w) at y
  have hy₀ : y = 0 := by
    apply Subsingleton.elim
  exact hy.symm.trans ((congrArg _ hy₀).trans (map_zero _))

end CategoryTheory.GrothendieckTopology.MayerVietorisSquare

namespace TopCat.Sheaf.MayerVietoris

open TopologicalSpace

variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Topological form of Mayer--Vietoris vanishing, stated using ordinary sheaf cohomology on
the intersection, the two pieces, and their union. -/
theorem restrictedCohomology_succ_subsingleton (U V : Opens X) (n : ℕ)
    [Subsingleton (TopCat.Sheaf.OpenRestriction.restrictedCohomologyGroup
      (U ⊓ V) F n)]
    [Subsingleton (TopCat.Sheaf.OpenRestriction.restrictedCohomologyGroup
      U F (n + 1))]
    [Subsingleton (TopCat.Sheaf.OpenRestriction.restrictedCohomologyGroup
      V F (n + 1))] :
    Subsingleton (TopCat.Sheaf.OpenRestriction.restrictedCohomologyGroup
      (U ⊔ V) F (n + 1)) := by
  let S := Opens.mayerVietorisSquare U V
  let _ : Subsingleton (F.H' n (U ⊓ V)) :=
    (TopCat.Sheaf.OpenRestriction.cohomologyEquiv (U ⊓ V) F n).toEquiv
      |>.subsingleton_congr.mpr inferInstance
  let _ : Subsingleton (F.H' (n + 1) U) :=
    (TopCat.Sheaf.OpenRestriction.cohomologyEquiv U F (n + 1)).toEquiv
      |>.subsingleton_congr.mpr inferInstance
  let _ : Subsingleton (F.H' (n + 1) V) :=
    (TopCat.Sheaf.OpenRestriction.cohomologyEquiv V F (n + 1)).toEquiv
      |>.subsingleton_congr.mpr inferInstance
  let _ : Subsingleton (F.H' n S.X₁) := by
    change Subsingleton (F.H' n (U ⊓ V))
    infer_instance
  let _ : Subsingleton (F.H' (n + 1) S.X₂) := by
    change Subsingleton (F.H' (n + 1) U)
    infer_instance
  let _ : Subsingleton (F.H' (n + 1) S.X₃) := by
    change Subsingleton (F.H' (n + 1) V)
    infer_instance
  let h : Subsingleton (F.H' (n + 1) (U ⊔ V)) :=
    ((S.cohomology_succ_subsingleton F n) : Subsingleton (F.H' (n + 1) S.X₄))
  exact (TopCat.Sheaf.OpenRestriction.cohomologyEquiv (U ⊔ V) F (n + 1)).toEquiv
    |>.subsingleton_congr.mp h

end TopCat.Sheaf.MayerVietoris

end
