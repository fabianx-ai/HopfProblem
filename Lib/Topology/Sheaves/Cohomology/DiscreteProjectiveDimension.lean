/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.RepresentedOpenProjectiveDimension
public import Lib.Topology.Sheaves.H1Vanishing.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sheaf cohomological dimension of discrete spaces

On a discrete space, sections extend across inclusions one point at a time and are glued over the
singleton cover.  Hence every additive sheaf is flasque, every represented-open sheaf is
projective, and in particular the integral unit sheaf has projective dimension zero.

A sheaf on a discrete space is the product of its stalks; see Bredon, *Sheaf Theory*, I.1.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf.OpenRestriction

section Discrete

variable {X : TopCat.{u}}

private def pointOpen [DiscreteTopology X] (x : X) : Opens X :=
  ⟨{x}, isOpen_discrete {x}⟩

private theorem pointOpen_mem [DiscreteTopology X] (x : X) : x ∈ pointOpen x := by
  simp [pointOpen]

private theorem pointOpen_le [DiscreteTopology X] {U : Opens X} (x : U) :
    pointOpen x.1 ≤ U := by
  intro y hy
  have hyx : y = x.1 := by simpa [pointOpen] using hy
  exact hyx.symm ▸ x.2

/-- Every additive sheaf on a discrete space is flasque. -/
instance sheaf_isFlasque_of_discreteTopology [DiscreteTopology X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) : F.IsFlasque where
  epi {U V} i := by
    classical
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    let W : U.unop → Opens X := fun x => pointOpen x.1
    have hWU (x : U.unop) : W x ≤ U.unop := pointOpen_le x
    have hcover : U.unop ≤ iSup W := by
      intro x hx
      rw [Opens.mem_iSup]
      exact ⟨⟨x, hx⟩, pointOpen_mem x⟩
    let sf : ∀ x : U.unop, F.presheaf.obj (op (W x)) := fun x =>
      if hx : x.1 ∈ V.unop then
        F.presheaf.map (homOfLE (show W x ≤ V.unop by
          intro y hy
          have hyx : y = x.1 := by simpa [W, pointOpen] using hy
          exact hyx.symm ▸ hx)).op s
      else 0
    have hcompatible : TopCat.Presheaf.IsCompatible F.presheaf W sf := by
      intro x y
      by_cases hxy : x = y
      · subst y
        rfl
      · apply TopCat.Presheaf.section_ext F (W x ⊓ W y) _ _
        intro z hz
        have hzx : z = x.1 := by simpa [W, pointOpen] using hz.1
        have hzy : z = y.1 := by simpa [W, pointOpen] using hz.2
        exact (hxy (Subtype.ext (hzx.symm.trans hzy))).elim
    obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' W U.unop
      (fun x => homOfLE (hWU x)) hcover sf hcompatible
    refine ⟨t, ?_⟩
    apply TopCat.Presheaf.section_ext F V.unop _ _
    intro x hx
    let xu : U.unop := ⟨x, i.unop.le hx⟩
    have hxW : x ∈ W xu := pointOpen_mem x
    rw [F.presheaf.germ_res_apply' i]
    rw [← F.presheaf.germ_res_apply (homOfLE (hWU xu)) x hxW t]
    rw [ht xu]
    have hxuV : xu.1 ∈ V.unop := hx
    simp only [sf, dif_pos hxuV]
    exact F.presheaf.germ_res_apply
      (homOfLE (show W xu ≤ V.unop by
        intro y hy
        have hyx : y = xu.1 := by simpa [W, pointOpen] using hy
        exact hyx.symm ▸ hx)) x hxW s

end Discrete

variable {X : TopCat.{0}}

/-- The sheaf represented by any open of a discrete space is projective. -/
instance freeOpen_projective_of_discreteTopology [DiscreteTopology X] (U : Opens X) :
    Projective (freeOpen U) := by
  apply projective_iff_hasProjectiveDimensionLT_one.mpr
  apply (freeOpen_hasProjectiveDimensionLT_iff X U 1).mpr
  intro F
  change Subsingleton (CategoryTheory.Sheaf.H ((restriction U).obj F) 1)
  exact TopCat.SheafH1.subsingleton_h1_of_isFlasque ((restriction U).obj F)

/-- The integral unit sheaf on a discrete space is projective. -/
instance integralSheaf_projective_of_discreteTopology [DiscreteTopology X] :
    Projective (TopCat.ConstantSheaf.integralSheaf X) :=
  Projective.of_iso (integralSheafFreeTopIso X).symm inferInstance

end TopCat.Sheaf.OpenRestriction
