/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Category.Grp.Images
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Order.WithBotTop

/-!
# The total filtration of an abelian spectral object

For a spectral object indexed by the extended integers, the maps from lower truncation intervals
`[⊥,q]` to the total interval `[⊥,⊤]` induce an increasing filtration on the underlying
additive group of the total object.  This file constructs that filtration as the ranges of those
maps and proves its bottom, top, and monotonicity properties.

This is one ingredient of convergence, not a complete convergence theorem.  In particular, this
file does not identify the successive quotients with stable spectral-sequence pages.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable (X : SpectralObject AddCommGrpCat EInt) (n : ℤ)

/-- The map from the part of a spectral object below `q` to its total interval. -/
def totalFiltrationMap (q : EInt) :
    (X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ q))) ⟶
      (X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) :=
  (X.H n).map (homMk₁ (𝟙 _) (homOfLE le_top))

/-- The transition map between two lower truncation levels. -/
def totalFiltrationTransition {q q' : EInt} (h : q ≤ q') :
    (X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ q))) ⟶
      (X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ q'))) :=
  (X.H n).map (homMk₁ (𝟙 _) (homOfLE h))

/-- A lower-to-total map factors through every larger lower truncation level. -/
@[reassoc]
lemma totalFiltrationTransition_comp {q q' : EInt} (h : q ≤ q') :
    X.totalFiltrationTransition n h ≫ X.totalFiltrationMap n q' =
      X.totalFiltrationMap n q := by
  dsimp [totalFiltrationTransition, totalFiltrationMap]
  rw [← Functor.map_comp]
  congr 1

/-- The filtration subgroup at `q` is the range of the map from the interval `[⊥,q]` into the
total interval. -/
def totalFiltration (q : EInt) :
    AddSubgroup ((X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) :=
  AddMonoidHom.range (X.totalFiltrationMap n q).hom

/-- The total filtration is increasing in the truncation level. -/
lemma totalFiltration_mono : Monotone (X.totalFiltration n) := by
  intro q q' h x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(X.totalFiltrationTransition n h).hom y, ?_⟩
  simpa only [ConcreteCategory.comp_apply] using
    congrArg (fun φ => φ.hom y) (X.totalFiltrationTransition_comp n h)

/-- The bottom level of the total filtration is trivial. -/
lemma totalFiltration_bot : X.totalFiltration n ⊥ = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    have hy : y = 0 :=
      (AddCommGrpCat.subsingleton_of_isZero
        (show IsZero ((X.H n).obj
            (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊥)))) from by
          simpa using X.isZero_H_map_mk₁_of_isIso n (𝟙 (⊥ : EInt)))).elim _ _
    simp [hy]
  · exact bot_le

/-- The top level of the total filtration is the whole total group. -/
lemma totalFiltration_top : X.totalFiltration n ⊤ = ⊤ := by
  rw [totalFiltration, AddMonoidHom.range_eq_top]
  intro x
  refine ⟨x, ?_⟩
  have hmap : X.totalFiltrationMap n ⊤ = 𝟙 _ := by
    unfold totalFiltrationMap
    rw [show homMk₁ (𝟙 _) (homOfLE le_top) = 𝟙 _ by
      apply hom_ext₁ <;> apply Subsingleton.elim]
    apply Functor.map_id
  rw [hmap]
  rfl

end CategoryTheory.Abelian.SpectralObject
