/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.FiniteClosedPushforward.Cohomology

/-!
# Native pullback on constant-sheaf cohomology

This file defines the contravariant map on Mathlib's Ext-defined sheaf cohomology associated to
a finite closed map.  The construction uses only the native constant-sheaf pushforward morphism
and the exact finite-closed pushforward comparison.

It deliberately makes no singular-cohomology comparison and no proper-base-change assertion.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace TopCat.ConstantSheafCohomology

variable {X Y : TopCat.{0}} [T2Space X]

/-- The native Ext-defined pullback on cohomology with constant coefficient group `A`, for a
closed map with finite fibres. -/
def pullback (f : X ⟶ Y) (hf : IsClosedMap f)
    (hfinite : ∀ y : Y, (f ⁻¹' ({y} : Set Y)).Finite)
    (A : AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGrpCat.of
        (CategoryTheory.Sheaf.H.{0} (TopCat.ConstantSheaf.sheaf Y A) n) ⟶
      AddCommGrpCat.of
        (CategoryTheory.Sheaf.H.{0} (TopCat.ConstantSheaf.sheaf X A) n) :=
  AddCommGrpCat.ofHom
    ((TopCat.FiniteClosedPushforward.cohomologyEquiv f hf hfinite
      (TopCat.ConstantSheaf.sheaf X A) n).toAddMonoidHom.comp
        (CategoryTheory.Sheaf.H.map (TopCat.ConstantSheaf.pushforwardHom A f) n))

/-- Applying the forward finite-pushforward comparison after native pullback recovers the
cohomology map induced by the constant-sheaf pushforward morphism. -/
@[reassoc]
theorem pullback_forward (f : X ⟶ Y) (hf : IsClosedMap f)
    (hfinite : ∀ y : Y, (f ⁻¹' ({y} : Set Y)).Finite)
    (A : AddCommGrpCat.{0}) (n : ℕ) :
    pullback f hf hfinite A n ≫
        AddCommGrpCat.ofHom
          (TopCat.FiniteClosedPushforward.cohomologyForward f hf hfinite
            (TopCat.ConstantSheaf.sheaf X A) n) =
      AddCommGrpCat.ofHom
        (CategoryTheory.Sheaf.H.map (TopCat.ConstantSheaf.pushforwardHom A f) n) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact TopCat.FiniteClosedPushforward.cohomologyForward_equiv f hf hfinite
    (TopCat.ConstantSheaf.sheaf X A) n
    (CategoryTheory.Sheaf.H.map (TopCat.ConstantSheaf.pushforwardHom A f) n x)

end TopCat.ConstantSheafCohomology
