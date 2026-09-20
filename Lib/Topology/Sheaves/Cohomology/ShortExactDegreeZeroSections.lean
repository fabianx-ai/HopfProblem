/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.ShortExactDegreeOne

/-!
# Global sections of the subobject in a short exact sheaf sequence

For `0 ⟶ F ⟶ G ⟶ Q ⟶ 0`, left exactness identifies `F(X)` with the kernel of
`G(X) ⟶ Q(X)`. This file packages that familiar degree-zero statement as an additive
equivalence, with the forward map characterized by the literal sheaf morphism on the top open.

This is the left exactness of the global-sections functor (Hartshorne, *Algebraic Geometry*,
II Ex. 1.8; Godement, *Topologie algébrique et théorie des faisceaux*, II.2), combined with the
standard identification of sheaf `H⁰` with global sections.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.SheafCohomology

variable {X : TopCat.{0}}

/-- The abelian group of global sections of a sheaf, as a type: the value of `F` on the top
open. -/
abbrev GlobalSections (F : TopCat.Sheaf AddCommGrpCat.{0} X) :=
  (F.obj.obj (op (⊤ : Opens X)) : Type)

/-- The additive map on global sections induced by a morphism of sheaves. -/
def topSectionsMap {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) :
    GlobalSections F →+ GlobalSections G :=
  (f.hom.app (op (⊤ : Opens X))).hom

/-- In a short exact sheaf sequence, global sections of the subobject are canonically the
kernel of the literal quotient map on global sections. -/
def globalSectionsSubobjectEquivKer
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.ShortExact) :
    GlobalSections S.X₁ ≃+ (topSectionsMap S.g).ker := by
  let P :=
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift.{0} ℤ))
  let eExt : CategoryTheory.Sheaf.H.{0} S.X₁ 0 ≃+
      (CategoryTheory.Sheaf.H.map.{0} S.g 0).ker :=
    CategoryTheory.Abelian.Ext.extZeroEquivKerPostcompG P hS
  let eSections : (CategoryTheory.Sheaf.H.map.{0} S.g 0).ker ≃+
      (topSectionsMap S.g).ker := {
    toFun x := ⟨CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop x.1, by
      change topSectionsMap S.g
        (CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop x.1) = 0
      rw [topSectionsMap,
        CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop S.g x.1,
        x.2]
      simp⟩
    invFun s := ⟨(CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop).symm s.1, by
      apply (CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).injective
      rw [← CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop S.g]
      simp only [AddEquiv.apply_symm_apply, AddEquiv.map_zero]
      exact s.2⟩
    left_inv x := by
      apply Subtype.ext
      exact (CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop).symm_apply_apply x.1
    right_inv s := by
      apply Subtype.ext
      exact (CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop).apply_symm_apply s.1
    map_add' x y := by
      apply Subtype.ext
      exact map_add _ _ _
  }
  exact (CategoryTheory.Sheaf.H.equiv₀ S.X₁ isTerminalTop).symm.trans
    (eExt.trans eSections)

/-- The equivalence of `globalSectionsSubobjectEquivKer` is given by the sheaf morphism `S.f`
evaluated on the top open. -/
@[simp]
theorem globalSectionsSubobjectEquivKer_apply_val
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.ShortExact) (s : GlobalSections S.X₁) :
    (globalSectionsSubobjectEquivKer hS s).1 =
      S.f.hom.app (op (⊤ : Opens X)) s := by
  let P : TopCat.Sheaf AddCommGrpCat.{0} X :=
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift.{0} ℤ))
  change CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop
      ((CategoryTheory.Abelian.Ext.extZeroEquivKerPostcompG
        P hS)
        ((CategoryTheory.Sheaf.H.equiv₀ S.X₁ isTerminalTop).symm s)).1 = _
  rw [CategoryTheory.Abelian.Ext.extZeroEquivKerPostcompG_apply
    (C := TopCat.Sheaf AddCommGrpCat.{0} X) P hS
    ((CategoryTheory.Sheaf.H.equiv₀ S.X₁ isTerminalTop).symm s)]
  change CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop
      (CategoryTheory.Sheaf.H.map S.f 0
        ((CategoryTheory.Sheaf.H.equiv₀ S.X₁ isTerminalTop).symm s)) = _
  simpa using
    (CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop S.f
      ((CategoryTheory.Sheaf.H.equiv₀ S.X₁ isTerminalTop).symm s)).symm

end TopCat.SheafCohomology

end
