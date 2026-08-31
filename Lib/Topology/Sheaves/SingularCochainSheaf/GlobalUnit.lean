/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalResolutionH1

/-!
# The global singular-cochain sheafification unit

This is the literal map from native singular cochains on a space to global sections of the
sheafified native cochain presheaf.  It is only a structural comparison here: no quasi-isomorphism
claim is made in this module.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- A native global cochain followed by restriction to the top open and sheafification. -/
def globalCochainUnit (n : ℕ) :
    (AlgebraicTopology.SingularCochains.complex X A).X n ⟶
      (sheaf X A n).obj.obj (op ⊤) :=
  (AlgebraicTopology.SingularCochains.pullback A
    (⟨Subtype.val, continuous_subtype_val⟩ : C((⊤ : Opens X), X))).f n ≫
    (unit X A n).app (op ⊤)

/-- The global unit is a map of the actual native cochain complexes. -/
def globalCochainComparison :
    AlgebraicTopology.SingularCochains.complex X A ⟶ globalCochainComplex X A where
  f n := globalCochainUnit X A n
  comm' i j _ := by
    let f : C((⊤ : Opens X), X) := ⟨Subtype.val, continuous_subtype_val⟩
    change ((AlgebraicTopology.SingularCochains.pullback A f).f i ≫
        (unit X A i).app (op ⊤)) ≫
          (sheafDifferential X A i j).hom.app (op ⊤) =
      ((AlgebraicTopology.SingularCochains.complex X A).d i j ≫
        (AlgebraicTopology.SingularCochains.pullback A f).f j) ≫
          (unit X A j).app (op ⊤)
    calc
      _ = (AlgebraicTopology.SingularCochains.pullback A f).f i ≫
          ((unit X A i).app (op ⊤) ≫
            (sheafDifferential X A i j).hom.app (op ⊤)) := Category.assoc _ _ _
      _ = (AlgebraicTopology.SingularCochains.pullback A f).f i ≫
          ((differential X A i j).app (op ⊤) ≫ (unit X A j).app (op ⊤)) :=
        congrArg (fun k => (AlgebraicTopology.SingularCochains.pullback A f).f i ≫ k)
          (NatTrans.congr_app (unit_d X A i j) (op ⊤))
      _ = ((AlgebraicTopology.SingularCochains.pullback A f).f i ≫
          (AlgebraicTopology.SingularCochains.complex (⊤ : Opens X) A).d i j) ≫
            (unit X A j).app (op ⊤) := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun k => k ≫ (unit X A j).app (op ⊤))
        ((AlgebraicTopology.SingularCochains.pullback A f).comm i j)

@[simp]
theorem globalCochainComparison_f (n : ℕ) :
    (globalCochainComparison X A).f n = globalCochainUnit X A n := rfl

end TopCat.SingularCochainSheaf
