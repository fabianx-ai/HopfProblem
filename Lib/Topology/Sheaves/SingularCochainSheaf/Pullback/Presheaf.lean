/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.Augmentation
public import Mathlib.Topology.Sheaves.Functors

/-!
# Functoriality of the singular-cochain presheaf in the space

A continuous map `f : X → Y` restricts over every open `U ⊆ Y` to a map `f⁻¹U → U`, and pullback
of singular cochains along those restrictions assembles to a map of presheaves
`S^n(·; A)_Y → f_*(S^n(·; A)_X)` commuting with the coboundary and with the constant
augmentation (Bredon, *Sheaf Theory* III.1).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The restriction of `f` from the preimage of an open set to that open set. -/
def preimageMap (U : Opens Y) : C((Opens.map f).obj U, U) where
  toFun x := ⟨f x.val, x.property⟩
  continuous_toFun := (f.hom.continuous.comp continuous_subtype_val).subtype_mk _

/-- The restriction of `f` to the preimage of `U` acts by `f` on underlying points. -/
@[simp]
theorem preimageMap_apply (U : Opens Y) (x : (Opens.map f).obj U) :
    preimageMap f U x = ⟨f x.val, x.property⟩ := rfl

/-- The restrictions of `f` to preimages of opens commute with the inclusions of opens. -/
theorem preimageMap_restrict {U V : Opens Y} (r : U ⟶ V) :
    (preimageMap f V).comp
        (((Opens.toTopCat X).map ((Opens.map f).map r)).hom) =
      (((Opens.toTopCat Y).map r).hom).comp (preimageMap f U) := by
  ext x
  rfl

variable (A : AddCommGrpCat.{0})

/-- Pullback of singular cochains along the restrictions of `f` commutes with restriction along
an inclusion of open sets. -/
theorem openPullback_restrict {_U _V : Opens Y} (r : _U ⟶ _V) :
    AlgebraicTopology.SingularCochains.pullback A
          (((Opens.toTopCat Y).map r).hom) ≫
        AlgebraicTopology.SingularCochains.pullback A (preimageMap f _U) =
      AlgebraicTopology.SingularCochains.pullback A (preimageMap f _V) ≫
        AlgebraicTopology.SingularCochains.pullback A
          (((Opens.toTopCat X).map ((Opens.map f).map r)).hom) := by
  exact (AlgebraicTopology.SingularCochains.pullback_comp A (preimageMap f _U)
      (((Opens.toTopCat Y).map r).hom)).symm.trans
    ((congrArg (AlgebraicTopology.SingularCochains.pullback A)
      (preimageMap_restrict f r).symm).trans
        (AlgebraicTopology.SingularCochains.pullback_comp A
          (((Opens.toTopCat X).map ((Opens.map f).map r)).hom) (preimageMap f _V)))

/-- Pullback of singular cochains along `f`, as a map of presheaves on `Y` into the pushforward
of the singular-cochain presheaf of `X`. -/
def presheafPullback (n : ℕ) : presheaf Y A n ⟶
    (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).obj (presheaf X A n) where
  app U := (AlgebraicTopology.SingularCochains.pullback A (preimageMap f U.unop)).f n
  naturality _ _ r := congrArg (fun g => g.f n) (openPullback_restrict f A r.unop)

/-- Over an open `U`, the pullback map of presheaves is pullback of singular cochains along the
restriction `f⁻¹U → U`. -/
@[simp]
theorem presheafPullback_app (n : ℕ) (U : Opens Y) :
    (presheafPullback f A n).app (op U) =
      (AlgebraicTopology.SingularCochains.pullback A (preimageMap f U)).f n := rfl

/-- Pullback of singular cochains along `f` commutes with the coboundary. -/
@[reassoc]
theorem presheafPullback_d (i j : ℕ) :
    presheafPullback f A i ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).map
          (differential X A i j) =
      differential Y A i j ≫ presheafPullback f A j := by
  apply NatTrans.ext
  funext U
  exact (AlgebraicTopology.SingularCochains.pullback A
    (preimageMap f U.unop)).comm i j

/-- Pullback of the constant presheaf leaves coefficient values unchanged. -/
def constantPresheafPullback : TopCat.ConstantSheaf.presheaf Y A ⟶
    (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).obj
      (TopCat.ConstantSheaf.presheaf X A) where
  app _ := 𝟙 A
  naturality _ _ _ := rfl

/-- The constant augmentation `A → S^0(·; A)` is natural in the space. -/
@[reassoc]
theorem presheafPullback_augmentation :
    presheafAugmentation Y A ≫ presheafPullback f A 0 =
      constantPresheafPullback f A ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).map
          (presheafAugmentation X A) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact pullback_constant A (preimageMap f U.unop) a

end TopCat.SingularCochainSheaf
