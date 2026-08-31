/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SheafificationPushforward
public import Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.Presheaf

/-!
# Pullback on sheafified native singular cochains

The presheaf pullbacks extend through actual sheafification and assemble to a map of cochain
sheaves into genuine topological pushforward.  The constant augmentation is natural for this map.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.SingularCochainSheaf

open TopCat.SheafificationPushforward

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (A : AddCommGrpCat.{0})

/-- The sheafified native cochain pullback in degree `n`. -/
def cochainPullback (n : ℕ) : sheaf Y A n ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj (sheaf X A n) :=
  sheafifyPullback f (presheafPullback f A n)

@[reassoc]
theorem unit_cochainPullback (n : ℕ) :
    unit Y A n ≫ (cochainPullback f A n).hom =
      presheafPullback f A n ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).map (unit X A n) :=
  toSheafify_sheafifyPullback f (presheafPullback f A n)

/-- Sheafified cochain pullback commutes with the native differential. -/
@[reassoc]
theorem cochainPullback_d (i j : ℕ) :
    cochainPullback f A i ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
          (sheafDifferential X A i j) =
      sheafDifferential Y A i j ≫ cochainPullback f A j :=
  (sheafifyPullback_naturality f (differential Y A i j) (differential X A i j)
    (presheafPullback f A i) (presheafPullback f A j)
      (presheafPullback_d f A i j).symm).symm

/-- The generic sheafification lift of the constant presheaf map is the canonical owner map. -/
theorem constant_sheafifyPullback :
    sheafifyPullback f (constantPresheafPullback f A) =
      TopCat.ConstantSheaf.pushforwardHom A f := rfl

/-- The genuine constant augmentation is natural under continuous-map pullback. -/
@[reassoc]
theorem cochainPullback_augmentation :
    sheafAugmentation Y A ≫ cochainPullback f A 0 =
      TopCat.ConstantSheaf.pushforwardHom A f ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
          (sheafAugmentation X A) := by
  have h := sheafifyPullback_naturality f
    (presheafAugmentation Y A) (presheafAugmentation X A)
    (constantPresheafPullback f A) (presheafPullback f A 0)
    (presheafPullback_augmentation f A)
  change sheafAugmentation Y A ≫ cochainPullback f A 0 =
    sheafifyPullback f (constantPresheafPullback f A) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
        (sheafAugmentation X A) at h
  rw [constant_sheafifyPullback] at h
  exact h

/-- Degreewise pullback forms a map to the pushed-forward cochain complex. -/
def cochainPullbackComplex : complexSheaf Y A ⟶
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (complexSheaf X A) where
  f n := cochainPullback f A n
  comm' i j _ := cochainPullback_d f A i j

@[simp]
theorem cochainPullbackComplex_f (n : ℕ) :
    (cochainPullbackComplex f A).f n = cochainPullback f A n := rfl

end TopCat.SingularCochainSheaf
