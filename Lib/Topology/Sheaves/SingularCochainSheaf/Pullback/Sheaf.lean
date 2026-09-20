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
# Functoriality of the singular-cochain sheaf in the space

Pullback of the singular-cochain presheaves along a continuous map `f : X → Y` extends through
sheafification to a map of complexes of sheaves `𝒮^•_Y → f_* 𝒮^•_X`, natural for the constant
augmentation (Bredon, *Sheaf Theory* III.1).

## Main definitions

* `TopCat.SingularCochainSheaf.cochainPullback`, `…cochainPullbackComplex`

## Main results

* `TopCat.SingularCochainSheaf.cochainPullback_augmentation`
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.SingularCochainSheaf

open TopCat.SheafificationPushforward

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (A : AddCommGrpCat.{0})

/-- Pullback along `f` on the degree-`n` singular-cochain sheaves, `𝒮^n_Y → f_* 𝒮^n_X`. -/
def cochainPullback (n : ℕ) : sheaf Y A n ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj (sheaf X A n) :=
  sheafifyPullback f (presheafPullback f A n)

/-- The sheafification unit intertwines pullback on presheaves with pullback on sheaves. -/
@[reassoc]
theorem unit_cochainPullback (n : ℕ) :
    unit Y A n ≫ (cochainPullback f A n).hom =
      presheafPullback f A n ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).map (unit X A n) :=
  toSheafify_sheafifyPullback f (presheafPullback f A n)

/-- Pullback on the singular-cochain sheaves commutes with the coboundary. -/
@[reassoc]
theorem cochainPullback_d (i j : ℕ) :
    cochainPullback f A i ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
          (sheafDifferential X A i j) =
      sheafDifferential Y A i j ≫ cochainPullback f A j :=
  (sheafifyPullback_naturality f (differential Y A i j) (differential X A i j)
    (presheafPullback f A i) (presheafPullback f A j)
      (presheafPullback_d f A i j).symm).symm

/-- Sheafifying the pullback of the constant presheaf gives the canonical map
`A_Y → f_* A_X`. -/
theorem constant_sheafifyPullback :
    sheafifyPullback f (constantPresheafPullback f A) =
      TopCat.ConstantSheaf.pushforwardHom A f := rfl

/-- The augmentation `A_X → 𝒮^0_X` of the constant sheaf is natural in the space. -/
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

/-- Degreewise pullback as a map of complexes of sheaves `𝒮^•_Y → f_* 𝒮^•_X`. -/
def cochainPullbackComplex : complexSheaf Y A ⟶
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (complexSheaf X A) where
  f n := cochainPullback f A n
  comm' i j _ := cochainPullback_d f A i j

/-- In each degree the pullback map of complexes is the degreewise pullback. -/
@[simp]
theorem cochainPullbackComplex_f (n : ℕ) :
    (cochainPullbackComplex f A).f n = cochainPullback f A n := rfl

end TopCat.SingularCochainSheaf
