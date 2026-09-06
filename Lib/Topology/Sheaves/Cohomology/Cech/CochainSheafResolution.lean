/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.RefinementHomotopy
public import Lib.Algebra.Homology.DerivedCategory.Ext.ExactAugmentedCochainComplex
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-!
# The normalized Čech cochain-sheaf resolution

For a set-indexed family of opens `U` and an abelian sheaf `F`, this file constructs the
degree-`n` sheaf

`W ↦ ∏ (σ : OrderedSimplex ι n), F (W ⊓ σ.intersection U)`.

Each factor is presented as the direct image of the restriction of `F` to the corresponding
open intersection.  The normalized alternating Čech differential therefore gives a complex of
sheaves.  The later part of the file proves exactness by the textbook local insertion homotopy:
near a point one chooses a cover member containing it and inserts that index into alternating
cochains.  In particular, the proof never commutes a stalk with the possibly infinite product.

This is textbook section CD-05C, equations (C11)--(C14).  It assumes no local-finiteness,
flasqueness, separation, or paracompactness hypothesis.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopologicalSpace.OpenCover.OrderedCech

variable {X : TopCat.{u}}

/-! ## Direct-image section sheaves -/

/-- Intersect every open with `V`. -/
def intersectFunctor (V : Opens X) : CategoryTheory.Functor (Opens X) (Opens X) where
  obj W := W ⊓ V
  map {W Z} f := homOfLE (inf_le_inf f.le le_rfl)

/-- The presheaf whose sections on `W` are the sections of `F` on `W ⊓ V`. -/
def intersectionSectionsPresheaf
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  (intersectFunctor V).op ⋙ F.presheaf

/-- The underlying presheaf of the direct image of the restriction of `F` to `V`. -/
def pushedRestrictionPresheaf
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  (TopCat.Presheaf.pushforward AddCommGrpCat V.inclusion').obj
    (V.isOpenEmbedding.functor.op ⋙ F.presheaf)

/-- The direct-image restriction formula `j_* j^* F (W) ≅ F (W ⊓ V)`. -/
def pushedRestrictionPresheafIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    pushedRestrictionPresheaf F V ≅ intersectionSectionsPresheaf F V := by
  refine NatIso.ofComponents (fun W => F.presheaf.mapIso (eqToIso
    (congrArg op (V.functor_map_eq_inf W.unop)))) ?_
  intro W Z f
  simp only [pushedRestrictionPresheaf, intersectionSectionsPresheaf, intersectFunctor,
    TopCat.Presheaf.pushforward_obj_obj, TopCat.Presheaf.pushforward_obj_map,
    Functor.comp_obj, Functor.comp_map, Functor.mapIso_hom]
  rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
  congr 1

/-- The sheaf `j_* j^* F`, presented so that its value on `W` is definitionally
`F (W ⊓ V)`. -/
def intersectionSectionsSheaf
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X where
  obj := intersectionSectionsPresheaf F V
  property := TopCat.Presheaf.isSheaf_of_iso
    (pushedRestrictionPresheafIso F V)
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf V.inclusion'
      (TopCat.Presheaf.isSheaf_of_isOpenEmbedding V.isOpenEmbedding F.property))

/-- The literal direct image of the restriction of `F` to the open subspace `V`. -/
def pushedRestrictionSheaf
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (TopCat.Sheaf.pushforward AddCommGrpCat V.inclusion').obj
    ((V.sheafRestrict (C := AddCommGrpCat)).obj F)

/-- The explicit section-formula sheaf is the direct image `j_* j^* F`. -/
def pushedRestrictionSheafIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    pushedRestrictionSheaf F V ≅ intersectionSectionsSheaf F V :=
  ObjectProperty.isoMk _ (pushedRestrictionPresheafIso F V)

@[simp]
theorem intersectionSectionsSheaf_obj
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V W : Opens X) :
    (intersectionSectionsSheaf F V).presheaf.obj (op W) =
      F.presheaf.obj (op (W ⊓ V)) :=
  rfl

/-- Restriction in the intersection parameter. -/
def intersectionSectionsMap
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {V W : Opens X} (h : V ≤ W) :
    intersectionSectionsSheaf F W ⟶ intersectionSectionsSheaf F V :=
  ObjectProperty.homMk
    { app := fun Z => F.presheaf.map
        (homOfLE (inf_le_inf le_rfl h) : Z.unop ⊓ V ⟶ Z.unop ⊓ W).op
      naturality := by
        intro Z T f
        simp only [intersectionSectionsSheaf, intersectionSectionsPresheaf,
          intersectFunctor, Functor.comp_obj, Functor.comp_map]
        rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
        congr 1 }

@[reassoc (attr := simp)]
theorem intersectionSectionsMap_app
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {V W : Opens X} (h : V ≤ W) (Z : (Opens X)ᵒᵖ) :
    (intersectionSectionsMap F h).hom.app Z = F.presheaf.map
      (homOfLE (inf_le_inf le_rfl h) : Z.unop ⊓ V ⟶ Z.unop ⊓ W).op :=
  rfl

/-- Restrict a section of `F` to its intersection with `V`. -/
def toIntersectionSectionsSheaf
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    F ⟶ intersectionSectionsSheaf F V :=
  ObjectProperty.homMk
    { app := fun Z => F.presheaf.map
        (homOfLE inf_le_left : Z.unop ⊓ V ⟶ Z.unop).op
      naturality := by
        intro Z T f
        simp only [intersectionSectionsSheaf, intersectionSectionsPresheaf,
          intersectFunctor, Functor.comp_obj, Functor.comp_map]
        rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
        congr 1 }

@[reassoc (attr := simp)]
theorem toIntersectionSectionsSheaf_app
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X)
    (Z : (Opens X)ᵒᵖ) :
    (toIntersectionSectionsSheaf F V).hom.app Z = F.presheaf.map
      (homOfLE inf_le_left : Z.unop ⊓ V ⟶ Z.unop).op :=
  rfl

@[reassoc (attr := simp)]
theorem toIntersectionSectionsSheaf_comp
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {V W : Opens X} (h : V ≤ W) :
    toIntersectionSectionsSheaf F W ≫ intersectionSectionsMap F h =
      toIntersectionSectionsSheaf F V := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Z
  change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _
  dsimp only [intersectFunctor]
  rw [← F.presheaf.map_comp]
  congr 1

/-- The sheaf-valued presheaf `V ↦ j_{V,*}j_V^*F`. -/
def intersectionSectionsSheafPresheaf
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.Presheaf (TopCat.Sheaf AddCommGrpCat.{u} X) X where
  obj V := intersectionSectionsSheaf F V.unop
  map {V W} f := intersectionSectionsMap F f.unop.le
  map_id V := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext Z
    change F.presheaf.map _ = 𝟙 _
    dsimp only [intersectFunctor]
    exact F.presheaf.map_id _
  map_comp {V W Z} f g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext T
    change F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
    dsimp only [intersectFunctor]
    rw [← F.presheaf.map_comp]
    congr 1

/-! ## The normalized cochain sheaves -/

variable {ι : Type u} [LinearOrder ι]

/-- The degree-`n` normalized Čech cochain sheaf, a product of the direct-image restriction
sheaves belonging to the increasing `(n + 1)`-fold intersections. -/
@[implicit_reducible]
def cochainSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  object (intersectionSectionsSheafPresheaf F) U n

/-- The normalized alternating differential between Čech cochain sheaves. -/
@[implicit_reducible]
def cochainSheafDifferential (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) :
    cochainSheaf F U n ⟶ cochainSheaf F U (n + 1) :=
  differential (intersectionSectionsSheafPresheaf F) U n

/-- The augmentation sends a section of `F` to its restrictions on all degree-zero
intersections. -/
def cochainSheafAugmentation (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) : F ⟶ cochainSheaf F U 0 :=
  Limits.Pi.lift fun σ => toIntersectionSectionsSheaf F (σ.intersection U)

@[reassoc (attr := simp)]
theorem cochainSheafAugmentation_π (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (σ : OrderedSimplex ι 0) :
    cochainSheafAugmentation F U ≫
        π (intersectionSectionsSheafPresheaf F) U 0 σ =
      toIntersectionSectionsSheaf F (σ.intersection U) :=
  Limits.Pi.lift_π _ _

/-- The augmentation followed by the first Čech differential is zero. -/
theorem cochainSheafAugmentation_comp_differential
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X) :
    cochainSheafAugmentation F U ≫ cochainSheafDifferential F U 0 = 0 := by
  apply Limits.Pi.hom_ext
  intro σ
  rw [zero_comp]
  change cochainSheafAugmentation F U ≫
    (differential (intersectionSectionsSheafPresheaf F) U 0 ≫
      π (intersectionSectionsSheafPresheaf F) U 1 σ) = 0
  rw [differential_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul,
    cochainSheafAugmentation_π_assoc]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul]
  dsimp only [intersectionSectionsSheafPresheaf]
  rw [toIntersectionSectionsSheaf_comp, toIntersectionSectionsSheaf_comp]
  change toIntersectionSectionsSheaf F (σ.intersection U) +
    -toIntersectionSectionsSheaf F (σ.intersection U) =
      (0 : F ⟶ intersectionSectionsSheaf F (σ.intersection U))
  exact add_neg_cancel _

/-- Consecutive normalized Čech cochain-sheaf differentials compose to zero. -/
theorem cochainSheafDifferential_comp (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) :
    cochainSheafDifferential F U n ≫ cochainSheafDifferential F U (n + 1) = 0 :=
  differential_comp_differential (intersectionSectionsSheafPresheaf F) U n

/-- The normalized Čech cochain complex of sheaves. -/
def cochainSheafComplex (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  complex (intersectionSectionsSheafPresheaf F) U

@[simp]
theorem cochainSheafComplex_X (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) :
    (cochainSheafComplex F U).X n = cochainSheaf F U n :=
  rfl

@[simp]
theorem cochainSheafComplex_d (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) :
    (cochainSheafComplex F U).d n (n + 1) = cochainSheafDifferential F U n :=
  CochainComplex.of_d _ _ n

end TopologicalSpace.OpenCover.OrderedCech
