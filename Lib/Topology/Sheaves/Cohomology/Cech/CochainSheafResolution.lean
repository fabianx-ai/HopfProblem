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
public import Mathlib.Topology.Sheaves.Limits

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

It assumes no local-finiteness, flasqueness, separation, or paracompactness hypothesis.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.5.2 (exactness of the Čech
  resolution `𝒞•(𝔘, F)` of a sheaf)
* R. Hartshorne, *Algebraic Geometry*, III, Lemma 4.2
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

/-- Sections of `F(- ⊓ V)` over an open `W` are the sections of `F` over `W ⊓ V`. -/
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

/-- The map `F(- ⊓ V) ⟶ F(- ⊓ W)` induced by `V ≤ W` is, on each open, the restriction map of
`F` along `Z ⊓ V ≤ Z ⊓ W`. -/
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

/-- The canonical map `F ⟶ F(- ⊓ V)` is, on each open `Z`, restriction along `Z ⊓ V ≤ Z`. -/
@[reassoc (attr := simp)]
theorem toIntersectionSectionsSheaf_app
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X)
    (Z : (Opens X)ᵒᵖ) :
    (toIntersectionSectionsSheaf F V).hom.app Z = F.presheaf.map
      (homOfLE inf_le_left : Z.unop ⊓ V ⟶ Z.unop).op :=
  rfl

/-- The canonical maps `F ⟶ F(- ⊓ V)` are compatible with the maps induced by `V ≤ W`. -/
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

/-- The component of the augmentation `F ⟶ 𝒞⁰(𝔘, F)` at an ordered zero-simplex `σ` is the
canonical map to the sections over the intersection of `σ`. -/
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

/-- The degree-`n` term of the cochain-sheaf complex is the degree-`n` Čech cochain sheaf. -/
@[simp]
theorem cochainSheafComplex_X (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) :
    (cochainSheafComplex F U).X n = cochainSheaf F U n :=
  rfl

/-- The differential of the cochain-sheaf complex is the alternating Čech differential. -/
@[simp]
theorem cochainSheafComplex_d (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) :
    (cochainSheafComplex F U).d n (n + 1) = cochainSheafDifferential F U n :=
  CochainComplex.of_d _ _ n

/-! ## Sections of a cochain sheaf on an actual open -/

/-- Evaluation of a sheaf on the open `W`.  This functor preserves products: the forgetful
functor from sheaves creates limits, and evaluation of presheaves preserves limits. -/
def sheafSectionsFunctor (W : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat X ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W)

/-- Evaluating an abelian sheaf on a fixed open is an additive functor. -/
instance sheafSectionsFunctor_additive (W : Opens X) :
    (sheafSectionsFunctor W).Additive := by
  constructor
  intro A B f g
  rfl

/-- Restrict every member of an indexed open family to the actual open `W`. -/
def restrictedFamily (W : Opens X) (U : ι → Opens X) : ι → Opens X :=
  fun i => W ⊓ U i

/-- Intersection with `W` distributes over a nonempty ordered simplex intersection. -/
theorem intersection_restrictedFamily (W : Opens X)
    (U : ι → Opens X) (n : ℕ) (σ : OrderedSimplex ι n) :
    σ.intersection (restrictedFamily W U) = W ⊓ σ.intersection U := by
  apply le_antisymm
  · apply le_inf
    · exact (iInf_le (fun j : Fin (n + 1) => W ⊓ U (σ j)) 0).trans inf_le_left
    · apply le_iInf
      intro j
      exact (iInf_le (fun k : Fin (n + 1) => W ⊓ U (σ k)) j).trans inf_le_right
  · apply le_iInf
    intro j
    exact le_inf inf_le_left (inf_le_right.trans (iInf_le (fun k => U (σ k)) j))

/-- Evaluating the product cochain sheaf on `W` gives the product of its component section
groups.  This uses preservation of products by sheaf evaluation, not any statement about
stalks. -/
def cochainSheafSectionsProductIso (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) (W : Opens X) :
    (cochainSheaf F U n).presheaf.obj (op W) ≅
      ∏ᶜ fun σ : OrderedSimplex ι n =>
        ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W)).obj
          ((TopCat.Sheaf.forget AddCommGrpCat X).obj
            (intersectionSectionsSheaf F (σ.intersection U))) :=
  ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W)).mapIso
      (Limits.PreservesProduct.iso (TopCat.Sheaf.forget AddCommGrpCat X)
        (fun σ : OrderedSimplex ι n =>
          intersectionSectionsSheaf F (σ.intersection U))) ≪≫
    Limits.PreservesProduct.iso
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W))
      (fun σ : OrderedSimplex ι n =>
        (TopCat.Sheaf.forget AddCommGrpCat X).obj
          (intersectionSectionsSheaf F (σ.intersection U)))

/-- The comparison between the sections of the product cochain sheaf and the product of the
sections is compatible with the projection to each ordered simplex. -/
@[reassoc (attr := simp)]
theorem cochainSheafSectionsProductIso_hom_π
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (n : ℕ) (W : Opens X) (σ : OrderedSimplex ι n) :
    (cochainSheafSectionsProductIso F U n W).hom ≫
        Limits.Pi.π (fun τ : OrderedSimplex ι n =>
          ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W)).obj
            ((TopCat.Sheaf.forget AddCommGrpCat X).obj
              (intersectionSectionsSheaf F (τ.intersection U)))) σ =
      (π (intersectionSectionsSheafPresheaf F) U n σ).hom.app (op W) := by
  change
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W)).map
        (Limits.piComparison (TopCat.Sheaf.forget AddCommGrpCat X)
          (fun τ : OrderedSimplex ι n =>
            intersectionSectionsSheaf F (τ.intersection U))) ≫
      Limits.piComparison
        ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W))
        (fun τ : OrderedSimplex ι n =>
          (TopCat.Sheaf.forget AddCommGrpCat X).obj
            (intersectionSectionsSheaf F (τ.intersection U))) ≫
      Limits.Pi.π (fun τ : OrderedSimplex ι n =>
        ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W)).obj
          ((TopCat.Sheaf.forget AddCommGrpCat X).obj
            (intersectionSectionsSheaf F (τ.intersection U)))) σ =
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W)).map
        ((TopCat.Sheaf.forget AddCommGrpCat X).map
          (Limits.Pi.π (fun τ : OrderedSimplex ι n =>
            intersectionSectionsSheaf F (τ.intersection U)) σ))
  rw [Limits.piComparison_comp_π, ← Functor.map_comp,
    Limits.piComparison_comp_π]

/-- The componentwise identification between evaluation of an intersection-section sheaf and
the corresponding coefficient group for the family restricted to `W`. -/
def cochainSheafSectionFactorIso (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) (W : Opens X) (σ : OrderedSimplex ι n) :
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W)).obj
        ((TopCat.Sheaf.forget AddCommGrpCat X).obj
          (intersectionSectionsSheaf F (σ.intersection U))) ≅
      F.presheaf.obj (op (σ.intersection (restrictedFamily W U))) :=
  F.presheaf.mapIso (eqToIso
    (congrArg op (intersection_restrictedFamily W U n σ).symm))

/-- Sections of the cochain sheaf on `W` are the ordinary normalized Čech cochains of the
restricted family `W ⊓ Uᵢ`. -/
def cochainSheafSectionsIso (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) (W : Opens X) :
    (cochainSheaf F U n).presheaf.obj (op W) ≅
      object F.presheaf (restrictedFamily W U) n :=
  cochainSheafSectionsProductIso F U n W ≪≫
    Limits.Pi.mapIso (fun σ => cochainSheafSectionFactorIso F U n W σ)

/-- Sections of the degree-`n` cochain sheaf over `W` are the degree-`n` Čech cochains of the
restricted family `W ⊓ U`, compatibly with the projection to each ordered simplex. -/
@[reassoc (attr := simp)]
theorem cochainSheafSectionsIso_hom_limit_π
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (n : ℕ) (W : Opens X) (σ : OrderedSimplex ι n) :
    (cochainSheafSectionsIso F U n W).hom ≫
        Limits.Pi.π (fun τ : OrderedSimplex ι n =>
          F.presheaf.obj (op (τ.intersection (restrictedFamily W U)))) σ =
      (π (intersectionSectionsSheafPresheaf F) U n σ).hom.app (op W) ≫
        F.presheaf.map (eqToHom
          (congrArg op (intersection_restrictedFamily W U n σ).symm)) := by
  change (cochainSheafSectionsProductIso F U n W).hom ≫
      (Limits.Pi.mapIso (fun τ : OrderedSimplex ι n =>
        cochainSheafSectionFactorIso F U n W τ)).hom ≫
        Limits.Pi.π (fun τ : OrderedSimplex ι n =>
          F.presheaf.obj (op (τ.intersection (restrictedFamily W U)))) σ = _
  rw [Limits.Pi.mapIso_hom_π, ← Category.assoc,
    cochainSheafSectionsProductIso_hom_π]
  rfl

/-- The same comparison, stated with the Čech projection of the restricted family. -/
@[reassoc (attr := simp)]
theorem cochainSheafSectionsIso_hom_π
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (n : ℕ) (W : Opens X) (σ : OrderedSimplex ι n) :
    (cochainSheafSectionsIso F U n W).hom ≫
        π F.presheaf (restrictedFamily W U) n σ =
      (π (intersectionSectionsSheafPresheaf F) U n σ).hom.app (op W) ≫
        F.presheaf.map (eqToHom
          (congrArg op (intersection_restrictedFamily W U n σ).symm)) := by
  change (cochainSheafSectionsIso F U n W).hom ≫
      Limits.Pi.π (fun τ : OrderedSimplex ι n =>
        F.presheaf.obj (op (τ.intersection (restrictedFamily W U)))) σ = _
  exact cochainSheafSectionsIso_hom_limit_π F U n W σ

/-- On sections over an open `W`, the cochain-sheaf differential is the alternating sum of the
face restrictions. -/
@[reassoc]
theorem cochainSheafDifferential_app_π
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (n : ℕ) (W : Opens X) (σ : OrderedSimplex ι (n + 1)) :
    (differential (intersectionSectionsSheafPresheaf F) U n).hom.app (op W) ≫
        (π (intersectionSectionsSheafPresheaf F) U (n + 1) σ).hom.app (op W) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        ((π (intersectionSectionsSheafPresheaf F) U n (σ.face k)).hom.app (op W) ≫
          ((intersectionSectionsSheafPresheaf F).map
            (σ.faceHom U k).op).hom.app (op W)) := by
  change (sheafSectionsFunctor W).map
      (differential (intersectionSectionsSheafPresheaf F) U n) ≫
        (sheafSectionsFunctor W).map
          (π (intersectionSectionsSheafPresheaf F) U (n + 1) σ) =
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      ((sheafSectionsFunctor W).map
          (π (intersectionSectionsSheafPresheaf F) U n (σ.face k)) ≫
        (sheafSectionsFunctor W).map
          ((intersectionSectionsSheafPresheaf F).map (σ.faceHom U k).op))
  rw [← Functor.map_comp, differential_π]
  rw [show (sheafSectionsFunctor W).map
      (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (π (intersectionSectionsSheafPresheaf F) U n (σ.face k) ≫
          (intersectionSectionsSheafPresheaf F).map (σ.faceHom U k).op)) =
      ∑ k : Fin (n + 2), (sheafSectionsFunctor W).map
        ((-1 : ℤ) ^ (k : ℕ) •
          (π (intersectionSectionsSheafPresheaf F) U n (σ.face k) ≫
            (intersectionSectionsSheafPresheaf F).map (σ.faceHom U k).op)) by
    exact map_sum (sheafSectionsFunctor W).mapAddHom _ Finset.univ]
  apply Finset.sum_congr rfl
  intro k _
  rw [Functor.map_zsmul, Functor.map_comp]

/-- The component transport to the family restricted to `W` commutes with every face
restriction. -/
@[reassoc]
theorem intersectionSectionsMap_app_comp_factorIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (n : ℕ) (W : Opens X) (σ : OrderedSimplex ι (n + 1))
    (k : Fin (n + 2)) :
    ((intersectionSectionsSheafPresheaf F).map (σ.faceHom U k).op).hom.app (op W) ≫
        (cochainSheafSectionFactorIso F U (n + 1) W σ).hom =
      (cochainSheafSectionFactorIso F U n W (σ.face k)).hom ≫
        F.presheaf.map (σ.faceHom (restrictedFamily W U) k).op := by
  change F.presheaf.map _ ≫ F.presheaf.map _ =
    F.presheaf.map _ ≫ F.presheaf.map _
  dsimp only [intersectFunctor]
  rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
  congr 1

/-- The Čech differential of the restricted family `W ⊓ U` is the alternating sum of the face
restrictions. -/
@[reassoc]
theorem differential_restrictedFamily_limit_π
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (n : ℕ) (W : Opens X) (σ : OrderedSimplex ι (n + 1)) :
    differential F.presheaf (restrictedFamily W U) n ≫
        Limits.Pi.π (fun τ : OrderedSimplex ι (n + 1) =>
          F.presheaf.obj (op (τ.intersection (restrictedFamily W U)))) σ =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (π F.presheaf (restrictedFamily W U) n (σ.face k) ≫
          F.presheaf.map (σ.faceHom (restrictedFamily W U) k).op) := by
  change differential F.presheaf (restrictedFamily W U) n ≫
      π F.presheaf (restrictedFamily W U) (n + 1) σ = _
  exact differential_π F.presheaf (restrictedFamily W U) n σ

/-- Under the canonical section comparison, the sheaf differential on an actual open `W` is
the ordinary normalized Čech differential for the restricted family `W ⊓ Uᵢ`. -/
@[reassoc]
theorem cochainSheafDifferential_app_comp_sectionsIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (n : ℕ) (W : Opens X) :
    (cochainSheafDifferential F U n).hom.app (op W) ≫
        (cochainSheafSectionsIso F U (n + 1) W).hom =
      (cochainSheafSectionsIso F U n W).hom ≫
        differential F.presheaf (restrictedFamily W U) n := by
  apply Limits.Pi.hom_ext
  intro σ
  simp only [Category.assoc]
  rw [cochainSheafSectionsIso_hom_limit_π]
  rw [differential_restrictedFamily_limit_π]
  dsimp only [cochainSheafDifferential]
  erw [cochainSheafDifferential_app_π_assoc]
  erw [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  calc
    ((π (intersectionSectionsSheafPresheaf F) U n (σ.face k)).hom.app (op W) ≫
          ((intersectionSectionsSheafPresheaf F).map
            (σ.faceHom U k).op).hom.app (op W)) ≫
        (cochainSheafSectionFactorIso F U (n + 1) W σ).hom =
      (π (intersectionSectionsSheafPresheaf F) U n (σ.face k)).hom.app (op W) ≫
        (((intersectionSectionsSheafPresheaf F).map
            (σ.faceHom U k).op).hom.app (op W) ≫
          (cochainSheafSectionFactorIso F U (n + 1) W σ).hom) :=
        Category.assoc _ _ _
    _ = (π (intersectionSectionsSheafPresheaf F) U n (σ.face k)).hom.app (op W) ≫
        ((cochainSheafSectionFactorIso F U n W (σ.face k)).hom ≫
          F.presheaf.map (σ.faceHom (restrictedFamily W U) k).op) :=
      congrArg (fun q =>
        (π (intersectionSectionsSheafPresheaf F) U n (σ.face k)).hom.app (op W) ≫ q)
        (intersectionSectionsMap_app_comp_factorIso F U n W σ k)
    _ = ((π (intersectionSectionsSheafPresheaf F) U n (σ.face k)).hom.app (op W) ≫
          (cochainSheafSectionFactorIso F U n W (σ.face k)).hom) ≫
        F.presheaf.map (σ.faceHom (restrictedFamily W U) k).op :=
      (Category.assoc _ _ _).symm
    _ = ((cochainSheafSectionsIso F U n W).hom ≫
          π F.presheaf (restrictedFamily W U) n (σ.face k)) ≫
        F.presheaf.map (σ.faceHom (restrictedFamily W U) k).op :=
      congrArg (fun q => q ≫
        F.presheaf.map (σ.faceHom (restrictedFamily W U) k).op)
        (cochainSheafSectionsIso_hom_π F U n W (σ.face k)).symm
    _ = (cochainSheafSectionsIso F U n W).hom ≫
        (π F.presheaf (restrictedFamily W U) n (σ.face k) ≫
          F.presheaf.map (σ.faceHom (restrictedFamily W U) k).op) :=
      Category.assoc _ _ _

/-! ## Insertion for a family with a terminal member -/

/-- Prepend the chosen index to an arbitrary tuple. -/
def prependIndex (i : ι) {n : ℕ} (f : Fin (n + 1) → ι) : Fin (n + 2) → ι :=
  Fin.cons i f

omit [LinearOrder ι] in
/-- Deleting the zeroth vertex of a tuple with an index prepended gives back the original
tuple. -/
@[simp]
theorem face_prependIndex_zero (i : ι) {n : ℕ} (f : Fin (n + 1) → ι) :
    IndexTuple.face (prependIndex i f) 0 = f := by
  funext j
  simp [IndexTuple.face, prependIndex]

omit [LinearOrder ι] in
/-- Deleting a later vertex of a tuple with an index prepended prepends the index to the
corresponding face of the original tuple. -/
@[simp]
theorem face_prependIndex_succ (i : ι) {n : ℕ} (f : Fin (n + 2) → ι)
    (k : Fin (n + 2)) :
    IndexTuple.face (prependIndex i f) k.succ =
      prependIndex i (IndexTuple.face f k) := by
  funext j
  refine Fin.cases ?_ (fun l => ?_) j
  · simp [IndexTuple.face, prependIndex]
  · simp [IndexTuple.face, prependIndex, Function.comp_apply]

/-- If `V i` contains every member of `V`, prepending `i` to an ordered simplex is subordinate
to the simplex intersection. -/
theorem prependIndex_subordinate (V : ι → Opens X) (i : ι)
    (hi : ∀ j, V j ≤ V i) {n : ℕ} (σ : OrderedSimplex ι n) :
    IndexTuple.Subordinate V (σ.intersection V) (prependIndex i σ) := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa [prependIndex] using (σ.intersection_le V 0).trans (hi (σ 0))
  · simpa [prependIndex] using σ.intersection_le V k

set_option backward.isDefEq.respectTransparency false in
/-- Restricted alternating evaluation on an increasing tuple, restricted to its own
intersection, is the normalized product projection. -/
theorem restrictedAlternatingEvaluation_orderedSimplex
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : ι → Opens X)
    (n : ℕ) (σ : OrderedSimplex ι n)
    (hσ : IndexTuple.Subordinate V (σ.intersection V) σ) :
    restrictedAlternatingEvaluation F.presheaf V n (σ.intersection V) σ hσ =
      π F.presheaf V n σ := by
  dsimp only [restrictedAlternatingEvaluation, IndexTuple.intersection,
    OrderedSimplex.intersection]
  rw [alternatingEvaluation_ordered]
  convert Category.comp_id _ using 1
  rw [← F.presheaf.map_id]
  congr 1

/-- The insertion operator obtained by prepending a member which contains every open of the
family.  Alternating evaluation supplies both the repeated-index zero and the sorting sign. -/
def terminalInsertion (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : ι → Opens X) (i : ι) (hi : ∀ j, V j ≤ V i) (n : ℕ) :
    object F.presheaf V (n + 1) ⟶ object F.presheaf V n :=
  Limits.Pi.lift fun σ =>
    restrictedAlternatingEvaluation F.presheaf V (n + 1) (σ.intersection V)
      (prependIndex i σ) (prependIndex_subordinate V i hi σ)

/-- The component of the insertion homotopy at an ordered simplex `σ` is the evaluation of the
cochain at `σ` with the distinguished index prepended. -/
@[reassoc (attr := simp)]
theorem terminalInsertion_π (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : ι → Opens X) (i : ι) (hi : ∀ j, V j ≤ V i)
    (n : ℕ) (σ : OrderedSimplex ι n) :
    terminalInsertion F V i hi n ≫ π F.presheaf V n σ =
      restrictedAlternatingEvaluation F.presheaf V (n + 1) (σ.intersection V)
        (prependIndex i σ) (prependIndex_subordinate V i hi σ) :=
  Limits.Pi.lift_π _ _

/-- A prepended face tuple remains subordinate after restricting from the face intersection to
the full simplex intersection. -/
theorem prependFace_subordinate (V : ι → Opens X) (i : ι)
    (hi : ∀ j, V j ≤ V i) {n : ℕ} (σ : OrderedSimplex ι (n + 1))
    (k : Fin (n + 2)) :
    IndexTuple.Subordinate V (σ.intersection V) (prependIndex i (σ.face k)) :=
  fun j => (σ.intersection_le_face V k).trans
    (prependIndex_subordinate V i hi (σ.face k) j)

/-- Composing the insertion homotopy with the Čech differential gives the alternating sum of the
evaluations at the faces of `σ` with the distinguished index prepended. -/
@[reassoc]
theorem terminalInsertion_comp_differential_π
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : ι → Opens X)
    (i : ι) (hi : ∀ j, V j ≤ V i) (n : ℕ)
    (σ : OrderedSimplex ι (n + 1)) :
    terminalInsertion F V i hi n ≫ differential F.presheaf V n ≫
        π F.presheaf V (n + 1) σ =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        restrictedAlternatingEvaluation F.presheaf V (n + 1)
          (σ.intersection V) (prependIndex i (σ.face k))
          (prependFace_subordinate V i hi σ k) := by
  rw [differential_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul,
    terminalInsertion_π_assoc]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simpa only [OrderedSimplex.faceHom] using
    restrictedAlternatingEvaluation_comp_map F.presheaf V (n + 1)
    (σ.intersection_le_face V k) (prependIndex i (σ.face k))
    (prependIndex_subordinate V i hi (σ.face k))

/-- Deleting the newly prepended zeroth vertex leaves the original ordered simplex, including
the associated restricted alternating evaluation. -/
theorem restrictedAlternatingEvaluation_face_prependIndex_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : ι → Opens X)
    (i : ι) (hi : ∀ j, V j ≤ V i) (n : ℕ) (σ : OrderedSimplex ι n) :
    restrictedAlternatingEvaluation F.presheaf V n (σ.intersection V)
        (IndexTuple.face (prependIndex i σ) 0)
        ((prependIndex_subordinate V i hi σ).face 0) =
      π F.presheaf V n σ := by
  calc
    _ = restrictedAlternatingEvaluation F.presheaf V n (σ.intersection V) σ
        (fun j => σ.intersection_le V j) :=
      restrictedAlternatingEvaluation_congr F.presheaf V n (σ.intersection V)
        (face_prependIndex_zero i σ) _ _
    _ = _ := restrictedAlternatingEvaluation_orderedSimplex F V n σ _

/-- Deleting a successor vertex after prepending `i` is the same alternating evaluation as
prepending `i` after deleting that vertex. -/
theorem restrictedAlternatingEvaluation_face_prependIndex_succ
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : ι → Opens X)
    (i : ι) (hi : ∀ j, V j ≤ V i) (n : ℕ)
    (σ : OrderedSimplex ι (n + 1)) (k : Fin (n + 2)) :
    restrictedAlternatingEvaluation F.presheaf V (n + 1) (σ.intersection V)
        (IndexTuple.face (prependIndex i σ) k.succ)
        ((prependIndex_subordinate V i hi σ).face k.succ) =
      restrictedAlternatingEvaluation F.presheaf V (n + 1) (σ.intersection V)
        (prependIndex i (σ.face k)) (prependFace_subordinate V i hi σ k) :=
  restrictedAlternatingEvaluation_congr F.presheaf V (n + 1) (σ.intersection V)
    (face_prependIndex_succ i σ k) _ _

/-- In the coboundary of a prepended tuple, the zeroth face is the original component and all
successor faces are the negatives of the terms occurring in insertion followed by coboundary. -/
theorem differential_comp_prependIndex_evaluation
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : ι → Opens X)
    (i : ι) (hi : ∀ j, V j ≤ V i) (n : ℕ)
    (σ : OrderedSimplex ι (n + 1)) :
    differential F.presheaf V (n + 1) ≫
        restrictedAlternatingEvaluation F.presheaf V (n + 2) (σ.intersection V)
          (prependIndex i σ) (prependIndex_subordinate V i hi σ) =
      π F.presheaf V (n + 1) σ -
        ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          restrictedAlternatingEvaluation F.presheaf V (n + 1)
            (σ.intersection V) (prependIndex i (σ.face k))
            (prependFace_subordinate V i hi σ k) := by
  rw [differential_comp_restrictedAlternatingEvaluation]
  rw [Fin.sum_univ_succ]
  rw [restrictedAlternatingEvaluation_face_prependIndex_zero]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ]
  rw [sub_eq_add_neg]
  congr 1
  erw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [restrictedAlternatingEvaluation_face_prependIndex_succ]
  simp only [mul_neg, mul_one, neg_smul]
  all_goals assumption

/-- Inserting a member which contains the whole family contracts the normalized Čech complex
in every positive degree. -/
theorem terminalInsertion_contraction
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : ι → Opens X)
    (i : ι) (hi : ∀ j, V j ≤ V i) (n : ℕ) :
    terminalInsertion F V i hi n ≫ differential F.presheaf V n +
        differential F.presheaf V (n + 1) ≫ terminalInsertion F V i hi (n + 1) =
      𝟙 (object F.presheaf V (n + 1)) := by
  apply Limits.Pi.hom_ext
  intro σ
  simp only [Preadditive.add_comp, Category.id_comp, Category.assoc]
  change terminalInsertion F V i hi n ≫ differential F.presheaf V n ≫
      π F.presheaf V (n + 1) σ +
    differential F.presheaf V (n + 1) ≫ terminalInsertion F V i hi (n + 1) ≫
      π F.presheaf V (n + 1) σ =
    π F.presheaf V (n + 1) σ
  rw [terminalInsertion_comp_differential_π F V i hi n σ]
  rw [terminalInsertion_π F V i hi (n + 1) σ]
  rw [differential_comp_prependIndex_evaluation F V i hi n σ]
  abel

/-! ## The augmented degree -/

/-- The unique increasing zero-simplex with vertex `i`. -/
def vertexSimplex (i : ι) : OrderedSimplex ι 0 :=
  OrderEmbedding.ofStrictMono (fun _ : Fin 1 => i) (by
    intro a b h
    omega)

/-- Every vertex of the ordered zero-simplex on an index is that index. -/
@[simp]
theorem vertexSimplex_apply (i : ι) (j : Fin 1) : vertexSimplex i j = i :=
  rfl

/-- The intersection over the ordered zero-simplex on an index `i` is the cover member `V i`. -/
@[simp]
theorem vertexSimplex_intersection (V : ι → Opens X) (i : ι) :
    (vertexSimplex i).intersection V = V i := by
  apply le_antisymm
  · exact iInf_le _ 0
  · apply le_iInf
    intro j
    simp

/-- Every simplex intersection lies in the chosen zero-simplex intersection when `V i`
contains the whole family. -/
theorem intersection_le_vertexSimplex (V : ι → Opens X) (i : ι)
    (hi : ∀ j, V j ≤ V i) (σ : OrderedSimplex ι 0) :
    σ.intersection V ≤ (vertexSimplex i).intersection V := by
  apply le_iInf
  intro j
  simpa using (σ.intersection_le V 0).trans (hi (σ 0))

/-- The augmented map for a family with a terminal member, with source the coefficient group
on the chosen vertex intersection. -/
def terminalAugmentation (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : ι → Opens X) (i : ι) (hi : ∀ j, V j ≤ V i) :
    F.presheaf.obj (op ((vertexSimplex i).intersection V)) ⟶
      object F.presheaf V 0 :=
  Limits.Pi.lift fun σ => F.presheaf.map
    (homOfLE (intersection_le_vertexSimplex V i hi σ)).op

/-- The component of the augmentation for a cover with a largest member is the restriction from
that largest member to the intersection of the given zero-simplex. -/
@[reassoc (attr := simp)]
theorem terminalAugmentation_π (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : ι → Opens X) (i : ι) (hi : ∀ j, V j ≤ V i)
    (σ : OrderedSimplex ι 0) :
    terminalAugmentation F V i hi ≫ π F.presheaf V 0 σ =
      F.presheaf.map (homOfLE (intersection_le_vertexSimplex V i hi σ)).op :=
  Limits.Pi.lift_π _ _

/-- Evaluation at the chosen terminal vertex retracts the terminal augmentation. -/
@[reassoc]
theorem terminalAugmentation_comp_vertexProjection
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : ι → Opens X)
    (i : ι) (hi : ∀ j, V j ≤ V i) :
    terminalAugmentation F V i hi ≫ π F.presheaf V 0 (vertexSimplex i) =
      𝟙 (F.presheaf.obj (op ((vertexSimplex i).intersection V))) := by
  rw [terminalAugmentation_π]
  rw [← F.presheaf.map_id]
  congr 1

/-- The chosen vertex is subordinate to every simplex intersection when its family member is
terminal. -/
theorem vertexSimplex_subordinate (V : ι → Opens X) (i : ι)
    (hi : ∀ j, V j ≤ V i) (σ : OrderedSimplex ι 0) :
    IndexTuple.Subordinate V (σ.intersection V) (vertexSimplex i) := by
  intro j
  simpa using (σ.intersection_le V 0).trans (hi (σ 0))

/-- The sole degree-zero prism tuple from the chosen vertex to `σ` is obtained by prepending
that vertex. -/
theorem prism_vertexSimplex_zero (i : ι) (σ : OrderedSimplex ι 0) :
    IndexTuple.prism (vertexSimplex i) σ 0 = prependIndex i σ := by
  funext j
  fin_cases j <;> simp [IndexTuple.prism, prependIndex]

/-- In degree zero, terminal insertion is the prism from the chosen vertex to the target
vertex. -/
theorem terminalInsertion_zero_π
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : ι → Opens X)
    (i : ι) (hi : ∀ j, V j ≤ V i) (σ : OrderedSimplex ι 0) :
    terminalInsertion F V i hi 0 ≫ π F.presheaf V 0 σ =
      prismComponent F.presheaf V 0 (σ.intersection V) (vertexSimplex i) σ
        (vertexSimplex_subordinate V i hi σ) (fun j => σ.intersection_le V j) := by
  rw [terminalInsertion_π]
  dsimp only [prismComponent]
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_zsmul]
  apply restrictedAlternatingEvaluation_congr F.presheaf V 1 (σ.intersection V)
    (prism_vertexSimplex_zero i σ).symm

/-- Restricting the chosen vertex projection to a simplex intersection is its restricted
alternating evaluation there. -/
theorem vertexProjection_comp_terminalAugmentation_π
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : ι → Opens X)
    (i : ι) (hi : ∀ j, V j ≤ V i) (σ : OrderedSimplex ι 0) :
    π F.presheaf V 0 (vertexSimplex i) ≫ terminalAugmentation F V i hi ≫
        π F.presheaf V 0 σ =
      restrictedAlternatingEvaluation F.presheaf V 0 (σ.intersection V)
        (vertexSimplex i) (vertexSimplex_subordinate V i hi σ) := by
  rw [terminalAugmentation_π]
  rw [← restrictedAlternatingEvaluation_orderedSimplex F V 0 (vertexSimplex i)
    (fun j => (vertexSimplex i).intersection_le V j)]
  exact restrictedAlternatingEvaluation_comp_map F.presheaf V 0
    (intersection_le_vertexSimplex V i hi σ) (vertexSimplex i)
    (fun j => (vertexSimplex i).intersection_le V j)

/-- The terminal augmentation and insertion contract the augmented complex in degree zero. -/
theorem terminalInsertion_contraction_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : ι → Opens X)
    (i : ι) (hi : ∀ j, V j ≤ V i) :
    π F.presheaf V 0 (vertexSimplex i) ≫ terminalAugmentation F V i hi +
        differential F.presheaf V 0 ≫ terminalInsertion F V i hi 0 =
      𝟙 (object F.presheaf V 0) := by
  apply Limits.Pi.hom_ext
  intro σ
  simp only [Preadditive.add_comp, Category.id_comp, Category.assoc]
  change π F.presheaf V 0 (vertexSimplex i) ≫ terminalAugmentation F V i hi ≫
      π F.presheaf V 0 σ +
    differential F.presheaf V 0 ≫ terminalInsertion F V i hi 0 ≫
      π F.presheaf V 0 σ =
    π F.presheaf V 0 σ
  rw [vertexProjection_comp_terminalAugmentation_π]
  rw [terminalInsertion_zero_π]
  rw [differential_comp_prismComponent_zero F.presheaf V (σ.intersection V)
    (vertexSimplex i) σ (vertexSimplex_subordinate V i hi σ)
    (fun j => σ.intersection_le V j)]
  rw [restrictedAlternatingEvaluation_orderedSimplex F V 0 σ
    (fun j => σ.intersection_le V j)]
  abel

/-! ## The insertion homotopy on an actual open -/

omit [LinearOrder ι] in
/-- If `W` lies in the chosen cover member `U i`, that member is terminal after restricting
the whole family to `W`. -/
theorem restrictedFamily_le_chosen (U : ι → Opens X) (W : Opens X)
    (i : ι) (hW : W ≤ U i) (j : ι) :
    restrictedFamily W U j ≤ restrictedFamily W U i :=
  le_inf inf_le_left (inf_le_left.trans hW)

/-- On `W ≤ U i`, the intersection belonging to the chosen restricted zero-simplex is `W`. -/
theorem vertexSimplex_intersection_restrictedFamily (U : ι → Opens X)
    (W : Opens X) (i : ι) (hW : W ≤ U i) :
    (vertexSimplex i).intersection (restrictedFamily W U) = W := by
  rw [vertexSimplex_intersection]
  exact inf_eq_left.mpr hW

/-- The canonical coefficient identification between sections on `W` and sections on the
chosen restricted zero-simplex intersection. -/
def terminalSectionIso (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (W : Opens X) (i : ι) (hW : W ≤ U i) :
    F.presheaf.obj (op W) ≅
      F.presheaf.obj (op ((vertexSimplex i).intersection (restrictedFamily W U))) :=
  F.presheaf.mapIso (eqToIso
    (congrArg op (vertexSimplex_intersection_restrictedFamily U W i hW)).symm)

/-- On sections over an open `W`, the component of the augmentation at an ordered zero-simplex
`σ` is restriction along `W ⊓ σ.intersection U ≤ W`. -/
@[reassoc]
theorem cochainSheafAugmentation_app_comp_projection
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (W : Opens X) (σ : OrderedSimplex ι 0) :
    (cochainSheafAugmentation F U).hom.app (op W) ≫
        (π (intersectionSectionsSheafPresheaf F) U 0 σ).hom.app (op W) =
      F.presheaf.map
        (homOfLE inf_le_left : W ⊓ σ.intersection U ⟶ W).op := by
  change (sheafSectionsFunctor W).map (cochainSheafAugmentation F U) ≫
      (sheafSectionsFunctor W).map
        (π (intersectionSectionsSheafPresheaf F) U 0 σ) = _
  rw [← Functor.map_comp, cochainSheafAugmentation_π]
  rfl

/-- Under the canonical section comparison, the sheaf augmentation over `W ≤ U i` is the
terminal-family augmentation, after identifying its source with `F(W)`. -/
@[reassoc]
theorem cochainSheafAugmentation_app_comp_sectionsIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (W : Opens X) (i : ι) (hW : W ≤ U i) :
    (cochainSheafAugmentation F U).hom.app (op W) ≫
        (cochainSheafSectionsIso F U 0 W).hom =
      (terminalSectionIso F U W i hW).hom ≫
        terminalAugmentation F (restrictedFamily W U) i
          (restrictedFamily_le_chosen U W i hW) := by
  apply Limits.Pi.hom_ext
  intro σ
  simp only [Category.assoc]
  change (cochainSheafAugmentation F U).hom.app (op W) ≫
      (cochainSheafSectionsIso F U 0 W).hom ≫
        π F.presheaf (restrictedFamily W U) 0 σ =
    (terminalSectionIso F U W i hW).hom ≫
      terminalAugmentation F (restrictedFamily W U) i
        (restrictedFamily_le_chosen U W i hW) ≫
          π F.presheaf (restrictedFamily W U) 0 σ
  rw [cochainSheafSectionsIso_hom_π]
  rw [terminalAugmentation_π]
  calc
    (cochainSheafAugmentation F U).hom.app (op W) ≫
          ((π (intersectionSectionsSheafPresheaf F) U 0 σ).hom.app (op W) ≫
            F.presheaf.map (eqToHom
              (congrArg op (intersection_restrictedFamily W U 0 σ).symm))) =
        ((cochainSheafAugmentation F U).hom.app (op W) ≫
            (π (intersectionSectionsSheafPresheaf F) U 0 σ).hom.app (op W)) ≫
          F.presheaf.map (eqToHom
            (congrArg op (intersection_restrictedFamily W U 0 σ).symm)) :=
      (Category.assoc _ _ _).symm
    _ = F.presheaf.map
          (homOfLE inf_le_left : W ⊓ σ.intersection U ⟶ W).op ≫
        F.presheaf.map (eqToHom
          (congrArg op (intersection_restrictedFamily W U 0 σ).symm)) :=
      congrArg (fun q => q ≫ F.presheaf.map (eqToHom
        (congrArg op (intersection_restrictedFamily W U 0 σ).symm)))
        (cochainSheafAugmentation_app_comp_projection F U W σ)
    _ = (terminalSectionIso F U W i hW).hom ≫
        F.presheaf.map
          (homOfLE (intersection_le_vertexSimplex (restrictedFamily W U) i
            (restrictedFamily_le_chosen U W i hW) σ)).op := by
      change F.presheaf.map _ ≫ F.presheaf.map _ =
        F.presheaf.map _ ≫ F.presheaf.map _
      rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
      congr 1

/-- The degree-minus-one part of the local insertion homotopy: evaluate a zero-cochain at the
chosen vertex and identify that restricted intersection with `W`. -/
def insertionHomotopyZero (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (W : Opens X) (i : ι) (hW : W ≤ U i) :
    (cochainSheaf F U 0).presheaf.obj (op W) ⟶ F.presheaf.obj (op W) :=
  (cochainSheafSectionsIso F U 0 W).hom ≫
    π F.presheaf (restrictedFamily W U) 0 (vertexSimplex i) ≫
    (terminalSectionIso F U W i hW).inv

/-- The local degree-minus-one insertion is a left inverse to the sheaf augmentation. -/
theorem cochainSheafAugmentation_app_comp_insertionHomotopyZero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (W : Opens X) (i : ι) (hW : W ≤ U i) :
    (cochainSheafAugmentation F U).hom.app (op W) ≫
        insertionHomotopyZero F U W i hW =
      𝟙 (F.presheaf.obj (op W)) := by
  dsimp only [insertionHomotopyZero]
  rw [cochainSheafAugmentation_app_comp_sectionsIso_assoc]
  rw [terminalAugmentation_comp_vertexProjection_assoc]
  simp only [Iso.hom_inv_id]
  all_goals assumption

/-- Conjugating the evaluated augmentation by the local source and section comparisons gives
the terminal-family augmentation. -/
@[reassoc]
theorem terminalSectionIso_inv_comp_augmentation_app_comp_sectionsIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (W : Opens X) (i : ι) (hW : W ≤ U i) :
    (terminalSectionIso F U W i hW).inv ≫
        (cochainSheafAugmentation F U).hom.app (op W) ≫
          (cochainSheafSectionsIso F U 0 W).hom =
      terminalAugmentation F (restrictedFamily W U) i
        (restrictedFamily_le_chosen U W i hW) := by
  rw [cochainSheafAugmentation_app_comp_sectionsIso]
  exact (terminalSectionIso F U W i hW).inv_hom_id_assoc _

/-- The inverse section comparison transports the evaluated sheaf differential to the
ordinary normalized differential for the restricted family. -/
@[reassoc]
theorem cochainSheafSectionsIso_inv_comp_differential_app
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (n : ℕ) (W : Opens X) :
    (cochainSheafSectionsIso F U n W).inv ≫
        (cochainSheafDifferential F U n).hom.app (op W) =
      differential F.presheaf (restrictedFamily W U) n ≫
        (cochainSheafSectionsIso F U (n + 1) W).inv := by
  apply (cancel_mono (cochainSheafSectionsIso F U (n + 1) W).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [cochainSheafDifferential_app_comp_sectionsIso]
  simp

/-- On sections over an actual open `W ≤ U i`, insert the chosen cover index `i` into an
alternating cochain.  This is equation (C13), transported through the canonical comparison
between sections of the product sheaf and the normalized Čech product. -/
def insertionHomotopy (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (W : Opens X) (i : ι) (hW : W ≤ U i) (n : ℕ) :
    (cochainSheaf F U (n + 1)).presheaf.obj (op W) ⟶
      (cochainSheaf F U n).presheaf.obj (op W) :=
  (cochainSheafSectionsIso F U (n + 1) W).hom ≫
    terminalInsertion F (restrictedFamily W U) i
      (restrictedFamily_le_chosen U W i hW) n ≫
    (cochainSheafSectionsIso F U n W).inv

/-- The degree-minus-one insertion and degree-zero insertion satisfy the augmented contraction
identity on sections over `W ≤ U i`. -/
theorem insertionHomotopy_contraction_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (W : Opens X) (i : ι) (hW : W ≤ U i) :
    insertionHomotopyZero F U W i hW ≫
          (cochainSheafAugmentation F U).hom.app (op W) +
        (cochainSheafDifferential F U 0).hom.app (op W) ≫
          insertionHomotopy F U W i hW 0 =
      𝟙 ((cochainSheaf F U 0).presheaf.obj (op W)) := by
  apply (cancel_epi (cochainSheafSectionsIso F U 0 W).inv).1
  apply (cancel_mono (cochainSheafSectionsIso F U 0 W).hom).1
  dsimp only [insertionHomotopyZero, insertionHomotopy]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [terminalSectionIso_inv_comp_augmentation_app_comp_sectionsIso]
  rw [cochainSheafSectionsIso_inv_comp_differential_app_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  simp only [Iso.inv_hom_id_assoc]
  rw [terminalInsertion_contraction_zero]

/-- The local insertion operator satisfies `h d + d h = 1` on sections over `W ≤ U i`.
This is the normalized form of equation (C14). -/
theorem insertionHomotopy_contraction
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (W : Opens X) (i : ι) (hW : W ≤ U i) (n : ℕ) :
    insertionHomotopy F U W i hW n ≫
          (cochainSheafDifferential F U n).hom.app (op W) +
        (cochainSheafDifferential F U (n + 1)).hom.app (op W) ≫
          insertionHomotopy F U W i hW (n + 1) =
      𝟙 ((cochainSheaf F U (n + 1)).presheaf.obj (op W)) := by
  apply (cancel_epi (cochainSheafSectionsIso F U (n + 1) W).inv).1
  apply (cancel_mono (cochainSheafSectionsIso F U (n + 1) W).hom).1
  dsimp only [insertionHomotopy]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [cochainSheafSectionsIso_inv_comp_differential_app_assoc]
  rw [cochainSheafDifferential_app_comp_sectionsIso_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  simp only [Iso.inv_hom_id_assoc]
  rw [terminalInsertion_contraction]

/-! ## Exactness on stalks -/

/-- A short complex of abelian sheaves is exact if every section in the local kernel acquires
a local preimage after shrinking.  The proof is the actual germ argument: represent a stalk
element on an open, shrink until its outgoing image is literally zero, and apply the supplied
local lift. -/
theorem sheafShortComplex_exact_of_local_kernels
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (h : ∀ (U : Opens X) (x : X) (_ : x ∈ U)
      (s : S.X₂.presheaf.obj (op U)), S.g.hom.app (op U) s = 0 →
      ∃ (V : Opens X) (hVU : V ≤ U) (_ : x ∈ V)
        (t : S.X₁.presheaf.obj (op V)),
        S.f.hom.app (op V) t = S.X₂.presheaf.map (homOfLE hVU).op s) :
    S.Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mpr
  intro x
  apply (ShortComplex.ab_exact_iff _).mpr
  intro a ha
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.presheaf.exists_germ_eq a
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
    (S.X₂.presheaf.germ U x hxU s) = 0 at ha
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ha
  have hz : S.X₃.presheaf.germ U x hxU (S.g.hom.app (op U) s) =
      S.X₃.presheaf.germ U x hxU 0 :=
    ha.trans (S.X₃.presheaf.germ U x hxU).hom.map_zero.symm
  obtain ⟨V, hxV, iVU, jVU, he⟩ :=
    S.X₃.presheaf.germ_eq x hxU hxU _ _ hz
  have hv : S.g.hom.app (op V) (S.X₂.presheaf.map iVU.op s) = 0 :=
    ((ConcreteCategory.congr_hom (S.g.hom.naturality iVU.op) s).trans he).trans
      (S.X₃.presheaf.map jVU.op).hom.map_zero
  obtain ⟨W, hWV, hxW, t, ht⟩ := h V x hxV _ hv
  refine ⟨S.X₁.presheaf.germ W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
    (S.X₁.presheaf.germ W x hxW t) = S.X₂.presheaf.germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht,
    S.X₂.presheaf.germ_res_apply, S.X₂.presheaf.germ_res_apply]

private theorem sheaf_mono_of_locally_split_mono
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (h : ∀ (U : Opens X) (x : X) (_ : x ∈ U),
      ∃ (V : Opens X) (_hVU : V ≤ U) (_ : x ∈ V)
        (r : G.presheaf.obj (op V) ⟶ F.presheaf.obj (op V)),
        f.hom.app (op V) ≫ r = 𝟙 _) :
    Mono f := by
  apply (TopCat.Presheaf.mono_iff_stalk_mono f).mpr
  intro x
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨U, hxU, s, rfl⟩ := F.presheaf.exists_germ_eq a
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ha
  have hz : G.presheaf.germ U x hxU (f.hom.app (op U) s) =
      G.presheaf.germ U x hxU 0 :=
    ha.trans (G.presheaf.germ U x hxU).hom.map_zero.symm
  obtain ⟨V, hxV, iVU, jVU, he⟩ :=
    G.presheaf.germ_eq x hxU hxU _ _ hz
  let sV := F.presheaf.map iVU.op s
  have hv : f.hom.app (op V) sV = 0 :=
    ((ConcreteCategory.congr_hom (f.hom.naturality iVU.op) s).trans he).trans
      (G.presheaf.map jVU.op).hom.map_zero
  obtain ⟨W, hWV, hxW, r, hr⟩ := h V x hxV
  let sW := F.presheaf.map (homOfLE hWV).op sV
  have hw : f.hom.app (op W) sW = 0 := by
    change f.hom.app (op W) (F.presheaf.map (homOfLE hWV).op sV) = 0
    rw [← ConcreteCategory.comp_apply, f.hom.naturality,
      ConcreteCategory.comp_apply, hv]
    exact (G.presheaf.map (homOfLE hWV).op).hom.map_zero
  have hsW : sW = 0 := by
    have heval := congrArg (fun z => r z) hw
    change r (f.hom.app (op W) sW) = r 0 at heval
    rw [← ConcreteCategory.comp_apply, hr] at heval
    simpa using heval
  calc
    F.presheaf.germ U x hxU s = F.presheaf.germ V x hxV sV :=
      (F.presheaf.germ_res_apply iVU x hxV s).symm
    _ = F.presheaf.germ W x hxW sW :=
      (F.presheaf.germ_res_apply (homOfLE hWV) x hxW sV).symm
    _ = F.presheaf.germ W x hxW 0 :=
      congrArg (F.presheaf.germ W x hxW) hsW
    _ = 0 := (F.presheaf.germ W x hxW).hom.map_zero

/-- The short complex around normalized Čech degree `n + 1`. -/
def cochainSheafShortComplex (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : ι → Opens X) (n : ℕ) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (cochainSheafDifferential F U n)
    (cochainSheafDifferential F U (n + 1))
    (cochainSheafDifferential_comp F U n)

/-- The augmented short complex `F ⟶ C⁰ ⟶ C¹`. -/
def augmentedCochainSheafShortComplex
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (cochainSheafAugmentation F U)
    (cochainSheafDifferential F U 0)
    (cochainSheafAugmentation_comp_differential F U)

/-- The normalized Čech cochain sheaves are exact in every positive degree for an arbitrary
set-indexed open cover.  The local primitive is insertion after restricting to `V ⊓ U i`. -/
theorem cochainSheafShortComplex_exact
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (hU : IsOpenCover U) (n : ℕ) :
    (cochainSheafShortComplex F U n).Exact := by
  apply sheafShortComplex_exact_of_local_kernels
  intro V x hxV s hs
  change (cochainSheafDifferential F U (n + 1)).hom.app (op V) s = 0 at hs
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  let W : Opens X := V ⊓ U i
  have hWV : W ≤ V := inf_le_left
  have hWi : W ≤ U i := inf_le_right
  have hxW : x ∈ W := ⟨hxV, hxi⟩
  let sW := (cochainSheaf F U (n + 1)).presheaf.map (homOfLE hWV).op s
  have hsW : (cochainSheafDifferential F U (n + 1)).hom.app (op W) sW = 0 := by
    calc
      _ = (cochainSheaf F U (n + 2)).presheaf.map (homOfLE hWV).op
          ((cochainSheafDifferential F U (n + 1)).hom.app (op V) s) :=
        ConcreteCategory.congr_hom
          ((cochainSheafDifferential F U (n + 1)).hom.naturality
            (homOfLE hWV).op) s
      _ = 0 := by rw [hs]; exact map_zero _
  refine ⟨W, hWV, hxW, insertionHomotopy F U W i hWi n sW, ?_⟩
  change (cochainSheafDifferential F U n).hom.app (op W)
      (insertionHomotopy F U W i hWi n sW) = sW
  have hc := ConcreteCategory.congr_hom
    (insertionHomotopy_contraction F U W i hWi n) sW
  change (cochainSheafDifferential F U n).hom.app (op W)
        (insertionHomotopy F U W i hWi n sW) +
      insertionHomotopy F U W i hWi (n + 1)
        ((cochainSheafDifferential F U (n + 1)).hom.app (op W) sW) = sW at hc
  rw [hsW] at hc
  simpa using hc

/-- The augmented sequence `F ⟶ C⁰ ⟶ C¹` is exact for an arbitrary set-indexed open cover. -/
theorem augmentedCochainSheafShortComplex_exact
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (hU : IsOpenCover U) :
    (augmentedCochainSheafShortComplex F U).Exact := by
  apply sheafShortComplex_exact_of_local_kernels
  intro V x hxV s hs
  change (cochainSheafDifferential F U 0).hom.app (op V) s = 0 at hs
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  let W : Opens X := V ⊓ U i
  have hWV : W ≤ V := inf_le_left
  have hWi : W ≤ U i := inf_le_right
  have hxW : x ∈ W := ⟨hxV, hxi⟩
  let sW := (cochainSheaf F U 0).presheaf.map (homOfLE hWV).op s
  have hsW : (cochainSheafDifferential F U 0).hom.app (op W) sW = 0 := by
    calc
      _ = (cochainSheaf F U 1).presheaf.map (homOfLE hWV).op
          ((cochainSheafDifferential F U 0).hom.app (op V) s) :=
        ConcreteCategory.congr_hom
          ((cochainSheafDifferential F U 0).hom.naturality
            (homOfLE hWV).op) s
      _ = 0 := by rw [hs]; exact map_zero _
  refine ⟨W, hWV, hxW, insertionHomotopyZero F U W i hWi sW, ?_⟩
  change (cochainSheafAugmentation F U).hom.app (op W)
      (insertionHomotopyZero F U W i hWi sW) = sW
  have hc := ConcreteCategory.congr_hom
    (insertionHomotopy_contraction_zero F U W i hWi) sW
  change (cochainSheafAugmentation F U).hom.app (op W)
        (insertionHomotopyZero F U W i hWi sW) +
      insertionHomotopy F U W i hWi 0
        ((cochainSheafDifferential F U 0).hom.app (op W) sW) = sW at hc
  rw [hsW] at hc
  simpa using hc

/-- The augmentation into normalized degree-zero cochains is a monomorphism for every open
cover.  Locally it is split by evaluation at a cover member containing the point. -/
theorem cochainSheafAugmentation_mono
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (hU : IsOpenCover U) : Mono (cochainSheafAugmentation F U) := by
  apply sheaf_mono_of_locally_split_mono
  intro V x hxV
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  let W : Opens X := V ⊓ U i
  have hWV : W ≤ V := inf_le_left
  have hWi : W ≤ U i := inf_le_right
  have hxW : x ∈ W := ⟨hxV, hxi⟩
  exact ⟨W, hWV, hxW, insertionHomotopyZero F U W i hWi,
    cochainSheafAugmentation_app_comp_insertionHomotopyZero F U W i hWi⟩

/-- Exactness of the entire augmented normalized Čech cochain-sheaf complex, stated as the
initial exact triple together with every positive exact triple. -/
theorem augmentedCochainSheafComplex_exact
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (hU : IsOpenCover U) :
    (augmentedCochainSheafShortComplex F U).Exact ∧
      ∀ n : ℕ, (cochainSheafShortComplex F U n).Exact :=
  ⟨augmentedCochainSheafShortComplex_exact F U hU,
    cochainSheafShortComplex_exact F U hU⟩

/-- The exact augmented normalized Čech cochain-sheaf complex attached to an arbitrary
set-indexed open cover. -/
def augmentedCochainSheafComplex
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)
    (hU : IsOpenCover U) :
    CategoryTheory.Abelian.Ext.ExactAugmentedCochainComplex
      (C := TopCat.Sheaf AddCommGrpCat.{u} X) where
  F := F
  complex := cochainSheafComplex F U
  ι := cochainSheafAugmentation F U
  zero := by
    change cochainSheafAugmentation F U ≫ cochainSheafDifferential F U 0 = 0
    exact cochainSheafAugmentation_comp_differential F U
  initialExact := by
    change (augmentedCochainSheafShortComplex F U).Exact
    exact (augmentedCochainSheafComplex_exact F U hU).1
  mono_ι := cochainSheafAugmentation_mono F U hU
  positiveExact n := by
    simpa only [cochainSheafComplex_X, cochainSheafComplex_d,
      cochainSheafShortComplex, Nat.add_assoc, Nat.reduceAdd] using
        (augmentedCochainSheafComplex_exact F U hU).2 n

end TopologicalSpace.OpenCover.OrderedCech
