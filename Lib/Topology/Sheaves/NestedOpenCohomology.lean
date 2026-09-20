/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.ConstantNormalizationConsequences
public import Lib.Topology.Sheaves.OpenEmbeddingCohomology

/-!
# Cohomology and constant coefficients for nested opens

For opens `U ⊆ W` of a space `X`, restriction of sheaves is transitive: `(F|_W)|_U = F|_U`
(Hartshorne, *Algebraic Geometry*, II §1; Iversen, *Cohomology of Sheaves*, II.2).  This file
records that natural isomorphism, deduces that restriction in the cohomology presheaf
`V ↦ H^n(V, F)` agrees with restriction of cohomology along `U ⊆ W`, and shows that the
constant-coefficient class is compatible with it.

## Main results

* `restrictionIso`: `(F|_W)|_U ≅ F|_U` naturally in `F`.
* `cohomologyEquiv_restrict`: restriction in the cohomology presheaf is restriction of
  cohomology along `U ⊆ W`.
* `intrinsicOpenClass_restrict`: the constant-coefficient class restricts to the
  constant-coefficient class.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace TopCat.Sheaf.NestedOpenCohomology

open TopCat.Sheaf.OpenRestriction
open CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization

variable {X : TopCat.{0}} {U W : Opens X}

/-- The inclusion `U ⟶ W` of nested open subspaces, as a map of topological spaces. -/
def inclusion (h : U ≤ W) : TopCat.of U ⟶ TopCat.of W :=
  TopCat.ofHom ⟨Opens.inclusion h, (Opens.isOpenEmbedding_of_le h).continuous⟩

/-- The inclusion of nested opens acts on points as the coercion `U → W`. -/
@[simp]
theorem inclusion_apply (h : U ≤ W) (x : U) :
    inclusion h x = Opens.inclusion h x := rfl

/-- The nested inclusion is an open embedding. -/
theorem inclusion_isOpenEmbedding (h : U ≤ W) :
    Topology.IsOpenEmbedding (inclusion h) :=
  Opens.isOpenEmbedding_of_le h

/-- The inclusion `U ⟶ W` followed by the inclusion of `W` into `X` is the inclusion of `U`
into `X`. -/
@[simp]
theorem inclusion_comp_ambientInclusion (h : U ≤ W) :
    inclusion h ≫ TopCat.Sheaf.OpenRestriction.inclusion W =
      TopCat.Sheaf.OpenRestriction.inclusion U := rfl

/-- Direct images of opens through the two literal inclusions agree. -/
theorem openImage_comp_obj (h : U ≤ W) (A : Opens U) :
    ((TopCat.Sheaf.OpenEmbeddingCohomology.openImage
        (inclusion h) (inclusion_isOpenEmbedding h) ⋙
      TopCat.Sheaf.OpenRestriction.openImage W).obj A) =
      (TopCat.Sheaf.OpenRestriction.openImage U).obj A := by
  ext x
  change x ∈ (TopCat.Sheaf.OpenRestriction.inclusion W) ''
      ((inclusion h) '' (A : Set U)) ↔
    x ∈ (TopCat.Sheaf.OpenRestriction.inclusion U) '' (A : Set U)
  constructor
  · rintro ⟨w, ⟨u, hu, huw⟩, hwx⟩
    exact ⟨u, hu, (congrArg Subtype.val huw).trans hwx⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u.1, h u.2⟩, ⟨u, hu, rfl⟩, rfl⟩

/-- Functorial form of `openImage_comp_obj`. -/
theorem openImage_comp (h : U ≤ W) :
    TopCat.Sheaf.OpenEmbeddingCohomology.openImage
        (inclusion h) (inclusion_isOpenEmbedding h) ⋙
      TopCat.Sheaf.OpenRestriction.openImage W =
    TopCat.Sheaf.OpenRestriction.openImage U :=
  CategoryTheory.Functor.ext (openImage_comp_obj h)
    (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- Transitivity of restriction: `(F|_W)|_U ≅ F|_U` for nested opens `U ⊆ W`, naturally in the
sheaf `F` (Hartshorne II §1; Iversen II.2). -/
def restrictionIso (h : U ≤ W) :
    TopCat.Sheaf.OpenRestriction.restriction W ⋙
        TopCat.Sheaf.OpenEmbeddingCohomology.restriction
          (inclusion h) (inclusion_isOpenEmbedding h) ≅
      TopCat.Sheaf.OpenRestriction.restriction U := by
  let _ : (TopCat.Sheaf.OpenEmbeddingCohomology.openImage
      (inclusion h) (inclusion_isOpenEmbedding h)).IsContinuous
      (Opens.grothendieckTopology (TopCat.of U))
      (Opens.grothendieckTopology (TopCat.of W)) :=
    TopCat.Sheaf.OpenEmbeddingCohomology.openImage_continuous
      (inclusion h) (inclusion_isOpenEmbedding h)
  exact CategoryTheory.Functor.sheafPushforwardContinuousComp'
    (eqToIso (openImage_comp h)) AddCommGrpCat
    (Opens.grothendieckTopology (TopCat.of U))
    (Opens.grothendieckTopology (TopCat.of W))
    (Opens.grothendieckTopology X)

/-- On sections over an open `A ⊆ U`, the transitivity isomorphism `(F|_W)|_U ≅ F|_U` is the
identity of `F(A)`, read through the two descriptions of `A` as an open of `X`. -/
@[simp]
theorem restrictionIso_hom_app (h : U ≤ W)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (A : Opens U) :
    (((restrictionIso h).hom.app F).hom.app (op A)) =
      F.obj.map (eqToHom (openImage_comp_obj h A).symm).op := by
  let _ : (TopCat.Sheaf.OpenEmbeddingCohomology.openImage
      (inclusion h) (inclusion_isOpenEmbedding h)).IsContinuous
      (Opens.grothendieckTopology (TopCat.of U))
      (Opens.grothendieckTopology (TopCat.of W)) :=
    TopCat.Sheaf.OpenEmbeddingCohomology.openImage_continuous
      (inclusion h) (inclusion_isOpenEmbedding h)
  exact (CategoryTheory.Functor.sheafPushforwardContinuousComp'_hom_app_hom_app
    (eqToIso (openImage_comp h)) AddCommGrpCat
    (Opens.grothendieckTopology (TopCat.of U))
    (Opens.grothendieckTopology (TopCat.of W))
    (Opens.grothendieckTopology X) F (op A)).trans
      (congrArg F.obj.map (Subsingleton.elim _ _))

/-- The canonical constant-sheaf restriction morphisms compose through the nested restriction
isomorphism. -/
theorem constantRestrictionHom_comp (h : U ≤ W) (A : AddCommGrpCat.{0}) :
    TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom
          (inclusion h) (inclusion_isOpenEmbedding h) A ≫
        (TopCat.Sheaf.OpenEmbeddingCohomology.restriction
          (inclusion h) (inclusion_isOpenEmbedding h)).map
          (openConstantRestrictionHom W A) ≫
        (restrictionIso h).hom.app (TopCat.ConstantSheaf.sheaf X A) =
      openConstantRestrictionHom U A := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext
    (Opens.grothendieckTopology (TopCat.of U)) _ _
    ((TopCat.Sheaf.OpenRestriction.restriction U).obj
      (TopCat.ConstantSheaf.sheaf X A)).property (by
      apply NatTrans.ext
      funext V
      apply ConcreteCategory.hom_ext
      intro a
      change (((restrictionIso h).hom.app
          (TopCat.ConstantSheaf.sheaf X A)).hom.app (op V.unop))
          ((openConstantRestrictionHom W A).hom.app
            (op ((TopCat.Sheaf.OpenEmbeddingCohomology.openImage
              (inclusion h) (inclusion_isOpenEmbedding h)).obj V.unop))
            ((TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom
              (inclusion h) (inclusion_isOpenEmbedding h) A).hom.app (op V.unop)
              ((TopCat.ConstantSheaf.unit (TopCat.of U) A).app (op V.unop) a))) =
        (openConstantRestrictionHom U A).hom.app (op V.unop)
          ((TopCat.ConstantSheaf.unit (TopCat.of U) A).app (op V.unop) a)
      let r := (eqToHom (openImage_comp_obj h V.unop).symm).op
      have h₁ := TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom_app_unit
        (inclusion h) (inclusion_isOpenEmbedding h) A V.unop a
      have h₂ := TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom_app_unit
        (TopCat.Sheaf.OpenRestriction.inclusion W)
        (TopCat.Sheaf.OpenRestriction.inclusion_isOpenEmbedding W) A
        ((TopCat.Sheaf.OpenEmbeddingCohomology.openImage
          (inclusion h) (inclusion_isOpenEmbedding h)).obj V.unop) a
      have hd := (congrArg
        ((openConstantRestrictionHom W A).hom.app
          (op ((TopCat.Sheaf.OpenEmbeddingCohomology.openImage
            (inclusion h) (inclusion_isOpenEmbedding h)).obj V.unop))) h₁).trans h₂
      exact (ConcreteCategory.congr_hom
        (restrictionIso_hom_app h (TopCat.ConstantSheaf.sheaf X A) V.unop) _).trans
        ((congrArg ((TopCat.ConstantSheaf.sheaf X A).obj.map r) hd).trans
          ((ConcreteCategory.congr_hom
            ((TopCat.ConstantSheaf.unit X A).naturality r) a).symm.trans
              (TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom_app_unit
                (TopCat.Sheaf.OpenRestriction.inclusion U)
                (TopCat.Sheaf.OpenRestriction.inclusion_isOpenEmbedding U)
                A V.unop a).symm)))

/-- The open-restriction representing endpoint sends the distinguished integral section to the
restriction of the universal represented section. -/
theorem representingUnit_app_unit (U : Opens X) (V : Opens U) :
    (representingUnit U).hom.app (op V)
        ((TopCat.ConstantSheaf.unit (TopCat.of U)
          (AddCommGrpCat.of (ULift.{0} ℤ))).app (op V) (ULift.up 1)) =
      (freeOpen U).obj.map (homOfLE (openImage_obj_le U V)).op
        (freeHomEquiv U (freeOpen U) (𝟙 _)) := by
  let F := freeOpen U
  let g := representingUnit U
  let q : V ⟶ (⊤ : Opens U) := homOfLE le_top
  let iV : (openImage U).obj V ⟶ U := homOfLE (openImage_obj_le U V)
  let iTop : op U ⟶ op ((openImage U).obj (⊤ : Opens U)) :=
    (eqToIso (congrArg op (openImage_top U))).inv
  let zTop := (TopCat.ConstantSheaf.unit (TopCat.of U)
    (AddCommGrpCat.of (ULift.{0} ℤ))).app (op (⊤ : Opens U)) (ULift.up 1)
  have hglobal := homRestrictionEquiv_sections U F (𝟙 F)
  have hnat := TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality
    (TopCat.of U) (𝟙 (TopCat.ConstantSheaf.integralSheaf (TopCat.of U))) g
  rw [Category.id_comp] at hnat
  have hid := TopCat.ConstantSheaf.integralHomGlobalEquiv_id (TopCat.of U)
  have hgeq : TopCat.ConstantSheaf.integralHomGlobalEquiv
        (TopCat.of U) ((restriction U).obj F) g =
      g.hom.app (op (⊤ : Opens U)) zTop :=
    hnat.trans (congrArg (g.hom.app (op (⊤ : Opens U))) hid)
  have hRg : restrictionGlobalEquiv U F
        (g.hom.app (op (⊤ : Opens U)) zTop) =
      freeHomEquiv U F (𝟙 F) := by
    rw [← hgeq]
    exact hglobal
  have hg : g.hom.app (op (⊤ : Opens U)) zTop =
      F.obj.map iTop (freeHomEquiv U F (𝟙 F)) := by
    have he := (restrictionGlobalEquiv U F).eq_symm_apply.mpr hRg
    change g.hom.app (op (⊤ : Opens U)) zTop =
      F.obj.map (eqToIso (congrArg op (openImage_top U))).inv
        (freeHomEquiv U F (𝟙 F)) at he
    exact he
  have hu := (TopCat.ConstantSheaf.unit (TopCat.of U)
    (AddCommGrpCat.of (ULift.{0} ℤ))).naturality q.op
  have hgn := g.hom.naturality q.op
  have hvalue : g.hom.app (op V)
        ((TopCat.ConstantSheaf.unit (TopCat.of U)
          (AddCommGrpCat.of (ULift.{0} ℤ))).app (op V) (ULift.up 1)) =
      F.obj.map ((openImage U).map q).op
        (g.hom.app (op (⊤ : Opens U)) zTop) := by
    have hu' := ConcreteCategory.congr_hom hu (ULift.up 1)
    change (TopCat.ConstantSheaf.unit (TopCat.of U)
        (AddCommGrpCat.of (ULift.{0} ℤ))).app (op V) (ULift.up 1) =
      (TopCat.ConstantSheaf.sheaf (TopCat.of U)
        (AddCommGrpCat.of (ULift.{0} ℤ))).obj.map q.op zTop at hu'
    have hgn' := ConcreteCategory.congr_hom hgn zTop
    exact (congrArg (g.hom.app (op V)) hu').trans hgn'
  rw [hvalue, hg]
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg F.obj.map (Subsingleton.elim
      (iTop ≫ ((openImage U).map q).op) iV.op)) _

/-- The integral global-section equivalence evaluates a morphism on the distinguished global
section. -/
theorem integralHomGlobalEquiv_eq_app_unit (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of U))
    (g : TopCat.ConstantSheaf.integralSheaf (TopCat.of U) ⟶ F) :
    TopCat.ConstantSheaf.integralHomGlobalEquiv (TopCat.of U) F g =
      g.hom.app (op (⊤ : Opens U))
        ((TopCat.ConstantSheaf.unit (TopCat.of U)
          (AddCommGrpCat.of (ULift.{0} ℤ))).app
            (op (⊤ : Opens U)) (ULift.up 1)) := by
  have hnat := TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality
    (TopCat.of U) (𝟙 (TopCat.ConstantSheaf.integralSheaf (TopCat.of U))) g
  rw [Category.id_comp] at hnat
  exact hnat.trans (congrArg (g.hom.app (op (⊤ : Opens U)))
    (TopCat.ConstantSheaf.integralHomGlobalEquiv_id (TopCat.of U)))

/-- The integral representing endpoints commute with restriction from `W` to `U`. -/
theorem representingUnit_comp (h : U ≤ W) :
    TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom
          (inclusion h) (inclusion_isOpenEmbedding h)
          (AddCommGrpCat.of (ULift.{0} ℤ)) ≫
        (TopCat.Sheaf.OpenEmbeddingCohomology.restriction
          (inclusion h) (inclusion_isOpenEmbedding h)).map
          (representingUnit W) ≫
        (restrictionIso h).hom.app (freeOpen W) =
      representingUnit U ≫
        (restriction U).map
          ((CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.freeOpenFunctor X).map
            (homOfLE h)) := by
  let F := freeOpen W
  let φ : freeOpen U ⟶ F :=
    (CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.freeOpenFunctor X).map
      (homOfLE h)
  let V : Opens W :=
    (TopCat.Sheaf.OpenEmbeddingCohomology.openImage
      (inclusion h) (inclusion_isOpenEmbedding h)).obj ⊤
  let s := freeHomEquiv W F (𝟙 F)
  let iW : (openImage W).obj V ⟶ W := homOfLE (openImage_obj_le W V)
  let iU : (openImage U).obj (⊤ : Opens U) ⟶ U :=
    homOfLE (openImage_obj_le U ⊤)
  let r : U ⟶ W := homOfLE h
  let e := (eqToHom (openImage_comp_obj h (⊤ : Opens U)).symm).op
  apply (TopCat.ConstantSheaf.integralHomGlobalEquiv (TopCat.of U)
    ((restriction U).obj F)).injective
  rw [integralHomGlobalEquiv_eq_app_unit,
    integralHomGlobalEquiv_eq_app_unit]
  change (((restrictionIso h).hom.app F).hom.app (op (⊤ : Opens U)))
      ((representingUnit W).hom.app (op V)
        ((TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom
          (inclusion h) (inclusion_isOpenEmbedding h)
          (AddCommGrpCat.of (ULift.{0} ℤ))).hom.app (op (⊤ : Opens U))
            ((TopCat.ConstantSheaf.unit (TopCat.of U)
              (AddCommGrpCat.of (ULift.{0} ℤ))).app
                (op (⊤ : Opens U)) (ULift.up 1)))) =
    φ.hom.app (op ((openImage U).obj ⊤))
      ((representingUnit U).hom.app (op (⊤ : Opens U))
        ((TopCat.ConstantSheaf.unit (TopCat.of U)
          (AddCommGrpCat.of (ULift.{0} ℤ))).app
            (op (⊤ : Opens U)) (ULift.up 1)))
  rw [TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom_app_unit]
  rw [representingUnit_app_unit]
  rw [restrictionIso_hom_app]
  rw [representingUnit_app_unit]
  have hφ : freeHomEquiv U F φ = F.obj.map r.op s := by
    exact (congrArg (freeHomEquiv U F) (Category.comp_id φ)).symm.trans
      (freeHomEquiv_naturality_open r F (𝟙 F))
  have hnat := φ.hom.naturality iU.op
  have hright := ConcreteCategory.congr_hom hnat
    (freeHomEquiv U (freeOpen U) (𝟙 _))
  rw [ConcreteCategory.comp_apply] at hright
  have hright' : φ.hom.app (op ((openImage U).obj ⊤))
        ((freeOpen U).obj.map iU.op
          (freeHomEquiv U (freeOpen U) (𝟙 _))) =
      F.obj.map iU.op (F.obj.map r.op s) := by
    exact hright.trans (congrArg (F.obj.map iU.op) hφ)
  rw [hright']
  change F.obj.map e (F.obj.map iW.op s) =
    (F.obj.map r.op ≫ F.obj.map iU.op) s
  rw [← ConcreteCategory.comp_apply]
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg F.obj.map (Subsingleton.elim
      (iW.op ≫ e) (r.op ≫ iU.op))) _

/-- Restriction in the cohomology presheaf `V ↦ H^n(V, F)` from `W` to `U` agrees with
restriction of cohomology along the inclusion `U ⊆ W`, in every degree. -/
theorem cohomologyEquiv_restrict (h : U ≤ W)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{0} F n W) :
    CategoryTheory.Sheaf.H.map ((restrictionIso h).hom.app F) n
        (TopCat.Sheaf.OpenEmbeddingCohomology.cohomologyMap
          (inclusion h) (inclusion_isOpenEmbedding h)
          ((restriction W).obj F) n
          (cohomologyEquiv W F n a)) =
      cohomologyEquiv U F n
        ((CategoryTheory.Sheaf.cohomologyPresheaf F n).map
          (homOfLE h).op a) := by
  let φ : freeOpen U ⟶ freeOpen W :=
    (CategoryTheory.Sheaf.Leray.FibreStalkEvaluation.freeOpenFunctor X).map
      (homOfLE h)
  have hc := @Ext.ExactFunctorComparison.comp_natTrans
    (TopCat.Sheaf AddCommGrpCat.{0} X) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of W)) _ _
      (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of U)) _ _
      (IsGrothendieckAbelian.hasExt _)
    (restriction W) (restriction_additive W)
    (restriction_preservesFiniteLimits W) (restriction_preservesFiniteColimits W)
    (TopCat.Sheaf.OpenEmbeddingCohomology.restriction
      (inclusion h) (inclusion_isOpenEmbedding h))
    (TopCat.Sheaf.OpenEmbeddingCohomology.restriction_additive
      (inclusion h) (inclusion_isOpenEmbedding h))
    (TopCat.Sheaf.OpenEmbeddingCohomology.restriction_preservesFiniteLimits
      (inclusion h) (inclusion_isOpenEmbedding h))
    (TopCat.Sheaf.OpenEmbeddingCohomology.restriction_preservesFiniteColimits
      (inclusion h) (inclusion_isOpenEmbedding h))
    (restriction U) (restriction_additive U)
    (restriction_preservesFiniteLimits U) (restriction_preservesFiniteColimits U)
    (restrictionIso h).hom inferInstance
    (freeOpen W) F
    (TopCat.ConstantSheaf.integralSheaf (TopCat.of W))
    (TopCat.ConstantSheaf.integralSheaf (TopCat.of U))
    (representingUnit W)
    (TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom
      (inclusion h) (inclusion_isOpenEmbedding h)
      (AddCommGrpCat.of (ULift.{0} ℤ)))
    (representingUnit U ≫ (restriction U).map φ)
    (representingUnit_comp h) n a
  have hp := Ext.ExactFunctorComparison.precompose
    (restriction U) (representingUnit U) φ n a
  exact hc.trans hp.symm

set_option maxHeartbeats 250000 in
set_option linter.style.haveILetI false in
/-- The constant-coefficient cohomology class on `W` restricts to the constant-coefficient class
on a nested open `U ⊆ W`. -/
theorem intrinsicOpenClass_restrict (h : U ≤ W)
    [LocallyConnectedSpace (TopCat.of W)]
    [LocallyConnectedSpace (TopCat.of U)]
    (A : AddCommGrpCat.{0}) (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{0}
      (TopCat.ConstantSheaf.sheaf X A) n W) :
    intrinsicOpenClass U A n
        ((CategoryTheory.Sheaf.cohomologyPresheaf
          (TopCat.ConstantSheaf.sheaf X A) n).map (homOfLE h).op a) =
      TopCat.Sheaf.OpenEmbeddingCohomology.constantPullback
        (inclusion h) (inclusion_isOpenEmbedding h) A n
        (intrinsicOpenClass W A n a) := by
  let cX := TopCat.ConstantSheaf.sheaf X A
  let eW := openConstantRestrictionHom W A
  let eU := openConstantRestrictionHom U A
  let er := TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom
    (inclusion h) (inclusion_isOpenEmbedding h) A
  let R := TopCat.Sheaf.OpenEmbeddingCohomology.restriction
    (inclusion h) (inclusion_isOpenEmbedding h)
  let rho := restrictionIso h
  let xW := cohomologyEquiv W cX n a
  let y := TopCat.Sheaf.OpenEmbeddingCohomology.cohomologyMap
    (inclusion h) (inclusion_isOpenEmbedding h) ((restriction W).obj cX) n xW
  letI ieW : IsIso eW := openConstantRestrictionHom_isIso W A
  letI ieU : IsIso eU := openConstantRestrictionHom_isIso U A
  letI ier : IsIso er :=
    TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom_isIso
      (inclusion h) (inclusion_isOpenEmbedding h) A
  letI imap : IsIso (R.map eW) :=
    @CategoryTheory.Functor.map_isIso _ _ _ _ _ _ R eW ieW
  have hc0 : er ≫ R.map eW ≫ rho.hom.app cX = eU := by
    exact constantRestrictionHom_comp h A
  have hc : rho.hom.app cX ≫ inv eU (I := ieU) =
      R.map (inv eW (I := ieW)) ≫ inv er (I := ier) := by
    apply (IsIso.comp_inv_eq eU).2
    rw [← hc0]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc]
    rw [← R.map_comp, IsIso.inv_hom_id, R.map_id]
    exact (Category.id_comp _).symm
  have hnested := cohomologyEquiv_restrict h cX n a
  change CategoryTheory.Sheaf.H.map (rho.hom.app cX) n y =
    cohomologyEquiv U cX n
      ((CategoryTheory.Sheaf.cohomologyPresheaf cX n).map
        (homOfLE h).op a) at hnested
  have hnat := TopCat.Sheaf.OpenEmbeddingCohomology.cohomologyMap_naturality
    (inclusion h) (inclusion_isOpenEmbedding h)
    (inv eW (I := ieW)) n xW
  change TopCat.Sheaf.OpenEmbeddingCohomology.cohomologyMap
      (inclusion h) (inclusion_isOpenEmbedding h)
      (TopCat.ConstantSheaf.sheaf (TopCat.of W) A) n
      (CategoryTheory.Sheaf.H.map (inv eW (I := ieW)) n xW) =
    CategoryTheory.Sheaf.H.map (R.map (inv eW (I := ieW))) n y at hnat
  change CategoryTheory.Sheaf.H.map (inv eU (I := ieU)) n
      (cohomologyEquiv U cX n
        ((CategoryTheory.Sheaf.cohomologyPresheaf cX n).map
          (homOfLE h).op a)) =
    CategoryTheory.Sheaf.H.map (inv er (I := ier)) n
      (TopCat.Sheaf.OpenEmbeddingCohomology.cohomologyMap
        (inclusion h) (inclusion_isOpenEmbedding h)
        (TopCat.ConstantSheaf.sheaf (TopCat.of W) A) n
        (CategoryTheory.Sheaf.H.map (inv eW (I := ieW)) n xW))
  rw [← hnested, hnat]
  exact (CategoryTheory.Sheaf.H.map_comp_apply (rho.hom.app cX)
      (inv eU (I := ieU)) y).symm.trans
    ((congrArg (fun q ↦ CategoryTheory.Sheaf.H.map q n y) hc).trans
      (CategoryTheory.Sheaf.H.map_comp_apply
        (R.map (inv eW (I := ieW))) (inv er (I := ier)) y))

end TopCat.Sheaf.NestedOpenCohomology
