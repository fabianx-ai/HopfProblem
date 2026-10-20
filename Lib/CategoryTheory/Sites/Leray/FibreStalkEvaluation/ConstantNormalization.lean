/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.OpenRestrictionComposition
public import Lib.Topology.Sheaves.ConstantCohomologyPullback
public import Lib.Topology.Sheaves.OpenEmbeddingCohomology

/-!
# Constant-coefficient normalization of finite-source evaluation on an open

For a finite closed map whose image lies in an ambient open, this file identifies the native
fibre-evaluation class with constant-coefficient pullback along the induced map to that open.
The coefficient group and cohomological degree are arbitrary.  The comparison is elementary:
it uses exact finite pushforward, exact open restriction, and their literal-open composition.

Restriction and pushforward of constant sheaves along an open inclusion, and naturality of
`Hⁿ`: Bredon, *Sheaf Theory* II.9; Iversen, *Cohomology of Sheaves* II.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

universe u

namespace CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization

open TopCat.FiniteClosedPushforward
open TopCat.Sheaf.OpenRestriction
open CategoryTheory.Sheaf.Leray.FibreStalkEvaluation

variable {T X : TopCat.{u}} (i : T ⟶ X) (U : Opens X)
  (hU : ∀ t : T, i t ∈ U)

/-- The canonical constant-sheaf morphism for restriction to a literal open subspace. -/
abbrev openConstantRestrictionHom (A : AddCommGrpCat.{u}) :
    TopCat.ConstantSheaf.sheaf (TopCat.of U) A ⟶
      (restriction U).obj (TopCat.ConstantSheaf.sheaf X A) :=
  TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom
    (inclusion U) (inclusion_isOpenEmbedding U) A

/-- On a locally connected open subspace, literal restriction preserves every constant
coefficient sheaf up to the canonical isomorphism. -/
theorem openConstantRestrictionHom_isIso [LocallyConnectedSpace (TopCat.of U)]
    (A : AddCommGrpCat.{u}) : IsIso (openConstantRestrictionHom U A) :=
  TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom_isIso
    (inclusion U) (inclusion_isOpenEmbedding U) A

/-- Restricting an ambient constant sheaf to an open containing the finite source and then
evaluating on that source is the native constant-sheaf morphism for the induced map.  No
injectivity assumption on the original map is needed. -/
theorem openConstantRestriction_coefficient (A : AddCommGrpCat.{u}) :
    openConstantRestrictionHom U A ≫
        (restriction U).map (TopCat.ConstantSheaf.pushforwardHom A i) ≫
        (restrictionPushforwardIso i U hU).hom.app
          (TopCat.ConstantSheaf.sheaf T A) =
      TopCat.ConstantSheaf.pushforwardHom A (induced i U hU) := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology (TopCat.of U)) _ _
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (induced i U hU)).obj
      (TopCat.ConstantSheaf.sheaf T A)).property (by
      apply NatTrans.ext
      funext W
      apply ConcreteCategory.hom_ext
      intro a
      change (((restrictionPushforwardIso i U hU).hom.app
          (TopCat.ConstantSheaf.sheaf T A)).hom.app (op W.unop))
          ((TopCat.ConstantSheaf.pushforwardHom A i).hom.app
            (op ((openImage U).obj W.unop))
            ((openConstantRestrictionHom U A).hom.app (op W.unop)
              ((TopCat.ConstantSheaf.unit (TopCat.of U) A).app (op W.unop) a))) =
        (TopCat.ConstantSheaf.pushforwardHom A (induced i U hU)).hom.app (op W.unop)
          ((TopCat.ConstantSheaf.unit (TopCat.of U) A).app (op W.unop) a)
      let r := (eqToHom (openImage_preimage_obj i U hU W.unop).symm).op
      have hd := (congrArg
        ((TopCat.ConstantSheaf.pushforwardHom A i).hom.app
          (op ((openImage U).obj W.unop)))
        (TopCat.Sheaf.OpenEmbeddingCohomology.restrictionHom_app_unit
          (inclusion U) (inclusion_isOpenEmbedding U) A W.unop a)).trans
            (TopCat.ConstantSheaf.pushforwardHom_app_unit A i
              ((openImage U).obj W.unop) a)
      exact (ConcreteCategory.congr_hom
        (restrictionPushforwardIso_hom_app i U hU
          (TopCat.ConstantSheaf.sheaf T A) W.unop) _).trans
        ((congrArg ((TopCat.ConstantSheaf.sheaf T A).obj.map r) hd).trans
          ((ConcreteCategory.congr_hom
            ((TopCat.ConstantSheaf.unit T A).naturality r) a).symm.trans
              (TopCat.ConstantSheaf.pushforwardHom_app_unit A
                (induced i U hU) W.unop a).symm)))

/-- The normalized class on the literal open subspace represented by an ambient open-cohomology
class. -/
def intrinsicOpenClass [LocallyConnectedSpace (TopCat.of U)]
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : CategoryTheory.Sheaf.H'.{u} (TopCat.ConstantSheaf.sheaf X A) n U) :
    CategoryTheory.Sheaf.H.{u} (TopCat.ConstantSheaf.sheaf (TopCat.of U) A) n :=
  CategoryTheory.Sheaf.H.map
    (inv (openConstantRestrictionHom U A)
      (I := openConstantRestrictionHom_isIso U A)) n
    (cohomologyEquiv U (TopCat.ConstantSheaf.sheaf X A) n x)

/-- Finite-source evaluation followed by global finite-pushforward comparison is the cohomology
map induced by restricting the coefficient morphism to the open, in every degree. -/
theorem cohomologyEvaluation_forward_open
    [T2Space T]
    (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : CategoryTheory.Sheaf.H'.{u} (TopCat.ConstantSheaf.sheaf X A) n U) :
    cohomologyForward (induced i U hU)
        (induced_isClosedMap i U hU hi)
        (induced_finite_fibres i U hU hfinite)
        (TopCat.ConstantSheaf.sheaf T A) n
        (cohomologyEvaluation i hi hfinite
          (TopCat.ConstantSheaf.pushforwardHom A i) U hU n x) =
      CategoryTheory.Sheaf.H.map
        ((restriction U).map (TopCat.ConstantSheaf.pushforwardHom A i) ≫
          (restrictionPushforwardIso i U hU).hom.app
            (TopCat.ConstantSheaf.sheaf T A)) n
        (cohomologyEquiv U (TopCat.ConstantSheaf.sheaf X A) n x) := by
  let iU := induced i U hU
  let hiU := induced_isClosedMap i U hU hi
  let hfinU := induced_finite_fibres i U hU hfinite
  let cT := TopCat.ConstantSheaf.sheaf T A
  let cX := TopCat.ConstantSheaf.sheaf X A
  let k := TopCat.ConstantSheaf.pushforwardHom A i
  let rho := restrictionPushforwardIso i U hU
  let xU := cohomologyEquiv U cX n x
  let a := cohomologyEvaluation i hi hfinite k U hU n x
  have heval : neighborhoodCohomologyForward i U hU hi hfinite cT n a =
      (coefficientMap i k n).app (op U) x := by
    exact neighborhoodCohomologyForward_equiv i U hU hi hfinite cT n
      ((coefficientMap i k n).app (op U) x)
  have hopen := neighborhoodCohomologyForward_openRestriction
    i U hU hi hfinite cT n a
  rw [heval] at hopen
  have hnat := cohomologyEquiv_naturality U k n x
  rw [hnat] at hopen
  exact hopen.symm.trans
    (CategoryTheory.Sheaf.H.map_comp_apply
      ((restriction U).map k) (rho.hom.app cT) xU).symm

/-- Normalizing the ambient open class before applying the induced constant-sheaf morphism gives
the same coefficient map as restriction followed by finite-source evaluation. -/
theorem intrinsicOpenClass_coefficient
    [LocallyConnectedSpace (TopCat.of U)]
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : CategoryTheory.Sheaf.H'.{u} (TopCat.ConstantSheaf.sheaf X A) n U) :
    CategoryTheory.Sheaf.H.map
        ((restriction U).map (TopCat.ConstantSheaf.pushforwardHom A i) ≫
          (restrictionPushforwardIso i U hU).hom.app
            (TopCat.ConstantSheaf.sheaf T A)) n
        (cohomologyEquiv U (TopCat.ConstantSheaf.sheaf X A) n x) =
      CategoryTheory.Sheaf.H.map
        (TopCat.ConstantSheaf.pushforwardHom A (induced i U hU)) n
        (intrinsicOpenClass U A n x) := by
  let cT := TopCat.ConstantSheaf.sheaf T A
  let k := TopCat.ConstantSheaf.pushforwardHom A i
  let kU := TopCat.ConstantSheaf.pushforwardHom A (induced i U hU)
  let e := openConstantRestrictionHom U A
  let rho := restrictionPushforwardIso i U hU
  let xU := cohomologyEquiv U (TopCat.ConstantSheaf.sheaf X A) n x
  let ie : IsIso e := openConstantRestrictionHom_isIso U A
  unfold intrinsicOpenClass
  change CategoryTheory.Sheaf.H.map
      ((restriction U).map k ≫ rho.hom.app cT) n xU =
    CategoryTheory.Sheaf.H.map kU n
      (CategoryTheory.Sheaf.H.map (inv e (I := ie)) n xU)
  have hcoef : e ≫ ((restriction U).map k ≫ rho.hom.app cT) = kU := by
    exact openConstantRestriction_coefficient i U hU A
  have hc : inv e (I := ie) ≫ kU =
      ((restriction U).map k ≫ rho.hom.app cT) := by
    exact (congrArg (fun q ↦ inv e (I := ie) ≫ q) hcoef.symm).trans
      (IsIso.inv_hom_id_assoc e _ (I := ie))
  exact (congrArg (fun q ↦ CategoryTheory.Sheaf.H.map q n xU) hc.symm).trans
    (CategoryTheory.Sheaf.H.map_comp_apply (inv e (I := ie)) kU xU)

/-- The canonical evaluation of an ambient open class on the finite closed source. -/
def canonicalConstantEvaluation
    [T2Space T]
    (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : CategoryTheory.Sheaf.H'.{u} (TopCat.ConstantSheaf.sheaf X A) n U) :
    CategoryTheory.Sheaf.H.{u} (TopCat.ConstantSheaf.sheaf T A) n :=
  cohomologyEvaluation i hi hfinite
    (TopCat.ConstantSheaf.pushforwardHom A i) U hU n x

/-- The same class obtained intrinsically by constant-coefficient pullback along the induced map
to the open subspace. -/
def intrinsicConstantPullback
    [T2Space T] [LocallyConnectedSpace (TopCat.of U)]
    (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : CategoryTheory.Sheaf.H'.{u} (TopCat.ConstantSheaf.sheaf X A) n U) :
    CategoryTheory.Sheaf.H.{u} (TopCat.ConstantSheaf.sheaf T A) n :=
  TopCat.ConstantSheafCohomology.pullback (induced i U hU)
    (induced_isClosedMap i U hU hi)
    (induced_finite_fibres i U hU hfinite) A n
    (intrinsicOpenClass U A n x)

/-- Equality of finite-source classes can be checked after the exact finite-pushforward
comparison. -/
theorem fibreCohomology_eq_of_forward_eq
    [T2Space T]
    (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
    (A : AddCommGrpCat.{u}) (n : ℕ)
    {a b : CategoryTheory.Sheaf.H.{u} (TopCat.ConstantSheaf.sheaf T A) n}
    (hab : cohomologyForward (induced i U hU)
        (induced_isClosedMap i U hU hi)
        (induced_finite_fibres i U hU hfinite)
        (TopCat.ConstantSheaf.sheaf T A) n a =
      cohomologyForward (induced i U hU)
        (induced_isClosedMap i U hU hi)
        (induced_finite_fibres i U hU hfinite)
        (TopCat.ConstantSheaf.sheaf T A) n b) : a = b :=
  (cohomologyForward_bijective (induced i U hU)
    (induced_isClosedMap i U hU hi)
    (induced_finite_fibres i U hU hfinite)
    (TopCat.ConstantSheaf.sheaf T A) n).injective hab

/-- Forward finite pushforward of canonical evaluation is the literal-open coefficient map. -/
theorem canonicalConstantEvaluation_forward
    [T2Space T]
    (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : CategoryTheory.Sheaf.H'.{u} (TopCat.ConstantSheaf.sheaf X A) n U) :
    cohomologyForward (induced i U hU)
        (induced_isClosedMap i U hU hi)
        (induced_finite_fibres i U hU hfinite)
        (TopCat.ConstantSheaf.sheaf T A) n
        (canonicalConstantEvaluation i U hU hi hfinite A n x) =
      CategoryTheory.Sheaf.H.map
        ((restriction U).map (TopCat.ConstantSheaf.pushforwardHom A i) ≫
          (restrictionPushforwardIso i U hU).hom.app
            (TopCat.ConstantSheaf.sheaf T A)) n
        (cohomologyEquiv U (TopCat.ConstantSheaf.sheaf X A) n x) :=
  cohomologyEvaluation_forward_open i U hU hi hfinite A n x

end CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization
