/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.Neighborhood
public import Lib.Topology.Sheaves.FiniteClosedPushforward.Cohomology

/-!
# Finite-source evaluation after restriction to an open

If the image of a map `i : T ⟶ X` lies in an open `U ⊆ X`, then restricting `i_*G` to `U` gives
the pushforward of `G` along the induced map `i' : T ⟶ U`:

`(i_*G)|_U ≅ (i')_*G`.

This is the functoriality of pushforward for the factorisation `i = i' ≫ (U ↪ X)` together with
`(Opens.map i) ∘ (open image of U) = Opens.map i'`; see Hartshorne, *Algebraic Geometry*, II.1
and Godement II.1 for direct images and restriction of sheaves.  It is an elementary composition
statement, not proper base change.

The comparison respects the representing map out of the constant integral sheaf, and hence the
Ext-defined cohomology comparison of `TopCat.FiniteClosedPushforward` in every degree.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

universe u

namespace CategoryTheory.Sheaf.Leray.FibreStalkEvaluation

open TopCat.FiniteClosedPushforward
open TopCat.Sheaf.OpenRestriction

variable {T X : TopCat.{u}} (i : T ⟶ X) (U : Opens X)
  (hU : ∀ t : T, i t ∈ U)

/-- A map whose image lies in `U` as a map to the open subspace. -/
def induced : T ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun t ↦ ⟨i t, hU t⟩, i.hom.continuous.subtype_mk _⟩

/-- The underlying point of `induced i U hU t` in `X` is `i t`. -/
@[simp]
theorem induced_apply (t : T) : (induced i U hU t).1 = i t := rfl

/-- The induced map followed by inclusion is the original map. -/
theorem induced_comp_inclusion :
    induced i U hU ≫ inclusion U = i := rfl

/-- Closedness passes to the induced map into an open containing the image. -/
theorem induced_isClosedMap (hi : IsClosedMap i) :
    IsClosedMap (induced i U hU) :=
  hi.subtype_mk hU

/-- Finite fibres pass to the induced map into an open containing the image. -/
theorem induced_finite_fibres
    (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
    (u : U) : ((induced i U hU) ⁻¹' ({u} : Set U)).Finite := by
  apply (hfinite u.1).subset
  intro t ht
  exact congrArg Subtype.val ht

/-- On each open of `U`, pushforward along `i` after open restriction and pushforward along the
induced map have the same inverse-image open. -/
theorem openImage_preimage_obj (W : Opens U) :
    ((openImage U ⋙ Opens.map i).obj W) =
      (Opens.map (induced i U hU)).obj W := by
  ext t
  constructor
  · rintro ⟨u, hu, hut⟩
    have hueq : u = induced i U hU t := Subtype.ext hut
    simpa [hueq] using hu
  · intro ht
    exact ⟨induced i U hU t, ht, rfl⟩

/-- Functorial form of `openImage_preimage_obj`. -/
theorem openImage_preimage :
    openImage U ⋙ Opens.map i = Opens.map (induced i U hU) :=
  CategoryTheory.Functor.ext (openImage_preimage_obj i U hU)
    (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- Restricting the pushforward of `i` to `U` is pushforward along the induced map into `U`. -/
def restrictionPushforwardIso :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} i ⋙ restriction U ≅
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} (induced i U hU) := by
  let _ : (Opens.map (induced i U hU)).IsContinuous
      (Opens.grothendieckTopology (TopCat.of U))
      (Opens.grothendieckTopology T) := by
    exact CategoryTheory.Functor.isContinuous_of_coverPreserving
      (compatiblePreserving_opens_map (induced i U hU))
      (coverPreserving_opens_map (induced i U hU))
  exact CategoryTheory.Functor.sheafPushforwardContinuousComp'
    (eqToIso (openImage_preimage i U hU)) AddCommGrpCat
    (Opens.grothendieckTopology (TopCat.of U))
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology T)

/-- On the open `W ⊆ U`, the comparison `(i_*G)|_U ≅ (i')_*G` is the restriction map of `G`
along the equality of inverse images `openImage_preimage_obj`. -/
@[simp]
theorem restrictionPushforwardIso_hom_app
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (W : Opens U) :
    (((restrictionPushforwardIso i U hU).hom.app F).hom.app (op W)) =
      F.obj.map (eqToHom (openImage_preimage_obj i U hU W).symm).op := by
  let _ : (Opens.map (induced i U hU)).IsContinuous
      (Opens.grothendieckTopology (TopCat.of U))
      (Opens.grothendieckTopology T) := by
    exact CategoryTheory.Functor.isContinuous_of_coverPreserving
      (compatiblePreserving_opens_map (induced i U hU))
      (coverPreserving_opens_map (induced i U hU))
  exact (CategoryTheory.Functor.sheafPushforwardContinuousComp'_hom_app_hom_app
    (eqToIso (openImage_preimage i U hU)) AddCommGrpCat
    (Opens.grothendieckTopology (TopCat.of U))
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology T) F (op W)).trans
      (congrArg F.obj.map (Subsingleton.elim _ _))

/-- On global sections, the pushforward-restriction isomorphism is the evident source-global
section comparison. -/
theorem restrictionPushforwardIso_global
    (G : TopCat.Sheaf AddCommGrpCat.{u} T)
    (s : ((restriction U).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G)).obj.obj
        (op (⊤ : Opens U))) :
    ((restrictionPushforwardIso i U hU).hom.app G).hom.app
        (op (⊤ : Opens U)) s =
      sectionsEquiv i U hU G
        (restrictionGlobalEquiv U
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) s) := by
  rw [restrictionPushforwardIso_hom_app]
  simp only [sectionsEquiv, restrictionGlobalEquiv]
  let fd := (eqToHom
    (openImage_preimage_obj i U hU (⊤ : Opens U)).symm).op
  let fr := (Opens.map i).op.map
    (eqToIso (congrArg op (openImage_top U))).hom
  let fs := (eqToIso (congrArg op (inverseImage_eq_top i U hU))).hom
  let P : CategoryTheory.Functor (Opposite (Opens T)) AddCommGrpCat := G.obj
  let s' : P.obj (op ((openImage U ⋙ Opens.map i).obj ⊤)) := s
  change (P.map fd) s' = (P.map fs) ((P.map fr) s')
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg P.map (Subsingleton.elim fd (fr ≫ fs))) s

/-- The representing endpoint obtained by neighborhood evaluation and open restriction is the
native integral constant-sheaf pushforward endpoint for the induced map. -/
theorem restrictionPushforwardIso_neighborhoodUnit :
    representingUnit U ≫
        (restriction U).map (neighborhoodUnit i U hU) ≫
        (restrictionPushforwardIso i U hU).hom.app
          (TopCat.ConstantSheaf.integralSheaf T) =
      TopCat.ConstantSheaf.pushforwardHom
        (AddCommGrpCat.of (ULift.{u} ℤ)) (induced i U hU) := by
  apply (TopCat.ConstantSheaf.integralHomGlobalEquiv (TopCat.of U)
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (induced i U hU)).obj
      (TopCat.ConstantSheaf.integralSheaf T))).injective
  rw [← Category.assoc, representingUnit_comp,
    TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality]
  rw [restrictionPushforwardIso_global, homRestrictionEquiv_sections]
  rw [TopCat.ConstantSheaf.integralPushforwardHom_global]
  exact neighborhoodHomEquiv_sections i U hU
    (TopCat.ConstantSheaf.integralSheaf T) (𝟙 _)

variable [T2Space T] (hi : IsClosedMap i)
  (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)

/-- Neighborhood cohomology followed by genuine open restriction agrees with the global
finite-closed comparison for the induced map, in every degree. -/
theorem neighborhoodCohomologyForward_openRestriction
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{u} F n) :
    CategoryTheory.Sheaf.H.map
        ((restrictionPushforwardIso i U hU).hom.app F) n
      (cohomologyEquiv U
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F) n
        (neighborhoodCohomologyForward i U hU hi hfinite F n a)) =
      TopCat.FiniteClosedPushforward.cohomologyForward
        (induced i U hU) (induced_isClosedMap i U hU hi)
        (induced_finite_fibres i U hU hfinite) F n a := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits i hi hfinite).1
  let _ := pushforward_preservesFiniteColimits i hi hfinite
  let hiU := induced_isClosedMap i U hU hi
  let hfinU := induced_finite_fibres i U hU hfinite
  let _ := (pushforward_preservesFiniteLimitsAndColimits
    (induced i U hU) hiU hfinU).1
  let _ := pushforward_preservesFiniteColimits (induced i U hU) hiU hfinU
  exact @Ext.ExactFunctorComparison.comp_natTrans
    (TopCat.Sheaf AddCommGrpCat.{u} T) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of U)) _ _
      (IsGrothendieckAbelian.hasExt _)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)
    (TopCat.Sheaf.pushforwardAdditive i)
    (pushforward_preservesFiniteLimitsAndColimits i hi hfinite).1
    (pushforward_preservesFiniteColimits i hi hfinite)
    (restriction U) (restriction_additive U)
    (restriction_preservesFiniteLimits U) (restriction_preservesFiniteColimits U)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (induced i U hU))
    (TopCat.Sheaf.pushforwardAdditive (induced i U hU))
    (pushforward_preservesFiniteLimitsAndColimits
      (induced i U hU) hiU hfinU).1
    (pushforward_preservesFiniteColimits (induced i U hU) hiU hfinU)
    (restrictionPushforwardIso i U hU).hom inferInstance
    (TopCat.ConstantSheaf.integralSheaf T) F
    (freeOpen U) (TopCat.ConstantSheaf.integralSheaf (TopCat.of U))
    (neighborhoodUnit i U hU) (representingUnit U)
    (TopCat.ConstantSheaf.pushforwardHom
      (AddCommGrpCat.of (ULift.{u} ℤ)) (induced i U hU))
    (restrictionPushforwardIso_neighborhoodUnit i U hU) n a

end CategoryTheory.Sheaf.Leray.FibreStalkEvaluation
