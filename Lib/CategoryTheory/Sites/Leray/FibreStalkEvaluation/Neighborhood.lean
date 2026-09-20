/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.ConstantPushforward.GlobalSections
public import Lib.Topology.Sheaves.Cohomology.AddCommGroup
public import Lib.Topology.Sheaves.FiniteClosedPushforward.Exact
public import Lib.Topology.Sheaves.OpenRestriction.Cohomology
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Cohomology evaluation on finite closed neighborhoods

For a finite-fibre closed map whose image lies in an ambient open, this module compares
Mathlib's native Ext cohomology on that neighborhood with native sheaf cohomology on the
source. It proves both orientations of nested-open compatibility and constructs the resulting
coefficient evaluation. No proper-base-change or geometric local-triviality assertion is made.

The underlying textbook fact is that a finite (more generally proper) map `i : T ⟶ X` has
exact pushforward, so `Hⁿ(U, i_*G) ≅ Hⁿ(T, G)` whenever `i(T) ⊆ U`: Bredon, *Sheaf Theory*
II.9–II.11; Iversen, *Cohomology of Sheaves* II; Godement II.4.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace CategoryTheory.Sheaf.Leray.FibreStalkEvaluation

open TopCat.FiniteClosedPushforward
open TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{u}}

/-- The free-open sheaves appearing in Mathlib's cohomology presheaf, functorially in the open. -/
abbrev freeOpenFunctor (X : TopCat.{u}) :
    Opens X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat

section Neighborhood

variable {T X : TopCat.{u}} (i : T ⟶ X) (U : Opens X)
  (hU : ∀ t : T, i t ∈ U)

include hU in
/-- An open containing the image of `i` has whole-source inverse image. -/
theorem inverseImage_eq_top : (Opens.map i).obj U = ⊤ := by
  ext t
  constructor
  · intro _
    trivial
  · intro _
    exact hU t

/-- Sections of a pushforward on a neighborhood containing the image are global source
sections. -/
def sectionsEquiv (G : TopCat.Sheaf AddCommGrpCat.{u} T) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G).obj.obj (op U) ≃+ G.obj.obj (op (⊤ : Opens T)) :=
  (G.obj.mapIso (eqToIso (congrArg op (inverseImage_eq_top i U hU)))).addCommGroupIsoToAddEquiv

/-- The section comparison is natural in the coefficient sheaf. -/
theorem sectionsEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} T} (g : F ⟶ G)
    (s : ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F).obj.obj (op U)) :
    sectionsEquiv i U hU G (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map g).hom.app (op U) s) =
      g.hom.app (op (⊤ : Opens T)) (sectionsEquiv i U hU F s) := by
  change G.obj.map (eqToHom (congrArg op (inverseImage_eq_top i U hU)))
      (g.hom.app (op ((Opens.map i).obj U)) s) =
    g.hom.app (op (⊤ : Opens T))
      (F.obj.map (eqToHom (congrArg op (inverseImage_eq_top i U hU))) s)
  exact (g.hom.naturality_apply
    (eqToHom (congrArg op (inverseImage_eq_top i U hU))) s).symm

/-- The two representing objects give the canonical neighborhood morphism comparison. -/
def neighborhoodHomEquiv (G : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (TopCat.ConstantSheaf.integralSheaf T ⟶ G) ≃
      (freeOpen U ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) :=
  (TopCat.ConstantSheaf.integralHomGlobalEquiv T G).toEquiv.trans
    ((sectionsEquiv i U hU G).toEquiv.symm.trans
      (freeHomEquiv U ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G)).symm)

/-- The neighborhood morphism comparison preserves its represented section. -/
theorem neighborhoodHomEquiv_sections (G : TopCat.Sheaf AddCommGrpCat.{u} T)
    (a : TopCat.ConstantSheaf.integralSheaf T ⟶ G) :
    sectionsEquiv i U hU G
      (freeHomEquiv U ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) (neighborhoodHomEquiv i U hU G a)) =
        TopCat.ConstantSheaf.integralHomGlobalEquiv T G a := by
  change sectionsEquiv i U hU G
    (freeHomEquiv U ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G)
      ((freeHomEquiv U ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G)).symm
        ((sectionsEquiv i U hU G).symm
          (TopCat.ConstantSheaf.integralHomGlobalEquiv T G a)))) = _
  rw [Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Naturality of the neighborhood morphism comparison. -/
theorem neighborhoodHomEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} T}
    (a : TopCat.ConstantSheaf.integralSheaf T ⟶ F) (g : F ⟶ G) :
    neighborhoodHomEquiv i U hU G (a ≫ g) =
      neighborhoodHomEquiv i U hU F a ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map g := by
  apply (freeHomEquiv U ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G)).injective
  apply (sectionsEquiv i U hU G).injective
  rw [neighborhoodHomEquiv_sections, freeHomEquiv_naturality,
    sectionsEquiv_naturality, neighborhoodHomEquiv_sections]
  exact TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality T a g

/-- The canonical endpoint from the represented open to the pushed integral sheaf. -/
def neighborhoodUnit :
    freeOpen U ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj (TopCat.ConstantSheaf.integralSheaf T) :=
  neighborhoodHomEquiv i U hU (TopCat.ConstantSheaf.integralSheaf T) (𝟙 _)

/-- Postcomposition by the neighborhood endpoint is the representing-object comparison. -/
theorem neighborhoodUnit_comp {G : TopCat.Sheaf AddCommGrpCat.{u} T}
    (a : TopCat.ConstantSheaf.integralSheaf T ⟶ G) :
    neighborhoodUnit i U hU ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map a =
      neighborhoodHomEquiv i U hU G a :=
  (neighborhoodHomEquiv_naturality i U hU (𝟙 _) a).symm.trans
    (congrArg (neighborhoodHomEquiv i U hU G) (Category.id_comp a))

/-- The degree-zero comparison represented by `neighborhoodUnit` is bijective. -/
theorem neighborhoodUnit_bijective (G : TopCat.Sheaf AddCommGrpCat.{u} T) :
    Function.Bijective (fun a : TopCat.ConstantSheaf.integralSheaf T ⟶ G ↦
      neighborhoodUnit i U hU ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map a) := by
  have he : (fun a : TopCat.ConstantSheaf.integralSheaf T ⟶ G ↦
      neighborhoodUnit i U hU ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map a) =
      neighborhoodHomEquiv i U hU G := funext (neighborhoodUnit_comp i U hU)
  rw [he]
  exact (neighborhoodHomEquiv i U hU G).bijective

variable [T2Space T] (hi : IsClosedMap i)
  (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)

/-- The exact finite-pushforward comparison from global source cohomology to neighborhood
cohomology. -/
def neighborhoodCohomologyForward (G : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} G n →+
      CategoryTheory.Sheaf.H'.{u} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n U := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits i hi hfinite).1
  let _ := pushforward_preservesFiniteColimits i hi hfinite
  exact Ext.ExactFunctorComparison.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i) (neighborhoodUnit i U hU) G n

/-- The neighborhood comparison is bijective in every degree. -/
theorem neighborhoodCohomologyForward_bijective (G : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ) :
    Function.Bijective (neighborhoodCohomologyForward i U hU hi hfinite G n) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits i hi hfinite).1
  let _ := pushforward_preservesFiniteColimits i hi hfinite
  let _ := pushforward_preservesInjectiveObjects i
  exact Ext.ExactFunctorComparison.map_bijective (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)
    (neighborhoodUnit i U hU) (neighborhoodUnit_bijective i U hU) G n

/-- Neighborhood cohomology of a finite closed pushforward is canonically source cohomology. -/
def neighborhoodCohomologyEquiv (G : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{u} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n U ≃+
      CategoryTheory.Sheaf.H.{u} G n :=
  (AddEquiv.ofBijective (neighborhoodCohomologyForward i U hU hi hfinite G n)
    (neighborhoodCohomologyForward_bijective i U hU hi hfinite G n)).symm

/-- The inverse of `neighborhoodCohomologyEquiv` *is* the forward comparison
`Hⁿ(T, G) → H'ⁿ(U, i_*G)`: the equivalence is that comparison, made into an `AddEquiv` by its
bijectivity and then reversed. -/
@[simp] theorem neighborhoodCohomologyEquiv_symm_apply (G : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{u} G n) :
    (neighborhoodCohomologyEquiv i U hU hi hfinite G n).symm a =
      neighborhoodCohomologyForward i U hU hi hfinite G n a := rfl

/-- Forward comparison after its inverse recovers the neighborhood class. -/
theorem neighborhoodCohomologyForward_equiv (G : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{u} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n U) :
    neighborhoodCohomologyForward i U hU hi hfinite G n
      (neighborhoodCohomologyEquiv i U hU hi hfinite G n a) = a :=
  (neighborhoodCohomologyEquiv i U hU hi hfinite G n).symm_apply_apply a

end Neighborhood

section Restriction

private theorem comparison_precompose
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [HasExt.{u} C] [HasExt.{u} D] {Z : C} {A A' : D}
    (η : A ⟶ R.obj Z) (η' : A' ⟶ R.obj Z) (r : A' ⟶ A) (hr : r ≫ η = η')
    (G : C) (n : ℕ) (a : Ext.{u} Z G n) :
    (Ext.mk₀ r).comp (Ext.ExactFunctorComparison.map R η G n a) (zero_add n) =
      Ext.ExactFunctorComparison.map R η' G n a := by
  subst η'
  exact Ext.mk₀_comp_mk₀_assoc r η (a.mapExactFunctor R)

variable {T X : TopCat.{u}} (i : T ⟶ X) {U V : Opens X} (r : U ⟶ V)
  (hU : ∀ t : T, i t ∈ U) (hV : ∀ t : T, i t ∈ V)

/-- Restriction of pushforward sections becomes the identity on global source sections. -/
theorem sectionsEquiv_restrict (G : TopCat.Sheaf AddCommGrpCat.{u} T)
    (s : ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G).obj.obj (op V)) :
    sectionsEquiv i U hU G (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G).obj.map r.op s) =
      sectionsEquiv i V hV G s := by
  change G.obj.map (eqToHom (congrArg op (inverseImage_eq_top i U hU)))
      (G.obj.map ((Opens.map i).map r).op s) =
    G.obj.map (eqToHom (congrArg op (inverseImage_eq_top i V hV))) s
  have he : G.obj.map ((Opens.map i).map r).op ≫
      G.obj.map (eqToHom (congrArg op (inverseImage_eq_top i U hU))) =
        G.obj.map (eqToHom (congrArg op (inverseImage_eq_top i V hV))) :=
    (G.obj.map_comp _ _).symm.trans (congrArg G.obj.map (Subsingleton.elim _ _))
  exact ConcreteCategory.congr_hom he s

/-- The neighborhood representing morphism commutes with restriction. -/
theorem neighborhoodHomEquiv_restrict (G : TopCat.Sheaf AddCommGrpCat.{u} T)
    (a : TopCat.ConstantSheaf.integralSheaf T ⟶ G) :
    (freeOpenFunctor X).map r ≫ neighborhoodHomEquiv i V hV G a =
      neighborhoodHomEquiv i U hU G a := by
  apply (freeHomEquiv U ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G)).injective
  apply (sectionsEquiv i U hU G).injective
  have hfree :
      freeHomEquiv U ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G)
          ((freeOpenFunctor X).map r ≫ neighborhoodHomEquiv i V hV G a) =
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G).obj.map r.op
          (freeHomEquiv V ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G)
            (neighborhoodHomEquiv i V hV G a)) := by
    exact TopCat.Sheaf.OpenRestriction.freeHomEquiv_naturality_open r _ _
  rw [hfree, sectionsEquiv_restrict i r hU hV,
    neighborhoodHomEquiv_sections i V hV,
    neighborhoodHomEquiv_sections i U hU]

/-- The canonical neighborhood endpoints commute with restriction. -/
theorem neighborhoodUnit_restrict :
    (freeOpenFunctor X).map r ≫ neighborhoodUnit i V hV =
      neighborhoodUnit i U hU :=
  neighborhoodHomEquiv_restrict i r hU hV
    (TopCat.ConstantSheaf.integralSheaf T) (𝟙 _)

variable [T2Space T] (hi : IsClosedMap i)
  (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)

/-- The forward Ext comparison intertwines neighborhood restriction. -/
theorem neighborhoodCohomologyForward_restrict (G : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{u} G n) :
    (CategoryTheory.Sheaf.cohomologyPresheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n).map r.op
      (neighborhoodCohomologyForward i V hV hi hfinite G n a) =
        neighborhoodCohomologyForward i U hU hi hfinite G n a := by
  exact @comparison_precompose
    (TopCat.Sheaf AddCommGrpCat.{u} T) (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ _ _
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i) (TopCat.Sheaf.pushforwardAdditive i)
    (pushforward_preservesFiniteLimitsAndColimits i hi hfinite).1
    (pushforward_preservesFiniteColimits i hi hfinite)
    (IsGrothendieckAbelian.hasExt _) (IsGrothendieckAbelian.hasExt _)
    (TopCat.ConstantSheaf.integralSheaf T) (freeOpen V) (freeOpen U)
    (neighborhoodUnit i V hV) (neighborhoodUnit i U hU)
    ((freeOpenFunctor X).map r) (neighborhoodUnit_restrict i r hU hV)
    G n a

/-- The inverse neighborhood comparison is independent of shrinking. -/
theorem neighborhoodCohomologyEquiv_restrict (G : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{u} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n V) :
    neighborhoodCohomologyEquiv i U hU hi hfinite G n
      ((CategoryTheory.Sheaf.cohomologyPresheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n).map r.op a) =
        neighborhoodCohomologyEquiv i V hV hi hfinite G n a := by
  obtain ⟨b, rfl⟩ := (neighborhoodCohomologyForward_bijective i V hV hi hfinite G n).surjective a
  rw [neighborhoodCohomologyForward_restrict]
  exact (neighborhoodCohomologyEquiv i U hU hi hfinite G n).apply_symm_apply b |>.trans
    ((neighborhoodCohomologyEquiv i V hV hi hfinite G n).apply_symm_apply b).symm

end Restriction

section Evaluation

variable {T X : TopCat.{u}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
  {F : TopCat.Sheaf AddCommGrpCat.{u} X} {G : TopCat.Sheaf AddCommGrpCat.{u} T} (κ : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G)

/-- The coefficient map on Mathlib's native cohomology presheaves. -/
abbrev coefficientMap (n : ℕ) :
    CategoryTheory.Sheaf.cohomologyPresheaf F n ⟶
      CategoryTheory.Sheaf.cohomologyPresheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) n :=
  (CategoryTheory.Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology X) n).map κ

/-- Restriction of a neighborhood class to the finite closed source. -/
def cohomologyEvaluation (U : Opens X) (hU : ∀ t : T, i t ∈ U) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{u} F n U →+ CategoryTheory.Sheaf.H.{u} G n :=
  (neighborhoodCohomologyEquiv i U hU hi hfinite G n).toAddMonoidHom.comp
    ((coefficientMap i κ n).app (op U)).hom

/-- `cohomologyEvaluation` is the coefficient map `κ : F ⟶ i_*G` in degree `n` on the
neighborhood `U`, followed by the comparison isomorphism `H'ⁿ(U, i_*G) ≅ Hⁿ(T, G)`. -/
@[simp] theorem cohomologyEvaluation_apply (U : Opens X) (hU : ∀ t : T, i t ∈ U)
    (n : ℕ) (a : CategoryTheory.Sheaf.H'.{u} F n U) :
    cohomologyEvaluation i hi hfinite κ U hU n a =
      neighborhoodCohomologyEquiv i U hU hi hfinite G n ((coefficientMap i κ n).app (op U) a) := rfl

/-- Fibre evaluation commutes with restriction of neighborhoods. -/
theorem cohomologyEvaluation_restrict {U V : Opens X} (r : U ⟶ V)
    (hU : ∀ t : T, i t ∈ U) (hV : ∀ t : T, i t ∈ V)
    (n : ℕ) (a : CategoryTheory.Sheaf.H'.{u} F n V) :
    cohomologyEvaluation i hi hfinite κ U hU n
      ((CategoryTheory.Sheaf.cohomologyPresheaf F n).map r.op a) =
        cohomologyEvaluation i hi hfinite κ V hV n a := by
  have he := (coefficientMap i κ n).naturality_apply r.op a
  exact (congrArg (neighborhoodCohomologyEquiv i U hU hi hfinite G n) he).trans
    (neighborhoodCohomologyEquiv_restrict i r hU hV hi hfinite G n
      ((coefficientMap i κ n).app (op V) a))

end Evaluation

end CategoryTheory.Sheaf.Leray.FibreStalkEvaluation
