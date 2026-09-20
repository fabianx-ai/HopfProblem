/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.ProjectiveDimension
public import Lib.Topology.Sheaves.OpenRestriction.Cohomology

/-!
# Projective dimension of represented opens

The free additive sheaf represented by an ambient open `U` computes sheaf cohomology after
restriction to `U`.  Consequently its projective-dimension bound is equivalent to uniform
vanishing in the first requested degree.  The represented top open is canonically isomorphic to
the integral unit sheaf, connecting open-cover arguments to ordinary global sheaf cohomology.

The represented sheaf `ℤ[U]` satisfies `Ext^n(ℤ[U], F) ≅ H^n(U, F)`; see Godement, *Topologie
algébrique et théorie des faisceaux*, II.4, and Hartshorne, *Algebraic Geometry*, III.2.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf.OpenRestriction

/-- The universal integral section regarded as a map to the free sheaf represented by the top
open. -/
def integralToFreeTop (X : TopCat.{u}) :
    TopCat.SheafH1.unitSheaf X ⟶ freeOpen (⊤ : Opens X) :=
  (TopCat.ConstantSheaf.integralHomGlobalEquiv X (freeOpen (⊤ : Opens X))).symm
    (freeHomEquiv (⊤ : Opens X) (freeOpen (⊤ : Opens X)) (𝟙 _))

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition by `integralToFreeTop` identifies the two representations of a global
section. -/
theorem integralToFreeTop_comp_section (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (g : freeOpen (⊤ : Opens X) ⟶ F) :
    TopCat.ConstantSheaf.integralHomGlobalEquiv X F (integralToFreeTop X ≫ g) =
      freeHomEquiv (⊤ : Opens X) F g := by
  rw [TopCat.ConstantSheaf.integralHomGlobalEquiv_naturality]
  simp only [integralToFreeTop, AddEquiv.apply_symm_apply]
  rw [← freeHomEquiv_naturality]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition by `integralToFreeTop` is bijective on every target Hom-set. -/
theorem integralToFreeTop_comp_bijective (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Bijective
      (fun g : freeOpen (⊤ : Opens X) ⟶ F ↦ integralToFreeTop X ≫ g) := by
  constructor
  · intro a b hab
    apply (freeHomEquiv (⊤ : Opens X) F).injective
    calc
      freeHomEquiv (⊤ : Opens X) F a =
          TopCat.ConstantSheaf.integralHomGlobalEquiv X F (integralToFreeTop X ≫ a) :=
        (integralToFreeTop_comp_section X F a).symm
      _ = TopCat.ConstantSheaf.integralHomGlobalEquiv X F (integralToFreeTop X ≫ b) :=
        congrArg (TopCat.ConstantSheaf.integralHomGlobalEquiv X F) hab
      _ = freeHomEquiv (⊤ : Opens X) F b :=
        integralToFreeTop_comp_section X F b
  · intro q
    obtain ⟨g, hg⟩ := (freeHomEquiv (⊤ : Opens X) F).surjective
      (TopCat.ConstantSheaf.integralHomGlobalEquiv X F q)
    refine ⟨g, (TopCat.ConstantSheaf.integralHomGlobalEquiv X F).injective ?_⟩
    exact (integralToFreeTop_comp_section X F g).trans hg

set_option backward.isDefEq.respectTransparency false in
/-- The integral unit sheaf is the free additive sheaf represented by the top open. -/
def unitFreeTopIso (X : TopCat.{u}) :
    TopCat.SheafH1.unitSheaf X ≅ freeOpen (⊤ : Opens X) := by
  let e := integralToFreeTop X
  letI : IsIso e := isIso_of_coyoneda_map_bijective e
    (integralToFreeTop_comp_bijective X)
  exact asIso e

/-- Projective dimension of a represented open is equivalent to uniform vanishing, in the
first requested degree, of cohomology after restriction to that open. -/
theorem freeOpen_hasProjectiveDimensionLT_iff (X : TopCat.{u})
    (U : Opens X) (n : ℕ) :
    HasProjectiveDimensionLT (freeOpen U) n ↔
      ∀ F : TopCat.Sheaf AddCommGrpCat.{u} X,
        Subsingleton (restrictedCohomologyGroup U F n) := by
  constructor
  · intro h F
    let _ : HasProjectiveDimensionLT (freeOpen U) n := h
    exact (cohomologyEquiv U F n).toEquiv.subsingleton_congr.mp
      (HasProjectiveDimensionLT.subsingleton (freeOpen U) n n (le_refl n) F)
  · intro h
    apply hasProjectiveDimensionLT_of_enoughInjectives (freeOpen U) n
    intro F
    exact (cohomologyEquiv U F n).toEquiv.subsingleton_congr.mpr (h F)

/-- A projective-dimension bound for the global unit sheaf is equivalent to the same bound for
the sheaf represented by the top open. -/
theorem unitSheaf_hasProjectiveDimensionLT_iff_freeOpen_top (X : TopCat.{u}) (n : ℕ) :
    HasProjectiveDimensionLT (TopCat.SheafH1.unitSheaf X) n ↔
      HasProjectiveDimensionLT (freeOpen (⊤ : Opens X)) n := by
  constructor
  · intro h
    let _ := h
    exact hasProjectiveDimensionLT_of_iso (unitFreeTopIso X) n
  · intro h
    let _ := h
    exact hasProjectiveDimensionLT_of_iso (unitFreeTopIso X).symm n

end TopCat.Sheaf.OpenRestriction
