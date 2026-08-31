/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolutionH1Naturality
public import Lib.Topology.Sheaves.Cohomology.AcyclicResolutionH1

/-!
# Naturality of the sheaf H¹ acyclic-resolution comparison
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace TopCat.SheafH1.AcyclicResolutionH1

private theorem composition_naturality {C : Type*} [Category C]
    {A B D A' B' D' : C}
    (a : A ⟶ B) (b : B ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ D')
    (x : A ⟶ A') (y : B ⟶ B') (z : D ⟶ D')
    (ha : x ≫ a' = a ≫ y) (hb : y ≫ b' = b ≫ z) :
    x ≫ (a' ≫ b') = (a ≫ b) ≫ z := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

variable {X : TopCat.{0}}
  {R S : CategoryTheory.Abelian.Ext.AcyclicResolutionH1
    (C := TopCat.Sheaf AddCommGrpCat.{0} X)}

namespace Hom

variable (φ : CategoryTheory.Abelian.Ext.AcyclicResolutionH1.Hom R S)

/-- The map of literal global-section complexes. -/
def globalMap : globalComplex R ⟶ globalComplex S :=
  (globalSectionsFunctor X).mapShortComplex.map φ.complex

theorem extZeroGlobalIso_naturality :
    φ.extZeroMap (unitSheaf X) ≫ (extZeroGlobalIso S).hom =
      (extZeroGlobalIso R).hom ≫ globalMap φ := by
  apply ShortComplex.hom_ext
  · exact h0GlobalIso_naturality φ.complex.τ₁
  · exact h0GlobalIso_naturality φ.complex.τ₂
  · exact h0GlobalIso_naturality φ.complex.τ₃

/-- The sheaf H¹/global-section comparison commutes with every augmented-resolution map. -/
theorem h1GlobalIso_naturality
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)] :
    (CategoryTheory.Sheaf.functorH _ 1).map φ.augmentation ≫ (h1GlobalIso S).hom =
      (h1GlobalIso R).hom ≫ ShortComplex.homologyMap (globalMap φ) := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) S.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)›
  change (extFunctorObj (unitSheaf X) 1).map φ.augmentation ≫
      ((S.extOneIso (unitSheaf X)).hom ≫
        ShortComplex.homologyMap (extZeroGlobalIso S).hom) =
    ((R.extOneIso (unitSheaf X)).hom ≫
      ShortComplex.homologyMap (extZeroGlobalIso R).hom) ≫
        ShortComplex.homologyMap (globalMap φ)
  refine composition_naturality
    (R.extOneIso (unitSheaf X)).hom
    (ShortComplex.homologyMap (extZeroGlobalIso R).hom)
    (S.extOneIso (unitSheaf X)).hom
    (ShortComplex.homologyMap (extZeroGlobalIso S).hom)
    ((extFunctorObj (unitSheaf X) 1).map φ.augmentation)
    (ShortComplex.homologyMap (φ.extZeroMap (unitSheaf X)))
    (ShortComplex.homologyMap (globalMap φ))
    (φ.extOneIso_naturality (unitSheaf X)) ?_
  have hmap :
      ShortComplex.homologyMap
          (φ.extZeroMap (unitSheaf X) ≫ (extZeroGlobalIso S).hom) =
          ShortComplex.homologyMap ((extZeroGlobalIso R).hom ≫ globalMap φ) :=
    congrArg (fun k => ShortComplex.homologyMap k) (extZeroGlobalIso_naturality φ)
  exact ((ShortComplex.homologyMap_comp
    (φ.extZeroMap (unitSheaf X)) (extZeroGlobalIso S).hom).symm.trans hmap).trans
      (ShortComplex.homologyMap_comp (extZeroGlobalIso R).hom (globalMap φ))

end Hom

end TopCat.SheafH1.AcyclicResolutionH1
