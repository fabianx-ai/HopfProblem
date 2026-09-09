module
public import Lib.Topology.Sheaves.Cohomology.Cech.Ext
public import Lib.Topology.Sheaves.Cohomology.DerivedGlobalSections

/-!
# The fixed Ext factorization of the normalized Čech comparison

For a paracompact Hausdorff space and arbitrary abelian sheaf coefficients, compose
the fixed Čech-to-Ext morphism with the fixed Ext-to-derived-global-sections morphism.
Its inverse is the fixed reverse Ext comparison after the inverse model morphism.
Both composites are identity delta morphisms. The whole degree-zero transformation
is the Čech gluing identification followed by the inverse derived normalization,
using the same intervening Ext evaluation. Čech-source universality identifies
any comparison with this normalization with that fixed composite (textbook M13,
lines 1864–1878, C29i). C30 is the forward name of this characterization; the later
original two-source construction is not a premise here.

The construction of Ext, its effacement, and its fixed isomorphism with derived
global sections use only their earlier injective-resolution and constant-sheaf
adjunction inputs, independently of the Čech comparison. This file applies those
already constructed maps; it does not select a replacement model isomorphism by
universality or impose Čech hypotheses on their arbitrary-space construction.
-/

public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace
open TopCat.SheafCohomology
open TopologicalSpace.OpenCover.SetOpenCover
variable (X : TopCat.{u}) [ParacompactSpace X] [T2Space X]
local instance : HasExt.{u}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives.{u,u,u+1} _

namespace TopologicalSpace.OpenCover.SetOpenCover

/-- The fixed Čech-to-derived-sections morphism is α followed by Φ. Composition
retains coefficient naturality and every original positive connecting square
(textbook M13, C29i). -/
def cechDerivedGlobalSectionsHom : CategoryTheory.CohomologicalDeltaFunctor.Hom
    (cechCohomologyDeltaFunctor X) (derivedGlobalSectionsDeltaFunctor X) :=
  CategoryTheory.CohomologicalDeltaFunctor.Hom.comp
    (cechCohomologyToExt X) (extDerivedGlobalSectionsHom X)

/-- The reverse fixed morphism is Φ inverse followed by β, with the same natural
coefficient maps and positive connecting compatibility (textbook M13, C29i). -/
def cechDerivedGlobalSectionsInv : CategoryTheory.CohomologicalDeltaFunctor.Hom
    (derivedGlobalSectionsDeltaFunctor X) (cechCohomologyDeltaFunctor X) :=
  CategoryTheory.CohomologicalDeltaFunctor.Hom.comp
    (extDerivedGlobalSectionsInv X) (extToCechCohomology X)

/-- Every whole degree natural transformation factors through the same α and Φ,
not through independently chosen component isomorphisms (textbook M13, C29i). -/
theorem cechDerivedGlobalSectionsHom_app (n : ℕ) :
    (cechDerivedGlobalSectionsHom X).app n =
      (cechCohomologyToExt X).app n ≫
        (extFunctorObjIsoDerivedGlobalSections X n).hom := by
  unfold cechDerivedGlobalSectionsHom
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    extDerivedGlobalSectionsHom_app]

/-- The whole reverse degree transformation is the inverse fixed model map
followed by the fixed Ext-to-Čech map (textbook M13, C29i). -/
theorem cechDerivedGlobalSectionsInv_app (n : ℕ) :
    (cechDerivedGlobalSectionsInv X).app n =
      (extFunctorObjIsoDerivedGlobalSections X n).inv ≫
        (extToCechCohomology X).app n := by
  unfold cechDerivedGlobalSectionsInv
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    extDerivedGlobalSectionsInv_app]
  rfl

/-- Forward followed by reverse is the identity on Čech as a whole delta morphism.
First cancel Φ followed by its inverse on Ext, then α followed by β on Čech;
the reverse composite identity is not used (textbook M13, two-sided comparison). -/
theorem cechDerivedGlobalSectionsHom_comp_inv :
    CategoryTheory.CohomologicalDeltaFunctor.Hom.comp
      (cechDerivedGlobalSectionsHom X) (cechDerivedGlobalSectionsInv X) =
        CategoryTheory.CohomologicalDeltaFunctor.Hom.id (cechCohomologyDeltaFunctor X) := by
  apply CategoryTheory.CohomologicalDeltaFunctor.Hom.ext
  intro n
  have hPhi := congrArg (fun θ => θ.app n) (extDerivedGlobalSectionsHom_comp_inv X)
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    CategoryTheory.CohomologicalDeltaFunctor.Hom.id_app,
    extDerivedGlobalSectionsHom_app, extDerivedGlobalSectionsInv_app] at hPhi
  have hC := congrArg (fun θ => θ.app n)
    (cechCohomologyToExt_comp_extToCechCohomology X)
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    CategoryTheory.CohomologicalDeltaFunctor.Hom.id_app] at hC
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    CategoryTheory.CohomologicalDeltaFunctor.Hom.id_app,
    cechDerivedGlobalSectionsHom_app, cechDerivedGlobalSectionsInv_app,
    Category.assoc, ← Category.assoc (extFunctorObjIsoDerivedGlobalSections X n).hom,
    hPhi, Category.id_comp]
  exact hC

/-- Reverse followed by forward is the identity on derived global sections.
Independently cancel β followed by α on Ext and then Φ inverse followed by Φ
on derived sections (textbook M13, the other two-sided identity). -/
theorem cechDerivedGlobalSectionsInv_comp_hom :
    CategoryTheory.CohomologicalDeltaFunctor.Hom.comp
      (cechDerivedGlobalSectionsInv X) (cechDerivedGlobalSectionsHom X) =
        CategoryTheory.CohomologicalDeltaFunctor.Hom.id (derivedGlobalSectionsDeltaFunctor X) := by
  apply CategoryTheory.CohomologicalDeltaFunctor.Hom.ext
  intro n
  have hE := congrArg (fun θ => θ.app n)
    (extToCechCohomology_comp_cechCohomologyToExt X)
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    CategoryTheory.CohomologicalDeltaFunctor.Hom.id_app] at hE
  have hD := congrArg (fun θ => θ.app n) (extDerivedGlobalSectionsInv_comp_hom X)
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    CategoryTheory.CohomologicalDeltaFunctor.Hom.id_app,
    extDerivedGlobalSectionsInv_app, extDerivedGlobalSectionsHom_app] at hD
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    CategoryTheory.CohomologicalDeltaFunctor.Hom.id_app,
    cechDerivedGlobalSectionsInv_app, cechDerivedGlobalSectionsHom_app,
    Category.assoc, ← Category.assoc ((extToCechCohomology X).app n),
    hE, Category.id_comp]
  exact hD

/-- The entire degree-zero transformation is χ followed by κ inverse. The fixed
α-zero and Φ-zero receipts cancel the SAME ε inverse and ε, all over literal
global sections (textbook M13, fixed natural degree-zero identifications). -/
theorem cechDerivedGlobalSectionsHom_app_zero :
    (cechDerivedGlobalSectionsHom X).app 0 =
      (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫
        (derivedGlobalSectionsDegreeZeroIso X).inv := by
  unfold cechDerivedGlobalSectionsHom
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    cechCohomologyToExt_app_zero, extDerivedGlobalSectionsHom_app_zero]
  erw [Category.assoc, Iso.inv_hom_id_assoc]

/-- Every other delta morphism with the same whole degree-zero normalization
equals this fixed composite. Universality of the Čech SOURCE verifies its
characterization; it never selects a replacement Φ or uses the later C30
construction as a premise (textbook M13). -/
theorem cechDerivedGlobalSectionsHom_unique
    (η : CategoryTheory.CohomologicalDeltaFunctor.Hom
      (cechCohomologyDeltaFunctor X) (derivedGlobalSectionsDeltaFunctor X))
    (hη : η.app 0 =
      (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫
        (derivedGlobalSectionsDegreeZeroIso X).inv) :
    η = cechDerivedGlobalSectionsHom X :=
  (cechCohomologyDeltaFunctor_effaceable X).isUniversal.hom_ext
    (hη.trans (cechDerivedGlobalSectionsHom_app_zero X).symm)

end TopologicalSpace.OpenCover.SetOpenCover
