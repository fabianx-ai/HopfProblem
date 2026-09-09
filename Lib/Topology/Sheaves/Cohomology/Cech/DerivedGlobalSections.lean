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

/-!
## The original two-source comparison

Čech universality extends the fixed identification with literal global sections
to the original forward comparison C30. Independently, universality of actual
derived global sections extends the inverse degree-zero identification.
Each composite extends its own source identity in degree zero; uniqueness from
that source gives its whole delta-morphism identity. Thus every degree is a
natural isomorphism, proving the textbook comparison statement (4). Both original
morphisms retain all coefficient naturalities and original positive connecting
squares. Any other normalized comparison equals the original forward morphism.
Only afterward is this comparison identified with the earlier fixed Ext composite
(textbook M14, lines 1880–1891 through “sections must be (C30).”).
No Godement comparison is used in this construction or its canonicity.
-/

/-- The original forward comparison C30, selected by Čech-source universality
from χ followed by κ inverse over the same literal global-sections functor. -/
def cechToDerivedGlobalSections : CategoryTheory.CohomologicalDeltaFunctor.Hom
    (cechCohomologyDeltaFunctor X) (derivedGlobalSectionsDeltaFunctor X) :=
  (cechCohomologyDeltaFunctor_effaceable X).isUniversal.extend
    (derivedGlobalSectionsDeltaFunctor X)
    ((cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫
      (derivedGlobalSectionsDegreeZeroIso X).inv)

/-- The original reverse comparison, selected independently by derived-source
universality from κ followed by χ inverse. -/
def derivedGlobalSectionsToCech : CategoryTheory.CohomologicalDeltaFunctor.Hom
    (derivedGlobalSectionsDeltaFunctor X) (cechCohomologyDeltaFunctor X) :=
  (derivedGlobalSectionsIsUniversal X).extend (cechCohomologyDeltaFunctor X)
    ((derivedGlobalSectionsDegreeZeroIso X).hom ≫
      (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).inv)

/-- The original forward comparison is the fixed identification with global
sections in whole degree zero, not merely at individual coefficients. -/
theorem cechToDerivedGlobalSections_app_zero :
    (cechToDerivedGlobalSections X).app 0 =
      (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫
        (derivedGlobalSectionsDegreeZeroIso X).inv := by
  unfold cechToDerivedGlobalSections
  exact (cechCohomologyDeltaFunctor_effaceable X).isUniversal.extend_app_zero
    (derivedGlobalSectionsDeltaFunctor X)
    ((cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫
      (derivedGlobalSectionsDegreeZeroIso X).inv)

/-- The independently selected reverse comparison extends the inverse fixed
identification with global sections in whole degree zero. -/
theorem derivedGlobalSectionsToCech_app_zero :
    (derivedGlobalSectionsToCech X).app 0 =
      (derivedGlobalSectionsDegreeZeroIso X).hom ≫
        (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).inv := by
  unfold derivedGlobalSectionsToCech
  exact (derivedGlobalSectionsIsUniversal X).extend_app_zero
    (cechCohomologyDeltaFunctor X)
    ((derivedGlobalSectionsDegreeZeroIso X).hom ≫
      (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).inv)

/-- Forward followed by reverse is the whole identity on Čech cohomology:
cancel κ then χ in degree zero and apply Čech-source uniqueness. -/
theorem cechToDerivedGlobalSections_comp_reverse :
    CategoryTheory.CohomologicalDeltaFunctor.Hom.comp
      (cechToDerivedGlobalSections X) (derivedGlobalSectionsToCech X) =
        CategoryTheory.CohomologicalDeltaFunctor.Hom.id (cechCohomologyDeltaFunctor X) := by
  apply (cechCohomologyDeltaFunctor_effaceable X).isUniversal.hom_ext
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    CategoryTheory.CohomologicalDeltaFunctor.Hom.id_app,
    cechToDerivedGlobalSections_app_zero, derivedGlobalSectionsToCech_app_zero]
  erw [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]

/-- Reverse followed by forward is independently the whole identity on derived
global sections: cancel χ then κ and apply derived-source uniqueness. -/
theorem derivedGlobalSectionsToCech_comp_forward :
    CategoryTheory.CohomologicalDeltaFunctor.Hom.comp
      (derivedGlobalSectionsToCech X) (cechToDerivedGlobalSections X) =
        CategoryTheory.CohomologicalDeltaFunctor.Hom.id (derivedGlobalSectionsDeltaFunctor X) := by
  apply (derivedGlobalSectionsIsUniversal X).hom_ext
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    CategoryTheory.CohomologicalDeltaFunctor.Hom.id_app,
    derivedGlobalSectionsToCech_app_zero, cechToDerivedGlobalSections_app_zero]
  erw [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]

/-- Every degree of C30 is a coefficient-natural isomorphism, with the original
forward and reverse morphisms as its arrows. Both independently proved whole
identities supply its inverse laws, proving the comparison statement (4). -/
def cechCohomologyIsoDerivedGlobalSections (n : ℕ) :
    ((cechCohomologyDeltaFunctor X).T n).obj ≅
      ((derivedGlobalSectionsDeltaFunctor X).T n).obj := by
  have cDegree := congrArg (fun θ => θ.app n) (cechToDerivedGlobalSections_comp_reverse X)
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    CategoryTheory.CohomologicalDeltaFunctor.Hom.id_app] at cDegree
  have dDegree := congrArg (fun θ => θ.app n) (derivedGlobalSectionsToCech_comp_forward X)
  erw [CategoryTheory.CohomologicalDeltaFunctor.Hom.comp_app,
    CategoryTheory.CohomologicalDeltaFunctor.Hom.id_app] at dDegree
  exact
    { hom := (cechToDerivedGlobalSections X).app n
      inv := (derivedGlobalSectionsToCech X).app n
      hom_inv_id := cDegree
      inv_hom_id := dDegree }

/-- The natural isomorphism's entire forward arrow is the original C30 map;
its coefficient components require no unfolding of the selected comparison. -/
theorem cechCohomologyIsoDerivedGlobalSections_hom (n : ℕ) :
    (cechCohomologyIsoDerivedGlobalSections X n).hom =
      (cechToDerivedGlobalSections X).app n := by
  unfold cechCohomologyIsoDerivedGlobalSections
  rfl

/-- The natural isomorphism's entire inverse arrow is the independently selected
derived-to-Čech map, also publicly available at every coefficient component. -/
theorem cechCohomologyIsoDerivedGlobalSections_inv (n : ℕ) :
    (cechCohomologyIsoDerivedGlobalSections X n).inv =
      (derivedGlobalSectionsToCech X).app n := by
  unfold cechCohomologyIsoDerivedGlobalSections
  rfl

/-- Canonicity: any other delta morphism equal to the fixed global-sections
identification in degree zero is C30, by Čech-source uniqueness. -/
theorem cechToDerivedGlobalSections_unique
    (η : CategoryTheory.CohomologicalDeltaFunctor.Hom
      (cechCohomologyDeltaFunctor X) (derivedGlobalSectionsDeltaFunctor X))
    (hη : η.app 0 =
      (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫
        (derivedGlobalSectionsDegreeZeroIso X).inv) :
    η = cechToDerivedGlobalSections X :=
  (cechCohomologyDeltaFunctor_effaceable X).isUniversal.hom_ext
    (hη.trans (cechToDerivedGlobalSections_app_zero X).symm)

/-- The original two-source comparison is the same normalized forward morphism
as the earlier fixed Ext factorization. That factorization was not used to
select these original maps or prove either original composite identity. -/
theorem cechToDerivedGlobalSections_eq_fixed :
    cechToDerivedGlobalSections X = cechDerivedGlobalSectionsHom X :=
  cechDerivedGlobalSectionsHom_unique X (cechToDerivedGlobalSections X)
    (cechToDerivedGlobalSections_app_zero X)

end TopologicalSpace.OpenCover.SetOpenCover
