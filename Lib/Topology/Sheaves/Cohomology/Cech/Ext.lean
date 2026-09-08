module
public import Lib.Topology.Sheaves.Cohomology.Cech.Effacement
public import Lib.Topology.Sheaves.ConstantSheaf.GlobalSections
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Ext

/-!
# Normalized Čech and native Ext comparison morphisms

On a paracompact Hausdorff space, the universal Čech source extends its fixed
degree-zero global-sections identification followed by the inverse native Ext
normalization. Conversely, the universal native Ext source extends its normalization
followed by the inverse Čech identification. These are the two morphisms of
textbook lines 1831–1849, (C29h). Each is unique with its prescribed degree-zero
natural transformation; their Hom fields give coefficient naturality in every degree
and compatibility with every original short exact sequence's positive connecting map.
This section does not assert that their composites are identities.
-/

public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.CohomologicalDeltaFunctor
open Opposite TopologicalSpace TopologicalSpace.OpenCover.SetOpenCover
variable (X : TopCat.{u}) [ParacompactSpace X] [T2Space X]
local instance : HasExt.{u}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives.{u,u,u+1} _

namespace TopologicalSpace.OpenCover.SetOpenCover

/-- The unique Čech-to-native-Ext delta morphism extending χ followed by ε inverse.
Čech is the universal source; coefficients are arbitrary abelian sheaves and the fixed
first Ext object is the sheafified constant integer sheaf (textbook 1835–1836, C29h).
Its degreewise natural transformations and Hom.comm retain both coefficient maps and
positive quotient-to-subobject connecting squares. -/
def cechCohomologyToExt : Hom (cechCohomologyDeltaFunctor X) (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))) :=
  (cechCohomologyDeltaFunctor_effaceable X).isUniversal.extend (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))) ((cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫ (TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).inv)

/-- The unique native-Ext-to-Čech delta morphism extending ε followed by χ inverse.
Native Ext is the universal source, not an assumed universal target. The fixed ε is
canonical Ext degree zero followed by evaluation on the global integer generator;
χ is the original Čech gluing identification (textbook 1837–1838, C29h). -/
def extToCechCohomology : Hom (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))) (cechCohomologyDeltaFunctor X) :=
  (ofExt_isUniversal ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))).extend (cechCohomologyDeltaFunctor X) ((TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).hom ≫ (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).inv)

/-- The entire degree-zero natural transformation of the Čech-source extension is
χ followed by ε inverse. This fixes its normalization on every coefficient sheaf;
source universality supplies uniqueness (textbook 1835–1836). -/
theorem cechCohomologyToExt_app_zero :
    (cechCohomologyToExt X).app 0 = (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫ (TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).inv := by
  unfold cechCohomologyToExt
  exact (cechCohomologyDeltaFunctor_effaceable X).isUniversal.extend_app_zero (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))) ((cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫ (TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).inv)

/-- The entire degree-zero natural transformation of the native-source extension is
ε followed by χ inverse, with the same literal global-sections functor between them.
Source universality supplies uniqueness (textbook 1837–1838). -/
theorem extToCechCohomology_app_zero :
    (extToCechCohomology X).app 0 = (TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).hom ≫ (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).inv := by
  unfold extToCechCohomology
  exact (ofExt_isUniversal ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))).extend_app_zero (cechCohomologyDeltaFunctor X) ((TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).hom ≫ (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).inv)

end TopologicalSpace.OpenCover.SetOpenCover
