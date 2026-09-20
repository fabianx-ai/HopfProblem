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

set_option backward.isDefEq.respectTransparency false in
/-- The Čech-to-Ext morphism followed by the fixed Ext-to-Čech morphism is the
identity delta morphism. In degree zero the path is χ, ε inverse, ε, χ inverse,
so the two inverse cancellations give the identity on the whole Čech degree-zero
functor. Uniqueness from the Čech source then gives the whole-Hom identity
(textbook lines 1850–1858, 1860–1862), including every coefficient and connecting
component. This argument does not assume the reverse composite identity. -/
theorem cechCohomologyToExt_comp_extToCechCohomology :
    Hom.comp (cechCohomologyToExt X) (extToCechCohomology X) = Hom.id (cechCohomologyDeltaFunctor X) := by
  apply (cechCohomologyDeltaFunctor_effaceable X).isUniversal.hom_ext
  calc
    (Hom.comp (cechCohomologyToExt X) (extToCechCohomology X)).app 0 =
        ((cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫
          (TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).inv) ≫
        ((TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).hom ≫
          (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).inv) := by
      rw [Hom.comp_app, cechCohomologyToExt_app_zero, extToCechCohomology_app_zero]
    _ = 𝟙 ((cechCohomologyDeltaFunctor X).T 0).obj := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
    _ = (Hom.id (cechCohomologyDeltaFunctor X)).app 0 :=
      (Hom.id_app (cechCohomologyDeltaFunctor X) 0).symm

set_option backward.isDefEq.respectTransparency false in
/-- The fixed Ext-to-Čech morphism followed by the Čech-to-Ext morphism is the
identity on the native Ext delta functor at the constant integer sheaf. Its whole
degree-zero path is ε, χ inverse, χ, ε inverse, hence the identity after inverse
cancellation. Independently, uniqueness from the native Ext source proves this
whole-Hom identity (textbook lines 1850–1856, 1858–1862). Together the two identities
make the original morphisms inverse, without replacing their normalization or models. -/
theorem extToCechCohomology_comp_cechCohomologyToExt :
    Hom.comp (extToCechCohomology X) (cechCohomologyToExt X) = Hom.id (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))) := by
  apply (ofExt_isUniversal ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))).hom_ext
  calc
    (Hom.comp (extToCechCohomology X) (cechCohomologyToExt X)).app 0 =
        ((TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).hom ≫
          (cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).inv) ≫
        ((cechCohomologyDeltaFunctor_zeroIsoGlobalSections X).hom ≫
          (TopCat.ConstantSheaf.extFunctorObjZeroIsoGlobalSections X).inv) := by
      rw [Hom.comp_app, extToCechCohomology_app_zero, cechCohomologyToExt_app_zero]
    _ = 𝟙 ((ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))).T 0).obj := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, ofExt_T_obj]
    _ = (Hom.id (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))))).app 0 :=
      (Hom.id_app (ofExt ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) 0).symm

end TopologicalSpace.OpenCover.SetOpenCover
