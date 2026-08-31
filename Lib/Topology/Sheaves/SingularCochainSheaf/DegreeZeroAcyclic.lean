/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.H1Vanishing.Flasque
public import Lib.Topology.Sheaves.SingularCochainSheaf.DegreeZeroFunctions

/-!
# Degree-zero singular-cochain sheaf acyclicity in H¹

The degree-zero cochain presheaf is already the flasque sheaf of arbitrary functions.  Its native
sheafification is therefore isomorphic to that function sheaf, and the generic flasque-to-Ext
bridge gives the only acyclicity statement needed by the degree-one resolution.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The native degree-zero cochain presheaf already satisfies the sheaf condition. -/
theorem zeroCochainPresheaf_isSheaf : (presheaf X A 0).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iso_iff (zeroCochainPresheafIsoFunctions X A)).mpr
    (TopCat.FunctionSheaf.isSheaf X A)

/-- The degree-zero cochain presheaf regarded directly as a sheaf. -/
def zeroCochainDirectSheaf : TopCat.Sheaf AddCommGrpCat.{0} X :=
  ⟨presheaf X A 0, zeroCochainPresheaf_isSheaf X A⟩

/-- The direct degree-zero cochain sheaf is the arbitrary-function sheaf. -/
def zeroCochainDirectIsoFunctions :
    zeroCochainDirectSheaf X A ≅ TopCat.FunctionSheaf.sheaf X A :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}).preimageIso (zeroCochainPresheafIsoFunctions X A)

/-- The actual native sheafification in degree zero is the arbitrary-function sheaf. -/
def zeroCochainSheafIsoFunctions :
    sheaf X A 0 ≅ TopCat.FunctionSheaf.sheaf X A :=
  (CategoryTheory.sheafificationIso (zeroCochainDirectSheaf X A)).symm ≪≫
    zeroCochainDirectIsoFunctions X A

/-- Flasqueness is transported to the actual native degree-zero cochain sheaf. -/
instance zeroCochainSheaf_isFlasque : (sheaf X A 0).IsFlasque where
  epi {U V} i := by
    let e := zeroCochainSheafIsoFunctions X A
    let : IsIso e.hom.hom := by
      change IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{0} X).map e.hom)
      infer_instance
    let : IsIso e.inv.hom := by
      change IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{0} X).map e.inv)
      infer_instance
    have hinv_hom : e.inv.hom.app V ≫ e.hom.hom.app V = 𝟙 _ := by
      have h := congrArg
        (fun k : TopCat.FunctionSheaf.sheaf X A ⟶
          TopCat.FunctionSheaf.sheaf X A => k.hom.app V) e.inv_hom_id
      change e.inv.hom.app V ≫ e.hom.hom.app V = 𝟙 _ at h
      exact h
    have hmap : (sheaf X A 0).obj.map i =
        e.hom.hom.app U ≫ (TopCat.FunctionSheaf.sheaf X A).obj.map i ≫
          e.inv.hom.app V := by
      rw [← cancel_mono (e.hom.hom.app V)]
      rw [e.hom.hom.naturality i]
      simp only [Category.assoc, hinv_hom, Category.comp_id]
    rw [hmap]
    infer_instance

/-- The actual degree-zero singular-cochain sheaf has zero Ext-defined `H¹`. -/
theorem zeroCochainSheaf_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf X A 0) 1) :=
  TopCat.SheafH1.subsingleton_h1_of_isFlasque (sheaf X A 0)

end TopCat.SingularCochainSheaf
