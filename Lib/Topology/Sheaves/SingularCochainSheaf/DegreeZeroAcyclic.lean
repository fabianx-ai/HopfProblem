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
# Acyclicity of the degree-zero singular-cochain sheaf

The degree-zero singular-cochain presheaf `S^0(X; A)` is the sheaf of all `A`-valued functions on
`X` (Bredon, *Sheaf Theory*, III §1; Warner 5.31).  That sheaf is flasque, and flasque sheaves are
acyclic (Bredon II §5; Godement II.3.1), so the degree-zero cochain sheaf has vanishing `H¹`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The degree-zero singular-cochain presheaf already satisfies the sheaf condition: it is the
presheaf of all `A`-valued functions. -/
theorem zeroCochainPresheaf_isSheaf : (presheaf X A 0).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iso_iff (zeroCochainPresheafIsoFunctions X A)).mpr
    (TopCat.DependentFunctionSheaf.isSheaf X (fun _ => A))

/-- The degree-zero cochain presheaf regarded directly as a sheaf. -/
def zeroCochainDirectSheaf : TopCat.Sheaf AddCommGrpCat.{0} X :=
  ⟨presheaf X A 0, zeroCochainPresheaf_isSheaf X A⟩

/-- The direct degree-zero cochain sheaf is the arbitrary-function sheaf. -/
def zeroCochainDirectIsoFunctions :
    zeroCochainDirectSheaf X A ≅ TopCat.DependentFunctionSheaf.sheaf X (fun _ => A) :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}).preimageIso (zeroCochainPresheafIsoFunctions X A)

/-- The sheafification of the degree-zero singular-cochain presheaf is the sheaf of all
`A`-valued functions on `X` (Bredon III §1). -/
def zeroCochainSheafIsoFunctions :
    sheaf X A 0 ≅ TopCat.DependentFunctionSheaf.sheaf X (fun _ => A) :=
  (CategoryTheory.sheafificationIso (zeroCochainDirectSheaf X A)).symm ≪≫
    zeroCochainDirectIsoFunctions X A

/-- The degree-zero singular-cochain sheaf is flasque, being the sheaf of all `A`-valued
functions. -/
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
        (fun k : TopCat.DependentFunctionSheaf.sheaf X (fun _ => A) ⟶
          TopCat.DependentFunctionSheaf.sheaf X (fun _ => A) => k.hom.app V) e.inv_hom_id
      change e.inv.hom.app V ≫ e.hom.hom.app V = 𝟙 _ at h
      exact h
    have hmap : (sheaf X A 0).obj.map i =
        e.hom.hom.app U ≫ (TopCat.DependentFunctionSheaf.sheaf X (fun _ => A)).obj.map i ≫
          e.inv.hom.app V := by
      rw [← cancel_mono (e.hom.hom.app V)]
      rw [e.hom.hom.naturality i]
      simp only [Category.assoc, hinv_hom, Category.comp_id]
    rw [hmap]
    infer_instance

/-- The degree-zero singular-cochain sheaf is acyclic in degree one: `H¹(X, 𝒮^0(X; A)) = 0`
(flasque sheaves are acyclic, Godement II.3.1). -/
theorem zeroCochainSheaf_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf X A 0) 1) :=
  TopCat.SheafH1.subsingleton_h1_of_isFlasque (sheaf X A 0)

end TopCat.SingularCochainSheaf
