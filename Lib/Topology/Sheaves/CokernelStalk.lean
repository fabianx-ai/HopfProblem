/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Topology.Sheaves.Abelian

/-!
# Stalks of cokernel sheaves

For sheaves of abelian groups, the stalk functor is exact and therefore preserves cokernels.
This file exposes the resulting canonical isomorphism and its compatibility with the quotient
map.  It also packages two consequences: an epimorphic stalk map gives a zero cokernel stalk, and
a map out of the local cokernel canonically induces a map out of the stalk of the sheaf cokernel.

Reference: Hartshorne, *Algebraic Geometry*, II Ex. 1.2 (exactness of the stalk functor); see
also Godement, *Topologie algébrique et théorie des faisceaux*, II.2.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- The stalk of a cokernel sheaf is canonically the cokernel of the stalk map. -/
def stalkCokernelIso {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj (cokernel f).obj ≅
      cokernel ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) :=
  PreservesCokernel.iso
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) f

/-- The canonical stalk--cokernel isomorphism carries the sheaf quotient map to the local
quotient map. -/
@[reassoc]
theorem stalk_cokernelπ_comp_stalkCokernelIso_hom
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (cokernel.π f).hom ≫
      (stalkCokernelIso f x).hom =
        cokernel.π ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) :=
  PreservesCokernel.π_iso_hom
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) f

/-- An epimorphic stalk map has zero cokernel stalk. -/
theorem stalkCokernel_isZero_of_epi
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (x : X)
    [Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom)] :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj (cokernel f).obj) :=
  (isZero_cokernel_of_epi
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom)).of_iso
      (stalkCokernelIso f x)

/-- Transport a map from the cokernel of a stalk map to a map from the stalk of the sheaf
cokernel. -/
def stalkCokernelHom {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (x : X) (A : AddCommGrpCat.{u})
    (g : cokernel ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) ⟶ A) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj (cokernel f).obj ⟶ A :=
  (stalkCokernelIso f x).hom ≫ g

/-- The transported local quotient map agrees with the sheaf quotient map on the stalk. -/
@[reassoc]
theorem stalk_cokernelπ_comp_stalkCokernelHom
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (x : X) (A : AddCommGrpCat.{u})
    (g : cokernel ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) ⟶ A) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (cokernel.π f).hom ≫
      stalkCokernelHom f x A g =
        cokernel.π ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) ≫ g := by
  unfold stalkCokernelHom
  rw [← Category.assoc, stalk_cokernelπ_comp_stalkCokernelIso_hom]

end TopCat.Sheaf

end
