/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

import Lib.CategoryTheory.Sites.Leray.SheafificationStalkCompatibility
public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.Stalk
import Lib.Topology.Sheaves.SheafificationLocalGerm
public import Lib.Topology.Sheaves.SheafificationLocal

/-!
# Local representatives and normalized higher-direct-image germs

A section of `Rⁿf_*F` near `y` is, by Hartshorne III.8.1 and the fact that sheafification
preserves stalks (Hartshorne II.1.2), represented on some neighbourhood `U` of `y` by a class in
`Hⁿ(Γ(f⁻¹U, I))`.  This file identifies the germ at `y` of such a local representative with the
normalized Ext-defined neighbourhood germ of `FibreStalkEvaluation.derivedNeighborhoodGerm`.

There is no separate textbook statement: it is the compatibility of the two descriptions of a
germ of `Rⁿf_*F` used here.  It assumes no proper-base-change theorem and does not identify a
higher-direct-image stalk with the cohomology of a geometric fibre.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace CategoryTheory.Sheaf.Leray

open FibreStalkEvaluation

variable {X Y : TopCat.{0}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A sheafified section represented locally in the resolution presheaf is, in the actual
higher-direct-image stalk, the normalized Ext neighborhood germ of that representative. -/
theorem derivedNeighborhoodGerm_eq_germ_of_localRepresentative
    (f : X ⟶ Y) (F : AbelianSheaf X) (I : InjectiveResolution F) (n : ℕ)
    (rho : ResolutionCohomologyNormalization (F := F) f I n)
    {U V : Opens Y} (hVU : V ≤ U)
    (s : (higherDirectImageSheaf f F n).obj.obj (op U))
    (t : (homologyPresheaf (pushedResolution f I) n).obj (op V))
    (hrep :
      (TopCat.SheafificationLocal.unit
        (homologyPresheaf (pushedResolution f I) n)).app (op V) t =
      (TopCat.SheafificationLocal.sheaf
        (homologyPresheaf (pushedResolution f I) n)).obj.map
          (homOfLE hVU).op
        ((higherDirectImageResolutionSheafificationIso f F I n).hom.hom.app
          (op U) s))
    (y : Y) (hy : y ∈ V) :
    derivedNeighborhoodGerm (F := F) f y I n rho V hy
        (rho.hom.app (op V) t) =
      TopCat.Presheaf.germ (higherDirectImageSheaf f F n).presheaf
        U y (hVU hy) s := by
  let P := homologyPresheaf (pushedResolution f I) n
  let R := higherDirectImageSheaf f F n
  have hlocal :=
    TopCat.SheafificationLocal.inv_unit_stalk_map_iso_germ_eq_germ_of_localRepresentative
      P R (higherDirectImageResolutionSheafificationIso f F I n)
      hVU s t hrep y hy
  have hresolution :
      (higherDirectImageResolutionStalkIso f F I n y).hom
          (TopCat.Presheaf.germ R.presheaf U y (hVU hy) s) =
        P.germ V y hy t := by
    rw [← higherDirectImageResolutionSheafificationStalkIso_eq f F I n y]
    exact hlocal
  have hnormalized :
      rho.hom.app (op V) ≫
          derivedNeighborhoodGerm (F := F) f y I n rho V hy =
        P.germ V y hy ≫
          (higherDirectImageResolutionStalkIso f F I n y).inv := by
    unfold derivedNeighborhoodGerm derivedStalkIso
    rw [← Category.assoc,
      ← TopCat.Presheaf.stalkFunctor_map_germ]
    simp [P]
  have happ := ConcreteCategory.congr_hom hnormalized t
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at happ
  have hinv :
      (higherDirectImageResolutionStalkIso f F I n y).inv
          (P.germ V y hy t) =
        R.presheaf.germ U y (hVU hy) s := by
    rw [← hresolution]
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id]
    rfl
  exact happ.trans hinv

end CategoryTheory.Sheaf.Leray
