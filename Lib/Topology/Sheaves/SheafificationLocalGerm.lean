/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SheafificationLocal

/-!
# Germs of local representatives in sheafification

If a section of a sheaf identified with the sheafification of a presheaf is represented by a
presheaf section after shrinking, its stalk value becomes the literal presheaf germ after
applying that identification and undoing the sheafification unit on the stalk.

This is the compatibility of germs with the sheafification unit
(`TopCat.Presheaf.stalkFunctor_map_germ`, which is an isomorphism for sheafification), read
through a local representative.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopCat.SheafificationLocal

variable {X : TopCat.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A local sheafification representative gives the expected literal presheaf germ after
inverting the sheafification unit on the stalk. -/
theorem inv_unit_stalk_map_iso_germ_eq_germ_of_localRepresentative
    (P : TopCat.Presheaf AddCommGrpCat.{u} X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (e : F ≅ sheaf P)
    {U V : Opens X} (hVU : V ≤ U)
    (s : F.obj.obj (op U)) (t : P.obj (op V))
    (hrep : (unit P).app (op V) t =
      (sheaf P).obj.map (homOfLE hVU).op (e.hom.hom.app (op U) s))
    (x : X) (hx : x ∈ V) :
    inv ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unit P))
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map e.hom.hom
          (F.presheaf.germ U x (hVU hx) s)) =
      P.germ V x hx t := by
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rw [← TopCat.Presheaf.germ_res_apply (sheaf P).obj
    (homOfLE hVU) x hx]
  rw [← hrep]
  have hunit :
      TopCat.Presheaf.germ (sheaf P).obj V x hx ((unit P).app (op V) t) =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unit P)
          (P.germ V x hx t) := by
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply
      V x hx (unit P) t).symm
  calc
    _ = inv ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unit P))
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unit P)
          (P.germ V x hx t)) := congrArg _ hunit
    _ = P.germ V x hx t := by
      rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id]
      rfl

end TopCat.SheafificationLocal
