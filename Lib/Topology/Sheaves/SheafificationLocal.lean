/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Sheafification
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Local representatives in concrete sheafification

Concrete sheafification is locally surjective, and its unit is an isomorphism on stalks.  These
facts let us retain literal presheaf representatives after shrinking an open neighborhood.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.SheafificationLocal

variable {X : TopCat.{0}}

abbrev sheaf (P : TopCat.Presheaf AddCommGrpCat.{0} X) :
    TopCat.Sheaf AddCommGrpCat.{0} X :=
  (TopCat.Sheaf.sheafification X).obj P

def unit (P : TopCat.Presheaf AddCommGrpCat.{0} X) : P ⟶ (sheaf P).obj :=
  toSheafify (Opens.grothendieckTopology X) P

instance unit_stalk_isIso (P : TopCat.Presheaf AddCommGrpCat.{0} X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unit P)) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P

theorem unit_stalk_injective (P : TopCat.Presheaf AddCommGrpCat.{0} X) (x : X) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unit P)) :=
  ((ConcreteCategory.isIso_iff_bijective _).mp (unit_stalk_isIso P x)).injective

/-- Every sheafified section has a presheaf representative near each point. -/
theorem exists_local_representative (P : TopCat.Presheaf AddCommGrpCat.{0} X)
    (U : Opens X) (s : (sheaf P).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (t : P.obj (op V)), x ∈ V ∧
      (unit P).app (op V) t = (sheaf P).obj.map (homOfLE hVU).op s := by
  have hloc : TopCat.Presheaf.IsLocallySurjective (unit P) := by
    change CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X) (toSheafify (Opens.grothendieckTopology X) P)
    infer_instance
  obtain ⟨V, hVU, ⟨t, ht⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (unit P)).mp hloc U s x hx
  exact ⟨V, hVU, t, hxV, ht⟩

/-- Equality of unit germs is equality of the original presheaf germs. -/
theorem germ_unit_eq_iff (P : TopCat.Presheaf AddCommGrpCat.{0} X)
    (U V : Opens X) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : P.obj (op U)) (t : P.obj (op V)) :
    TopCat.Presheaf.germ (sheaf P).obj U x hxU ((unit P).app (op U) s) =
      TopCat.Presheaf.germ (sheaf P).obj V x hxV ((unit P).app (op V) t) ↔
        P.germ U x hxU s = P.germ V x hxV t := by
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact (unit_stalk_injective P x).eq_iff

/-- Equal unit germs have literally equal restrictions on a common smaller neighborhood. -/
theorem exists_restriction_eq_of_germ_unit_eq
    (P : TopCat.Presheaf AddCommGrpCat.{0} X)
    (U V : Opens X) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : P.obj (op U)) (t : P.obj (op V))
    (h : TopCat.Presheaf.germ (sheaf P).obj U x hxU ((unit P).app (op U) s) =
      TopCat.Presheaf.germ (sheaf P).obj V x hxV ((unit P).app (op V) t)) :
    ∃ (W : Opens X), x ∈ W ∧ ∃ (i : W ⟶ U) (j : W ⟶ V),
      P.map i.op s = P.map j.op t := by
  obtain ⟨W, hxW, i, j, hij⟩ :=
    P.germ_eq _ _ _ _ _ ((germ_unit_eq_iff P U V x hxU hxV s t).mp h)
  exact ⟨W, hxW, i, j, hij⟩

end TopCat.SheafificationLocal
