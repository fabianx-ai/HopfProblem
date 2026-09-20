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
# Local representatives for concrete sheafification

Let `P` be a presheaf of abelian groups on a topological space `X` and let `P⁺` be its
sheafification, with unit `η : P ⟶ P⁺`.  Two standard facts drive this file: `η` is locally
surjective, and `η` induces an isomorphism on every stalk.  Together they say that a section
of `P⁺` is, after shrinking the open set around any given point, literally a section of `P`,
and that two sections of `P` become equal in `P⁺` exactly when they already agreed on some
smaller open set.

## Main results

* `TopCat.SheafificationLocal.exists_local_representative`: every section of the
  sheafification restricts, on some smaller open neighbourhood of a given point, to the image
  of a section of the original presheaf.
* `TopCat.SheafificationLocal.germ_unit_eq_iff`: the unit is injective on germs, so germs of
  sheafified sections agree iff the germs of their presheaf representatives agree.
* `TopCat.SheafificationLocal.exists_restriction_eq_of_germ_unit_eq`: equal germs after
  sheafification means literally equal restrictions to a common smaller open set.

## References

The two inputs are Mathlib's:

* `CategoryTheory.Presheaf.isLocallySurjective_toSheafify`
  (`Mathlib/CategoryTheory/Sites/LocallySurjective.lean`), read through the site-free
  criterion `TopCat.Presheaf.isLocallySurjective_iff`
  (`Mathlib/Topology/Sheaves/LocallySurjective.lean`);
* `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`
  (`Mathlib/Topology/Sheaves/Stalks.lean`), together with `TopCat.Presheaf.germ_eq` from the
  same file.

Mathlib does not state the three results above in this shrink-the-neighbourhood form; that is
what this file adds.  Everything is stated for `TopCat.{u}` with `AddCommGrpCat.{u}`
coefficients.
-/
@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopCat.SheafificationLocal

variable {X : TopCat.{u}}

/-- The sheafification of `P`, as an object of `TopCat.Sheaf AddCommGrpCat X`: an
abbreviation for `(TopCat.Sheaf.sheafification X).obj P`. -/
abbrev sheaf (P : TopCat.Presheaf AddCommGrpCat.{u} X) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (TopCat.Sheaf.sheafification X).obj P

/-- The unit of the sheafification adjunction at `P`, i.e. Mathlib's
`CategoryTheory.toSheafify (Opens.grothendieckTopology X) P`, viewed as a morphism of
presheaves from `P` to the underlying presheaf of `sheaf P`. -/
def unit (P : TopCat.Presheaf AddCommGrpCat.{u} X) : P ⟶ (sheaf P).obj :=
  toSheafify (Opens.grothendieckTopology X) P

/-- Sheafification does not change stalks: the unit induces an isomorphism on the stalk at
every point.  This is Mathlib's `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`
restated for `unit`. -/
instance unit_stalk_isIso (P : TopCat.Presheaf AddCommGrpCat.{u} X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unit P)) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P

/-- The injectivity half of `unit_stalk_isIso`: distinct germs of `P` stay distinct after
sheafification. -/
theorem unit_stalk_injective (P : TopCat.Presheaf AddCommGrpCat.{u} X) (x : X) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unit P)) :=
  ((ConcreteCategory.isIso_iff_bijective _).mp (unit_stalk_isIso P x)).injective

/-- Every sheafified section has a presheaf representative near each point. -/
theorem exists_local_representative (P : TopCat.Presheaf AddCommGrpCat.{u} X)
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
theorem germ_unit_eq_iff (P : TopCat.Presheaf AddCommGrpCat.{u} X)
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
    (P : TopCat.Presheaf AddCommGrpCat.{u} X)
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
