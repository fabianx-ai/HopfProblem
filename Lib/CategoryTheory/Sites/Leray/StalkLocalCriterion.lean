/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Topology.Sheaves.Stalks

/-!
# A local lift-and-kill criterion for stalk maps

A map out of a sheaf stalk is bijective when every target element has a representative on some
neighborhood and every local section in its kernel vanishes after shrinking.  This is the standard
filtered-colimit argument, packaged independently of any geometric application.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace CategoryTheory.Sheaf.Leray

variable {X : TopCat.{0}} (P : TopCat.Presheaf AddCommGrpCat.{0} X)
  (x : X) (A : AddCommGrpCat.{0})
  (m : TopCat.Presheaf.stalk P x ⟶ A)
  (e : ∀ (U : Opens X), x ∈ U → (P.obj (op U) ⟶ A))

/-- A stalk map is bijective if every target class has a neighborhood lift and every neighborhood
class in its kernel dies after shrinking. -/
theorem stalkMap_bijective_of_local_lift_kill
    (he : ∀ (U : Opens X) (hx : x ∈ U), P.germ U x hx ≫ m = e U hx)
    (hlift : ∀ b : A, ∃ (U : Opens X) (hx : x ∈ U) (a : P.obj (op U)),
      e U hx a = b)
    (hkill : ∀ (U : Opens X) (hx : x ∈ U) (a : P.obj (op U)),
      e U hx a = 0 → ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V),
        P.map (homOfLE hVU).op a = 0) :
    Function.Bijective m := by
  constructor
  · intro s t hst
    have hz : m (s - t) = 0 := by
      rw [map_sub, hst, sub_self]
    obtain ⟨U, hxU, a, ha⟩ := P.exists_germ_eq (s - t)
    have hea : e U hxU a = 0 := by
      rw [← ConcreteCategory.congr_hom (he U hxU) a,
        ConcreteCategory.comp_apply, ha, hz]
    obtain ⟨V, hVU, hxV, hzero⟩ := hkill U hxU a hea
    have hg : P.germ U x hxU a = 0 := by
      rw [← P.germ_res_apply (homOfLE hVU) x hxV a, hzero, map_zero]
    exact sub_eq_zero.mp (ha.symm.trans hg)
  · intro b
    obtain ⟨U, hxU, a, ha⟩ := hlift b
    refine ⟨P.germ U x hxU a, ?_⟩
    exact (ConcreteCategory.congr_hom (he U hxU) a).trans ha

end CategoryTheory.Sheaf.Leray
