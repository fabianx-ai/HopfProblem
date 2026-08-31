/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalSections

/-!
# The local kernel of the global cochain unit

The sheafification unit kills a native global cochain exactly when that cochain restricts to zero
on a neighborhood of every point.  The reverse implication uses the genuine stalk isomorphism of
the concrete sheafification unit.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Set TopologicalSpace

namespace TopCat.SingularCochainSheaf

open AlgebraicTopology.SingularCochains

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ)

/-- A locally zero native cochain has zero image under the global sheafification unit. -/
theorem globalCochainUnit_eq_zero_of_local (phi : Cochains X A n)
    (hphi : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ restrictGlobalCochain A n phi U = 0) :
    globalCochainUnit X A n phi = 0 := by
  apply TopCat.Presheaf.section_ext (sheaf X A n) ⊤
  intro x hx
  obtain ⟨U, hxU, hU⟩ := hphi x
  calc
    (sheaf X A n).presheaf.germ ⊤ x hx (globalCochainUnit X A n phi) =
      (sheaf X A n).presheaf.germ U x hxU
        ((unit X A n).app (op U) (restrictGlobalCochain A n phi U)) :=
      globalCochainUnit_germ X A n phi U x hxU
    _ = 0 := by
      rw [hU]
      have hu : (unit X A n).app (op U) (0 : (presheaf X A n).obj (op U)) =
          (0 : (sheaf X A n).obj.obj (op U)) := map_zero _
      have hg : (sheaf X A n).presheaf.germ U x hxU
          (0 : (sheaf X A n).obj.obj (op U)) = 0 := map_zero _
      exact (congrArg
        (fun z : (sheaf X A n).obj.obj (op U) =>
          (sheaf X A n).presheaf.germ U x hxU z) hu).trans hg
    _ = (sheaf X A n).presheaf.germ ⊤ x hx 0 := (map_zero _).symm

/-- A zero under the global unit restricts literally to zero near every point. -/
theorem globalCochainUnit_locally_zero (phi : Cochains X A n)
    (hphi : globalCochainUnit X A n phi = 0) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ restrictGlobalCochain A n phi U = 0 := by
  have hg : (sheaf X A n).presheaf.germ ⊤ x (by trivial)
      ((unit X A n).app (op ⊤) (restrictGlobalCochain A n phi ⊤)) =
    (sheaf X A n).presheaf.germ ⊤ x (by trivial)
      ((unit X A n).app (op ⊤) 0) := by
    change (sheaf X A n).presheaf.germ ⊤ x (by trivial)
      (globalCochainUnit X A n phi) = _
    rw [hphi, map_zero, map_zero, map_zero]
  obtain ⟨U, hxU, i, j, hij⟩ :=
    TopCat.SheafificationLocal.exists_restriction_eq_of_germ_unit_eq
      (presheaf X A n) ⊤ ⊤ x (by trivial) (by trivial)
      (restrictGlobalCochain A n phi ⊤) 0 hg
  exact ⟨U, hxU, (restrictGlobalCochain_restrict A n phi i).symm.trans
    (hij.trans (map_zero _))⟩

/-- Exact local criterion for the kernel of the global sheafification unit. -/
theorem globalCochainUnit_eq_zero_iff_local (phi : Cochains X A n) :
    globalCochainUnit X A n phi = 0 ↔
      ∀ x : X, ∃ U : Opens X, x ∈ U ∧ restrictGlobalCochain A n phi U = 0 :=
  ⟨globalCochainUnit_locally_zero X A n phi,
    globalCochainUnit_eq_zero_of_local X A n phi⟩

end TopCat.SingularCochainSheaf
