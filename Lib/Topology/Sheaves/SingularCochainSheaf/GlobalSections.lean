/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalPatchLocal
public import Lib.Topology.Sheaves.SheafificationLocal
public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnit

/-!
# Global sections of the sheafified cochain presheaf

On a normal paracompact space, closed locally finite patching gives every global section of the
sheafified native cochain presheaf an honest global singular-cochain representative.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Set TopologicalSpace

namespace TopCat.SingularCochainSheaf

open AlgebraicTopology.SingularCochains

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ)

@[simp]
theorem globalCochainUnit_apply (phi : Cochains X A n) :
    globalCochainUnit X A n phi =
      (unit X A n).app (op ⊤) (restrictGlobalCochain A n phi ⊤) := rfl

/-- Naturality of the sheafification unit on open restrictions. -/
theorem unit_restrict {U V : Opens X} (i : U ⟶ V)
    (t : Cochains V A n) :
    (unit X A n).app (op U) ((presheaf X A n).map i.op t) =
      (sheaf X A n).obj.map i.op ((unit X A n).app (op V) t) :=
  congrArg (fun l => l t) ((unit X A n).naturality i.op)

/-- Restricting the global unit is the unit of the literal restricted cochain. -/
theorem globalCochainUnit_restrict (phi : Cochains X A n) (U : Opens X) :
    (sheaf X A n).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      (globalCochainUnit X A n phi) =
        (unit X A n).app (op U) (restrictGlobalCochain A n phi U) := by
  exact (unit_restrict X A n (homOfLE le_top)
    (restrictGlobalCochain A n phi ⊤)).symm.trans
      (congrArg ((unit X A n).app (op U))
        (restrictGlobalCochain_restrict A n phi (homOfLE le_top)))

/-- Germs of the global unit are germs of literal restricted cochains. -/
theorem globalCochainUnit_germ (phi : Cochains X A n) (U : Opens X)
    (x : X) (hx : x ∈ U) :
    (sheaf X A n).presheaf.germ ⊤ x (by trivial) (globalCochainUnit X A n phi) =
      (sheaf X A n).presheaf.germ U x hx
        ((unit X A n).app (op U) (restrictGlobalCochain A n phi U)) := by
  exact ((sheaf X A n).presheaf.germ_res_apply (homOfLE le_top) x hx
    (globalCochainUnit X A n phi)).symm.trans
      (congrArg ((sheaf X A n).presheaf.germ U x hx)
        (globalCochainUnit_restrict X A n phi U))

/-- Every global section has a native global singular-cochain representative. -/
theorem globalCochainUnit_surjective [NormalSpace X] [ParacompactSpace X] :
    Function.Surjective (globalCochainUnit X A n) := by
  classical
  intro s
  choose U hU t hxU ht using fun x : X =>
    TopCat.SheafificationLocal.exists_local_representative
      (presheaf X A n) ⊤ s x (by trivial)
  let R : ClosedRefinement U :=
    (exists_closedRefinement U (fun x => ⟨x, hxU x⟩)).some
  refine ⟨patchedCochain A n U R t, ?_⟩
  apply TopCat.Presheaf.section_ext (sheaf X A n) ⊤
  intro x hx
  let j := R.index x
  have hxj := R.mem_support_index x
  have hlocal : ∀ i, x ∈ R.support i →
      ∃ V : Opens X, x ∈ V ∧ ∃ (f : V ⟶ U i) (g : V ⟶ U j),
        (presheaf X A n).map f.op (t i) = (presheaf X A n).map g.op (t j) := by
    intro i hi
    apply TopCat.SheafificationLocal.exists_restriction_eq_of_germ_unit_eq
      (presheaf X A n) (U i) (U j) x
      (R.subordinate i hi) (R.subordinate j hxj) (t i) (t j)
    rw [ht i, ht j]
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  obtain ⟨W, hxW, f, hf⟩ :=
    exists_neighborhood_patchedCochain_eq A n U R t x j hxj hlocal
  calc
    (sheaf X A n).presheaf.germ ⊤ x hx
        (globalCochainUnit X A n (patchedCochain A n U R t)) =
      (sheaf X A n).presheaf.germ W x hxW
        ((unit X A n).app (op W)
          (restrictGlobalCochain A n (patchedCochain A n U R t) W)) :=
      globalCochainUnit_germ X A n _ W x hxW
    _ = (sheaf X A n).presheaf.germ W x hxW
        ((unit X A n).app (op W) ((presheaf X A n).map f.op (t j))) := by rw [hf]
    _ = (sheaf X A n).presheaf.germ (U j) x (R.subordinate j hxj)
        ((unit X A n).app (op (U j)) (t j)) := by
      have hu := unit_restrict X A n f (t j)
      have hg := congrArg ((sheaf X A n).presheaf.germ W x hxW) hu
      exact hg.trans ((sheaf X A n).presheaf.germ_res_apply
        f x hxW ((unit X A n).app (op (U j)) (t j)))
    _ = (sheaf X A n).presheaf.germ ⊤ x hx s := by
      exact (congrArg ((sheaf X A n).presheaf.germ (U j) x
        (R.subordinate j hxj)) (ht j)).trans
          ((sheaf X A n).presheaf.germ_res_apply
            (homOfLE (hU j)) x (R.subordinate j hxj) s)

end TopCat.SingularCochainSheaf
