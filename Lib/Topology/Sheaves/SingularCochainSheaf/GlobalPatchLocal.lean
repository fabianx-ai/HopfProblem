/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalPatch

/-!
# Local agreement of the patched cochain with its local representatives

Because the selector attached to a locally finite closed refinement is locally constant in the
relevant sense, compatible local cochains agree with the patched global cochain on a
neighbourhood of every point.  This is a step in the proof of Bredon, *Sheaf Theory*,
III §1.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Set TopologicalSpace

namespace TopCat.SingularCochainSheaf

open AlgebraicTopology.SingularCochains

variable {X : TopCat.{0}} (A : AddCommGrpCat.{0}) (n : ℕ)
variable {ι : Type*} (U : ι → Opens X) (R : ClosedRefinement U)
  (t : ∀ i, Cochains (U i) A n)

/-- On an open `W` controlled by the refinement, the patched cochain restricts to the given
local cochain, provided the local cochains agree on `W`. -/
theorem patchedCochain_restrict_of_compatible
    (x : X) (W : Opens X) (j : ι) (hj : W ≤ U j)
    (hcontrol : ∀ y ∈ W, ∀ i, y ∈ R.support i → x ∈ R.support i)
    (hW : ∀ i, x ∈ R.support i → W ≤ U i)
    (hcompat : ∀ i (hi : x ∈ R.support i),
      (presheaf X A n).map (homOfLE (hW i hi)).op (t i) =
        (presheaf X A n).map (homOfLE hj).op (t j)) :
    restrictGlobalCochain A n (patchedCochain A n U R t) W =
      (presheaf X A n).map (homOfLE hj).op (t j) := by
  apply cochain_ext A n
  intro sigma
  let tau : TopCat.SingularSmallChains.SingularSimplex X n :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(W, X)).comp sigma
  let i := patchIndex n U R tau
  let v : stdSimplex ℝ (Fin (n + 1)) :=
    stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))
  have hi : x ∈ R.support i :=
    hcontrol (tau v) (sigma v).property i (R.mem_support_index _)
  have htau : Set.range tau ⊆ U i := by
    rintro _ ⟨z, rfl⟩
    exact hW i hi (sigma z).property
  have hvalues := congrArg
    (fun c : Cochains W A n =>
      c (TopCat.SingularSmallChains.simplexChain W n sigma)) (hcompat i hi)
  calc
    restrictGlobalCochain A n (patchedCochain A n U R t) W
        (TopCat.SingularSmallChains.simplexChain W n sigma) =
      patchedCochain A n U R t
        (TopCat.SingularSmallChains.simplexChain X n tau) :=
        restrictGlobalCochain_simplex A n _ W sigma
    _ = t i (TopCat.SingularSmallChains.simplexChain (U i) n
        (simplexInOpen n tau (U i) htau)) :=
      patchedCochain_simplex_of_subset A n U R t tau htau
    _ = (show Cochains W A n from
        (presheaf X A n).map (homOfLE (hW i hi)).op (t i))
          (TopCat.SingularSmallChains.simplexChain W n sigma) :=
      (pullback_simplex A ((Opens.toTopCat X).map (homOfLE (hW i hi))).hom
        n (t i) sigma).symm
    _ = (show Cochains W A n from
        (presheaf X A n).map (homOfLE hj).op (t j))
          (TopCat.SingularSmallChains.simplexChain W n sigma) := hvalues

/-- If the local cochains agree near `x` after shrinking, there is a neighbourhood of `x` on
which the patched cochain restricts to one of them. -/
theorem exists_neighborhood_patchedCochain_eq
    (x : X) (j : ι) (hxj : x ∈ R.support j)
    (hlocal : ∀ i, x ∈ R.support i →
      ∃ V : Opens X, x ∈ V ∧ ∃ (f : V ⟶ U i) (g : V ⟶ U j),
        (presheaf X A n).map f.op (t i) = (presheaf X A n).map g.op (t j)) :
    ∃ W : Opens X, x ∈ W ∧ ∃ f : W ⟶ U j,
      restrictGlobalCochain A n (patchedCochain A n U R t) W =
        (presheaf X A n).map f.op (t j) := by
  classical
  have hall : ∀ i, ∃ V : Opens X, x ∈ V ∧
      (x ∈ R.support i → ∃ (f : V ⟶ U i) (g : V ⟶ U j),
        (presheaf X A n).map f.op (t i) = (presheaf X A n).map g.op (t j)) := by
    intro i
    by_cases hi : x ∈ R.support i
    · obtain ⟨V, hxV, f, g, heq⟩ := hlocal i hi
      exact ⟨V, hxV, fun _ => ⟨f, g, heq⟩⟩
    · exact ⟨⊤, by simp, fun h => (hi h).elim⟩
  choose V hxV hV using hall
  obtain ⟨W, hxW, hWV, hcontrol⟩ :=
    R.exists_controlled_neighborhood x V (fun i _ => hxV i)
  have hWU : ∀ i, x ∈ R.support i → W ≤ U i := by
    intro i hi
    exact (hWV i hi).trans (leOfHom (hV i hi).choose)
  have hcompat : ∀ i (hi : x ∈ R.support i),
      (presheaf X A n).map (homOfLE (hWU i hi)).op (t i) =
        (presheaf X A n).map (homOfLE (hWU j hxj)).op (t j) := by
    intro i hi
    obtain ⟨f, g, heq⟩ := hV i hi
    have h := congrArg
      (fun c => (presheaf X A n).map (homOfLE (hWV i hi)).op c) heq
    let P := presheaf X A n
    let k : W ⟶ V i := homOfLE (hWV i hi)
    have hf := congrArg
      (fun l : P.obj (op (U i)) ⟶ P.obj (op W) => l (t i))
      (P.map_comp f.op k.op)
    have hg := congrArg
      (fun l : P.obj (op (U j)) ⟶ P.obj (op W) => l (t j))
      (P.map_comp g.op k.op)
    exact hf.trans (h.trans hg.symm)
  exact ⟨W, hxW, homOfLE (hWU j hxj),
    patchedCochain_restrict_of_compatible A n U R t x W j (hWU j hxj)
      hcontrol hWU hcompat⟩

end TopCat.SingularCochainSheaf
