/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Basic

/-! # Native singular-chain operations used by barycentric subdivision -/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

namespace TopCat.SingularSmallChains.Barycentric

/-- Mathlib's actual standard topological `n`-simplex. -/
abbrev Simplex (n : ℕ) := stdSimplex ℝ (Fin (n + 1))

/-- The underlying native integral singular-chain group. -/
abbrev Chains (X : Type) [TopologicalSpace X] (n : ℕ) :=
  (AlgebraicTopology.SingularCochains.chains X).X n

/-- The underlying native integral singular-chain complex. -/
abbrev singularComplex (X : Type) [TopologicalSpace X] :=
  AlgebraicTopology.SingularCochains.chains X

/-- The native singular chain map induced by a continuous map. -/
abbrev singularChainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : singularComplex X ⟶ singularComplex Y :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)

/-- The induced linear map on native singular chains. -/
abbrev inducedChain {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) : Chains X n →ₗ[ℤ] Chains Y n :=
  ((singularChainMap f).f n).hom

theorem simplexFace_apply (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    TopCat.SingularSmallChains.simplexFace n i s = stdSimplex.map i.succAbove s := rfl

@[simp]
theorem simplexFace_apply_self (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    TopCat.SingularSmallChains.simplexFace n i s i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (s : Fin (n + 1) → ℝ) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro k hk
  exact False.elim (Fin.succAbove_ne i k (Finset.mem_filter.mp hk).2)

@[simp]
theorem simplexFace_apply_succAbove (n : ℕ) (i : Fin (n + 2))
    (s : Simplex n) (k : Fin (n + 1)) :
    TopCat.SingularSmallChains.simplexFace n i s (i.succAbove k) = s k := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (s : Fin (n + 1) → ℝ)
    (i.succAbove k) = s k
  simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_right_injective.eq_iff,
    Finset.sum_filter]

theorem simplexZero_eq_vertex (s : Simplex 0) :
    s = stdSimplex.vertex (S := ℝ) (0 : Fin 1) := by
  let : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  apply Subtype.ext
  funext k
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  change s 0 = 1
  exact stdSimplex.eq_one_of_unique (s : stdSimplex ℝ (Fin 1)) (0 : Fin 1)

theorem simplexIndex_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (sigma : TopCat.SingularSmallChains.SingularSimplex X n) :
    (TopCat.toSSet.map (TopCat.ofHom f)).app
        (Opposite.op (SimplexCategory.mk n))
        (TopCat.SingularSmallChains.simplexIndex X n sigma) =
      TopCat.SingularSmallChains.simplexIndex Y n (f.comp sigma) := rfl

@[simp]
theorem inducedChain_simplex {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (sigma : TopCat.SingularSmallChains.SingularSimplex X n) :
    inducedChain f n (TopCat.SingularSmallChains.simplexChain X n sigma) =
      TopCat.SingularSmallChains.simplexChain Y n (f.comp sigma) := by
  have h := SSet.ι_chainComplexMap_f
    (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y))
    (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)
    (TopCat.SingularSmallChains.simplexIndex X n sigma)
  exact congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ Chains Y n => g.hom 1) h

theorem inducedChain_boundary {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (i j : ℕ) (c : Chains X i) :
    inducedChain f j ((singularComplex X).d i j c) =
      (singularComplex Y).d i j (inducedChain f i c) :=
  congrArg (fun g : Chains X i ⟶ Chains Y j => g.hom c) ((singularChainMap f).comm i j).symm

theorem inducedChain_comp {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    inducedChain (g.comp f) n = (inducedChain g n).comp (inducedChain f n) := by
  apply TopCat.SingularSmallChains.chainMap_ext X n
  intro sigma
  simp only [LinearMap.comp_apply, inducedChain_simplex]
  rfl

end TopCat.SingularSmallChains.Barycentric
