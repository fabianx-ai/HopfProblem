/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.AffineChains
public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.FormalIteration

/-!
# Barycentric subdivision on native singular chains

The universal subdivided simplex is evaluated as genuine affine singular simplices and then
pushed forward by the original singular simplex.  These operators act directly on Mathlib's
native integral singular-chain complex.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace TopCat.SingularSmallChains.Barycentric

/-- `k` barycentric subdivisions of native integral singular chains. -/
def subdivision (X : Type) [TopologicalSpace X] (k n : ℕ) :
    Chains X n →ₗ[ℤ] Chains X n :=
  TopCat.SingularSmallChains.chainLift X n fun sigma => inducedChain sigma n
    (affineChainMap n n
      ((formalSubdivision (simplexCenter n) (n + 1))^[k]
        (formalSimplex (stdVertices n))))

@[simp]
theorem subdivision_simplex (X : Type) [TopologicalSpace X] (k n : ℕ)
    (sigma : TopCat.SingularSmallChains.SingularSimplex X n) :
    subdivision X k n (TopCat.SingularSmallChains.simplexChain X n sigma) =
      inducedChain sigma n
        (affineChainMap n n
          ((formalSubdivision (simplexCenter n) (n + 1))^[k]
            (formalSimplex (stdVertices n)))) :=
  TopCat.SingularSmallChains.chainLift_simplex X n _ sigma

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The zeroth subdivision iterate is the identity. -/
@[simp]
theorem subdivision_zero (n : ℕ) (c : Chains X n) : subdivision X 0 n c = c := by
  have h : subdivision X 0 n = LinearMap.id := by
    apply TopCat.SingularSmallChains.chainMap_ext X n
    intro sigma
    simp only [subdivision_simplex, Function.iterate_zero_apply,
      affineChainMap_stdVertices, inducedChain_simplex, ContinuousMap.comp_id,
      LinearMap.id_apply]
  exact LinearMap.congr_fun h c

/-- Subdivision is natural under every continuous map. -/
theorem inducedChain_subdivision (f : C(X, Y)) (k n : ℕ) (c : Chains X n) :
    inducedChain f n (subdivision X k n c) =
      subdivision Y k n (inducedChain f n c) := by
  have h : (inducedChain f n).comp (subdivision X k n) =
      (subdivision Y k n).comp (inducedChain f n) := by
    apply TopCat.SingularSmallChains.chainMap_ext X n
    intro sigma
    simp only [LinearMap.comp_apply, subdivision_simplex, inducedChain_simplex]
    rw [inducedChain_comp]
    rfl
  exact LinearMap.congr_fun h c

/-- The image of the ordered standard vertices under an affine simplex map. -/
theorem affineSimplex_comp_stdVertices {n p : ℕ} (v : Fin (n + 1) → Simplex p) :
    affineSimplex v ∘ stdVertices n = v := by
  funext i
  exact affineSimplex_vertex v i

/-- On an affine simplex, native subdivision evaluates the corresponding formal subdivision. -/
theorem subdivision_affineChainMap (p k n : ℕ)
    (c : FormalChains (Simplex p) (n + 1)) :
    subdivision (Simplex p) k n (affineChainMap p n c) =
      affineChainMap p n ((formalSubdivision (simplexCenter p) (n + 1))^[k] c) := by
  have h : (subdivision (Simplex p) k n).comp (affineChainMap p n) =
      (affineChainMap p n).comp ((formalSubdivision (simplexCenter p) (n + 1)) ^ k) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, affineChainMap_simplex, subdivision_simplex,
      Module.End.pow_apply]
    rw [inducedChain_affineChainMap,
      formalMap_subdivision_iterate (simplexCenter n) (simplexCenter p)
        (affineSimplex v) (affineSimplex_preserves_center v),
      formalMap_simplex, affineSimplex_comp_stdVertices]
  simpa only [LinearMap.comp_apply, Module.End.pow_apply] using LinearMap.congr_fun h c

/-- Barycentric subdivision commutes with every nonzero native singular differential. -/
theorem subdivision_boundary (k n : ℕ) (c : Chains X (n + 1)) :
    ((singularComplex X).d (n + 1) n).hom (subdivision X k (n + 1) c) =
      subdivision X k n (((singularComplex X).d (n + 1) n).hom c) := by
  have h : (((singularComplex X).d (n + 1) n).hom).comp
      (subdivision X k (n + 1)) =
      (subdivision X k n).comp ((singularComplex X).d (n + 1) n).hom := by
    apply TopCat.SingularSmallChains.chainMap_ext X (n + 1)
    intro sigma
    change ((singularComplex X).d (n + 1) n).hom
        (subdivision X k (n + 1)
          (TopCat.SingularSmallChains.simplexChain X (n + 1) sigma)) = _
    rw [subdivision_simplex, ← inducedChain_boundary, affineChainMap_boundary,
      formalBoundary_subdivision_iterate, ← subdivision_affineChainMap,
      inducedChain_subdivision, ← affineChainMap_boundary, inducedChain_boundary,
      affineChainMap_stdVertices, inducedChain_simplex, ContinuousMap.comp_id]
    rfl
  exact LinearMap.congr_fun h c

/-- Adding iteration counts composes subdivision operators. -/
theorem subdivision_add (k l n : ℕ) (c : Chains X n) :
    subdivision X (k + l) n c = subdivision X k n (subdivision X l n c) := by
  have h : subdivision X (k + l) n =
      (subdivision X k n).comp (subdivision X l n) := by
    apply TopCat.SingularSmallChains.chainMap_ext X n
    intro sigma
    simp only [LinearMap.comp_apply, subdivision_simplex]
    rw [← inducedChain_subdivision, subdivision_affineChainMap,
      Function.iterate_add_apply]
  exact LinearMap.congr_fun h c

/-- The universal `k`-fold formula is the iterate of one subdivision. -/
theorem subdivision_eq_iterate (k n : ℕ) (c : Chains X n) :
    subdivision X k n c = (subdivision X 1 n)^[k] c := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        _ = subdivision X 1 n (subdivision X k n c) := by
          rw [Nat.add_comm k 1, subdivision_add]
        _ = (subdivision X 1 n)^[k + 1] c := by
          rw [Function.iterate_succ_apply', ih]

/-- Barycentric subdivision as a native singular-chain map. -/
def subdivisionChainMap (X : Type) [TopologicalSpace X] (k : ℕ) :
    singularComplex X ⟶ singularComplex X where
  f n := ModuleCat.ofHom (subdivision X k n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact subdivision_boundary k j c

@[simp]
theorem subdivisionChainMap_f (X : Type) [TopologicalSpace X] (k n : ℕ) :
    ((subdivisionChainMap X k).f n).hom = subdivision X k n := rfl

/-- Subdivision commutes with every differential, including shape-zero differentials. -/
theorem subdivision_d (k i j : ℕ) (c : Chains X i) :
    ((singularComplex X).d i j).hom (subdivision X k i c) =
      subdivision X k j (((singularComplex X).d i j).hom c) :=
  congrArg (fun f : Chains X i ⟶ Chains X j => f.hom c)
    ((subdivisionChainMap X k).comm i j)

/-- Naturality at the level of native singular chain maps. -/
theorem subdivisionChainMap_natural (f : C(X, Y)) (k : ℕ) :
    subdivisionChainMap X k ≫ singularChainMap f =
      singularChainMap f ≫ subdivisionChainMap Y k := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact inducedChain_subdivision f k n c

end TopCat.SingularSmallChains.Barycentric
