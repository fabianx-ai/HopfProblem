/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.AffineChains
public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric.FormalSupport

/-! # Support of realized barycentric formal chains -/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open Set

namespace TopCat.SingularSmallChains.Barycentric

variable {V M : Type} [AddCommGroup M] [Module ℤ M]

/-- A linear image belongs to a submodule when this holds on every nonzero formal generator. -/
theorem formalLinearMap_mem_of_support {n : ℕ}
    (f : FormalChains V n →ₗ[ℤ] M) (P : Submodule ℤ M) (c : FormalChains V n)
    (hf : ∀ v ∈ c.support, f (formalSimplex v) ∈ P) : f c ∈ P := by
  have h : Finsupp.supported ℤ ℤ (c.support : Set (Fin n → V)) ≤ P.comap f := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    exact hf v hv
  exact h (fun _ hv => hv)

variable {X : Type} [TopologicalSpace X]

/-- The finite-support principle for native singular chains. -/
theorem singularLinearMap_mem_of_support (n : ℕ) (f : Chains X n →ₗ[ℤ] M)
    (P : Submodule ℤ M) (c : Chains X n)
    (hf : ∀ sigma ∈ (TopCat.SingularSmallChains.chainsEquivFinsupp X n c).support,
      f (TopCat.SingularSmallChains.simplexChain X n sigma) ∈ P) : f c ∈ P := by
  let S : Set (TopCat.SingularSmallChains.SingularSimplex X n) :=
    (TopCat.SingularSmallChains.chainsEquivFinsupp X n c).support
  have hc : c ∈ Submodule.span ℤ
      (TopCat.SingularSmallChains.simplexChain X n '' S) :=
    (TopCat.SingularSmallChains.mem_simplex_span_iff X n S c).mpr (Subset.refl _)
  have h : Submodule.span ℤ
      (TopCat.SingularSmallChains.simplexChain X n '' S) ≤ P.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨sigma, hsigma, rfl⟩
    exact hf sigma hsigma
  exact h hc

/-- A linear map preserves cover-small membership when this holds on each small simplex
generator. -/
theorem singularLinearMap_mem_of_small {I : Type} (U : I → Set X) (n : ℕ)
    (f : Chains X n →ₗ[ℤ] M) (P : Submodule ℤ M) (c : Chains X n)
    (hc : c ∈ TopCat.SingularSmallChains.submodule U n)
    (hf : ∀ sigma : TopCat.SingularSmallChains.SingularSimplex X n,
      TopCat.SingularSmallChains.IsSmallSimplex U sigma →
        f (TopCat.SingularSmallChains.simplexChain X n sigma) ∈ P) :
    f c ∈ P := by
  have h : TopCat.SingularSmallChains.submodule U n ≤ P.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨sigma, hsigma, rfl⟩
    exact hf sigma hsigma
  exact h hc

/-- Every affine-chain realization stays small when its original singular simplex is small. -/
theorem realizedChain_mem_small {I : Type} (U : I → Set X) (p n : ℕ)
    (sigma : C(Simplex p, X))
    (hsigma : TopCat.SingularSmallChains.IsSmallSimplex U sigma)
    (c : FormalChains (Simplex p) (n + 1)) :
    inducedChain sigma n (affineChainMap p n c) ∈
      TopCat.SingularSmallChains.submodule U n := by
  obtain ⟨i, hi⟩ := hsigma
  apply formalLinearMap_mem_of_support
    ((inducedChain sigma n).comp (affineChainMap p n))
    (TopCat.SingularSmallChains.submodule U n) c
  intro v hv
  simp only [LinearMap.comp_apply, affineChainMap_simplex, inducedChain_simplex]
  apply TopCat.SingularSmallChains.simplexChain_mem
  refine ⟨i, ?_⟩
  rintro x ⟨t, rfl⟩
  exact hi ⟨affineSimplex v t, rfl⟩

/-- More generally, a realized chain is small when each nonzero affine term lies in a cover
member. -/
theorem realizedChain_mem_small_of_support {I : Type} (U : I → Set X) (p n : ℕ)
    (sigma : C(Simplex p, X)) (c : FormalChains (Simplex p) (n + 1))
    (hc : ∀ v ∈ c.support, ∃ i, range (sigma.comp (affineSimplex v)) ⊆ U i) :
    inducedChain sigma n (affineChainMap p n c) ∈
      TopCat.SingularSmallChains.submodule U n := by
  apply formalLinearMap_mem_of_support
    ((inducedChain sigma n).comp (affineChainMap p n))
    (TopCat.SingularSmallChains.submodule U n) c
  intro v hv
  simp only [LinearMap.comp_apply, affineChainMap_simplex, inducedChain_simplex]
  exact TopCat.SingularSmallChains.simplexChain_mem U n
    (sigma.comp (affineSimplex v)) (hc v hv)

end TopCat.SingularSmallChains.Barycentric
