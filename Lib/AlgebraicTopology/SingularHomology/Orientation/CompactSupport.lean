/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Orientation.DualityMap

/-!
# Compactly supported cohomology and the limit duality map

Hatcher's compactly supported cohomology `H^k_c(M) = colim_K H^k(M, M ∖ K)`, the direct limit
over the compact subsets `K` of `M` (directed by inclusion) of the relative cohomology groups along
the restriction maps `H^k(M, M ∖ K) → H^k(M, M ∖ K')` for `K ⊆ K'` (§3.3, before Theorem 3.35),
and the **limit duality map** `D_M : H^k_c(M) → H_{n-k}(M)` of an oriented `n`-manifold assembled
from the duality maps `D_K` of `DualityMap.lean`, which are compatible with the restrictions
(`dualityMap_cohomologyRestriction`).  For closed `M` the component at `K = M` is the absolute
duality map (`limitDualityMap_of_univ`).

This is the object on which the Mayer–Vietoris induction of Theorem 3.35 runs (placeholder P-1 of
`Lib/reports/poincare/PLACEHOLDERS.md`); the induction itself is not formalized.

## Main definitions and results

* `PoincareDuality.compactRestriction`, the directed system of relative cohomology groups.
* `PoincareDuality.CompactlySupportedCohomology M k`, `PoincareDuality.ofCompact`.
* `PoincareDuality.limitDualityMap`, `limitDualityMap_ofCompact`, `limitDualityMap_of_univ`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3 (cohomology with compact supports)

## Tags

Poincaré duality, compact support, direct limit
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace PoincareDuality

open SingularChains SingularMayerVietoris RelativeSingularHomology RelativeSingularCohomology
open ManifoldOrientation SingularCapProduct CochainCocycle TopologicalSpace
open AlgebraicTopology.SingularCochains AlgebraicTopology.SingularCochains.DualEvaluation

/-! ### Functoriality of the restriction maps -/

section Restriction

variable {X : Type} [TopologicalSpace X]

theorem cohomologyRestriction_refl (A : Set X) (q : ℕ) :
    cohomologyRestriction (subset_refl A) q = AddMonoidHom.id _ := by
  have h : restrictionChainMap (subset_refl A) = 𝟙 (relativeComplex X A) :=
    ChainSubmodule.quotientMap_id _
  change CohomologyLongExact.cohomologyHom (dualMap intCoeff (restrictionChainMap (subset_refl A))) q = _
  rw [h, dualMap_id, CohomologyLongExact.cohomologyHom, HomologicalComplex.homologyMap_id]
  rfl

theorem cohomologyRestriction_trans {A A' A'' : Set X} (h : A ⊆ A') (h' : A' ⊆ A'') (q : ℕ)
    (φ : RelativeCohomology X A'' q) :
    cohomologyRestriction h q (cohomologyRestriction h' q φ) = cohomologyRestriction (h.trans h') q φ := by
  have hc : restrictionChainMap h ≫ restrictionChainMap h' = restrictionChainMap (h.trans h') :=
    ChainSubmodule.quotientMap_comp _ _
  change CohomologyLongExact.cohomologyHom (dualMap intCoeff (restrictionChainMap h)) q
    (CohomologyLongExact.cohomologyHom (dualMap intCoeff (restrictionChainMap h')) q φ) =
    CohomologyLongExact.cohomologyHom (dualMap intCoeff (restrictionChainMap (h.trans h'))) q φ
  rw [← hc, dualMap_comp, CohomologyLongExact.cohomologyHom_comp]
  rfl

end Restriction

/-! ### The directed system and its limit -/

section Limit

variable (M : Type) [TopologicalSpace M] (k : ℕ)

/-- The restriction `H^k(M, M ∖ K) → H^k(M, M ∖ K')` for compact `K ⊆ K'`. -/
def compactRestriction (K K' : Compacts M) (h : K ≤ K') :
    RelativeCohomology M (K : Set M)ᶜ k →+ RelativeCohomology M (K' : Set M)ᶜ k :=
  cohomologyRestriction (compl_subset_compl.mpr h) k

instance compactRestriction_directedSystem :
    DirectedSystem (fun K : Compacts M => RelativeCohomology M (K : Set M)ᶜ k)
      (fun K K' h => compactRestriction M k K K' h) where
  map_self K φ := by
    change cohomologyRestriction (subset_refl _) k φ = φ
    rw [cohomologyRestriction_refl]
    rfl
  map_map _ _ _ _ _ φ := cohomologyRestriction_trans _ _ k φ

/-- **Compactly supported cohomology** `H^k_c(M) = colim_K H^k(M, M ∖ K)` over the compact
subsets of `M`. -/
abbrev CompactlySupportedCohomology : Type :=
  DirectLimit (fun K : Compacts M => RelativeCohomology M (K : Set M)ᶜ k) (compactRestriction M k)

/-- The canonical map `H^k(M, M ∖ K) → H^k_c(M)`. -/
def ofCompact (K : Compacts M) : RelativeCohomology M (K : Set M)ᶜ k →+ CompactlySupportedCohomology M k :=
  AddMonoidHom.mk' (fun φ => (⟦⟨K, φ⟩⟧ : CompactlySupportedCohomology M k)) fun x y =>
    (DirectLimit.add_def (f := compactRestriction M k) K x y).symm

theorem ofCompact_apply (K : Compacts M) (φ : RelativeCohomology M (K : Set M)ᶜ k) :
    ofCompact M k K φ = ⟦⟨K, φ⟩⟧ := rfl

/-- The canonical maps are compatible with restriction. -/
theorem ofCompact_compactRestriction (K K' : Compacts M) (h : K ≤ K')
    (φ : RelativeCohomology M (K : Set M)ᶜ k) :
    ofCompact M k K' (compactRestriction M k K K' h φ) = ofCompact M k K φ := by
  rw [ofCompact_apply, ofCompact_apply]
  exact DirectLimit.mk_apply (f := compactRestriction M k) K K' φ h

/-- Every compactly supported class comes from some `H^k(M, M ∖ K)`. -/
theorem exists_ofCompact_eq (x : CompactlySupportedCohomology M k) :
    ∃ (K : Compacts M) (φ : RelativeCohomology M (K : Set M)ᶜ k), ofCompact M k K φ = x := by
  obtain ⟨K, φ, rfl⟩ := DirectLimit.exists_eq_mk (compactRestriction M k) x
  exact ⟨K, φ, rfl⟩

end Limit

/-! ### The limit duality map -/

section Duality

variable {M : Type} [TopologicalSpace M] {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [T2Space M]

/-- The limit duality map `D_M : H^k_c(M) → H_l(M)`, `k + l = n`, assembled from the `D_K`. -/
def limitDualityMap (hn : 2 ≤ n) (μ : Orientation M n) (k l : ℕ) (h : k + l = n) :
    CompactlySupportedCohomology M k →+ SingularHomology M l :=
  AddMonoidHom.mk'
    (DirectLimit.lift (compactRestriction M k) (fun K => dualityMap hn μ K.isCompact k l h)
      (fun K K' hKK' φ => (dualityMap_cohomologyRestriction hn μ K.isCompact K'.isCompact hKK' k l h φ).symm))
    (DirectLimit.lift_add (f := compactRestriction M k)
      (fun K => dualityMap hn μ K.isCompact k l h) _)

/-- On the component at `K`, the limit duality map is `D_K`. -/
theorem limitDualityMap_ofCompact (hn : 2 ≤ n) (μ : Orientation M n) (k l : ℕ) (h : k + l = n)
    (K : Compacts M) (φ : RelativeCohomology M (K : Set M)ᶜ k) :
    limitDualityMap hn μ k l h (ofCompact M k K φ) = dualityMap hn μ K.isCompact k l h φ := rfl

/-- For closed `M`, the limit duality map on the component at `K = M` is the absolute duality
map. -/
theorem limitDualityMap_of_univ [CompactSpace M] (hn : 2 ≤ n) (μ : Orientation M n) (k l : ℕ)
    (h : k + l = n) (φ : SingularCohomology M k) :
    limitDualityMap hn μ k l h (ofCompact M k ⊤
        (cohomologyRestriction (A := (univ : Set M)ᶜ) (A' := ∅) (compl_univ (α := M)).subset k
          (cohomologyEquivOfEmpty M k φ))) =
      absoluteDualityMap hn μ k l h φ := by
  rw [limitDualityMap_ofCompact, absoluteDualityMap_eq]

end Duality

end PoincareDuality
