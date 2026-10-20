/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularCochains.CapProduct.Cup
public import Lib.AlgebraicTopology.SingularHomology.Orientation.DualityMap

/-!
# The intersection pairing of a closed oriented manifold

For a closed oriented `n`-manifold `M` the cup product pairing
`H^k(M; ℤ) × H^{n-k}(M; ℤ) → ℤ`, `(φ, ψ) ↦ ⟨φ ∪ ψ, [M]⟩`, is the Kronecker pairing of `ψ` with the
Poincaré dual `D φ = [M] ⌢ φ` (Hatcher §3.3, the discussion before Proposition 3.38):

  `⟨φ ∪ ψ, [M]⟩ = ⟨ψ, [M] ⌢ φ⟩`  (`cohomologyEvaluation_cupProduct_fundamentalClass`).

This is the "cup/cap + duality" content of the intersection form (consumer (b)); its unimodularity
on the free parts needs in addition Poincaré duality (placeholder P-1) and the reflexivity of
finitely generated free `ℤ`-modules, and is not formalized here.

## Main results

* `SingularCapProduct.relOfCochain`, `cohomologyEquivOfEmpty_cocycleClass`,
  `relativeHomologyEquivOfEmpty_cycleClass`.
* `PoincareDuality.cohomologyEvaluation_cupProduct_fundamentalClass`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3 (Poincaré duality and the cup product
  pairing)

## Tags

intersection form, cup product, cap product, Poincaré duality
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace PoincareDuality

open SingularChains SingularMayerVietoris RelativeSingularHomology RelativeSingularCohomology
open ManifoldOrientation SingularCapProduct CochainCocycle
open AlgebraicTopology.SingularCochains AlgebraicTopology.SingularCochains.DualEvaluation

/-! ### Absolute classes as relative classes for `A = ∅` -/

section Empty

variable {X : Type} [TopologicalSpace X]

/-- An absolute cochain as a relative cochain of `(X, ∅)`. -/
def relOfCochain (k : ℕ) (φ : (complex X intCoeff).X k) : (relativeCochains X ∅).X k :=
  linearCochain intCoeff (relativeComplex X ∅) k
    (Submodule.liftQ (supportedChainSubmodule ∅ k) (toCochain k φ) (by
      rw [supportedChainSubmodule_empty]
      exact bot_le))

theorem cochainAddHom_relOfCochain (k : ℕ) (φ : (complex X intCoeff).X k) (c : Chains X k) :
    cochainAddHom intCoeff (relativeComplex X ∅) k (relOfCochain k φ) (relativeClass ∅ k c) =
      cochainAddHom intCoeff (chains X) k φ c := rfl

/-- The relative cochain restricts back to the absolute cochain. -/
theorem dualMap_relativeProjection_relOfCochain (k : ℕ) (φ : (complex X intCoeff).X k) :
    (dualMap intCoeff (relativeProjection X ∅)).f k (relOfCochain k φ) = φ :=
  AddMonoidHom.ext fun _ => rfl

/-- The lifted cochain of `relOfCochain φ` is the linear cochain of `φ`. -/
theorem liftedCochain_relOfCochain (k : ℕ) (φ : (complex X intCoeff).X k) :
    liftedCochain ∅ k (relOfCochain k φ) = toCochain k φ :=
  LinearMap.ext fun _ => rfl

/-- The relative cochain of a cocycle is a cocycle. -/
def relOfCocycle (k : ℕ) (φ : Cocycle (complex X intCoeff) k) : Cocycle (relativeCochains X ∅) k :=
  mkCocycle _ k (relOfCochain k φ.1) (by
    apply AddMonoidHom.ext
    intro z
    obtain ⟨c, rfl⟩ := exists_relativeClass_eq ∅ (k + 1) z
    change cochainAddHom intCoeff (relativeComplex X ∅) (k + 1) _ (relativeClass ∅ (k + 1) c) = 0
    rw [dualComplex_d_apply_apply, relativeComplex_d_relativeClass, cochainAddHom_relOfCochain]
    have h1 := dualComplex_d_apply_apply intCoeff (chains X) k (k + 1) φ.1 c
    rw [cocycle_condition] at h1
    exact h1.symm.trans rfl)

@[simp] theorem relOfCocycle_val (k : ℕ) (φ : Cocycle (complex X intCoeff) k) :
    (relOfCocycle k φ).1 = relOfCochain k φ.1 := rfl

/-- `H^k(X) ≅ H^k(X, ∅)` on cocycle classes. -/
theorem cohomologyEquivOfEmpty_cocycleClass (k : ℕ) (φ : Cocycle (complex X intCoeff) k) :
    cohomologyEquivOfEmpty X k (cocycleClass _ k φ) = cocycleClass _ k (relOfCocycle k φ) := by
  apply (cohomologyEquivOfEmpty X k).symm.injective
  rw [AddEquiv.symm_apply_apply]
  change cocycleClass _ k φ = cohomologyProjection ∅ k (cocycleClass _ k (relOfCocycle k φ))
  have h2 := cohomologyHom_cocycleClass (L := relativeCochains X ∅) (L' := complex X intCoeff) k
    (dualMap intCoeff (relativeProjection X ∅)) (relOfCocycle k φ)
  refine Eq.trans ?_ h2.symm
  exact congrArg (cocycleClass _ k) (Subtype.ext (dualMap_relativeProjection_relOfCochain k φ.1).symm)

/-- `H_n(X) ≅ H_n(X, ∅)` on cycle classes. -/
theorem relativeHomologyEquivOfEmpty_cycleClass (n : ℕ) (z : ModuleHomology.Cycle (singularComplex X) n) :
    relativeHomologyEquivOfEmpty X n (ModuleHomology.cycleClass _ n z) =
      relativeHomologyClass ∅ n z.1 (by
        rw [ModuleHomology.cycle_condition]
        exact Submodule.zero_mem _) := by
  rw [relativeHomologyEquivOfEmpty_apply, relativeProjectionHomologyMap_cycleClass]

end Empty

/-! ### The intersection pairing -/

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [T2Space M] [CompactSpace M]

/-- **The cup product pairing is the Kronecker pairing with the Poincaré dual**:
`⟨φ ∪ ψ, [M]⟩ = ⟨ψ, [M] ⌢ φ⟩` for `φ ∈ H^k(M)`, `ψ ∈ H^{l+1}(M)`, `k + (l + 1) = n + 1`. -/
theorem cohomologyEvaluation_cupProduct_fundamentalClass (hn : 2 ≤ n + 1)
    (μ : Orientation M (n + 1)) (k l : ℕ) (h : k + (l + 1) = n + 1)
    (φ : SingularCohomology M k) (ψ : SingularCohomology M (l + 1)) :
    cohomologyEvaluation intCoeff (chains M) n (cupProduct M k (l + 1) (n + 1) h φ ψ)
        (fundamentalClass hn μ) =
      cohomologyEvaluation intCoeff (chains M) l ψ (absoluteDualityMap hn μ k (l + 1) h φ) := by
  obtain ⟨φ, rfl⟩ := cocycleClass_surjective _ k φ
  obtain ⟨ψ, rfl⟩ := cocycleClass_surjective _ (l + 1) ψ
  obtain ⟨z, hz⟩ := ModuleHomology.cycleClass_surjective (singularComplex M) (n + 1) (fundamentalClass hn μ)
  rw [cupProduct_cocycleClass, absoluteDualityMap_apply, cohomologyEquivOfEmpty_cocycleClass, ← hz,
    relativeHomologyEquivOfEmpty_cycleClass, relativeCap_apply]
  have e1 := cohomologyEvaluation_cocycle_cycle intCoeff (chains M) n
    (ofCocycle _ (n + 1) (cupCocycle k (l + 1) (n + 1) h φ ψ)) z
  have e2 := cohomologyEvaluation_cocycle_cycle intCoeff (chains M) l (ofCocycle _ (l + 1) ψ)
    (ModuleHomology.mkCycle _ (l + 1)
      (capChain k (l + 1) (n + 1) h (liftedCochain ∅ k (relOfCocycle k φ).1) z.1)
      (capChain_isCycle ∅ k (l + 1) (n + 1) h _ (liftedCochain_eq_zero_of_mem ∅ k _)
        (coboundary_liftedCochain ∅ k _) z.1 (by
          rw [ModuleHomology.cycle_condition]
          exact Submodule.zero_mem _)))
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [positiveCocycleValue_eq_literal_val, positiveCocycleValue_eq_literal_val]
  change cochainAddHom intCoeff (chains M) (n + 1) (cupCocycle k (l + 1) (n + 1) h φ ψ).1 z.1 =
    cochainAddHom intCoeff (chains M) (l + 1) ψ.1
      (capChain k (l + 1) (n + 1) h (liftedCochain ∅ k (relOfCocycle k φ).1) z.1)
  rw [cupCocycle_val, cochainAddHom_ofCochain, relOfCocycle_val, liftedCochain_relOfCochain]
  rfl

end Manifold

end PoincareDuality
