/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Orientation.FundamentalClass
public import Lib.AlgebraicTopology.SingularCochains.CapProduct.Relative

/-!
# The duality maps of an oriented manifold

For an oriented `n`-manifold `M` (M1/M2: `ChartedSpace (EuclideanSpace ℝ (Fin n)) M`, `T2Space M`,
an `Orientation M n`, `n ≥ 2`) and a compact `K ⊆ M`, Lemma 3.27 provides the **relative
fundamental class** `μ_K ∈ H_n(M, M ∖ K)` (`compactClass`), the unique class restricting to the
orientation at every point of `K`; it is compatible with the restrictions along `K ⊆ K'`.  The
**duality map** of Hatcher's proof of Theorem 3.35 is

  `D_K : H^k(M, M ∖ K) → H_{n-k}(M)`, `φ ↦ μ_K ⌢ φ`

(`dualityMap`), compatible with the restriction maps `H^k(M, M ∖ K) → H^k(M, M ∖ K')` for
`K ⊆ K'` (`dualityMap_cohomologyRestriction`), so that it passes to the direct limit
`H^k_c(M) → H_{n-k}(M)`.  For closed `M` the absolute duality map `H^k(M) → H_{n-k}(M)`,
`φ ↦ [M] ⌢ φ`, is `absoluteDualityMap`.

## Main definitions and results

* `PoincareDuality.compactClass`, `pointRestriction_compactClass`, `compactClass_unique`,
  `restriction_compactClass`.
* `PoincareDuality.dualityMap`, `dualityMap_cohomologyRestriction`.
* `PoincareDuality.cohomologyEquivOfEmpty`, `PoincareDuality.absoluteDualityMap`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3, the proof of Theorem 3.35

## Tags

Poincaré duality, cap product, fundamental class
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace PoincareDuality

open SingularChains SingularMayerVietoris RelativeSingularHomology RelativeSingularCohomology
open ManifoldOrientation SingularCapProduct CochainCocycle
open AlgebraicTopology.SingularCochains AlgebraicTopology.SingularCochains.DualEvaluation

variable {M : Type} [TopologicalSpace M] {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [T2Space M]

/-! ### The relative fundamental class of a compact set -/

/-- The relative fundamental class `μ_K ∈ H_n(M, M ∖ K)` of a compact set `K` (Hatcher, Lemma
3.27 (b)): the class restricting to the orientation at every point of `K`. -/
def compactClass (hn : 2 ≤ n) (μ : Orientation M n) {K : Set M} (hK : IsCompact K) :
    RelativeHomology M Kᶜ n :=
  Classical.choose
    ((LocalToGlobal.of_isCompact hn hK).exists_of_consistent μ.cls μ.isLocallyConsistent)

theorem pointRestriction_compactClass (hn : 2 ≤ n) (μ : Orientation M n) {K : Set M}
    (hK : IsCompact K) {x : M} (hx : x ∉ Kᶜ) :
    pointRestriction hx n (compactClass hn μ hK) = μ.cls x :=
  Classical.choose_spec
    ((LocalToGlobal.of_isCompact hn hK).exists_of_consistent μ.cls μ.isLocallyConsistent) x hx

/-- The relative fundamental class is the unique class restricting to the orientation on `K`. -/
theorem compactClass_unique (hn : 2 ≤ n) (μ : Orientation M n) {K : Set M} (hK : IsCompact K)
    (α : RelativeHomology M Kᶜ n) (h : ∀ x (hx : x ∉ Kᶜ), pointRestriction hx n α = μ.cls x) :
    α = compactClass hn μ hK := by
  rw [← sub_eq_zero]
  apply (LocalToGlobal.of_isCompact hn hK).unique
  intro x hx
  rw [map_sub, h x hx, pointRestriction_compactClass, sub_self]

/-- The relative fundamental classes are compatible with restriction: for `K ⊆ K'`, `μ_{K'}`
restricts to `μ_K`. -/
theorem restriction_compactClass (hn : 2 ≤ n) (μ : Orientation M n) {K K' : Set M}
    (hK : IsCompact K) (hK' : IsCompact K') (hKK' : K ⊆ K') :
    restriction (compl_subset_compl.mpr hKK') n (compactClass hn μ hK') = compactClass hn μ hK := by
  apply compactClass_unique
  intro x hx
  rw [pointRestriction_restriction, pointRestriction_compactClass]

/-- For closed `M`, the relative fundamental class of `M` itself is the fundamental class. -/
theorem restriction_fundamentalClass [CompactSpace M] (hn : 2 ≤ n) (μ : Orientation M n) :
    restriction (empty_subset (univ : Set M)ᶜ) n
        (relativeHomologyEquivOfEmpty M n (fundamentalClass hn μ)) =
      compactClass hn μ isCompact_univ := by
  apply compactClass_unique
  intro x hx
  rw [pointRestriction_restriction]
  exact absoluteRestriction_fundamentalClass hn μ x

/-! ### The duality maps -/

/-- The duality map `D_K : H^k(M, M ∖ K) → H_l(M)`, `φ ↦ μ_K ⌢ φ`, for `k + l = n`. -/
def dualityMap (hn : 2 ≤ n) (μ : Orientation M n) {K : Set M} (hK : IsCompact K) (k l : ℕ)
    (h : k + l = n) : RelativeCohomology M Kᶜ k →+ SingularHomology M l :=
  (LinearMap.applyₗ (compactClass hn μ hK)).toAddMonoidHom.comp (relativeCap Kᶜ k l n h)

theorem dualityMap_apply (hn : 2 ≤ n) (μ : Orientation M n) {K : Set M} (hK : IsCompact K) (k l : ℕ)
    (h : k + l = n) (φ : RelativeCohomology M Kᶜ k) :
    dualityMap hn μ hK k l h φ = relativeCap Kᶜ k l n h φ (compactClass hn μ hK) := rfl

/-- The duality maps are compatible with restriction along `K ⊆ K'`:
`D_{K'} (φ|_{(M, M ∖ K')}) = D_K φ`. -/
theorem dualityMap_cohomologyRestriction (hn : 2 ≤ n) (μ : Orientation M n) {K K' : Set M}
    (hK : IsCompact K) (hK' : IsCompact K') (hKK' : K ⊆ K') (k l : ℕ) (h : k + l = n)
    (φ : RelativeCohomology M Kᶜ k) :
    dualityMap hn μ hK' k l h (cohomologyRestriction (compl_subset_compl.mpr hKK') k φ) =
      dualityMap hn μ hK k l h φ := by
  rw [dualityMap_apply, dualityMap_apply, relativeCap_cohomologyRestriction,
    restriction_compactClass hn μ hK hK' hKK']

/-! ### The absolute duality map of a closed manifold -/

/-- `H^k(X) ≅ H^k(X, ∅)`, the inverse of the map induced by the relative projection. -/
def cohomologyEquivOfEmpty (X : Type) [TopologicalSpace X] (k : ℕ) :
    SingularCohomology X k ≃+ RelativeCohomology X ∅ k :=
  (AddEquiv.ofBijective (cohomologyProjection ∅ k) (by
    have : IsIso (dualMap intCoeff (relativeProjection X ∅)) := by
      rw [← relativeComplexIsoOfEmpty_hom]
      infer_instance
    exact (ConcreteCategory.isIso_iff_bijective _).mp
      (inferInstanceAs (IsIso (HomologicalComplex.homologyMap
        (dualMap intCoeff (relativeProjection X ∅)) k))))).symm

theorem cohomologyProjection_cohomologyEquivOfEmpty (X : Type) [TopologicalSpace X] (k : ℕ)
    (φ : SingularCohomology X k) :
    cohomologyProjection ∅ k (cohomologyEquivOfEmpty X k φ) = φ :=
  (AddEquiv.ofBijective (cohomologyProjection ∅ k) _).apply_symm_apply φ

/-- The absolute duality map `H^k(M) → H_l(M)`, `φ ↦ [M] ⌢ φ`, of a closed oriented manifold,
`k + l = n`. -/
def absoluteDualityMap [CompactSpace M] (hn : 2 ≤ n) (μ : Orientation M n) (k l : ℕ) (h : k + l = n) :
    SingularCohomology M k →+ SingularHomology M l :=
  ((LinearMap.applyₗ (relativeHomologyEquivOfEmpty M n (fundamentalClass hn μ))).toAddMonoidHom.comp
    (relativeCap ∅ k l n h)).comp (cohomologyEquivOfEmpty M k).toAddMonoidHom

theorem absoluteDualityMap_apply [CompactSpace M] (hn : 2 ≤ n) (μ : Orientation M n) (k l : ℕ)
    (h : k + l = n) (φ : SingularCohomology M k) :
    absoluteDualityMap hn μ k l h φ =
      relativeCap ∅ k l n h (cohomologyEquivOfEmpty M k φ)
        (relativeHomologyEquivOfEmpty M n (fundamentalClass hn μ)) := rfl

/-- For closed `M`, the relative fundamental class of `M` restricts (along `M ∖ M = ∅`) to the
fundamental class. -/
theorem restriction_compactClass_univ [CompactSpace M] (hn : 2 ≤ n) (μ : Orientation M n) :
    restriction (compl_univ (α := M)).subset n (compactClass hn μ isCompact_univ) =
      relativeHomologyEquivOfEmpty M n (fundamentalClass hn μ) := by
  rw [← (relativeHomologyEquivOfEmpty M n).apply_symm_apply
    (restriction (compl_univ (α := M)).subset n (compactClass hn μ isCompact_univ))]
  congr 1
  apply fundamentalClass_unique
  intro x
  rw [absoluteRestriction_apply, LinearEquiv.apply_symm_apply, pointRestriction_restriction,
    pointRestriction_compactClass]

/-- The absolute duality map of a closed manifold is the duality map of the compact set `M`
through `H^k(M) ≅ H^k(M, ∅) → H^k(M, M ∖ M)`. -/
theorem absoluteDualityMap_eq [CompactSpace M] (hn : 2 ≤ n) (μ : Orientation M n) (k l : ℕ)
    (h : k + l = n) (φ : SingularCohomology M k) :
    absoluteDualityMap hn μ k l h φ =
      dualityMap hn μ (K := univ) isCompact_univ k l h
        (cohomologyRestriction (A := (univ : Set M)ᶜ) (A' := ∅) (compl_univ (α := M)).subset k
          (cohomologyEquivOfEmpty M k φ)) := by
  rw [absoluteDualityMap_apply, dualityMap_apply, relativeCap_cohomologyRestriction,
    restriction_compactClass_univ]

end PoincareDuality
