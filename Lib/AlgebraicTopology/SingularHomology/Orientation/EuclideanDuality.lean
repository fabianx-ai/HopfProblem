/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Orientation.DualityMap
public import Lib.AlgebraicTopology.SingularCochains.DualEvaluation.Free

/-!
# The Euclidean base case of Poincaré duality

For `E = ℝ^{m+2}` and a closed ball `K`, the duality map
`D_K : H^k(E, E ∖ K) → H_{m+2-k}(E)` is an isomorphism (Hatcher, proof of Theorem 3.35, the case
`M = ℝⁿ`, `K` a ball).  The ingredients are:

* the relative chain complexes `C(X, A)` are degreewise free (`relativeComplex_free`), so the
  **universal coefficient theorem** of `Lib` applies to pairs
  (`cohomologyEvaluation_relative_isIso`): `H^{q+1}(X, A) ≅ Hom(H_{q+1}(X, A), ℤ)` when
  `H_q(X, A)` is projective, and `H^0(X, A) = 0` when `H_0(X, A) = 0`;
* `H_k(E, E ∖ K) ≅ H_k(E, E ∖ {c})` is `ℤ` in degree `m + 2` and `0` otherwise (M1), so
  `H^k(E, E ∖ K) = 0` for `k ≠ m + 2`, and `H_l(E) = 0` for `l ≠ 0` (contractibility);
* in degree `k = m + 2` the composite `H^{m+2}(E, E ∖ K) → H_0(E) ≅ ℤ` of `D_K` with the
  augmentation is the Kronecker evaluation at the relative fundamental class `μ_K`
  (`augmentation_relativeCap_top`), which generates `H_{m+2}(E, E ∖ K)`; evaluation at a
  generator is an isomorphism `Hom(H, ℤ) ≅ ℤ`.

## Main results

* `PoincareDuality.relativeComplex_free`, `cohomologyEvaluation_relative_isIso`,
  `relativeCohomology_zero_subsingleton`, `relativeCohomology_succ_subsingleton`.
* `PoincareDuality.relativeHomology_closedBall_subsingleton`,
  `relativeHomologyClosedBallEquiv`.
* `PoincareDuality.augmentation_dualityMap`, `PoincareDuality.dualityMap_closedBall_bijective`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3, Theorem 3.35 (the case of `ℝⁿ`)

## Tags

Poincaré duality, universal coefficient theorem, Euclidean space
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace PoincareDuality

open SingularChains SingularMayerVietoris RelativeSingularHomology RelativeSingularCohomology
open ManifoldOrientation SingularCapProduct CochainCocycle
open AlgebraicTopology.SingularCochains AlgebraicTopology.SingularCochains.DualEvaluation

/-! ### Freeness of relative chains and the universal coefficient theorem for pairs -/

section Pairs

variable {X : Type} [TopologicalSpace X]

/-- The relative chain groups `C_m(X, A)` are free: the complement section embeds them into
`C_m(X)`. -/
theorem relativeComplex_free (A : Set X) (m : ℕ) : Module.Free ℤ ((relativeComplex X A).X m) := by
  let s := complementSection (isSpannedBy_supportedSubmodule A m)
  have hinj : Function.Injective s := by
    intro x y hxy
    have h := congrArg ((supportedSubmodule A).π.f m).hom hxy
    rwa [π_complementSection, π_complementSection] at h
  have hfree : Module.Free ℤ (Chains X m) := LocalUCT.singularChains_free X m
  let _ : Module ℤ (LinearMap.range s) := (LinearMap.range s).module
  have : Module.Free ℤ (LinearMap.range s) := Module.FreeIntSubmodule.submodule_free_int _
  exact Module.Free.of_equiv (LinearEquiv.ofInjective s hinj).symm

instance relativeComplex_free' (A : Set X) (m : ℕ) : Module.Free ℤ ((relativeComplex X A).X m) :=
  relativeComplex_free A m

/-- **Universal coefficients for pairs**: `H^{q+1}(X, A) → Hom(H_{q+1}(X, A), ℤ)` is an isomorphism
when `H_q(X, A)` is projective. -/
theorem cohomologyEvaluation_relative_isIso (A : Set X) (q : ℕ)
    [Module.Projective ℤ (RelativeHomology X A q)] :
    IsIso (cohomologyEvaluation intCoeff (relativeComplex X A) q) :=
  LocalUCT.cohomologyEvaluation_isIso_of_free_of_projective intCoeff (relativeComplex X A) q

/-- A `0`-cocycle vanishes on every relative `0`-chain when `H_0(X, A) = 0`. -/
theorem cocycle_zero_apply_eq_zero (A : Set X) (h : Subsingleton (RelativeHomology X A 0))
    (φ : Cocycle (relativeCochains X A) 0) (z : (relativeComplex X A).X 0) :
    cochainAddHom intCoeff (relativeComplex X A) 0 φ.1 z = 0 := by
  have hz : ModuleHomology.cycleClass (relativeComplex X A) 0 (ModuleHomology.mkCycle _ 0 z (by
      rw [(relativeComplex X A).shape 0 (0 - 1) (by simp)]
      rfl)) = 0 := Subsingleton.elim _ _
  obtain ⟨b, hb⟩ := (ModuleHomology.cycleClass_eq_zero_iff _ 0 _).mp hz
  change ((relativeComplex X A).d 1 0).hom b = z at hb
  rw [← hb, ← dualComplex_d_apply_apply, cocycle_condition]
  rfl

/-- `H^0(X, A) = 0` when `H_0(X, A) = 0`. -/
theorem relativeCohomology_zero_subsingleton (A : Set X) (h : Subsingleton (RelativeHomology X A 0)) :
    Subsingleton (RelativeCohomology X A 0) := by
  constructor
  intro x y
  obtain ⟨ψ, rfl⟩ := cocycleClass_surjective _ 0 x
  obtain ⟨χ, rfl⟩ := cocycleClass_surjective _ 0 y
  rw [cocycleClass_eq_iff_zero]
  change cochainAddHom intCoeff (relativeComplex X A) 0 ψ.1 = cochainAddHom intCoeff (relativeComplex X A) 0 χ.1
  exact AddMonoidHom.ext fun z =>
    (cocycle_zero_apply_eq_zero A h ψ z).trans (cocycle_zero_apply_eq_zero A h χ z).symm

/-- `H^{q+1}(X, A) = 0` when `H_{q+1}(X, A) = 0` and `H_q(X, A)` is projective. -/
theorem relativeCohomology_succ_subsingleton (A : Set X) (q : ℕ)
    [Module.Projective ℤ (RelativeHomology X A q)] (h : Subsingleton (RelativeHomology X A (q + 1))) :
    Subsingleton (RelativeCohomology X A (q + 1)) := by
  have hiso := cohomologyEvaluation_relative_isIso A q
  have hinj : Function.Injective (cohomologyEvaluation intCoeff (relativeComplex X A) q) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp hiso).1
  have hsub : Subsingleton (RelativeHomology X A (q + 1) →+ ℤ) := ⟨fun f g => AddMonoidHom.ext fun x => by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact hinj.subsingleton

end Pairs

/-! ### Projectivity helpers -/

theorem projective_of_subsingleton {H : Type} [AddCommGroup H] [Module ℤ H] [Subsingleton H] :
    Module.Projective ℤ H :=
  haveI : Module.Free ℤ H := Module.Free.of_basis (Module.Basis.empty H : Module.Basis Empty ℤ H)
  inferInstance

theorem projective_of_equiv_int {H : Type} [AddCommGroup H] [Module ℤ H] (e : H ≃ₗ[ℤ] ℤ) :
    Module.Projective ℤ H :=
  haveI : Module.Free ℤ H := Module.Free.of_equiv e.symm
  inferInstance

/-- Evaluation at an element `g` with `e g` a unit, for an isomorphism `e : H ≃ ℤ`, is a bijection
`Hom(H, ℤ) ≅ ℤ`. -/
theorem evalAt_bijective {H : Type} [AddCommGroup H] [Module ℤ H] (e : H ≃ₗ[ℤ] ℤ) (g : H)
    (hg : IsUnit (e g)) : Function.Bijective (fun f : H →+ ℤ => f g) := by
  have hu : e g * e g = 1 := by
    rcases Int.isUnit_iff.mp hg with h | h <;> rw [h] <;> norm_num
  have hval : ∀ (f : H →+ ℤ) (x : H), f x = e x * f (e.symm 1) := by
    intro f x
    have h1 : f x = (f.comp e.symm.toAddEquiv.toAddMonoidHom) (e x) :=
      congrArg f (e.symm_apply_apply x).symm
    rw [h1, AddMonoidHom.apply_int, zsmul_eq_mul, Int.cast_id]
    rfl
  constructor
  · intro f f' hff'
    have h0 : f (e.symm 1) = f' (e.symm 1) := by
      have := congrArg (fun z => e g * z) (show f g = f' g from hff')
      simp only [hval f g, hval f' g, ← mul_assoc, hu, one_mul] at this
      exact this
    exact AddMonoidHom.ext fun x => by rw [hval f x, hval f' x, h0]
  · intro z
    refine ⟨(z * e g) • e.toLinearMap.toAddMonoidHom, ?_⟩
    change (z * e g) • e g = z
    rw [zsmul_eq_mul, Int.cast_id, mul_assoc, hu, mul_one]

/-! ### The homology of `(ℝ^{m+2}, ℝ^{m+2} ∖ closed ball)` -/

section Euclidean

variable (m : ℕ)

/-- Euclidean space is path-connected (through convexity; the contractibility route is slow for
instance search). -/
instance euclideanPathConnectedSpace : PathConnectedSpace (EuclideanSpace ℝ (Fin (m + 2))) :=
  pathConnectedSpace_iff_univ.mpr (convex_univ.isPathConnected ⟨0, trivial⟩)

theorem relativeHomology_closedBall_subsingleton (c : EuclideanSpace ℝ (Fin (m + 2))) {r : ℝ}
    (hr : 0 ≤ r) (k : ℕ) (hk : k ≠ m + 2) :
    Subsingleton (RelativeHomology (EuclideanSpace ℝ (Fin (m + 2))) (Metric.closedBall c r)ᶜ k) :=
  haveI := localHomologyEuclidean_subsingleton m c k hk
  (isHomologyBall_closedBall c r k c (Metric.mem_closedBall_self hr)).1.subsingleton

/-- `H_{m+2}(ℝ^{m+2}, ℝ^{m+2} ∖ K) ≅ ℤ` for a closed ball `K`. -/
def relativeHomologyClosedBallEquiv (c : EuclideanSpace ℝ (Fin (m + 2))) {r : ℝ} (hr : 0 ≤ r) :
    RelativeHomology (EuclideanSpace ℝ (Fin (m + 2))) (Metric.closedBall c r)ᶜ (m + 2) ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective _ (isHomologyBall_closedBall c r (m + 2) c (Metric.mem_closedBall_self hr))).trans
    (localHomologyEuclideanEquiv m c)

theorem relativeHomology_closedBall_projective (c : EuclideanSpace ℝ (Fin (m + 2))) {r : ℝ}
    (hr : 0 ≤ r) (k : ℕ) :
    Module.Projective ℤ (RelativeHomology (EuclideanSpace ℝ (Fin (m + 2))) (Metric.closedBall c r)ᶜ k) := by
  by_cases hk : k = m + 2
  · subst hk
    exact projective_of_equiv_int (relativeHomologyClosedBallEquiv m c hr)
  · have := relativeHomology_closedBall_subsingleton m c hr k hk
    exact projective_of_subsingleton

/-- `H^k(ℝ^{m+2}, ℝ^{m+2} ∖ K) = 0` for `k ≠ m + 2` and a closed ball `K`. -/
theorem relativeCohomology_closedBall_subsingleton (c : EuclideanSpace ℝ (Fin (m + 2))) {r : ℝ}
    (hr : 0 ≤ r) (k : ℕ) (hk : k ≠ m + 2) :
    Subsingleton (RelativeCohomology (EuclideanSpace ℝ (Fin (m + 2))) (Metric.closedBall c r)ᶜ k) := by
  cases k with
  | zero => exact relativeCohomology_zero_subsingleton _ (relativeHomology_closedBall_subsingleton m c hr 0 hk)
  | succ q =>
    have := relativeHomology_closedBall_projective m c hr q
    exact relativeCohomology_succ_subsingleton _ q (relativeHomology_closedBall_subsingleton m c hr (q + 1) hk)

/-! ### The duality map of a ball -/

/-- The relative fundamental class of a closed ball generates `H_{m+2}(E, E ∖ K)`. -/
theorem span_compactClass_closedBall (μ : Orientation (EuclideanSpace ℝ (Fin (m + 2))) (m + 2))
    (c : EuclideanSpace ℝ (Fin (m + 2))) {r : ℝ} (hr : 0 ≤ r) :
    Submodule.span ℤ {compactClass (by omega) μ (isCompact_closedBall c r)} = ⊤ := by
  rw [← isGenerator_localRestriction_iff (isHomologyBall_closedBall c r (m + 2))
    (Metric.mem_closedBall_self hr), ← pointRestriction_eq_localRestriction,
    pointRestriction_compactClass]
  exact μ.isGenerator c

/-- The augmentation of the top-degree duality map is the Kronecker evaluation at the relative
fundamental class: `ε(μ_K ⌢ φ) = ⟨φ, μ_K⟩`. -/
theorem augmentation_dualityMap (μ : Orientation (EuclideanSpace ℝ (Fin (m + 2))) (m + 2))
    (c : EuclideanSpace ℝ (Fin (m + 2))) (r : ℝ) (h : m + 2 + 0 = m + 2)
    (φ : RelativeCohomology (EuclideanSpace ℝ (Fin (m + 2))) (Metric.closedBall c r)ᶜ (m + 2)) :
    SingularHomology.connectedHomologyZeroEquiv (EuclideanSpace ℝ (Fin (m + 2)))
        (dualityMap (by omega) μ (isCompact_closedBall c r) (m + 2) 0 h φ) =
      cohomologyEvaluation intCoeff (relativeComplex _ (Metric.closedBall c r)ᶜ) (m + 1) φ
        (compactClass (by omega) μ (isCompact_closedBall c r)) := by
  obtain ⟨ψ, rfl⟩ := cocycleClass_surjective _ (m + 2) φ
  obtain ⟨z, hz, hzc⟩ := relativeHomologyClass_surjective (Metric.closedBall c r)ᶜ (m + 2)
    (compactClass (by omega) μ (isCompact_closedBall c r))
  rw [dualityMap_apply, ← hzc, augmentation_relativeCap_top]
  change _ = cohomologyEvaluation intCoeff _ (m + 1) (positiveCocycleClass _ (m + 1) (ofCocycle _ (m + 2) ψ))
    (HomologicalComplex.ChainCycleLift.cycleClass _ (m + 2) (relativeCycle _ (m + 2) z hz))
  rw [cohomologyEvaluation_cocycle_cycle, positiveCocycleValue_eq_literal_val]
  rfl

/-- **The Euclidean base case of Poincaré duality**: for a closed ball `K ⊆ ℝ^{m+2}` and any
orientation, `D_K : H^k(ℝ^{m+2}, ℝ^{m+2} ∖ K) → H_{m+2-k}(ℝ^{m+2})` is bijective. -/
theorem dualityMap_closedBall_bijective (μ : Orientation (EuclideanSpace ℝ (Fin (m + 2))) (m + 2))
    (c : EuclideanSpace ℝ (Fin (m + 2))) {r : ℝ} (hr : 0 ≤ r) (k l : ℕ) (h : k + l = m + 2) :
    Function.Bijective (dualityMap (by omega) μ (isCompact_closedBall c r) k l h) := by
  cases l with
  | zero =>
    have hk : k = m + 2 := by omega
    subst hk
    -- `ε ∘ D_K = ev_{μ_K} ∘ (cohomology evaluation)`, a composite of bijections
    have hε := (SingularHomology.connectedHomologyZeroEquiv (EuclideanSpace ℝ (Fin (m + 2)))).bijective
    have := relativeHomology_closedBall_projective m c hr (m + 1)
    have huct : Function.Bijective (cohomologyEvaluation intCoeff
        (relativeComplex _ (Metric.closedBall c r)ᶜ) (m + 1)) :=
      (ConcreteCategory.isIso_iff_bijective _).mp (cohomologyEvaluation_relative_isIso _ (m + 1))
    have hunit : IsUnit (relativeHomologyClosedBallEquiv m c hr
        (compactClass (by omega) μ (isCompact_closedBall c r))) :=
      Ideal.span_singleton_eq_top.mp
        ((span_singleton_eq_top_iff_of_linearEquiv (relativeHomologyClosedBallEquiv m c hr) _).mpr
          (span_compactClass_closedBall m μ c hr))
    have hev := evalAt_bijective (relativeHomologyClosedBallEquiv m c hr) _ hunit
    have hcomp : ∀ φ, SingularHomology.connectedHomologyZeroEquiv (EuclideanSpace ℝ (Fin (m + 2)))
        (dualityMap (by omega) μ (isCompact_closedBall c r) (m + 2) 0 h φ) =
        (fun f : RelativeHomology _ (Metric.closedBall c r)ᶜ (m + 2) →+ ℤ =>
          f (compactClass (by omega) μ (isCompact_closedBall c r)))
          (cohomologyEvaluation intCoeff (relativeComplex _ (Metric.closedBall c r)ᶜ) (m + 1) φ) :=
      fun φ => augmentation_dualityMap m μ c r h φ
    have hcomp' : (SingularHomology.connectedHomologyZeroEquiv (EuclideanSpace ℝ (Fin (m + 2))) ∘
        dualityMap (by omega) μ (isCompact_closedBall c r) (m + 2) 0 h) =
        (fun f : RelativeHomology _ (Metric.closedBall c r)ᶜ (m + 2) →+ ℤ =>
          f (compactClass (by omega) μ (isCompact_closedBall c r))) ∘
          cohomologyEvaluation intCoeff (relativeComplex _ (Metric.closedBall c r)ᶜ) (m + 1) :=
      funext hcomp
    have hbij := hev.comp huct
    rw [← hcomp'] at hbij
    exact ⟨fun x y hxy => hbij.1 (by simp only [Function.comp_apply, hxy]),
      fun y => by
        obtain ⟨x, hx⟩ := hbij.2 (SingularHomology.connectedHomologyZeroEquiv _ y)
        exact ⟨x, (SingularHomology.connectedHomologyZeroEquiv _).injective hx⟩⟩
  | succ l =>
    have hdom := relativeCohomology_closedBall_subsingleton m c hr k (by omega)
    have hcod := euclidean_homology_subsingleton m (l + 1) (by omega)
    exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end Euclidean

end PoincareDuality
