/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Orientation.EuclideanDuality

/-!
# Consequences of Poincaré duality for closed oriented manifolds

The statement of Poincaré duality for a closed oriented `n`-manifold is recorded as the hypothesis
structure `PoincareDuality.IsPoincareDuality hn μ` ("every absolute duality map
`φ ↦ [M] ⌢ φ : H^k(M) → H_{n-k}(M)` is bijective"); its proof (the Mayer–Vietoris and union
inductions of Hatcher's Theorem 3.35, Lemma 3.36) is registered in
`Lib/reports/poincare/PLACEHOLDERS.md` and not formalized here.  What this file proves:

* unconditional consequences of the universal coefficient theorem: `H^0(X)` is torsion-free,
  `H^{q+1}(X)` is torsion-free when `H_q(X)` is projective, and `H^{q+1}(X) = 0` when moreover
  `H_{q+1}(X) = 0`; for a closed connected oriented manifold, `H^k(M) = 0` for `k > n`;
* under the duality hypothesis: `H^k(M) ≃ H_{n-k}(M)`, `H^n(M) ≅ ℤ` for connected `M`, and the
  **torsion dictionary in dimension 4**: for a closed connected oriented 4-manifold with finitely
  generated homology and torsion-free `H_1`, every `H^q(M; ℤ)` is torsion-free
  (consumer (a) in generic form).

## Main definitions and results

* `PoincareDuality.IsPoincareDuality`.
* `PoincareDuality.cohomology_zero_isTorsionFree`, `cohomology_succ_isTorsionFree`,
  `cohomology_succ_subsingleton`, `cohomology_subsingleton_of_lt`.
* `PoincareDuality.IsPoincareDuality.cohomologyEquiv`, `.cohomology_top_equiv_int`,
  `.cohomology_isTorsionFree_of_dim_four`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.1 (universal coefficients), §3.3
  (Theorem 3.35 and its corollaries)

## Tags

Poincaré duality, universal coefficient theorem, torsion
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace PoincareDuality

open SingularChains SingularMayerVietoris RelativeSingularHomology RelativeSingularCohomology
open ManifoldOrientation SingularCapProduct CochainCocycle
open AlgebraicTopology.SingularCochains AlgebraicTopology.SingularCochains.DualEvaluation

/-! ### Torsion-freeness through the universal coefficient theorem -/

/-- Integer-valued additive maps form a torsion-free group. -/
theorem isTorsionFree_addMonoidHom_int (A : Type) [AddCommGroup A] :
    Module.IsTorsionFree ℤ (A →+ ℤ) where
  isSMulRegular r hr f g hfg := by
    have hr0 : r ≠ 0 := isRegular_iff_ne_zero.mp hr
    ext x
    have h := congrArg (fun k : A →+ ℤ => k x) hfg
    simp only [AddMonoidHom.smul_apply, zsmul_eq_mul] at h
    exact mul_left_cancel₀ hr0 h

/-- Torsion-freeness does not depend on the choice of the (unique) integral module structure. -/
theorem isTorsionFree_int_congr {H : Type} [AddCommGroup H] (i₁ i₂ : Module ℤ H)
    (h : @Module.IsTorsionFree ℤ H _ _ i₁) : @Module.IsTorsionFree ℤ H _ _ i₂ := by
  rw [Subsingleton.elim i₂ i₁]
  exact h

/-- Torsion-freeness transfers along an injective additive map (for the integral module structures
of the additive groups). -/
theorem isTorsionFree_of_injective {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (hB : Module.IsTorsionFree ℤ B) : Module.IsTorsionFree ℤ A :=
  hf.moduleIsTorsionFree f fun r m => map_zsmul f r m

section UCT

variable (X : Type) [TopologicalSpace X]

instance singularChains_free' (k : ℕ) : Module.Free ℤ ((chains X).X k) :=
  LocalUCT.singularChains_free X k

/-- `H^0(X; ℤ)` is torsion-free: a `0`-cocycle class is determined by its cocycle, an integer-valued
functional on `0`-chains. -/
theorem cohomology_zero_isTorsionFree : Module.IsTorsionFree ℤ (SingularCohomology X 0) := by
  let f : SingularCohomology X 0 →+ (complex X intCoeff).X 0 :=
    cohomologyDescZero _ (AddSubgroup.subtype _)
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨z, rfl⟩ := cocycleClass_surjective _ 0 x
    obtain ⟨w, rfl⟩ := cocycleClass_surjective _ 0 y
    rw [cocycleClass_eq_iff_zero]
    simpa [f, cohomologyDescZero_cocycleClass] using hxy
  exact isTorsionFree_of_injective f hf (isTorsionFree_addMonoidHom_int ((chains X).X 0))

/-- `H^{q+1}(X; ℤ)` is torsion-free when `H_q(X; ℤ)` is projective (universal coefficients:
`H^{q+1} ≅ Hom(H_{q+1}, ℤ)`). -/
theorem cohomology_succ_isTorsionFree (q : ℕ) [Module.Projective ℤ (SingularHomology X q)] :
    Module.IsTorsionFree ℤ (SingularCohomology X (q + 1)) := by
  have : Module.Projective ℤ ((chains X).homology q) :=
    inferInstanceAs (Module.Projective ℤ (SingularHomology X q))
  have hiso := LocalUCT.cohomologyEvaluation_isIso_of_free_of_projective intCoeff (chains X) q
  have hinj : Function.Injective (cohomologyEvaluation intCoeff (chains X) q).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).mp hiso).1
  exact isTorsionFree_of_injective _ hinj (isTorsionFree_addMonoidHom_int _)

/-- `H^{q+1}(X; ℤ) = 0` when `H_{q+1}(X; ℤ) = 0` and `H_q(X; ℤ)` is projective. -/
theorem cohomology_succ_subsingleton (q : ℕ) [Module.Projective ℤ (SingularHomology X q)]
    (h : Subsingleton (SingularHomology X (q + 1))) : Subsingleton (SingularCohomology X (q + 1)) := by
  have : Module.Projective ℤ ((chains X).homology q) :=
    inferInstanceAs (Module.Projective ℤ (SingularHomology X q))
  have h' : Subsingleton ((chains X).homology (q + 1)) := h
  have hiso := LocalUCT.cohomologyEvaluation_isIso_of_free_of_projective intCoeff (chains X) q
  have hinj : Function.Injective (cohomologyEvaluation intCoeff (chains X) q).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).mp hiso).1
  have hsub : Subsingleton ((chains X).homology (q + 1) →+ ℤ) := ⟨fun f g => AddMonoidHom.ext fun x => by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact hinj.subsingleton

end UCT

/-! ### Closed oriented manifolds -/

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [CompactSpace M]

/-- **Poincaré duality** for a closed oriented `n`-manifold, as a hypothesis: every absolute
duality map `H^k(M; ℤ) → H_{n-k}(M; ℤ)`, `φ ↦ [M] ⌢ φ`, is bijective.  (The proof by the
Mayer–Vietoris induction of Hatcher 3.35/3.36 is not formalized; see
`Lib/reports/poincare/PLACEHOLDERS.md`.) -/
structure IsPoincareDuality (hn : 2 ≤ n) (μ : Orientation M n) : Prop where
  /-- Every duality map is bijective. -/
  bijective : ∀ (k l : ℕ) (h : k + l = n), Function.Bijective (absoluteDualityMap hn μ k l h)

/-- The cohomology of a closed connected oriented manifold vanishes above the dimension
(universal coefficients and `H_i(M) = 0` for `i > n`, `H_n(M) ≅ ℤ`). -/
theorem cohomology_subsingleton_of_lt [PreconnectedSpace M] [Nonempty M] (hn : 2 ≤ n)
    (μ : Orientation M n) (k : ℕ) (hk : n < k) : Subsingleton (SingularCohomology M k) := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  have hq : Module.Projective ℤ (SingularHomology M q) := by
    rcases Nat.lt_or_ge n q with hlt | hge
    · have := homology_subsingleton_of_lt (M := M) hn q hlt
      exact projective_of_subsingleton
    · have hqn : q = n := by omega
      subst hqn
      obtain ⟨e⟩ := exists_homology_equiv_int hn μ
      exact projective_of_equiv_int e
  exact cohomology_succ_subsingleton M q (homology_subsingleton_of_lt (M := M) hn (q + 1) hk)

namespace IsPoincareDuality

variable {hn : 2 ≤ n} {μ : Orientation M n}

/-- `H^k(M) ≃ H_{n-k}(M)` under Poincaré duality. -/
def cohomologyEquiv (hD : IsPoincareDuality hn μ) (k l : ℕ) (h : k + l = n) :
    SingularCohomology M k ≃+ SingularHomology M l :=
  AddEquiv.ofBijective _ (hD.bijective k l h)

/-- `H^n(M; ℤ) ≅ ℤ` for a closed connected oriented manifold satisfying duality. -/
theorem cohomology_top_equiv_int [PathConnectedSpace M] (hD : IsPoincareDuality hn μ) :
    Nonempty (SingularCohomology M n ≃+ ℤ) :=
  ⟨(hD.cohomologyEquiv n 0 (by omega)).trans
    (SingularHomology.connectedHomologyZeroEquiv M).toAddEquiv⟩

/-- Under duality, torsion-freeness of `H^k(M)` gives torsion-freeness of `H_{n-k}(M)` (for the
module structure of the homology object). -/
theorem homology_isTorsionFree (hD : IsPoincareDuality hn μ) (k l : ℕ) (h : k + l = n)
    (hk : Module.IsTorsionFree ℤ (SingularCohomology M k)) :
    Module.IsTorsionFree ℤ (SingularHomology M l) :=
  isTorsionFree_int_congr _ _
    (isTorsionFree_of_injective (hD.cohomologyEquiv k l h).symm.toAddMonoidHom
      (hD.cohomologyEquiv k l h).symm.injective hk)

end IsPoincareDuality

end Manifold

/-! ### The torsion dictionary in dimension 4 (consumer (a)) -/

section DimFour

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [T2Space M]
  [CompactSpace M]

/-- **Torsion-freeness of the integral cohomology of a closed oriented 4-manifold** with finitely
generated homology and torsion-free `H_1`, under Poincaré duality: every `H^q(M; ℤ)` is
torsion-free.  (`H^1 ≅ Hom(H_1, ℤ)`, `H^2 ≅ Hom(H_2, ℤ)` since `H_1` is free, `H_2 ≅ H^2` is then
free, so `H^3 ≅ Hom(H_3, ℤ)`, `H_3 ≅ H^1` is free, so `H^4 ≅ Hom(H_4, ℤ)`; `H^0` is always
torsion-free and `H^q = 0` for `q > 4`.) -/
theorem IsPoincareDuality.cohomology_isTorsionFree_of_dim_four [PathConnectedSpace M]
    {hn : 2 ≤ 4} {μ : Orientation M 4} (hD : IsPoincareDuality hn μ)
    (hfin : ∀ q, Module.Finite ℤ (SingularHomology M q))
    (h1 : Module.IsTorsionFree ℤ (SingularHomology M 1)) (q : ℕ) :
    Module.IsTorsionFree ℤ (SingularCohomology M q) := by
  -- `H_0 ≅ ℤ`
  have h0 : Module.Projective ℤ (SingularHomology M 0) :=
    projective_of_equiv_int (SingularHomology.connectedHomologyZeroEquiv M)
  -- `H^1` torsion-free
  have hc1 : Module.IsTorsionFree ℤ (SingularCohomology M 1) := cohomology_succ_isTorsionFree M 0
  -- `H_1` free, `H^2` torsion-free
  have hp1 : Module.Projective ℤ (SingularHomology M 1) := by
    have := hfin 1
    exact inferInstance
  have hc2 : Module.IsTorsionFree ℤ (SingularCohomology M 2) := cohomology_succ_isTorsionFree M 1
  -- `H_2 ≅ H^2` torsion-free hence free, `H^3` torsion-free
  have hp2 : Module.Projective ℤ (SingularHomology M 2) := by
    have := hfin 2
    have := hD.homology_isTorsionFree 2 2 rfl hc2
    exact inferInstance
  have hc3 : Module.IsTorsionFree ℤ (SingularCohomology M 3) := cohomology_succ_isTorsionFree M 2
  -- `H_3 ≅ H^1` torsion-free hence free, `H^4` torsion-free
  have hp3 : Module.Projective ℤ (SingularHomology M 3) := by
    have := hfin 3
    have := hD.homology_isTorsionFree 1 3 rfl hc1
    exact inferInstance
  have hc4 : Module.IsTorsionFree ℤ (SingularCohomology M 4) := cohomology_succ_isTorsionFree M 3
  match q with
  | 0 => exact cohomology_zero_isTorsionFree M
  | 1 => exact hc1
  | 2 => exact hc2
  | 3 => exact hc3
  | 4 => exact hc4
  | q + 5 =>
    have := cohomology_subsingleton_of_lt hn μ (q + 5) (by omega)
    exact inferInstance

end DimFour

end PoincareDuality
