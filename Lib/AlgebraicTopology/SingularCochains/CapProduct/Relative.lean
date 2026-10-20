/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularCochains.CapProduct.Chain
public import Lib.AlgebraicTopology.SingularCochains.Relative
public import Lib.Algebra.Homology.CocycleClass
public import Lib.AlgebraicTopology.SingularHomology.CircleProduct

/-!
# The relative cap product on homology

The cap product of Hatcher §3.3 in its relative form
`H^k(X, A; ℤ) × H_m(X, A; ℤ) → H_l(X; ℤ)` for `k + l = m`: a relative cocycle `ψ` is a cochain on
`X` vanishing on the chains of `A` (`liftedCochain`), and `c ⌢ ψ` for a relative cycle `c` is a
cycle of `X` by the Leibniz formula `∂(c ⌢ ψ) = ±(∂c ⌢ ψ - c ⌢ δψ)`, since `∂c ⌢ ψ = 0` (the
front faces of simplices in `A` lie in `A`) and `δψ = 0`.  The same formula shows that the class
depends only on the classes of `ψ` and `c`.

## Main definitions and results

* `SingularCapProduct.liftedCochain`, `capChain_eq_zero_of_mem`, `capChain_isCycle`.
* `SingularCapProduct.relativeCap A k l m h :
    RelativeCohomology X A k →+ (RelativeHomology X A m →ₗ[ℤ] SingularHomology X l)`.
* `SingularCapProduct.relativeCap_apply` (the value on representatives),
  `relativeCap_cohomologyRestriction` (compatibility with `A ⊆ A'`).
* `SingularCapProduct.augmentation_relativeCap_top`: in top degree `k = m`, `l = 0`, the
  augmentation of `α ⌢ ψ` is the Kronecker pairing `ψ(α)`, for path-connected `X`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3 (the cap product and its relative forms)

## Tags

cap product, relative homology, relative cohomology
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace SingularCapProduct

open SingularChains SingularMayerVietoris RelativeSingularHomology RelativeSingularCohomology
open AlgebraicTopology.SingularCochains AlgebraicTopology.SingularCochains.DualEvaluation
open CochainCocycle

variable {X : Type} [TopologicalSpace X] (A : Set X)

/-! ### Algebra of the chain-level cap -/

theorem capChain_zero (k l m : ℕ) (h : k + l = m) : capChain (X := X) k l m h 0 = 0 := by
  apply chainMap_ext X m
  intro σ
  rw [capChain_simplexChain, capSimplex, LinearMap.zero_apply, zero_smul, LinearMap.zero_apply]

theorem capChain_add (k l m : ℕ) (h : k + l = m) (φ φ' : Cochain X k) :
    capChain k l m h (φ + φ') = capChain k l m h φ + capChain k l m h φ' := by
  apply chainMap_ext X m
  intro σ
  simp only [LinearMap.add_apply, capChain_simplexChain, capSimplex, add_zsmul]

/-- A chain supported in `A` caps to zero against a cochain vanishing on `A`. -/
theorem capChain_eq_zero_of_mem (k l m : ℕ) (h : k + l = m) (φ : Cochain X k)
    (hφ : ∀ a ∈ supportedChainSubmodule A k, φ a = 0) (c : Chains X m)
    (hc : c ∈ supportedChainSubmodule A m) : capChain k l m h φ c = 0 := by
  refine LinearMap.eqOn_span (R := ℤ) (f := capChain k l m h φ) (g := 0) ?_ hc
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' : Set.range σ ⊆ A := hσ
  change capChain k l m h φ (simplexChain X m σ) = 0
  rw [capChain_simplexChain, capSimplex, hφ _ (simplexChain_mem_supported A k _ (by
    rw [ContinuousMap.coe_comp]
    exact (Set.range_comp_subset_range _ _).trans hσ')), zero_smul]

/-- The cap of a relative cycle with a relative cocycle is a cycle. -/
theorem capChain_isCycle (k l m : ℕ) (h : k + l = m) (φ : Cochain X k)
    (hφ : ∀ a ∈ supportedChainSubmodule A k, φ a = 0) (hδ : coboundary k φ = 0) (c : Chains X m)
    (hc : ((singularComplex X).d m (m - 1)).hom c ∈ supportedChainSubmodule A (m - 1)) :
    ((singularComplex X).d l (l - 1)).hom (capChain k l m h φ c) = 0 := by
  cases l with
  | zero =>
    rw [(singularComplex X).shape 0 (0 - 1) (by simp)]
    rfl
  | succ l =>
    have hm : m = k + l + 1 := by omega
    subst hm
    have hc' : ((singularComplex X).d (k + l + 1) (k + l)).hom c ∈ supportedChainSubmodule A (k + l) := hc
    change ((singularComplex X).d (l + 1) l).hom (capChain k (l + 1) (k + l + 1) rfl φ c) = 0
    rw [boundary_capChain, hδ, capChain_zero, LinearMap.zero_apply, sub_zero,
      capChain_eq_zero_of_mem A k l (k + l) rfl φ hφ _ hc', zsmul_zero]

/-! ### Relative cochains as cochains vanishing on `A` -/

/-- The cochain on `X` underlying a relative cochain of `(X, A)`. -/
def liftedCochain (k : ℕ) (ψ : (relativeCochains X A).X k) : Cochain X k where
  toFun c := cochainAddHom intCoeff (relativeComplex X A) k ψ (relativeClass A k c)
  map_add' c d := by
    change cochainAddHom intCoeff (relativeComplex X A) k ψ (Submodule.Quotient.mk (c + d)) = _
    rw [Submodule.Quotient.mk_add, map_add]
  map_smul' r c := by
    simp only [RingHom.id_apply]
    have h := (cochainLinear intCoeff (relativeComplex X A) k ψ).map_smul r (relativeClass A k c)
    rw [← Submodule.Quotient.mk_smul] at h
    exact h

theorem liftedCochain_apply (k : ℕ) (ψ : (relativeCochains X A).X k) (c : Chains X k) :
    liftedCochain A k ψ c = cochainAddHom intCoeff (relativeComplex X A) k ψ (relativeClass A k c) :=
  rfl

theorem liftedCochain_zero (k : ℕ) : liftedCochain A k 0 = 0 :=
  LinearMap.ext fun _ => rfl

theorem liftedCochain_add (k : ℕ) (ψ ψ' : (relativeCochains X A).X k) :
    liftedCochain A k (ψ + ψ') = liftedCochain A k ψ + liftedCochain A k ψ' :=
  LinearMap.ext fun _ => rfl

/-- The lifted cochain vanishes on chains supported in `A`. -/
theorem liftedCochain_eq_zero_of_mem (k : ℕ) (ψ : (relativeCochains X A).X k) (a : Chains X k)
    (ha : a ∈ supportedChainSubmodule A k) : liftedCochain A k ψ a = 0 := by
  rw [liftedCochain_apply, (relativeClass_eq_zero_iff A k a).mpr ha, map_zero]

/-- The lifted cochain of a coboundary is the coboundary of the lifted cochain. -/
theorem liftedCochain_d (k : ℕ) (ψ : (relativeCochains X A).X k) :
    liftedCochain A (k + 1) ((relativeCochains X A).d k (k + 1) ψ) =
      coboundary k (liftedCochain A k ψ) := by
  apply LinearMap.ext
  intro c
  rw [liftedCochain_apply, coboundary_apply, liftedCochain_apply, dualComplex_d_apply_apply,
    relativeComplex_d_relativeClass]

/-- The lifted cochain of a cocycle is closed. -/
theorem coboundary_liftedCochain (k : ℕ) (ψ : Cocycle (relativeCochains X A) k) :
    coboundary k (liftedCochain A k ψ.1) = 0 := by
  rw [← liftedCochain_d, cocycle_condition, liftedCochain_zero]

/-! ### The cap with a relative cocycle on relative cycles -/

/-- Every relative chain is the class of a chain (stated with the relative chain group as the
target type). -/
theorem exists_relativeClass_eq (m : ℕ) (z : (relativeComplex X A).X m) :
    ∃ c : Chains X m, relativeClass A m c = z :=
  Submodule.Quotient.mk_surjective _ z

/-- The module structure on relative cycles (the submodule one; instance search does not find
`ModuleHomology.cycleModule` through the quotient complex abbreviation). -/
instance relativeCycleModule (m : ℕ) : Module ℤ (ModuleHomology.Cycle (relativeComplex X A) m) :=
  ModuleHomology.cycleModule _ _

/-- The cap with a cochain vanishing on `A`, on relative chains. -/
def capRel (k l m : ℕ) (h : k + l = m) (φ : Cochain X k)
    (hφ : ∀ a ∈ supportedChainSubmodule A k, φ a = 0) :
    (relativeComplex X A).X m →ₗ[ℤ] Chains X l :=
  Submodule.liftQ (supportedChainSubmodule A m) (capChain k l m h φ) fun c hc => by
    rw [LinearMap.mem_ker]
    exact capChain_eq_zero_of_mem A k l m h φ hφ c hc

@[simp]
theorem capRel_relativeClass (k l m : ℕ) (h : k + l = m) (φ : Cochain X k) (hφ) (c : Chains X m) :
    capRel A k l m h φ hφ (relativeClass A m c) = capChain k l m h φ c := rfl

/-- The boundary of a chain representing a relative cycle is supported in `A`. -/
theorem boundary_mem_of_cycle (m : ℕ) (z : ModuleHomology.Cycle (relativeComplex X A) m)
    (c : Chains X m) (hc : relativeClass A m c = z.1) :
    ((singularComplex X).d m (m - 1)).hom c ∈ supportedChainSubmodule A (m - 1) := by
  have hz := ModuleHomology.cycle_condition (relativeComplex X A) m z
  rw [← hc, relativeComplex_d_relativeClass] at hz
  exact (relativeClass_eq_zero_iff A (m - 1) _).mp hz

/-- The cap of a relative cycle with a relative cocycle, as a cycle of `X`. -/
def capCycle (k l m : ℕ) (h : k + l = m) (ψ : Cocycle (relativeCochains X A) k) :
    ModuleHomology.Cycle (relativeComplex X A) m →ₗ[ℤ] ModuleHomology.Cycle (singularComplex X) l :=
  ((capRel A k l m h (liftedCochain A k ψ.1) (liftedCochain_eq_zero_of_mem A k ψ.1)).comp
    (ModuleHomology.Cycle (relativeComplex X A) m).subtype).codRestrict _ fun z => by
      obtain ⟨c, hc⟩ := exists_relativeClass_eq A m z.1
      change ((singularComplex X).d l ((ComplexShape.down ℕ).next l)).hom
        (capRel A k l m h (liftedCochain A k ψ.1) (liftedCochain_eq_zero_of_mem A k ψ.1) z.1) = 0
      rw [ModuleHomology.next_nat, ← hc, capRel_relativeClass]
      exact capChain_isCycle A k l m h _ (liftedCochain_eq_zero_of_mem A k ψ.1)
        (coboundary_liftedCochain A k ψ) c (boundary_mem_of_cycle A m z c hc)

@[simp]
theorem capCycle_val (k l m : ℕ) (h : k + l = m) (ψ : Cocycle (relativeCochains X A) k)
    (z : ModuleHomology.Cycle (relativeComplex X A) m) :
    (capCycle A k l m h ψ z).1 = capRel A k l m h (liftedCochain A k ψ.1) (liftedCochain_eq_zero_of_mem A k ψ.1) z.1 :=
  rfl

/-- The cap with a relative boundary is a boundary (Leibniz, `δψ = 0`). -/
theorem cycleClass_capCycle_boundaryCycle (k l m : ℕ) (h : k + l = m)
    (ψ : Cocycle (relativeCochains X A) k) (b : (relativeComplex X A).X (m + 1)) :
    ModuleHomology.cycleClass (singularComplex X) l
      (capCycle A k l m h ψ (ModuleHomology.boundaryCycle (relativeComplex X A) m b)) = 0 := by
  subst h
  obtain ⟨e, rfl⟩ := exists_relativeClass_eq A (k + l + 1) b
  rw [ModuleHomology.cycleClass_eq_zero_iff]
  refine ⟨(-1 : ℤ) ^ k • capChain k (l + 1) (k + l + 1) rfl (liftedCochain A k ψ.1) e, ?_⟩
  rw [capCycle_val, map_zsmul]
  change (-1 : ℤ) ^ k • ((singularComplex X).d (l + 1) l).hom
      (capChain k (l + 1) (k + l + 1) rfl (liftedCochain A k ψ.1) e) =
    capRel A k l (k + l) rfl _ _ (((relativeComplex X A).d (k + l + 1) (k + l)).hom (relativeClass A (k + l + 1) e))
  rw [boundary_capChain, coboundary_liftedCochain, capChain_zero, LinearMap.zero_apply, sub_zero,
    relativeComplex_d_relativeClass, capRel_relativeClass, ← mul_zsmul, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_zsmul]

/-- The cap with a fixed relative cocycle, on relative homology. -/
def capHomology (k l m : ℕ) (h : k + l = m) (ψ : Cocycle (relativeCochains X A) k) :
    RelativeHomology X A m →ₗ[ℤ] SingularHomology X l :=
  SingularHomology.homologyDesc (relativeComplex X A) m
    ((ModuleHomology.cycleClass (singularComplex X) l).comp (capCycle A k l m h ψ))
    (cycleClass_capCycle_boundaryCycle A k l m h ψ)

theorem capHomology_cycleClass (k l m : ℕ) (h : k + l = m) (ψ : Cocycle (relativeCochains X A) k)
    (z : ModuleHomology.Cycle (relativeComplex X A) m) :
    capHomology A k l m h ψ (ModuleHomology.cycleClass _ m z) =
      ModuleHomology.cycleClass (singularComplex X) l (capCycle A k l m h ψ z) :=
  SingularHomology.homologyDesc_cycleClass _ m _ _ z

theorem capHomology_add (k l m : ℕ) (h : k + l = m) (ψ ψ' : Cocycle (relativeCochains X A) k) :
    capHomology A k l m h (ψ + ψ') = capHomology A k l m h ψ + capHomology A k l m h ψ' := by
  apply SingularHomology.homologyLinearMap_ext
  intro z
  rw [LinearMap.add_apply, capHomology_cycleClass, capHomology_cycleClass, capHomology_cycleClass,
    ← map_add]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_add, capCycle_val, capCycle_val, capCycle_val]
  obtain ⟨c, hc⟩ := exists_relativeClass_eq A m z.1
  rw [← hc, capRel_relativeClass, capRel_relativeClass, capRel_relativeClass, AddSubgroup.coe_add,
    liftedCochain_add, capChain_add, LinearMap.add_apply]

/-- The cap with a relative coboundary is zero on relative homology (Leibniz, `∂c ⌢ χ = 0`). -/
theorem capHomology_coboundary (k l m : ℕ) (h : k + 1 + l = m) (χ : (relativeCochains X A).X k)
    (hb : (relativeCochains X A).d (k + 1) (k + 1 + 1) ((relativeCochains X A).d k (k + 1) χ) = 0) :
    capHomology A (k + 1) l m h (mkCocycle _ (k + 1) ((relativeCochains X A).d k (k + 1) χ) hb) = 0 := by
  have hm : m = k + l + 1 := by omega
  subst hm
  apply SingularHomology.homologyLinearMap_ext
  intro z
  rw [capHomology_cycleClass, LinearMap.zero_apply, ModuleHomology.cycleClass_eq_zero_iff]
  obtain ⟨c, hc⟩ := exists_relativeClass_eq A (k + l + 1) z.1
  have hc' : ((singularComplex X).d (k + l + 1) (k + l)).hom c ∈ supportedChainSubmodule A (k + l) :=
    boundary_mem_of_cycle A _ z c hc
  refine ⟨-((-1 : ℤ) ^ k • capChain k (l + 1) (k + l + 1) rfl (liftedCochain A k χ) c), ?_⟩
  rw [capCycle_val, ← hc, capRel_relativeClass, mkCocycle_val, liftedCochain_d, map_neg, map_zsmul,
    boundary_capChain, capChain_eq_zero_of_mem A k l (k + l) rfl _ (liftedCochain_eq_zero_of_mem A k χ)
      _ hc', zero_sub]
  simp only [zsmul_neg, neg_neg]
  rw [← mul_zsmul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_zsmul]

/-- **The relative cap product** `H^k(X, A) × H_m(X, A) → H_l(X)`, `k + l = m`. -/
def relativeCap (k l m : ℕ) (h : k + l = m) :
    RelativeCohomology X A k →+ (RelativeHomology X A m →ₗ[ℤ] SingularHomology X l) :=
  match k, h with
  | 0, h => cohomologyDescZero (relativeCochains X A)
      (AddMonoidHom.mk' (capHomology A 0 l m h) (capHomology_add A 0 l m h))
  | k + 1, h => cohomologyDescSucc (relativeCochains X A) k
      (AddMonoidHom.mk' (capHomology A (k + 1) l m h) (capHomology_add A (k + 1) l m h))
      (capHomology_coboundary A k l m h)

/-- The relative cap product on cocycle and cycle classes. -/
theorem relativeCap_cocycleClass (k l m : ℕ) (h : k + l = m) (ψ : Cocycle (relativeCochains X A) k) :
    relativeCap A k l m h (cocycleClass _ k ψ) = capHomology A k l m h ψ := by
  cases k with
  | zero =>
    exact cohomologyDescZero_cocycleClass _
      (AddMonoidHom.mk' (capHomology A 0 l m h) (capHomology_add A 0 l m h)) ψ
  | succ k =>
    exact cohomologyDescSucc_cocycleClass _ k
      (AddMonoidHom.mk' (capHomology A (k + 1) l m h) (capHomology_add A (k + 1) l m h))
      (capHomology_coboundary A k l m h) ψ

/-- The relative cap product on representatives: `[c] ⌢ [ψ] = [c ⌢ ψ]`. -/
theorem relativeCap_apply (k l m : ℕ) (h : k + l = m) (ψ : Cocycle (relativeCochains X A) k)
    (c : Chains X m) (hc : ((singularComplex X).d m (m - 1)).hom c ∈ supportedChainSubmodule A (m - 1)) :
    relativeCap A k l m h (cocycleClass _ k ψ) (relativeHomologyClass A m c hc) =
      ModuleHomology.cycleClass (singularComplex X) l
        (ModuleHomology.mkCycle _ l (capChain k l m h (liftedCochain A k ψ.1) c)
          (capChain_isCycle A k l m h _ (liftedCochain_eq_zero_of_mem A k ψ.1)
            (coboundary_liftedCochain A k ψ) c hc)) := by
  rw [relativeCap_cocycleClass, relativeHomologyClass, capHomology_cycleClass]
  rfl

/-! ### Compatibility with restriction -/

/-- Cycle classes of equal chains agree (with arbitrary cycle proofs). -/
theorem cycleClass_mkCycle_congr {K : ChainComplex (ModuleCat.{0} ℤ) ℕ} {n : ℕ} {c c' : K.X n}
    (h : c = c') (hc : (K.d n (n - 1)).hom c = 0) (hc' : (K.d n (n - 1)).hom c' = 0) :
    ModuleHomology.cycleClass K n (ModuleHomology.mkCycle K n c hc) =
      ModuleHomology.cycleClass K n (ModuleHomology.mkCycle K n c' hc') := by
  subst h
  rfl

/-- The lifted cochain of a restricted relative cochain is the same cochain. -/
theorem liftedCochain_cochainRestrictionMap {A A' : Set X} (hA : A ⊆ A') (k : ℕ)
    (ψ : (relativeCochains X A').X k) :
    liftedCochain A k (((cochainRestrictionMap hA).f k) ψ) = liftedCochain A' k ψ :=
  LinearMap.ext fun _ => rfl

/-- The cap product is compatible with restriction along `A ⊆ A'`:
`α ⌢ (ψ|_(X,A)) = (α|_(X,A')) ⌢ ψ` for `ψ ∈ H^k(X, A')`, `α ∈ H_m(X, A)`. -/
theorem relativeCap_cohomologyRestriction {A A' : Set X} (hA : A ⊆ A') (k l m : ℕ) (h : k + l = m)
    (ψ : RelativeCohomology X A' k) (α : RelativeHomology X A m) :
    relativeCap A k l m h (cohomologyRestriction hA k ψ) α =
      relativeCap A' k l m h ψ (restriction hA m α) := by
  obtain ⟨ψ, rfl⟩ := cocycleClass_surjective _ k ψ
  obtain ⟨c, hc, rfl⟩ := relativeHomologyClass_surjective A m α
  rw [cohomologyHom_cocycleClass, restriction_relativeHomologyClass, relativeCap_apply,
    relativeCap_apply]
  exact cycleClass_mkCycle_congr (by rw [mapCocycle_val, liftedCochain_cochainRestrictionMap]) _ _

/-! ### The top-degree pairing -/

/-- Every `0`-chain is a cycle. -/
def zeroCycle (c : Chains X 0) : ModuleHomology.Cycle (singularComplex X) 0 :=
  ModuleHomology.mkCycle _ 0 c (by
    rw [(singularComplex X).shape 0 (0 - 1) (by simp)]
    rfl)

@[simp] theorem zeroCycle_val (c : Chains X 0) : (zeroCycle c).1 = c := rfl

/-- Every `0`-chain is a cycle, as a linear map. -/
def zeroCycleLinear : Chains X 0 →ₗ[ℤ] ModuleHomology.Cycle (singularComplex X) 0 :=
  LinearMap.codRestrict _ LinearMap.id fun c => (zeroCycle c).2

@[simp] theorem zeroCycleLinear_apply (c : Chains X 0) : zeroCycleLinear c = zeroCycle c := rfl

/-- The augmentation `C_0(X) → ℤ` of a path-connected space, through `H_0(X) ≅ ℤ`. -/
def augmentation [PathConnectedSpace X] : Chains X 0 →ₗ[ℤ] ℤ :=
  (SingularHomology.connectedHomologyZeroEquiv X).toLinearMap ∘ₗ
    ModuleHomology.cycleClass (singularComplex X) 0 ∘ₗ zeroCycleLinear

theorem augmentation_apply [PathConnectedSpace X] (c : Chains X 0) :
    augmentation c = SingularHomology.connectedHomologyZeroEquiv X (ModuleHomology.cycleClass _ 0 (zeroCycle c)) :=
  rfl

/-- The augmentation of a `0`-simplex is `1`. -/
theorem augmentation_simplex [PathConnectedSpace X] (σ : SingularSimplex X 0) :
    augmentation (simplexChain X 0 σ) = 1 := by
  have hσ : σ = ContinuousMap.const (Simplex 0) (σ (stdSimplex.vertex 0)) := by
    ext t
    exact congrArg σ (simplexZero_eq_vertex t)
  rw [augmentation_apply, hσ]
  exact SingularHomology.connectedHomologyZeroEquiv_pointClass _

/-- In top degree the cap product followed by the augmentation is the Kronecker pairing:
`ε(c ⌢ φ) = φ(c)`. -/
theorem augmentation_capChain_top [PathConnectedSpace X] (k : ℕ) (h : k + 0 = k) (φ : Cochain X k)
    (c : Chains X k) : augmentation (capChain k 0 k h φ c) = φ c := by
  have key : augmentation ∘ₗ capChain k 0 k h φ = φ := by
    apply chainMap_ext X k
    intro σ
    rw [LinearMap.comp_apply, capChain_simplexChain, capSimplex, map_zsmul, augmentation_simplex,
      zsmul_eq_mul, mul_one, frontFace_top]
    rfl
  exact LinearMap.congr_fun key c

/-- The relative cap product in top degree, followed by `H_0(X) ≅ ℤ`, is the Kronecker pairing
of the relative cocycle with the relative cycle. -/
theorem augmentation_relativeCap_top [PathConnectedSpace X] (k : ℕ) (h : k + 0 = k)
    (ψ : Cocycle (relativeCochains X A) k) (c : Chains X k)
    (hc : ((singularComplex X).d k (k - 1)).hom c ∈ supportedChainSubmodule A (k - 1)) :
    SingularHomology.connectedHomologyZeroEquiv X
        (relativeCap A k 0 k h (cocycleClass _ k ψ) (relativeHomologyClass A k c hc)) =
      cochainAddHom intCoeff (relativeComplex X A) k ψ.1 (relativeClass A k c) := by
  rw [relativeCap_apply]
  change augmentation (capChain k 0 k h (liftedCochain A k ψ.1) c) = _
  rw [augmentation_capChain_top]
  rfl

end SingularCapProduct
