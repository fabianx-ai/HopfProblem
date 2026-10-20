/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularCochains.CapProduct.Relative

/-!
# The cup product on singular cohomology

The cup product `H^k(X; ℤ) × H^l(X; ℤ) → H^m(X; ℤ)`, `k + l = m`, descended from the chain-level
`cupChain` of M3 through the Leibniz formula `δ(φ ∪ ψ) = δφ ∪ ψ + (-1)^k φ ∪ δψ`
(Hatcher §3.2): the cup of two cocycles is a cocycle, and it changes by a coboundary when either
factor does.  The cochains of `Lib`'s dual complex (`(complex X ℤ).X k`, additive maps) and the
linear cochains `Cochain X k` of M3 are identified by `toCochain`/`ofCochain`.

## Main definitions and results

* `SingularCapProduct.toCochain`, `ofCochain`, `toCochain_d`.
* `SingularCapProduct.cupCocycle`, `SingularCapProduct.cupProduct X k l m h :
    SingularCohomology X k →+ (SingularCohomology X l →+ SingularCohomology X m)`.
* `SingularCapProduct.cupProduct_cocycleClass` (the value on representatives).

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.2 (the cup product)

## Tags

cup product, singular cohomology
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace SingularCapProduct

open SingularChains SingularMayerVietoris RelativeSingularHomology RelativeSingularCohomology
open AlgebraicTopology.SingularCochains AlgebraicTopology.SingularCochains.DualEvaluation
open CochainCocycle

variable {X : Type} [TopologicalSpace X]

/-! ### Additive and linear cochains -/

/-- The linear cochain underlying a cochain of the dual complex. -/
def toCochain (k : ℕ) (ψ : (complex X intCoeff).X k) : Cochain X k where
  toFun c := cochainAddHom intCoeff (chains X) k ψ c
  map_add' c d := map_add _ c d
  map_smul' r c := by
    simp only [RingHom.id_apply]
    exact (cochainLinear intCoeff (chains X) k ψ).map_smul r c

theorem toCochain_apply (k : ℕ) (ψ : (complex X intCoeff).X k) (c : Chains X k) :
    toCochain k ψ c = cochainAddHom intCoeff (chains X) k ψ c := rfl

/-- A linear cochain as a cochain of the dual complex. -/
def ofCochain (k : ℕ) (φ : Cochain X k) : (complex X intCoeff).X k :=
  linearCochain intCoeff (chains X) k φ

theorem cochainAddHom_ofCochain (k : ℕ) (φ : Cochain X k) (c : Chains X k) :
    cochainAddHom intCoeff (chains X) k (ofCochain k φ) c = φ c := rfl

@[simp]
theorem toCochain_ofCochain (k : ℕ) (φ : Cochain X k) : toCochain k (ofCochain k φ) = φ :=
  LinearMap.ext fun _ => rfl

@[simp]
theorem ofCochain_toCochain (k : ℕ) (ψ : (complex X intCoeff).X k) : ofCochain k (toCochain k ψ) = ψ :=
  AddMonoidHom.ext fun _ => rfl

theorem toCochain_zero (k : ℕ) : toCochain (X := X) k 0 = 0 := LinearMap.ext fun _ => rfl

theorem toCochain_add (k : ℕ) (ψ ψ' : (complex X intCoeff).X k) :
    toCochain k (ψ + ψ') = toCochain k ψ + toCochain k ψ' := LinearMap.ext fun _ => rfl

theorem ofCochain_add (k : ℕ) (φ φ' : Cochain X k) :
    ofCochain k (φ + φ') = ofCochain k φ + ofCochain k φ' := AddMonoidHom.ext fun _ => rfl

theorem ofCochain_zsmul (k : ℕ) (r : ℤ) (φ : Cochain X k) :
    ofCochain k (r • φ) = r • ofCochain k φ := AddMonoidHom.ext fun _ => rfl

theorem ofCochain_neg (k : ℕ) (φ : Cochain X k) : ofCochain k (-φ) = -ofCochain k φ :=
  AddMonoidHom.ext fun _ => rfl

/-- The differential of the dual complex is the coboundary. -/
theorem toCochain_d (k : ℕ) (ψ : (complex X intCoeff).X k) :
    toCochain (k + 1) ((complex X intCoeff).d k (k + 1) ψ) = coboundary k (toCochain k ψ) :=
  LinearMap.ext fun c => by
    rw [toCochain_apply, coboundary_apply, toCochain_apply]
    exact dualComplex_d_apply_apply intCoeff (chains X) k (k + 1) ψ c

theorem d_ofCochain (k : ℕ) (φ : Cochain X k) :
    (complex X intCoeff).d k (k + 1) (ofCochain k φ) = ofCochain (k + 1) (coboundary k φ) := by
  rw [← ofCochain_toCochain (k + 1) ((complex X intCoeff).d k (k + 1) (ofCochain k φ)), toCochain_d,
    toCochain_ofCochain]

/-- The lifted cochain of a cocycle is closed. -/
theorem coboundary_toCochain (k : ℕ) (ψ : Cocycle (complex X intCoeff) k) :
    coboundary k (toCochain k ψ.1) = 0 := by
  rw [← toCochain_d, cocycle_condition, toCochain_zero]

/-! ### Algebra of the chain-level cup -/

theorem cupChain_zero_left (k l m : ℕ) (h : k + l = m) (ψ : Cochain X l) :
    cupChain k l m h 0 ψ = 0 := by
  rw [cupChain, capChain_zero, LinearMap.comp_zero]

theorem cupChain_zero_right (k l m : ℕ) (h : k + l = m) (φ : Cochain X k) :
    cupChain k l m h φ 0 = 0 := rfl

theorem cupChain_add_left (k l m : ℕ) (h : k + l = m) (φ φ' : Cochain X k) (ψ : Cochain X l) :
    cupChain k l m h (φ + φ') ψ = cupChain k l m h φ ψ + cupChain k l m h φ' ψ := by
  rw [cupChain, cupChain, cupChain, capChain_add, LinearMap.comp_add]

theorem cupChain_add_right (k l m : ℕ) (h : k + l = m) (φ : Cochain X k) (ψ ψ' : Cochain X l) :
    cupChain k l m h φ (ψ + ψ') = cupChain k l m h φ ψ + cupChain k l m h φ ψ' :=
  LinearMap.add_comp _ _ _

theorem cupChain_zsmul_right (k l m : ℕ) (h : k + l = m) (r : ℤ) (φ : Cochain X k) (ψ : Cochain X l) :
    cupChain k l m h φ (r • ψ) = r • cupChain k l m h φ ψ :=
  LinearMap.ext fun _ => rfl

/-- The cup product of two cocycles is a cocycle. -/
theorem coboundary_cupChain_eq_zero (k l m : ℕ) (h : k + l = m) (φ : Cochain X k) (ψ : Cochain X l)
    (hφ : coboundary k φ = 0) (hψ : coboundary l ψ = 0) :
    coboundary m (cupChain k l m h φ ψ) = 0 := by
  subst h
  rw [coboundary_cupChain, hφ, hψ, cupChain_zero_left, cupChain_zero_right, smul_zero, add_zero]

/-! ### The cup product on cohomology -/

/-- The cup of two cocycles, as a cocycle. -/
def cupCocycle (k l m : ℕ) (h : k + l = m) (φ : Cocycle (complex X intCoeff) k)
    (ψ : Cocycle (complex X intCoeff) l) : Cocycle (complex X intCoeff) m :=
  mkCocycle _ m (ofCochain m (cupChain k l m h (toCochain k φ.1) (toCochain l ψ.1))) (by
    rw [d_ofCochain, coboundary_cupChain_eq_zero k l m h _ _ (coboundary_toCochain k φ)
      (coboundary_toCochain l ψ)]
    rfl)

@[simp]
theorem cupCocycle_val (k l m : ℕ) (h : k + l = m) (φ : Cocycle (complex X intCoeff) k)
    (ψ : Cocycle (complex X intCoeff) l) :
    (cupCocycle k l m h φ ψ).1 = ofCochain m (cupChain k l m h (toCochain k φ.1) (toCochain l ψ.1)) :=
  rfl

theorem cupCocycle_add_right (k l m : ℕ) (h : k + l = m) (φ : Cocycle (complex X intCoeff) k)
    (ψ ψ' : Cocycle (complex X intCoeff) l) :
    cupCocycle k l m h φ (ψ + ψ') = cupCocycle k l m h φ ψ + cupCocycle k l m h φ ψ' := by
  apply Subtype.ext
  rw [AddSubgroup.coe_add, cupCocycle_val, cupCocycle_val, cupCocycle_val, AddSubgroup.coe_add,
    toCochain_add, cupChain_add_right, ofCochain_add]

theorem cupCocycle_add_left (k l m : ℕ) (h : k + l = m) (φ φ' : Cocycle (complex X intCoeff) k)
    (ψ : Cocycle (complex X intCoeff) l) :
    cupCocycle k l m h (φ + φ') ψ = cupCocycle k l m h φ ψ + cupCocycle k l m h φ' ψ := by
  apply Subtype.ext
  rw [AddSubgroup.coe_add, cupCocycle_val, cupCocycle_val, cupCocycle_val, AddSubgroup.coe_add,
    toCochain_add, cupChain_add_left, ofCochain_add]

/-- The cup of a cocycle with a coboundary is a coboundary (`φ ∪ δχ = ±δ(φ ∪ χ)`). -/
theorem cocycleClass_cupCocycle_coboundary_right (k l m : ℕ) (h : k + (l + 1) = m)
    (φ : Cocycle (complex X intCoeff) k) (χ : (complex X intCoeff).X l)
    (hb : (complex X intCoeff).d (l + 1) (l + 1 + 1) ((complex X intCoeff).d l (l + 1) χ) = 0) :
    cocycleClass _ m (cupCocycle k (l + 1) m h φ (mkCocycle _ (l + 1) ((complex X intCoeff).d l (l + 1) χ) hb)) = 0 := by
  have hm : m = k + l + 1 := by omega
  subst hm
  rw [cocycleClass_eq_zero_iff_succ]
  refine ⟨ofCochain (k + l) ((-1 : ℤ) ^ k • cupChain k l (k + l) rfl (toCochain k φ.1) (toCochain l χ)), ?_⟩
  rw [d_ofCochain, cupCocycle_val, mkCocycle_val, toCochain_d]
  congr 1
  have hL := coboundary_cupChain k l (toCochain k φ.1) (toCochain l χ)
  rw [coboundary_toCochain, cupChain_zero_left, zero_add] at hL
  have hδ : coboundary (k + l) ((-1 : ℤ) ^ k • cupChain k l (k + l) rfl (toCochain k φ.1) (toCochain l χ)) =
      (-1 : ℤ) ^ k • coboundary (k + l) (cupChain k l (k + l) rfl (toCochain k φ.1) (toCochain l χ)) :=
    LinearMap.smul_comp _ _ _
  rw [hδ, hL, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-- The cup of a coboundary with a cocycle is a coboundary (`δχ ∪ ψ = δ(χ ∪ ψ)`). -/
theorem cocycleClass_cupCocycle_coboundary_left (k l m : ℕ) (h : k + 1 + l = m)
    (χ : (complex X intCoeff).X k)
    (hb : (complex X intCoeff).d (k + 1) (k + 1 + 1) ((complex X intCoeff).d k (k + 1) χ) = 0)
    (ψ : Cocycle (complex X intCoeff) l) :
    cocycleClass _ m (cupCocycle (k + 1) l m h (mkCocycle _ (k + 1) ((complex X intCoeff).d k (k + 1) χ) hb) ψ) = 0 := by
  have hm : m = k + l + 1 := by omega
  subst hm
  rw [cocycleClass_eq_zero_iff_succ]
  refine ⟨ofCochain (k + l) (cupChain k l (k + l) rfl (toCochain k χ) (toCochain l ψ.1)), ?_⟩
  rw [d_ofCochain, cupCocycle_val, mkCocycle_val, toCochain_d]
  congr 1
  have hL := coboundary_cupChain k l (toCochain k χ) (toCochain l ψ.1)
  rw [coboundary_toCochain, cupChain_zero_right, smul_zero, add_zero] at hL
  exact hL

/-- The cup product with a fixed cocycle, on cohomology. -/
def cupHomology (k l m : ℕ) (h : k + l = m) (φ : Cocycle (complex X intCoeff) k) :
    SingularCohomology X l →+ SingularCohomology X m :=
  match l, h with
  | 0, h => cohomologyDescZero _
      (AddMonoidHom.mk' (fun ψ => cocycleClass _ m (cupCocycle k 0 m h φ ψ))
        (fun ψ ψ' => by rw [cupCocycle_add_right, map_add]))
  | l + 1, h => cohomologyDescSucc _ l
      (AddMonoidHom.mk' (fun ψ => cocycleClass _ m (cupCocycle k (l + 1) m h φ ψ))
        (fun ψ ψ' => by rw [cupCocycle_add_right, map_add]))
      (fun χ hb => cocycleClass_cupCocycle_coboundary_right k l m h φ χ hb)

theorem cupHomology_cocycleClass (k l m : ℕ) (h : k + l = m) (φ : Cocycle (complex X intCoeff) k)
    (ψ : Cocycle (complex X intCoeff) l) :
    cupHomology k l m h φ (cocycleClass _ l ψ) = cocycleClass _ m (cupCocycle k l m h φ ψ) := by
  cases l with
  | zero =>
    exact cohomologyDescZero_cocycleClass _
      (AddMonoidHom.mk' (fun ψ => cocycleClass _ m (cupCocycle k 0 m h φ ψ))
        (fun ψ ψ' => by rw [cupCocycle_add_right, map_add])) ψ
  | succ l =>
    exact cohomologyDescSucc_cocycleClass _ l
      (AddMonoidHom.mk' (fun ψ => cocycleClass _ m (cupCocycle k (l + 1) m h φ ψ))
        (fun ψ ψ' => by rw [cupCocycle_add_right, map_add]))
      (fun χ hb => cocycleClass_cupCocycle_coboundary_right k l m h φ χ hb) ψ

theorem cupHomology_add (k l m : ℕ) (h : k + l = m) (φ φ' : Cocycle (complex X intCoeff) k) :
    cupHomology k l m h (φ + φ') = cupHomology k l m h φ + cupHomology k l m h φ' := by
  apply cohomology_hom_ext
  intro ψ
  rw [AddMonoidHom.add_apply, cupHomology_cocycleClass, cupHomology_cocycleClass,
    cupHomology_cocycleClass, cupCocycle_add_left, map_add]

theorem cupHomology_coboundary (k l m : ℕ) (h : k + 1 + l = m) (χ : (complex X intCoeff).X k)
    (hb : (complex X intCoeff).d (k + 1) (k + 1 + 1) ((complex X intCoeff).d k (k + 1) χ) = 0) :
    cupHomology (k + 1) l m h (mkCocycle _ (k + 1) ((complex X intCoeff).d k (k + 1) χ) hb) = 0 := by
  apply cohomology_hom_ext
  intro ψ
  rw [cupHomology_cocycleClass, AddMonoidHom.zero_apply]
  exact cocycleClass_cupCocycle_coboundary_left k l m h χ hb ψ

/-- **The cup product** `H^k(X; ℤ) × H^l(X; ℤ) → H^m(X; ℤ)`, `k + l = m`. -/
def cupProduct (X : Type) [TopologicalSpace X] (k l m : ℕ) (h : k + l = m) :
    SingularCohomology X k →+ (SingularCohomology X l →+ SingularCohomology X m) :=
  match k, h with
  | 0, h => cohomologyDescZero _
      (AddMonoidHom.mk' (cupHomology 0 l m h) (cupHomology_add 0 l m h))
  | k + 1, h => cohomologyDescSucc _ k
      (AddMonoidHom.mk' (cupHomology (k + 1) l m h) (cupHomology_add (k + 1) l m h))
      (cupHomology_coboundary k l m h)

theorem cupProduct_zero (l m : ℕ) (h : 0 + l = m) :
    cupProduct X 0 l m h = cohomologyDescZero _
      (AddMonoidHom.mk' (cupHomology 0 l m h) (cupHomology_add 0 l m h)) := rfl

theorem cupProduct_succ (k l m : ℕ) (h : k + 1 + l = m) :
    cupProduct X (k + 1) l m h = cohomologyDescSucc _ k
      (AddMonoidHom.mk' (cupHomology (k + 1) l m h) (cupHomology_add (k + 1) l m h))
      (cupHomology_coboundary k l m h) := rfl

/-- The cup product on cocycle classes. -/
theorem cupProduct_cocycleClass (k l m : ℕ) (h : k + l = m) (φ : Cocycle (complex X intCoeff) k)
    (ψ : Cocycle (complex X intCoeff) l) :
    cupProduct X k l m h (cocycleClass _ k φ) (cocycleClass _ l ψ) =
      cocycleClass _ m (cupCocycle k l m h φ ψ) := by
  rw [← cupHomology_cocycleClass]
  cases k with
  | zero =>
    rw [cupProduct_zero]
    exact congrArg (fun F : SingularCohomology X l →+ SingularCohomology X m => F (cocycleClass _ l ψ))
      (cohomologyDescZero_cocycleClass (complex X intCoeff)
        (AddMonoidHom.mk' (cupHomology 0 l m h) (cupHomology_add 0 l m h)) φ)
  | succ k =>
    rw [cupProduct_succ]
    exact congrArg (fun F : SingularCohomology X l →+ SingularCohomology X m => F (cocycleClass _ l ψ))
      (cohomologyDescSucc_cocycleClass (complex X intCoeff) k
        (AddMonoidHom.mk' (cupHomology (k + 1) l m h) (cupHomology_add (k + 1) l m h))
        (cupHomology_coboundary k l m h) φ)

end SingularCapProduct
