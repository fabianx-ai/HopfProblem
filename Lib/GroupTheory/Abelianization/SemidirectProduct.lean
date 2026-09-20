/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Abelianization of semidirect products

This file identifies the abelianization of a semidirect product `K ⋊[φ] Q` with the product of
the abelianization of `Q` and the coinvariants of the induced `Q`-representation on the additive
group underlying `Abelianization K`.

The coinvariant factor is Mathlib's standard `Representation.Coinvariants`; no second quotient
notion is introduced.

## Main definitions

* `Abelianization.mapMulAut`: abelianization sends automorphisms to automorphisms.
* `SemidirectProduct.abelianizationRepresentation`: the induced integral representation on the
  abelianization of the normal factor.
* `SemidirectProduct.AbelianizationCoinvariants`: its standard representation coinvariants.
* `SemidirectProduct.abelianizationMulEquiv`: the abelianization formula for a semidirect product.

## References

* [Kenneth S. Brown, *Cohomology of Groups*][brown1982], Ch. II (the low-degree Lyndon–Hochschild–
  Serre sequence gives `H₁(K ⋊ Q) ≅ H₁(Q) ⊕ (H₁(K))_Q`).
-/

@[expose] public section

universe u v

namespace Abelianization

/-- Abelianization sends automorphisms of a group to automorphisms of its abelianization. -/
noncomputable def mapMulAut (K : Type u) [Group K] :
    MulAut K →* MulAut (Abelianization K) where
  toFun e := e.abelianizationCongr
  map_one' := abelianizationCongr_refl
  map_mul' e f := by
    apply MulEquiv.ext
    rintro ⟨k⟩
    rfl

end Abelianization

namespace SemidirectProduct

noncomputable section

variable {K : Type u} {Q : Type v} [Group K] [Group Q]

/-- The integral representation induced by an action on the abelianization of the acted-on group. -/
noncomputable def abelianizationRepresentation (φ : Q →* MulAut K) :
    Representation ℤ Q (Additive (Abelianization K)) := by
  letI : MulDistribMulAction Q (Abelianization K) :=
    MulDistribMulAction.compHom (Abelianization K) ((Abelianization.mapMulAut K).comp φ)
  exact Representation.ofMulDistribMulAction Q (Abelianization K)

/-- The coinvariants of the induced action on the abelianization of the acted-on group. -/
abbrev AbelianizationCoinvariants (φ : Q →* MulAut K) :=
  Representation.Coinvariants (abelianizationRepresentation φ)

/-- The canonical map from a group to the coinvariants of its abelianization. -/
noncomputable def coinvariantsMk (φ : Q →* MulAut K) :
    K →* Multiplicative (AbelianizationCoinvariants φ) where
  toFun k := Multiplicative.ofAdd <|
    Representation.Coinvariants.mk (abelianizationRepresentation φ) <|
      Additive.ofMul (Abelianization.of k)
  map_one' := by
    change Multiplicative.ofAdd
      (Representation.Coinvariants.mk (abelianizationRepresentation φ) 0) = 1
    simp
  map_mul' k l := by
    change Multiplicative.ofAdd
        (Representation.Coinvariants.mk (abelianizationRepresentation φ)
          (Additive.ofMul (Abelianization.of (k * l)))) =
      Multiplicative.ofAdd
        (Representation.Coinvariants.mk (abelianizationRepresentation φ)
          (Additive.ofMul (Abelianization.of k))) *
      Multiplicative.ofAdd
        (Representation.Coinvariants.mk (abelianizationRepresentation φ)
          (Additive.ofMul (Abelianization.of l)))
    simp

/-- The action is trivial after passing to the coinvariants of the abelianization. -/
@[simp]
theorem coinvariantsMk_action (φ : Q →* MulAut K) (q : Q) (k : K) :
    coinvariantsMk φ (φ q k) = coinvariantsMk φ k := by
  change Multiplicative.ofAdd
      (Representation.Coinvariants.mk (abelianizationRepresentation φ)
        (Additive.ofMul (Abelianization.of (φ q k)))) =
    Multiplicative.ofAdd
      (Representation.Coinvariants.mk (abelianizationRepresentation φ)
        (Additive.ofMul (Abelianization.of k)))
  exact congrArg Multiplicative.ofAdd <|
    Representation.Coinvariants.mk_self_apply
      (abelianizationRepresentation φ) q (Additive.ofMul (Abelianization.of k))

/-- The abelianization of a semidirect product is the product of the quotient's abelianization and
the coinvariants of the abelianization of the normal factor. -/
noncomputable def abelianizationMulEquiv (φ : Q →* MulAut K) :
    Abelianization (K ⋊[φ] Q) ≃*
      Abelianization Q × Multiplicative (AbelianizationCoinvariants φ) := by
  let toFactors :
      K ⋊[φ] Q →* Abelianization Q × Multiplicative (AbelianizationCoinvariants φ) :=
    { toFun := fun g => (Abelianization.of g.right, coinvariantsMk φ g.left)
      map_one' := by simp
      map_mul' := by
        intro g h
        ext
        · simp
        · simp }
  let abelianizationToFactors :
      Abelianization (K ⋊[φ] Q) →*
        Abelianization Q × Multiplicative (AbelianizationCoinvariants φ) :=
    Abelianization.lift toFactors
  let inlLinear :
      Additive (Abelianization K) →ₗ[ℤ] Additive (Abelianization (K ⋊[φ] Q)) :=
    (MonoidHom.toAdditive
      (Abelianization.map (SemidirectProduct.inl : K →* K ⋊[φ] Q))).toIntLinearMap
  have inlLinear_invariant (q : Q) :
      inlLinear ∘ₗ abelianizationRepresentation φ q = inlLinear := by
    ext x
    obtain ⟨k⟩ := x
    change Additive.ofMul
        (Abelianization.of (SemidirectProduct.inl (φ q k) : K ⋊[φ] Q)) =
      Additive.ofMul (Abelianization.of (SemidirectProduct.inl k : K ⋊[φ] Q))
    rw [SemidirectProduct.inl_aut]
    simp [mul_comm]
  let fromCoinvariantsLinear :
      AbelianizationCoinvariants φ →ₗ[ℤ] Additive (Abelianization (K ⋊[φ] Q)) :=
    Representation.Coinvariants.lift (abelianizationRepresentation φ) inlLinear
      inlLinear_invariant
  let fromCoinvariants :
      Multiplicative (AbelianizationCoinvariants φ) →* Abelianization (K ⋊[φ] Q) :=
    { toFun := fun x => (fromCoinvariantsLinear x.toAdd).toMul
      map_one' := by
        change (fromCoinvariantsLinear 0).toMul = 1
        simp
      map_mul' := by
        intro x y
        change (fromCoinvariantsLinear (x.toAdd + y.toAdd)).toMul =
          (fromCoinvariantsLinear x.toAdd).toMul * (fromCoinvariantsLinear y.toAdd).toMul
        simp }
  have fromCoinvariants_mk (k : K) :
      fromCoinvariants (coinvariantsMk φ k) =
        Abelianization.of (SemidirectProduct.inl k : K ⋊[φ] Q) := by
    rfl
  let factorsToAbelianization :
      Abelianization Q × Multiplicative (AbelianizationCoinvariants φ) →*
        Abelianization (K ⋊[φ] Q) :=
    (Abelianization.map (SemidirectProduct.inr : Q →* K ⋊[φ] Q)).coprod fromCoinvariants
  exact
    { toFun := abelianizationToFactors
      invFun := factorsToAbelianization
      map_mul' := map_mul _
      left_inv := by
        intro a
        obtain ⟨g⟩ := a
        change factorsToAbelianization (toFactors g) = Abelianization.of g
        calc
          _ = Abelianization.of (SemidirectProduct.inl g.left : K ⋊[φ] Q) *
              Abelianization.of (SemidirectProduct.inr g.right : K ⋊[φ] Q) := by
                simp [factorsToAbelianization, toFactors, fromCoinvariants_mk, mul_comm]
          _ = Abelianization.of
              (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right) :=
            (map_mul Abelianization.of _ _).symm
          _ = Abelianization.of g := by rw [SemidirectProduct.inl_left_mul_inr_right]
      right_inv := by
        intro a
        obtain ⟨q, kbar⟩ := a
        obtain ⟨q⟩ := q
        obtain ⟨kbar⟩ := kbar
        obtain ⟨k⟩ := kbar
        change abelianizationToFactors
            (factorsToAbelianization (Abelianization.of q, coinvariantsMk φ k)) =
          (Abelianization.of q, coinvariantsMk φ k)
        simp [abelianizationToFactors, factorsToAbelianization, toFactors,
          fromCoinvariants_mk] }

/-- On the image of the kernel, the abelianization formula is the canonical map to the
coinvariants. -/
@[simp]
theorem abelianizationMulEquiv_apply_of_inl (φ : Q →* MulAut K) (k : K) :
    abelianizationMulEquiv φ
        (Abelianization.of (SemidirectProduct.inl k : K ⋊[φ] Q)) =
      (1, coinvariantsMk φ k) := by
  rfl

/-- On the image of the quotient, the abelianization formula is the abelianization of `Q`. -/
@[simp]
theorem abelianizationMulEquiv_apply_of_inr (φ : Q →* MulAut K) (q : Q) :
    abelianizationMulEquiv φ
        (Abelianization.of (SemidirectProduct.inr q : K ⋊[φ] Q)) =
      (Abelianization.of q, 1) := by
  rfl

/-- The inverse of the abelianization formula sends a coinvariant class of the kernel back to the
class of the corresponding element of `K`. -/
@[simp]
theorem abelianizationMulEquiv_symm_apply_inl (φ : Q →* MulAut K) (k : K) :
    (abelianizationMulEquiv φ).symm (1, coinvariantsMk φ k) =
      Abelianization.of (SemidirectProduct.inl k : K ⋊[φ] Q) := by
  apply (abelianizationMulEquiv φ).injective
  simp

/-- The inverse of the abelianization formula sends a class of `Q` back to the class of the
corresponding element of the quotient factor. -/
@[simp]
theorem abelianizationMulEquiv_symm_apply_inr (φ : Q →* MulAut K) (q : Q) :
    (abelianizationMulEquiv φ).symm (Abelianization.of q, 1) =
      Abelianization.of (SemidirectProduct.inr q : K ⋊[φ] Q) := by
  apply (abelianizationMulEquiv φ).injective
  simp

end


end SemidirectProduct
