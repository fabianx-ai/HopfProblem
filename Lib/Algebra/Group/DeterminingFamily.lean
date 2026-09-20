/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Commutativity from a determining family

An element commuting with an endomorphism-determining family is central:
its inner conjugation agrees with the identity on that family, hence everywhere.
For an integer four-lattice whose image consists of powers of a fixed element,
two additional determining elements with product one reduce to one element
and its inverse. Commutation of the fixed element with the first one then
gives centrality of each, and finally commutativity of the entire group.
The argument uses no commutative-group instance or generation presentation.

## References

The first lemma is the folklore centrality criterion: an element whose inner automorphism
agrees with the identity on a family that determines endomorphisms lies in the centre
(`Subgroup.center`).  It is `MonoidHom.ext` applied to `MulAut.conj`.
-/

@[expose] public section
universe u v
namespace DeterminingFamily

/-- If `a` commutes with every member of a family `s` that determines
endomorphisms of `G` (two endomorphisms agreeing on `s` are equal), then `a`
commutes with every element of `G`, that is, `a` is central. -/
theorem commute_all_of_hom_ext
    {G : Type u} [Group G] {ι : Type v} (s : ι → G)
    (hext : ∀ f g : G →* G, (∀ i : ι, f (s i) = g (s i)) → f = g)
    (a : G) (ha : ∀ i : ι, Commute a (s i)) :
    ∀ b : G, Commute a b := by
  have hconj : (MulAut.conj a).toMonoidHom = MonoidHom.id G := by
    apply hext
    intro i
    change a * s i * a⁻¹ = s i
    rw [(ha i).eq]
    exact mul_inv_cancel_right (s i) a
  intro b
  have hb : a * b * a⁻¹ = b := DFunLike.congr_fun hconj b
  exact mul_inv_eq_iff_eq_mul.mp hb

/-- Write `c = φ (ofAdd ![1, 2, -4, 0])` and let `φ : Multiplicative (Fin 4 → ℤ) →* G` be given
by the exponent formula `φ (ofAdd z) = c ^ z 0` for every `z : Fin 4 → ℤ`, the exponent being the
zeroth coordinate of `z` (this is stronger than saying the image of `φ` lies in the powers of
`c`).  Let `x y : G` be such that the image of `φ` together with `x` and `y` determines
endomorphisms of `G`.  If `c` commutes with `x` and `x * y = 1`, then `G` is commutative. -/
theorem commute_all_of_lattice_image_eq_zpow
    {G : Type u} [Group G]
    (φ : Multiplicative (Fin 4 → ℤ) →* G) (x y : G)
    (hext : ∀ f g : G →* G,
      (∀ w : Multiplicative (Fin 4 → ℤ), f (φ w) = g (φ w)) →
      f x = g x → f y = g y → f = g)
    (hpow : ∀ z : Fin 4 → ℤ,
      φ (Multiplicative.ofAdd z) =
        φ (Multiplicative.ofAdd (![1, 2, -4, 0] : Fin 4 → ℤ)) ^ z 0)
    (hcx : Commute
      (φ (Multiplicative.ofAdd (![1, 2, -4, 0] : Fin 4 → ℤ))) x)
    (hxy : x * y = 1) :
    ∀ a b : G, Commute a b := by
  have hy : y = x⁻¹ := eq_inv_of_mul_eq_one_right hxy
  let c : G := φ (Multiplicative.ofAdd (![1, 2, -4, 0] : Fin 4 → ℤ))
  let s : Sum (Multiplicative (Fin 4 → ℤ)) Bool → G :=
    Sum.elim (fun w => φ w) (fun b => if b then y else x)
  have power (w : Multiplicative (Fin 4 → ℤ)) : φ w = c ^ (w.toAdd) 0 :=
    hpow w.toAdd
  have indexed : ∀ f g : G →* G, (∀ i, f (s i) = g (s i)) → f = g := by
    intro f g h
    exact hext f g (fun w => h (Sum.inl w)) (h (Sum.inr false)) (h (Sum.inr true))
  -- The lattice generator commutes with all its powers and with x and y.
  have hc : ∀ b : G, Commute c b := by
    apply commute_all_of_hom_ext s indexed c
    intro i
    rcases i with w | b
    · change Commute c (φ w)
      rw [power]
      exact (Commute.refl c).zpow_right _
    · cases b with
      | false => exact hcx
      | true =>
          change Commute c y
          rw [hy]
          exact hcx.inv_right
  -- Next the first element commutes with the same determining family.
  have hx : ∀ b : G, Commute x b := by
    apply commute_all_of_hom_ext s indexed x
    intro i
    rcases i with w | b
    · change Commute x (φ w)
      rw [power]
      exact hcx.symm.zpow_right _
    · cases b with
      | false => exact Commute.refl x
      | true =>
          change Commute x y
          rw [hy]
          exact (Commute.refl x).inv_right
  -- Symmetry of those two centrality statements controls every element.
  intro a
  apply commute_all_of_hom_ext s indexed a
  intro i
  rcases i with w | b
  · change Commute a (φ w)
    rw [power]
    exact (hc a).symm.zpow_right _
  · cases b with
    | false => exact (hx a).symm
    | true =>
        change Commute a y
        rw [hy]
        exact (hx a).symm.inv_right

end DeterminingFamily
