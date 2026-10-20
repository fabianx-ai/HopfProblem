/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Exact.Basic

/-!
# Surjectivity of a signed pair

An onto second component and an onto first component restricted to its kernel
make the same-domain signed pair onto. No module structure or splitting is needed.
-/

@[expose] public section

universe u v w z

namespace AddMonoidHom

/-- The signed pair `e ↦ (f e, -g e)` of two additive group homomorphisms out of the
same group `E` is surjective as soon as `g` is surjective and the restriction of `f`
to `ker g` is surjective.  (Elementary; compare `AddMonoidHom.prod` and
`AddMonoidHom.ker`.) -/
theorem surjective_signed_prod_of_surjective_ker
    {E : Type u} {A : Type v} {B : Type w}
    [AddCommGroup E] [AddCommGroup A] [AddCommGroup B]
    (f : E →+ A) (g : E →+ B)
    (hg : Function.Surjective g)
    (hf : Function.Surjective (f.domRestrict g.ker)) :
    Function.Surjective (fun e : E => (f e, -g e)) := by
  intro p
  obtain ⟨y, hy⟩ := hg (-p.2)
  obtain ⟨c, hc⟩ := hf (p.1 - f y)
  refine ⟨c.val + y, ?_⟩
  apply Prod.ext
  · change f (c.val + y) = p.1
    change f c.val = p.1 - f y at hc
    rw [map_add, hc, sub_add_cancel]
  · change -g (c.val + y) = p.2
    rw [map_add, c.property, zero_add, hy, neg_neg]

/-- If an onto homomorphism kills the signed pair and its second component is onto,
its restriction to the first factor is onto. Subtract a lift of the negative second target.
Textbook source: `CENTER_NATIVE_H2_CAP_ELIMINATION_TEXTBOOK.md`, HC5. -/
theorem surjective_restrict_left_of_signed_zero
    {E : Type u} {A : Type v} {B : Type w} {D : Type z}
    [AddCommGroup E] [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    (f : E →+ A) (g : E →+ B) (q : A × B →+ D)
    (hq : Function.Surjective q) (hg : Function.Surjective g)
    (hzero : ∀ e : E, q (f e, -g e) = 0) :
    Function.Surjective (fun a : A => q (a, 0)) := by
  intro d
  obtain ⟨⟨a, b⟩, hab⟩ := hq d
  obtain ⟨e, he⟩ := hg (-b)
  have hpair : (a, b) - (f e, -g e) = (a - f e, 0) := by
    apply Prod.ext
    · rfl
    · change b - -g e = 0
      rw [he, neg_neg, sub_self]
  refine ⟨a - f e, ?_⟩
  change q (a - f e, 0) = d
  rw [← hpair, map_sub, hab, hzero, sub_zero]

/-- Exactness of a signed pair characterizes the zero fibre of the restriction
 to the first factor, without any surjectivity assumption.
Textbook source: `CENTER_NATIVE_H2_CAP_ELIMINATION_TEXTBOOK.md`, HC6 signed-pair argument. -/
theorem restrict_left_eq_zero_iff_of_signed_exact
    {E : Type u} {A : Type v} {B : Type w} {D : Type z}
    [AddCommGroup E] [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    (f : E →+ A) (g : E →+ B) (q : A × B →+ D)
    (hexact : Function.Exact (fun e : E => (f e, -g e)) q)
    (a : A) :
    q (a, 0) = 0 ↔ ∃ e : E, g e = 0 ∧ f e = a := by
  constructor
  · intro ha
    obtain ⟨e, he⟩ := (hexact (a, 0)).mp ha
    have hg : -g e = 0 := congrArg Prod.snd he
    have hf : f e = a := congrArg Prod.fst he
    exact ⟨e, neg_eq_zero.mp hg, hf⟩
  · rintro ⟨e, hg, hf⟩
    have hpair : (f e, -g e) = (a, 0) := by
      apply Prod.ext
      · exact hf
      · rw [hg, neg_zero]
    rw [← hpair]
    exact hexact.apply_apply_eq_zero e

end AddMonoidHom
