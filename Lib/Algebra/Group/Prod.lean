module
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Surjectivity of a signed pair

An onto second component and an onto first component restricted to its kernel
make the same-domain signed pair onto. No module structure or splitting is needed.
-/

@[expose] public section

universe u v w

namespace AddMonoidHom

/-- Lift the negative second target through `g`, correct the first target inside
`ker(g)`, and add the two lifts. The resulting signed pair is surjective.
Textbook source: `CENTER_SIGNED_PAIR_SURJECTIVITY_TEXTBOOK.md`, SP1–SP6. -/
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

end AddMonoidHom
