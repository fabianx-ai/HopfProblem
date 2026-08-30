/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.GroupTheory.PushoutI

/-!
# A monoid-pushout equivalence from mutually inverse cocone data

This module isolates the final algebraic step of a pushout argument. A consumer supplies a cocone
into `K`, a reverse map, and hom extensionality on the chart maps; `equivOfCocone` packages those
data into a `MulEquiv`.
-/

@[expose] public section

namespace Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {H K : Type*}
variable [Nonempty ι] [∀ i, Monoid (G i)] [Monoid H] [Monoid K]
variable {phi : ∀ i, H →* G i}

/-- A cocone into `K` is a pushout equivalence when it has a reverse map agreeing on every chart
and maps out of `K` are determined by the chart maps. -/
def equivOfCocone
    (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (phi i) = k)
    (back : K →* PushoutI phi)
    (hback : ∀ i, back.comp (f i) = of i)
    (hom_ext : ∀ a b : K →* K, (∀ i, a.comp (f i) = b.comp (f i)) → a = b) :
    PushoutI phi ≃* K := by
  let forward : PushoutI phi →* K := lift f k hf
  have hforward (i : ι) : forward.comp (of i) = f i := by
    ext g
    exact lift_of f k hf g
  have hleft : back.comp forward = MonoidHom.id (PushoutI phi) := by
    apply Monoid.PushoutI.hom_ext_nonempty
    intro i
    rw [MonoidHom.comp_assoc, hforward i, hback i, MonoidHom.id_comp]
  have hright : forward.comp back = MonoidHom.id K := by
    apply hom_ext
    intro i
    rw [MonoidHom.comp_assoc, hback i, hforward i, MonoidHom.id_comp]
  exact
    { toFun := forward
      invFun := back
      left_inv := fun x ↦ DFunLike.congr_fun hleft x
      right_inv := fun x ↦ DFunLike.congr_fun hright x
      map_mul' := forward.map_mul }

@[simp]
theorem equivOfCocone_apply_of
    (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (phi i) = k)
    (back : K →* PushoutI phi)
    (hback : ∀ i, back.comp (f i) = of i)
    (hom_ext : ∀ a b : K →* K, (∀ i, a.comp (f i) = b.comp (f i)) → a = b)
    (i : ι) (g : G i) :
    equivOfCocone f k hf back hback hom_ext (of i g) = f i g := by
  exact lift_of f k hf g

@[simp]
theorem equivOfCocone_symm_apply_f
    (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (phi i) = k)
    (back : K →* PushoutI phi)
    (hback : ∀ i, back.comp (f i) = of i)
    (hom_ext : ∀ a b : K →* K, (∀ i, a.comp (f i) = b.comp (f i)) → a = b)
    (i : ι) (g : G i) :
    (equivOfCocone f k hf back hback hom_ext).symm (f i g) = of i g := by
  change back (f i g) = of i g
  exact DFunLike.congr_fun (hback i) g

end Monoid.PushoutI
