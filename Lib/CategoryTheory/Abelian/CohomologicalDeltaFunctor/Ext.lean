module
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Basic
public import Lib.CategoryTheory.Abelian.Injective.Ext
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Effaceable
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# The native fixed-source Ext cohomological delta functor

For a fixed object `P` of an abelian category with enough injectives, the family
`n ↦ Ext^n(P, -)` with its long-exact-sequence connecting morphisms is a cohomological
delta functor, and it is universal because `Ext^{n+1}(P, I) = 0` for `I` injective.
This is Weibel, *An Introduction to Homological Algebra*, Theorem 2.5.1 (see also
Example 2.4.8 and Hartshorne, *Algebraic Geometry* III.1.1A).

The positive boundary raises degree by one, from the quotient coefficient to the
subobject coefficient, without reversing coefficient maps. The degree-zero injection
`Hom(P, -) ↪ Ext^0(P, -)` remains the separate `ext_zero_injective` theorem; it is not
a field of the structure.
-/

public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Abelian
namespace CategoryTheory.CohomologicalDeltaFunctor
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
local instance : HasExt.{v} C := hasExt_of_enoughInjectives.{v,v,u} C

/-- For a fixed `P`, the family `n ↦ Ext^n(P, -)` with the connecting morphisms of the
Ext long exact sequence is a cohomological delta functor (Weibel 2.5.1): exactness at all
three positions, both zero composites and naturality in the short exact sequence hold. -/
@[expose] def ofExt (P : C) : CohomologicalDeltaFunctor C AddCommGrpCat.{v} where
  T n := AdditiveFunctor.of (extFunctorObj P n)
  δ hS n := extConnecting P hS n
  naturality hS hS' f n := extConnecting_naturality P hS hS' f n
  exact₁ hS n := ext_exact₁ P hS n
  comp₂ hS n := comp_extConnecting P hS n
  exact₂ hS n := ext_exact₂ P hS n
  comp₃ hS n := extConnecting_comp P hS n
  exact₃ hS n := ext_exact₃ P hS n

/-- The degree-`n` functor of `ofExt P`, including its action on coefficient maps, is
`Ext^n(P, -)`. -/
theorem ofExt_T_obj (P : C) (n : ℕ) :
    ((ofExt P).T n).obj = extFunctorObj P n := rfl

/-- The connecting morphism of `ofExt P` is the boundary of the Ext long exact sequence,
from the quotient coefficient in degree `n` to the subobject coefficient in degree
`n + 1`. -/
theorem ofExt_δ (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (ofExt P).δ hS n = extConnecting P hS n := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `Ext^n(P, -)` is effaceable in every positive degree: every object embeds into an
injective object `I`, and `Ext^{n+1}(P, I) = 0` (Weibel 2.5.1, using Weibel 2.4.5). -/
theorem ofExt_effaceable (P : C) : (ofExt P).Effaceable := by
  intro q hq A
  refine ⟨Injective.under A, Injective.ι A, inferInstance, ?_⟩
  cases q with
  | zero => exact (Nat.lt_irrefl 0 hq).elim
  | succ n =>
    let := Ext.subsingleton_of_injective P (Injective.under A) n
    exact (AddCommGrpCat.isZero_of_subsingleton
      (AddCommGrpCat.of (Ext.{v} P (Injective.under A) (n+1)))).eq_of_tgt _ _

/-- `n ↦ Ext^n(P, -)` is a universal cohomological delta functor: every natural
transformation out of its degree-zero part extends uniquely to a morphism of delta
functors (Weibel Theorem 2.5.1; Hartshorne III.1.1A). -/
theorem ofExt_isUniversal (P : C) : (ofExt P).IsUniversal :=
  (ofExt_effaceable P).isUniversal

end CategoryTheory.CohomologicalDeltaFunctor
