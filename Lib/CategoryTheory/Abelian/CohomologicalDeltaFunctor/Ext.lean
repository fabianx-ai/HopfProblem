module
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Basic
public import Lib.CategoryTheory.Abelian.Injective.Ext

/-!
# The native fixed-source Ext cohomological delta functor

The textbook Ext-model argument, lines 1744–1747, assembles the additive native
degree functors, exactness and naturality into the existing cohomological delta
functor interface. The positive boundary raises degree by one, from the quotient
coefficient to the subobject coefficient, without reversing coefficient maps.
The initial degree-zero injection remains the separate `ext_zero_injective`
theorem; it is not an additional field of the structure.
-/

public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Abelian
namespace CategoryTheory.CohomologicalDeltaFunctor
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
local instance : HasExt.{v} C := hasExt_of_enoughInjectives.{v,v,u} C

/-- Fixed-source native Ext, with its whole additive degree functors and the same
positive connecting maps, is a cohomological delta functor. Exactness at all three
positions, both zero composites and naturality for every original short exact
sequence morphism supply the existing eight fields (textbook lines 1744–1747). -/
@[expose] def ofExt (P : C) : CohomologicalDeltaFunctor C AddCommGrpCat.{v} where
  T n := AdditiveFunctor.of (extFunctorObj P n)
  δ hS n := extConnecting P hS n
  naturality hS hS' f n := extConnecting_naturality P hS hS' f n
  exact₁ hS n := ext_exact₁ P hS n
  comp₂ hS n := comp_extConnecting P hS n
  exact₂ hS n := ext_exact₂ P hS n
  comp₃ hS n := extConnecting_comp P hS n
  exact₃ hS n := ext_exact₃ P hS n

/-- The entire degree functor, including its coefficient maps, is the native Ext
functor used in the textbook assembly at line 1744. -/
theorem ofExt_T_obj (P : C) (n : ℕ) :
    ((ofExt P).T n).obj = extFunctorObj P n := rfl

/-- The packaged boundary is the same positive native boundary from quotient
degree `n` to subobject degree `n + 1` (textbook lines 1745–1747). -/
theorem ofExt_δ (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (ofExt P).δ hS n = extConnecting P hS n := rfl
end CategoryTheory.CohomologicalDeltaFunctor
