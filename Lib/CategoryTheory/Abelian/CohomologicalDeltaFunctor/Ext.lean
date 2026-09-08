module
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Basic
public import Lib.CategoryTheory.Abelian.Injective.Ext
public import Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.Effaceable
public import Mathlib.Algebra.Category.Grp.Zero

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

set_option backward.isDefEq.respectTransparency false in
/-- Positive native Ext is effaceable (textbook lines 1778–1783). The same original
embedding into an injective works in every positive degree. Its identity-augmentation
resolution is concentrated in degree zero; applying fixed-source Hom preserves this
concentration. The native Ext computation by that resolution identifies its positive
groups with zero, as supplied by the existing injective-vanishing theorem. -/
theorem ofExt_effaceable (P : C) : (ofExt P).Effaceable := by
  intro q hq A
  refine ⟨Injective.under A, Injective.ι A, inferInstance, ?_⟩
  cases q with
  | zero => exact (Nat.lt_irrefl 0 hq).elim
  | succ n =>
    let := Ext.subsingleton_of_injective P (Injective.under A) n
    exact (AddCommGrpCat.isZero_of_subsingleton
      (AddCommGrpCat.of (Ext.{v} P (Injective.under A) (n+1)))).eq_of_tgt _ _

/-- The native Ext delta functor is universal as a source (textbook lines 1784–1786):
every natural degree-zero map to another cohomological delta functor extends uniquely
to a delta-functor morphism. This is the existing effaceability universality theorem
applied to the same native family and boundary. -/
theorem ofExt_isUniversal (P : C) : (ofExt P).IsUniversal :=
  (ofExt_effaceable P).isUniversal

end CategoryTheory.CohomologicalDeltaFunctor
