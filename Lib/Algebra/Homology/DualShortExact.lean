/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularCochains.DualEvaluation

/-!
# The dual of a split short exact sequence of chain complexes

For a short exact sequence `0 → K₁ → K₂ → K₃ → 0` of chain complexes of `ℤ`-modules whose first
map has a degreewise retraction (as is the case when `K₃` is degreewise free, in particular for
the pair sequence `0 → C(A) → C(X) → C(X, A) → 0` of singular chains), the dual sequence of
cochain complexes with coefficients in any abelian group `A`,

  `0 → Hom(K₃, A) → Hom(K₂, A) → Hom(K₁, A) → 0`,

is short exact (`dualShortComplex_shortExact`).  This is the contravariant half of Hatcher's
§3.1 remark that `Hom(-, G)` turns the (degreewise split) short exact sequence of a pair into a
short exact sequence of cochain complexes, giving the long exact cohomology sequence of a pair.

## Main definitions and results

* `AlgebraicTopology.SingularCochains.dualShortComplex A S`.
* `AlgebraicTopology.SingularCochains.dualShortComplex_shortExact`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.1, the long exact sequence of a pair in
  cohomology

## Tags

cochains, dual complex, short exact sequence
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicTopology.SingularCochains

open DualEvaluation

variable (A : AddCommGrpCat.{0})

/-- The zero chain map evaluates to zero in every degree. -/
theorem zero_f_hom_apply {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (n : ℕ) (x : K.X n) :
    ((0 : K ⟶ L).f n).hom x = 0 := by
  simp

/-- The dual of a chain map with zero composite is zero: `Hom(X₃, A) → Hom(X₁, A)` vanishes. -/
theorem dualMap_comp_eq_zero {K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L) (g : L ⟶ M)
    (h : f ≫ g = 0) : dualMap A g ≫ dualMap A f = 0 := by
  rw [← dualMap_comp]
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  apply AddMonoidHom.ext
  intro x
  have hx : ((f ≫ g).f n).hom x = 0 := by rw [h]; exact zero_f_hom_apply n x
  change cochainAddHom A M n φ (((f ≫ g).f n).hom x) = 0
  rw [hx, map_zero]

/-- The dual of a short complex of chain complexes: `Hom(X₃, A) → Hom(X₂, A) → Hom(X₁, A)`. -/
def dualShortComplex (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)) :
    ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ) :=
  ShortComplex.mk (dualMap A S.g) (dualMap A S.f) (dualMap_comp_eq_zero A S.f S.g S.zero)

@[simp] theorem dualShortComplex_X₁ (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)) :
    (dualShortComplex A S).X₁ = dualComplex A S.X₃ := rfl
@[simp] theorem dualShortComplex_X₂ (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)) :
    (dualShortComplex A S).X₂ = dualComplex A S.X₂ := rfl
@[simp] theorem dualShortComplex_X₃ (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)) :
    (dualShortComplex A S).X₃ = dualComplex A S.X₁ := rfl
@[simp] theorem dualShortComplex_f (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)) :
    (dualShortComplex A S).f = dualMap A S.g := rfl
@[simp] theorem dualShortComplex_g (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)) :
    (dualShortComplex A S).g = dualMap A S.f := rfl

/-- A functional vanishing on the kernel of a surjective linear map descends along it. -/
theorem exists_comp_of_ker_le {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module ℤ M]
    [Module ℤ N] (g : M →ₗ[ℤ] N) (hg : Function.Surjective g) (φ : M →+ A)
    (hφ : ∀ x, g x = 0 → φ x = 0) : ∃ ψ : N →+ A, ψ.comp g.toAddMonoidHom = φ := by
  have hker : g.toAddMonoidHom.ker ≤ φ.ker := fun x hx => hφ x hx
  let e := QuotientAddGroup.quotientKerEquivOfSurjective g.toAddMonoidHom hg
  refine ⟨(QuotientAddGroup.lift _ φ hker).comp e.symm.toAddMonoidHom, ?_⟩
  apply AddMonoidHom.ext
  intro x
  change QuotientAddGroup.lift _ φ hker (e.symm (g x)) = φ x
  have : e.symm (g x) = QuotientAddGroup.mk x := by
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [this, QuotientAddGroup.lift_mk]

/-- **The dual of a degreewise split short exact sequence is short exact.**  If `S` is a short
exact sequence of chain complexes of `ℤ`-modules whose first map has a retraction in every degree,
then `Hom(S.X₃, A) → Hom(S.X₂, A) → Hom(S.X₁, A)` is short exact. -/
theorem dualShortComplex_shortExact (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ))
    (hS : S.ShortExact) (r : ∀ n, S.X₂.X n →ₗ[ℤ] S.X₁.X n)
    (hr : ∀ n (x : S.X₁.X n), r n ((S.f.f n).hom x) = x) :
    (dualShortComplex A S).ShortExact := by
  have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hn := hdeg n
  have hg : Function.Surjective (S.g.f n).hom := hn.moduleCat_surjective_g
  have hexact : Function.Exact (S.f.f n).hom (S.g.f n).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hn.exact
  have hmono : Mono ((dualMap A S.g).f n) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro φ φ' h
    apply AddMonoidHom.ext
    intro z
    obtain ⟨x, rfl⟩ := hg z
    exact congrArg (fun χ => cochainAddHom A S.X₂ n χ x) h
  have hepi : Epi ((dualMap A S.f).f n) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro ψ
    refine ⟨(cochainAddHom A S.X₁ n ψ).comp (r n).toAddMonoidHom, ?_⟩
    apply AddMonoidHom.ext
    intro x
    exact congrArg (cochainAddHom A S.X₁ n ψ) (hr n x)
  refine { exact := ?_, mono_f := hmono, epi_g := hepi }
  · -- exactness: a functional on `X₂` vanishing on the image of `X₁` descends to `X₃`
    rw [ShortComplex.ab_exact_iff]
    intro φ hφ
    change (dualMap A S.f).f n φ = 0 at hφ
    obtain ⟨ψ, hψ⟩ := exists_comp_of_ker_le A (S.g.f n).hom hg (cochainAddHom A S.X₂ n φ) (by
      intro x hx
      obtain ⟨y, rfl⟩ := (hexact x).mp hx
      exact congrArg (fun χ => cochainAddHom A S.X₁ n χ y) hφ)
    refine ⟨ψ, ?_⟩
    apply AddMonoidHom.ext
    intro x
    exact congrArg (fun χ : S.X₂.X n →+ A => χ x) hψ

end AlgebraicTopology.SingularCochains
