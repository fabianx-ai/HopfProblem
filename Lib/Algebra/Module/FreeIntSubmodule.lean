/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Arbitrary-rank submodules of free integral modules

Every submodule of a free integral module is free.  The proof well-orders an ambient basis and
uses lifts of generators of the leading-coefficient ideals as a triangular basis.  No finite-rank
hypothesis is used.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

namespace Module.FreeIntSubmodule

open Submodule Submodule.IsPrincipal

namespace FinsuppModel

variable {ι : Type*} [LinearOrder ι] (N : Submodule ℤ (ι →₀ ℤ))

/-- Vectors of the submodule supported on the closed initial segment at `i`. -/
def initialSubmodule (i : ι) : Submodule ℤ (ι →₀ ℤ) :=
  N ⊓ Finsupp.supported ℤ ℤ (Set.Iic i)

theorem mem_initialSubmodule_iff (i : ι) (x : ι →₀ ℤ) :
    x ∈ initialSubmodule N i ↔ x ∈ N ∧ ∀ j, i < j → x j = 0 := by
  simp only [initialSubmodule, Submodule.mem_inf, Finsupp.mem_supported',
    Set.mem_Iic, not_le]

/-- The ideal of coefficients in degree `i` of vectors with support at most `i`. -/
def leadingIdeal (i : ι) : Ideal ℤ :=
  (initialSubmodule N i).map (Finsupp.lapply i)

theorem exists_leadingVector (i : ι) :
    ∃ x : ι →₀ ℤ, x ∈ N ∧ (∀ j, i < j → x j = 0) ∧
      x i = generator (leadingIdeal N i) := by
  obtain ⟨x, hx, he⟩ := (show generator (leadingIdeal N i) ∈
    (initialSubmodule N i).map (Finsupp.lapply i) from
      generator_mem (leadingIdeal N i))
  exact ⟨x, (mem_initialSubmodule_iff N i x).mp hx |>.1,
    (mem_initialSubmodule_iff N i x).mp hx |>.2, he⟩

/-- A lift of the generator of the leading-coefficient ideal. -/
def leadingVector (i : ι) : N :=
  ⟨(exists_leadingVector N i).choose, (exists_leadingVector N i).choose_spec.1⟩

theorem leadingVector_above (i j : ι) (h : i < j) :
    (leadingVector N i).1 j = 0 :=
  (exists_leadingVector N i).choose_spec.2.1 j h

theorem leadingVector_diagonal (i : ι) :
    (leadingVector N i).1 i = generator (leadingIdeal N i) :=
  (exists_leadingVector N i).choose_spec.2.2

theorem generator_dvd_coefficient (i : ι) (x : N)
    (hx : ∀ j, i < j → x.1 j = 0) :
    generator (leadingIdeal N i) ∣ x.1 i := by
  apply (mem_iff_generator_dvd (leadingIdeal N i)).mp
  exact ⟨x.1, (mem_initialSubmodule_iff N i x.1).mpr ⟨x.2, hx⟩, rfl⟩

/-- Indices with a nonzero leading ideal. -/
abbrev LeadingIndex := {i : ι // generator (leadingIdeal N i) ≠ 0}

/-- The triangular family in the original submodule. -/
def leadingFamily (i : LeadingIndex N) : N := leadingVector N i.1

theorem leadingFamily_diagonal_ne_zero (i : LeadingIndex N) :
    (leadingFamily N i).1 i.1 ≠ 0 := by
  rw [leadingFamily, leadingVector_diagonal]
  exact i.2

theorem leadingFamily_above (i j : LeadingIndex N) (h : i < j) :
    (leadingFamily N i).1 j.1 = 0 :=
  leadingVector_above N i.1 j.1 h

end FinsuppModel

/-- A nonzero finitely supported vector has a largest nonzero coordinate. -/
theorem exists_largest_support {ι : Type*} [LinearOrder ι] (x : ι →₀ ℤ) (hx : x ≠ 0) :
    ∃ i, x i ≠ 0 ∧ ∀ j, i < j → x j = 0 := by
  classical
  have hs : x.support.Nonempty := Finsupp.support_nonempty_iff.mpr hx
  refine ⟨x.support.max' hs, Finsupp.mem_support_iff.mp (Finset.max'_mem _ _), ?_⟩
  intro j hj
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  exact not_le_of_gt hj (Finset.le_max' _ _ hmem)

/-- A triangular family with nonzero diagonal is linearly independent. -/
theorem triangular_linearIndependent {ι M : Type*} [LinearOrder ι]
    [AddCommGroup M] [Module ℤ M] (v : ι → M) (coord : ι → M →ₗ[ℤ] ℤ)
    (hdiag : ∀ i, coord i (v i) ≠ 0)
    (htri : ∀ i j, i < j → coord j (v i) = 0) : LinearIndependent ℤ v := by
  classical
  apply linearIndependent_iff.mpr
  intro l hl
  by_contra hne
  obtain ⟨i, hi, himax⟩ := exists_largest_support l hne
  have his : i ∈ l.support := Finsupp.mem_support_iff.mpr hi
  have heval : ∑ j ∈ l.support, l j * coord i (v j) = 0 := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
      smul_eq_mul, map_zero] using congrArg (coord i) hl
  have hsum : (∑ j ∈ l.support, l j * coord i (v j)) = l i * coord i (v i) := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      have hle : j ≤ i := le_of_not_gt fun hij ↦
        Finsupp.mem_support_iff.mp hj (himax j hij)
      rw [htri j i (lt_of_le_of_ne hle hji), mul_zero]
    · intro h
      exact (h his).elim
  rw [hsum] at heval
  exact (mul_ne_zero hi (hdiag i)) heval

namespace FinsuppModel

variable {ι : Type*} [LinearOrder ι] (N : Submodule ℤ (ι →₀ ℤ))

theorem leadingFamily_linearIndependent : LinearIndependent ℤ (leadingFamily N) := by
  apply triangular_linearIndependent (leadingFamily N)
    (fun i ↦ (Finsupp.lapply i.1).comp N.subtype)
  · intro i
    exact leadingFamily_diagonal_ne_zero N i
  · intro i j hij
    exact leadingFamily_above N i j hij

/-- The leading vectors span every bounded support segment. -/
theorem mem_span_leadingFamily_of_bounded [WellFoundedLT ι] (i : ι) :
    ∀ x : N, (∀ j, i < j → x.1 j = 0) →
      x ∈ Submodule.span ℤ (Set.range (leadingFamily N)) := by
  apply wellFounded_lt.induction i
  intro i ih x hx
  have below : ∀ y : N, (∀ j, i ≤ j → y.1 j = 0) →
      y ∈ Submodule.span ℤ (Set.range (leadingFamily N)) := by
    intro y hy
    by_cases hyzero : y = 0
    · simpa only [hyzero] using
        (Submodule.zero_mem (Submodule.span ℤ (Set.range (leadingFamily N))))
    have hyval : y.1 ≠ 0 := fun h ↦ hyzero (Subtype.ext h)
    obtain ⟨j, hj, hjmax⟩ := exists_largest_support y.1 hyval
    exact ih j (lt_of_not_ge fun hij ↦ hj (hy j hij)) y hjmax
  obtain ⟨r, hr⟩ := generator_dvd_coefficient N i x hx
  by_cases hg : generator (leadingIdeal N i) = 0
  · apply below x
    intro j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · simpa only [hg, zero_mul] using hr
    · exact hx j hij
  · let k : LeadingIndex N := ⟨i, hg⟩
    have hy : x - r • leadingFamily N k ∈
        Submodule.span ℤ (Set.range (leadingFamily N)) := by
      apply below
      intro j hij
      change x.1 j - r * (leadingVector N i).1 j = 0
      rcases eq_or_lt_of_le hij with rfl | hij
      · rw [leadingVector_diagonal, hr, mul_comm, sub_self]
      · rw [hx j hij, leadingVector_above N i j hij, mul_zero, sub_self]
    have hv : r • leadingFamily N k ∈
        Submodule.span ℤ (Set.range (leadingFamily N)) :=
      Submodule.smul_mem _ r (Submodule.subset_span ⟨k, rfl⟩)
    simpa only [sub_add_cancel] using Submodule.add_mem _ hy hv

theorem leadingFamily_span_eq_top [WellFoundedLT ι] :
    Submodule.span ℤ (Set.range (leadingFamily N)) = ⊤ := by
  apply top_unique
  intro x _
  by_cases hx : x = 0
  · simpa only [hx] using
      (Submodule.zero_mem (Submodule.span ℤ (Set.range (leadingFamily N))))
  obtain ⟨i, _, hi⟩ := exists_largest_support x.1 (fun h ↦ hx (Subtype.ext h))
  exact mem_span_leadingFamily_of_bounded N i x hi

/-- A triangular basis for an arbitrary submodule of a well-ordered free module. -/
def leadingBasis [WellFoundedLT ι] : Basis (LeadingIndex N) ℤ N :=
  Basis.mk (leadingFamily_linearIndependent N) (leadingFamily_span_eq_top N).ge

end FinsuppModel

/-- An arbitrary submodule of an integral finitely-supported function module is free. -/
theorem finsupp_submodule_free_int {ι : Type*} (N : Submodule ℤ (ι →₀ ℤ)) :
    @Module.Free ℤ N _ _ N.module := by
  obtain ⟨horder, hwf⟩ := exists_wellFoundedLT ι
  let := horder
  let := hwf
  exact Module.Free.of_basis (FinsuppModel.leadingBasis N)

/-- Every submodule of a free integral module is free, without a rank bound. -/
theorem submodule_free_int {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] (N : Submodule ℤ M) : @Module.Free ℤ N _ _ N.module := by
  cases Subsingleton.elim ‹Module ℤ M› (AddCommGroup.toIntModule M)
  let b := Module.Free.chooseBasis ℤ M
  let : Module.Free ℤ (N.map b.repr.toLinearMap) :=
    finsupp_submodule_free_int (N.map b.repr.toLinearMap)
  exact Module.Free.of_equiv (b.repr.submoduleMap N).symm

/-- Every submodule of a free integral module is projective for any displayed integral-module
structure on its carrier.  This explicit form is useful when an API installs a local module
instance definitionally different from `Submodule.module`; integral module structures on a fixed
additive group are nevertheless unique. -/
theorem submodule_projective_int_with_module {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] (N : Submodule ℤ M) (moduleN : Module ℤ N) :
    @Module.Projective ℤ _ N _ moduleN := by
  let hfree : @Module.Free ℤ N _ _ N.module := submodule_free_int N
  let hprojective : @Module.Projective ℤ _ N _ N.module := by
    let _ := hfree
    infer_instance
  have hmodule : N.module = moduleN := Subsingleton.elim _ _
  exact cast
    (congrArg (fun moduleN : Module ℤ N ↦
      @Module.Projective ℤ _ N _ moduleN) hmodule)
    hprojective

/-- Every submodule of a free integral module is projective, without a rank bound. -/
theorem submodule_projective_int {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] (N : Submodule ℤ M) :
    Module.Projective ℤ N :=
  submodule_projective_int_with_module N inferInstance

end Module.FreeIntSubmodule
