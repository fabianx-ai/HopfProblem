/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.GroupTheory.Archimedean

/-!
# Integral modules embedded nontrivially in the integers

Every nonzero subgroup of the additive integers is infinite cyclic.  Consequently, if an
integral module embeds in `ℤ` and its image is nonzero, the source is linearly equivalent to
`ℤ`.  The equivalence is noncanonical because it chooses a generator of the image subgroup.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

namespace LinearMap

/-- The domain of an injective integral-linear map into `ℤ` is a free rank-one module as soon
as the map takes one nonzero value.  The coordinate chooses a generator of the image subgroup. -/
def domainEquivIntOfInjectiveOfNonzero
    {A : Type*} [AddCommGroup A] [Module ℤ A]
    (f : A →ₗ[ℤ] ℤ) (hf : Function.Injective f)
    (hne : ∃ a, f a ≠ 0) : A ≃ₗ[ℤ] ℤ := by
  let H : Submodule ℤ ℤ := LinearMap.range f
  let d : ℤ := (Int.subgroup_cyclic H.toAddSubgroup).choose
  have hd : H.toAddSubgroup = AddSubgroup.closure {d} :=
    (Int.subgroup_cyclic H.toAddSubgroup).choose_spec
  have hdmem : d ∈ H := by
    change d ∈ H.toAddSubgroup
    rw [hd]
    exact AddSubgroup.subset_closure (Set.mem_singleton d)
  have hdne : d ≠ 0 := by
    intro hd0
    obtain ⟨a, ha⟩ := hne
    have hfa : f a ∈ H := LinearMap.mem_range_self f a
    have hfa' : f a ∈ H.toAddSubgroup := hfa
    rw [hd, hd0, AddSubgroup.closure_singleton_zero, AddSubgroup.mem_bot] at hfa'
    exact ha hfa'
  let g : ℤ →ₗ[ℤ] H :=
    { toFun := fun n => n • (⟨d, hdmem⟩ : H)
      map_add' := by intros; exact add_smul _ _ _
      map_smul' := by intros; exact mul_smul _ _ _ }
  have hg_injective : Function.Injective g := by
    intro a b hab
    have habval := congrArg Subtype.val hab
    change a • d = b • d at habval
    exact (smul_left_injective ℤ hdne) habval
  have hg_surjective : Function.Surjective g := by
    intro y
    have hy : y.1 ∈ H.toAddSubgroup := y.2
    rw [hd, AddSubgroup.mem_closure_singleton] at hy
    obtain ⟨n, hn⟩ := hy
    refine ⟨n, Subtype.ext ?_⟩
    simpa [g] using hn
  exact (LinearEquiv.ofInjective f hf).trans
    (LinearEquiv.ofBijective g ⟨hg_injective, hg_surjective⟩).symm

/-- An integral-linear map out of a module with a chosen rank-one coordinate is nonzero exactly
when it is nonzero on the coordinate generator. -/
theorem ne_zero_iff_apply_equivInt_symm_one
    {A B : Type*} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    (f : A →ₗ[ℤ] B) (e : A ≃ₗ[ℤ] ℤ) :
    f ≠ 0 ↔ f (e.symm 1) ≠ 0 := by
  constructor
  · intro hf hgen
    apply hf
    ext x
    have hx : x = e x • e.symm 1 := by
      apply e.injective
      simp
    calc
      f x = f (e x • e.symm 1) := congrArg f hx
      _ = e x • f (e.symm 1) := map_zsmul f _ _
      _ = e x • (0 : B) := congrArg (fun y ↦ e x • y) hgen
      _ = 0 := zsmul_zero _
      _ = (0 : A →ₗ[ℤ] B) x := rfl
  · intro hgen hf
    apply hgen
    rw [hf]
    rfl

end LinearMap
