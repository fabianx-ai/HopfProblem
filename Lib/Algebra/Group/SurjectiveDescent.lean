/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Descent of group homomorphisms along a surjection

This strict helper is independent of the Hopf development.  It packages the elementary
kernel criterion used when an overlap character descends across a surjective filling map.
-/

@[expose] public noncomputable section


/-- Descend a homomorphism across a surjective homomorphism when it is constant on fibres. -/
def descendHomOfSurjective
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (hf : Function.Surjective f) (g : A →* C)
    (hfg : ∀ a b, f a = f b → g a = g b) : B →* C where
  toFun b := g (hf b).choose
  map_one' := by
    have h := hfg (hf 1).choose 1 ((hf 1).choose_spec.trans f.map_one.symm)
    simpa using h
  map_mul' b₁ b₂ := by
    have h := hfg (hf (b₁ * b₂)).choose ((hf b₁).choose * (hf b₂).choose) (by
      rw [(hf (b₁ * b₂)).choose_spec, map_mul, (hf b₁).choose_spec, (hf b₂).choose_spec])
    simpa only [map_mul] using h

/-- A kernel inclusion makes a homomorphism constant on the fibres of another one. -/
theorem fibre_constant_of_ker_le
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : A →* C) (hker : f.ker ≤ g.ker) :
    ∀ a b, f a = f b → g a = g b := by
  intro a b hab
  have hk : a * b⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  have hg := hker hk
  rw [MonoidHom.mem_ker, map_mul, map_inv] at hg
  exact eq_of_mul_inv_eq_one hg

/-- The descended map composes back to the original map. -/
theorem descendHomOfSurjective_comp
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (hf : Function.Surjective f) (g : A →* C)
    (hfg : ∀ a b, f a = f b → g a = g b) :
    (descendHomOfSurjective f hf g hfg).comp f = g := by
  ext a
  exact hfg (hf (f a)).choose a (hf (f a)).choose_spec
