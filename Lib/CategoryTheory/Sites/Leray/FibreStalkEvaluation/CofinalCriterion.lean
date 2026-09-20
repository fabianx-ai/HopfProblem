/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.CanonicalPositive

/-!
# A cofinal-neighborhood criterion for positive fibre-stalk evaluation

The canonical positive-degree map from a higher-direct-image stalk to fibre cohomology is built
as a filtered colimit over neighborhoods.  This file packages the standard lift-and-kill
argument: if every neighborhood contains a smaller one on which the literal cohomology
evaluation is bijective, then the canonical stalk map is an isomorphism.

The constant-coefficient specialization is stated separately.  Neither theorem asserts that the
local bijectivity hypothesis holds; geometric applications must provide the cofinal family and
the corresponding evaluation isomorphisms.

This is the standard criterion for the base-change map to be an isomorphism:
Godement II.4.11; Bredon, *Sheaf Theory* II.10.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.Leray.FibreStalkEvaluation

open TopCat.FiniteClosedPushforward
open TopCat.Sheaf.OpenRestriction

variable {T X Y : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
  {F : AbelianSheaf X} {G : AbelianSheaf T} (κ : F ⟶ (pushforward i).obj G)
  (f : X ⟶ Y) (y : Y) (hfi : ∀ t : T, f (i t) = y)

/-- A cofinal supply of neighborhoods on which the literal cohomology evaluation is bijective
automatically discharges the filtered-colimit lift-and-kill criterion. -/
theorem canonicalDerivedStalkEvaluation_isIso_of_cofinal_bijectivePositive
    (I : InjectiveResolution F) (n : ℕ)
    (hlocal : ∀ (U : Opens Y) (_hy : y ∈ U),
      ∃ (V : Opens Y) (_hVU : V ≤ U) (hyV : y ∈ V),
        Function.Bijective
          (cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj V)
            (fibre_mem_preimage i f y hfi V hyV) (n + 1))) :
    IsIso (canonicalDerivedStalkEvaluationPositive
      i hi hfinite κ f y hfi I n) := by
  apply canonicalDerivedStalkEvaluation_isIso_of_local_lift_killPositive
    i hi hfinite κ f y hfi I n
  · intro b
    obtain ⟨V, _hVtop, hyV, hbij⟩ := hlocal ⊤ trivial
    obtain ⟨a, ha⟩ := hbij.surjective b
    exact ⟨V, hyV, a, ha⟩
  · intro U hy a ha
    obtain ⟨V, hVU, hyV, hbij⟩ := hlocal U hy
    refine ⟨V, hVU, hyV, ?_⟩
    change
      ((CategoryTheory.Sheaf.cohomologyPresheaf F (n + 1)).map
        ((Opens.map f).map (homOfLE hVU)).op) a = 0
    apply hbij.injective
    have hrestrict := cohomologyEvaluation_restrict i hi hfinite κ
      ((Opens.map f).map (homOfLE hVU))
      (fibre_mem_preimage i f y hfi V hyV)
      (fibre_mem_preimage i f y hfi U hy) (n + 1) a
    rw [hrestrict, ha]
    exact (map_zero
      (cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj V)
        (fibre_mem_preimage i f y hfi V hyV) (n + 1))).symm

namespace ConstantPointFibre

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y)
variable [T2Space X] [T1Space Y]

/-- Constant-coefficient specialization: a cofinal basis of neighborhoods whose Ext restriction
to the literal point fibre is bijective makes the canonical positive-degree stalk map an
isomorphism. -/
theorem canonicalStalkToFibrePositive_isIso_of_cofinal_bijective
    (A : AddCommGrpCat.{0})
    (I : InjectiveResolution (TopCat.ConstantSheaf.sheaf X A)) (n : ℕ)
    (hlocal : ∀ (U : Opens Y) (_hy : y ∈ U),
      ∃ (V : Opens Y) (_hVU : V ≤ U) (hyV : y ∈ V),
        Function.Bijective
          (cohomologyEvaluation (fibreInclusion f y)
            (fibreInclusion_isClosedMap f y) (fibreInclusion_finite_fibres f y)
            (TopCat.ConstantSheaf.pushforwardHom A (fibreInclusion f y))
            ((Opens.map f).obj V)
            (fibre_mem_preimage (fibreInclusion f y) f y
              (map_fibreInclusion f y) V hyV) (n + 1))) :
    IsIso (canonicalStalkToFibrePositive f y A I n) := by
  exact canonicalDerivedStalkEvaluation_isIso_of_cofinal_bijectivePositive
    (fibreInclusion f y) (fibreInclusion_isClosedMap f y)
    (fibreInclusion_finite_fibres f y)
    (TopCat.ConstantSheaf.pushforwardHom A (fibreInclusion f y))
    f y (map_fibreInclusion f y) I n hlocal

end ConstantPointFibre

end CategoryTheory.Sheaf.Leray.FibreStalkEvaluation
