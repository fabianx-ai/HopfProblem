/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.ConstantPointFibre
public import Lib.CategoryTheory.Sites.Leray.ResolutionCohomologyPresheaf

/-!
# Positive-degree resolution-normalized fibre-stalk evaluation

The positive-degree natural isomorphism between pushed-resolution homology and Mathlib's
Ext-defined cohomology presheaf supplies the displayed normalization expected by the low-level
fibre-stalk API. The convenience maps here remain relative to the chosen injective resolution and
to the displayed geometric and coefficient data. They do not assert proper base change.

The textbook statement being approached is the comparison between the stalk of `Rᵠf_*F` at `y`
and the cohomology of the fibre: Godement II.4.11.1; Bredon, *Sheaf Theory* II.10;
Iversen, *Cohomology of Sheaves* III.6.2.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace CategoryTheory.Sheaf.Leray.FibreStalkEvaluation

open TopCat.FiniteClosedPushforward
open TopCat.Sheaf.OpenRestriction

section Positive

variable {T X Y : TopCat.{u}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
  {F : AbelianSheaf X} {G : AbelianSheaf T} (κ : F ⟶ (pushforward i).obj G)
  (f : X ⟶ Y) (y : Y) (hfi : ∀ t : T, f (i t) = y)

/-- The proved positive-degree presheaf isomorphism, in the exact normalization type expected by
the low-level fibre-stalk API. This is relative to the displayed injective resolution. -/
abbrev canonicalResolutionCohomologyNormalizationPositive
    (I : InjectiveResolution F) (n : ℕ) :
    ResolutionCohomologyNormalization (F := F) f I (n + 1) :=
  pushedResolutionCohomologyPresheafIsoPositive f I n

/-- The higher-direct-image stalk comparison in positive degree with the proved presheaf
normalization supplied. -/
def canonicalDerivedStalkIsoPositive (I : InjectiveResolution F) (n : ℕ) :
    TopCat.Presheaf.stalk (higherDirectImageSheaf f F (n + 1)).obj y ≅
      TopCat.Presheaf.stalk (sourceCohomologyPresheaf (F := F) f (n + 1)) y :=
  derivedStalkIso (F := F) f y I (n + 1)
    (canonicalResolutionCohomologyNormalizationPositive f I n)

/-- Positive-degree derived-stalk evaluation with the proved presheaf normalization supplied. -/
def canonicalDerivedStalkEvaluationPositive (I : InjectiveResolution F) (n : ℕ) :
    TopCat.Presheaf.stalk (higherDirectImageSheaf f F (n + 1)).obj y ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} G (n + 1)) :=
  derivedStalkEvaluation i hi hfinite κ f y hfi I (n + 1)
    (canonicalResolutionCohomologyNormalizationPositive f I n)

/-- A positive-degree Ext neighborhood class as a germ in the derived stalk, using the proved
presheaf normalization. -/
def canonicalDerivedNeighborhoodGermPositive (I : InjectiveResolution F) (n : ℕ)
    (U : Opens Y) (hy : y ∈ U) :
    CategoryTheory.Sheaf.H'.{u} F (n + 1) ((Opens.map f).obj U) ⟶
      TopCat.Presheaf.stalk (higherDirectImageSheaf f F (n + 1)).obj y :=
  derivedNeighborhoodGerm f y I (n + 1)
    (canonicalResolutionCohomologyNormalizationPositive f I n) U hy

/-- The positive-degree normalized derived evaluation retains the literal neighborhood
finite-closed restriction formula. -/
theorem canonicalDerivedStalkEvaluation_germPositive
    (I : InjectiveResolution F) (n : ℕ) (U : Opens Y) (hy : y ∈ U) :
    canonicalDerivedNeighborhoodGermPositive (F := F) f y I n U hy ≫
      canonicalDerivedStalkEvaluationPositive i hi hfinite κ f y hfi I n =
        AddCommGrpCat.ofHom
          (cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
            (fibre_mem_preimage i f y hfi U hy) (n + 1)) :=
  derivedStalkEvaluation_germ i hi hfinite κ f y hfi I (n + 1)
    (canonicalResolutionCohomologyNormalizationPositive f I n) U hy

/-- In positive degree, the local lift-and-kill hypotheses make the normalized
higher-direct-image stalk evaluation an isomorphism. -/
theorem canonicalDerivedStalkEvaluation_isIso_of_local_lift_killPositive
    (I : InjectiveResolution F) (n : ℕ)
    (hlift : ∀ b : CategoryTheory.Sheaf.H.{u} G (n + 1),
      ∃ (U : Opens Y) (hy : y ∈ U)
        (a : CategoryTheory.Sheaf.H'.{u} F (n + 1) ((Opens.map f).obj U)),
        cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
          (fibre_mem_preimage i f y hfi U hy) (n + 1) a = b)
    (hkill : ∀ (U : Opens Y) (hy : y ∈ U)
        (a : CategoryTheory.Sheaf.H'.{u} F (n + 1) ((Opens.map f).obj U)),
      cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
          (fibre_mem_preimage i f y hfi U hy) (n + 1) a = 0 →
        ∃ (V : Opens Y) (hVU : V ≤ U) (_hyV : y ∈ V),
          (sourceCohomologyPresheaf (F := F) f (n + 1)).map (homOfLE hVU).op a = 0) :
    IsIso (canonicalDerivedStalkEvaluationPositive
      i hi hfinite κ f y hfi I n) :=
  derivedStalkEvaluation_isIso_of_local_lift_kill
    i hi hfinite κ f y hfi I (n + 1)
      (canonicalResolutionCohomologyNormalizationPositive f I n) hlift hkill

end Positive

namespace ConstantPointFibre

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
variable [T2Space X] [T1Space Y]

/-- Constant-coefficient evaluation on the literal point fibre in positive degree, with the
proved presheaf normalization supplied. -/
def canonicalStalkToFibrePositive (A : AddCommGrpCat.{u})
    (I : InjectiveResolution (TopCat.ConstantSheaf.sheaf X A)) (n : ℕ) :=
  stalkToFibre f y A I (n + 1)
    (canonicalResolutionCohomologyNormalizationPositive f I n)

/-- The positive-degree neighborhood germ used by the normalized literal-fibre map. -/
def canonicalNeighborhoodGermPositive (A : AddCommGrpCat.{u})
    (I : InjectiveResolution (TopCat.ConstantSheaf.sheaf X A)) (n : ℕ)
    (U : Opens Y) (hy : y ∈ U) :=
  neighborhoodGerm f y A I (n + 1)
    (canonicalResolutionCohomologyNormalizationPositive f I n) U hy

/-- On a positive-degree neighborhood germ, the normalized literal-fibre map is exactly the
native finite-closed-fibre Ext restriction. -/
theorem canonicalStalkToFibre_neighborhoodGermPositive
    (A : AddCommGrpCat.{u})
    (I : InjectiveResolution (TopCat.ConstantSheaf.sheaf X A)) (n : ℕ)
    (U : Opens Y) (hy : y ∈ U) :
    canonicalNeighborhoodGermPositive f y A I n U hy ≫
      canonicalStalkToFibrePositive f y A I n =
        @AddCommGrpCat.ofHom
          (CategoryTheory.Sheaf.H'.{u} (TopCat.ConstantSheaf.sheaf X A) (n + 1)
            ((Opens.map f).obj U))
          (CategoryTheory.Sheaf.H.{u}
            (TopCat.ConstantSheaf.sheaf (TopCat.of (Fibre f y)) A) (n + 1))
          Ext.instAddCommGroup
          (CategoryTheory.Sheaf.cohomologyAddCommGroup
            (TopCat.ConstantSheaf.sheaf (TopCat.of (Fibre f y)) A) (n + 1))
          (cohomologyEvaluation (fibreInclusion f y)
            (fibreInclusion_isClosedMap f y) (fibreInclusion_finite_fibres f y)
            (TopCat.ConstantSheaf.pushforwardHom A (fibreInclusion f y))
            ((Opens.map f).obj U)
            (fibre_mem_preimage (fibreInclusion f y) f y
              (map_fibreInclusion f y) U hy) (n + 1)) :=
  stalkToFibre_neighborhoodGerm f y A I (n + 1)
    (canonicalResolutionCohomologyNormalizationPositive f I n) U hy

end ConstantPointFibre

end CategoryTheory.Sheaf.Leray.FibreStalkEvaluation
