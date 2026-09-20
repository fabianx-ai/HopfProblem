/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.Stalk
public import Lib.Topology.Sheaves.ConstantPushforward

/-!
# Constant coefficients on the literal point fibre

This specialization uses the actual subtype fibre and Mathlib's native constant-sheaf
pushforward morphism. Its derived maps remain relative to the displayed resolution/Ext
normalization; no base-change bijectivity or replacement fibre is introduced.

The textbook statement being approached is the base-change comparison between the stalk of
`Rᵠf_*F` at `y` and the cohomology of the fibre `f⁻¹(y)`: Godement II.4.11.1;
Bredon, *Sheaf Theory* II.10; Iversen, *Cohomology of Sheaves* III.6.2.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.Leray.FibreStalkEvaluation

open TopCat.FiniteClosedPushforward
open TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{0}}

namespace ConstantPointFibre

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y)

/-- The literal point fibre, with its induced topology. -/
abbrev Fibre : Type := f ⁻¹' ({y} : Set Y)

/-- Inclusion of the literal point fibre into the total space. -/
def fibreInclusion : TopCat.of (Fibre f y) ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of the fibre `f⁻¹(y)` into `X` is injective. -/
theorem fibreInclusion_injective : Function.Injective (fibreInclusion f y) :=
  Subtype.val_injective

/-- For `T1` target the fibre `f⁻¹(y)` is closed, so its inclusion into `X` is a closed map. -/
theorem fibreInclusion_isClosedMap [T1Space Y] :
    IsClosedMap (fibreInclusion f y) := by
  change IsClosedMap (Subtype.val : (f ⁻¹' ({y} : Set Y)) → X)
  exact (isClosed_singleton.preimage f.hom.continuous).isClosedMap_subtype_val

/-- The inclusion of the fibre has finite (indeed at most singleton) point preimages. -/
theorem fibreInclusion_finite_fibres (x : X) :
    ((fibreInclusion f y) ⁻¹' ({x} : Set X)).Finite :=
  Set.Finite.preimage (fibreInclusion_injective f y).injOn (Set.finite_singleton x)

/-- Every point of the fibre `f⁻¹(y)` is sent to `y` by `f`. -/
@[simp]
theorem map_fibreInclusion (t : Fibre f y) : f (fibreInclusion f y t) = y :=
  t.property

variable [T2Space X] [T1Space Y]

/-- A displayed resolution/Ext normalization specialized to constant coefficients on a literal
point fibre. -/
abbrev ConstantNormalization (A : AddCommGrpCat.{0})
    (I : InjectiveResolution (TopCat.ConstantSheaf.sheaf X A)) (n : ℕ) :=
  ResolutionCohomologyNormalization f I n

/-- The constant-coefficient map relative to a displayed resolution/Ext normalization, from a
higher-direct-image stalk to native Ext cohomology of the literal point fibre.  No base-change
bijectivity is asserted. -/
def stalkToFibre (A : AddCommGrpCat.{0})
    (I : InjectiveResolution (TopCat.ConstantSheaf.sheaf X A)) (n : ℕ)
    (ρ : ConstantNormalization f A I n) :
    TopCat.Presheaf.stalk
        (higherDirectImageSheaf f (TopCat.ConstantSheaf.sheaf X A) n).obj y ⟶
      @AddCommGrpCat.of
        (CategoryTheory.Sheaf.H.{0}
          (TopCat.ConstantSheaf.sheaf (TopCat.of (Fibre f y)) A) n)
        (CategoryTheory.Sheaf.instAddCommGroupH
          (TopCat.ConstantSheaf.sheaf (TopCat.of (Fibre f y)) A) n) :=
  derivedStalkEvaluation (fibreInclusion f y)
    (fibreInclusion_isClosedMap f y) (fibreInclusion_finite_fibres f y)
    (TopCat.ConstantSheaf.pushforwardHom A (fibreInclusion f y))
    f y (map_fibreInclusion f y) I n ρ

/-- A class on an inverse-image neighborhood gives its literal derived-stalk germ. -/
def neighborhoodGerm (A : AddCommGrpCat.{0})
    (I : InjectiveResolution (TopCat.ConstantSheaf.sheaf X A)) (n : ℕ)
    (ρ : ConstantNormalization f A I n) (U : Opens Y) (hy : y ∈ U) :
    CategoryTheory.Sheaf.H'.{0} (TopCat.ConstantSheaf.sheaf X A) n
        ((Opens.map f).obj U) ⟶
      TopCat.Presheaf.stalk
        (higherDirectImageSheaf f (TopCat.ConstantSheaf.sheaf X A) n).obj y :=
  derivedNeighborhoodGerm f y I n ρ U hy

/-- On a neighborhood germ, `stalkToFibre` is exactly the native finite-closed-fibre Ext
restriction. -/
theorem stalkToFibre_neighborhoodGerm (A : AddCommGrpCat.{0})
    (I : InjectiveResolution (TopCat.ConstantSheaf.sheaf X A)) (n : ℕ)
    (ρ : ConstantNormalization f A I n) (U : Opens Y) (hy : y ∈ U) :
    neighborhoodGerm f y A I n ρ U hy ≫ stalkToFibre f y A I n ρ =
      @AddCommGrpCat.ofHom
        (CategoryTheory.Sheaf.H'.{0} (TopCat.ConstantSheaf.sheaf X A) n
          ((Opens.map f).obj U))
        (CategoryTheory.Sheaf.H.{0}
          (TopCat.ConstantSheaf.sheaf (TopCat.of (Fibre f y)) A) n)
        Ext.instAddCommGroup
        (CategoryTheory.Sheaf.instAddCommGroupH
          (TopCat.ConstantSheaf.sheaf (TopCat.of (Fibre f y)) A) n)
        (cohomologyEvaluation (fibreInclusion f y)
          (fibreInclusion_isClosedMap f y) (fibreInclusion_finite_fibres f y)
          (TopCat.ConstantSheaf.pushforwardHom A (fibreInclusion f y))
          ((Opens.map f).obj U)
          (fibre_mem_preimage (fibreInclusion f y) f y (map_fibreInclusion f y) U hy) n) :=
  derivedStalkEvaluation_germ (fibreInclusion f y)
    (fibreInclusion_isClosedMap f y) (fibreInclusion_finite_fibres f y)
    (TopCat.ConstantSheaf.pushforwardHom A (fibreInclusion f y))
    f y (map_fibreInclusion f y) I n ρ U hy

end ConstantPointFibre

end CategoryTheory.Sheaf.Leray.FibreStalkEvaluation
