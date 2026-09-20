/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.ConstantNormalizationConsequences

/-!
# Bijectivity of normalized finite-source evaluation

Canonical evaluation of constant-coefficient cohomology on an ambient open factors through two
maps: normalization to intrinsic cohomology of the open subspace, followed by native pullback to
the finite closed source.  The normalization is always bijective.  Hence evaluation is bijective
whenever the intrinsic pullback is an isomorphism.

Restriction of constant-sheaf cohomology to a subspace: Bredon, *Sheaf Theory* II.9–II.10.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory TopologicalSpace

namespace CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization

open CategoryTheory.Sheaf.Leray.FibreStalkEvaluation

/-- Normalizing an ambient open-cohomology class to intrinsic constant-sheaf cohomology of the
open subspace is bijective in every degree. -/
theorem intrinsicOpenClass_bijective {X : TopCat.{0}} (U : Opens X)
    [LocallyConnectedSpace (TopCat.of U)] (A : AddCommGrpCat.{0}) (n : ℕ) :
    Function.Bijective (intrinsicOpenClass U A n) := by
  letI : IsIso (openConstantRestrictionHom U A) :=
    openConstantRestrictionHom_isIso U A
  let qIso := ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology (TopCat.of U)) n).mapIso
      (@asIso _ _ _ _ (openConstantRestrictionHom U A)
        (openConstantRestrictionHom_isIso U A))).symm
  have hq : Function.Bijective qIso.hom :=
    ConcreteCategory.bijective_of_isIso qIso.hom
  have hc : Function.Bijective
      (TopCat.Sheaf.OpenRestriction.cohomologyEquiv U
        (TopCat.ConstantSheaf.sheaf X A) n) :=
    (TopCat.Sheaf.OpenRestriction.cohomologyEquiv U
      (TopCat.ConstantSheaf.sheaf X A) n).bijective
  have hfun : intrinsicOpenClass U A n =
      fun x => qIso.hom
        (TopCat.Sheaf.OpenRestriction.cohomologyEquiv U
          (TopCat.ConstantSheaf.sheaf X A) n x) := by
    rfl
  rw [hfun]
  exact hq.comp hc

/-- If native constant-sheaf pullback along the induced map from a finite closed source to an
open subspace is an isomorphism, then canonical evaluation of ambient open-cohomology classes on
that source is bijective. -/
theorem canonicalConstantEvaluation_bijective_of_pullback_isIso
    {T X : TopCat.{0}} [T2Space T]
    (i : T ⟶ X) (U : Opens X) (hU : ∀ t : T, i t ∈ U)
    (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)
    [LocallyConnectedSpace (TopCat.of U)]
    (A : AddCommGrpCat.{0}) (n : ℕ)
    [IsIso (TopCat.ConstantSheafCohomology.pullback (induced i U hU)
      (induced_isClosedMap i U hU hi)
      (induced_finite_fibres i U hU hfinite) A n)] :
    Function.Bijective (canonicalConstantEvaluation i U hU hi hfinite A n) := by
  let p := TopCat.ConstantSheafCohomology.pullback (induced i U hU)
    (induced_isClosedMap i U hU hi)
    (induced_finite_fibres i U hU hfinite) A n
  have hp : Function.Bijective p := ConcreteCategory.bijective_of_isIso p
  have hc := intrinsicOpenClass_bijective U A n
  have hfun : canonicalConstantEvaluation i U hU hi hfinite A n =
      fun x => p (intrinsicOpenClass U A n x) := by
    funext x
    exact canonicalConstantEvaluation_eq_intrinsicConstantPullback
      i U hU hi hfinite A n x
  rw [hfun]
  exact hp.comp hc

end CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization
