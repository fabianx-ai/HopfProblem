/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Sites.Leray.FibreStalkEvaluation.ConstantNormalization

/-!
# Consequences of constant finite-source normalization

This file records the direct equality between canonical finite-source evaluation of an ambient
open class and native constant-sheaf pullback of its intrinsic normalized class.  It has no
textbook counterpart: it is an identity between two maps defined in this library.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization

open CategoryTheory.Sheaf.Leray.FibreStalkEvaluation

variable {T X : TopCat.{u}} [T2Space T]
  (i : T ⟶ X) (U : Opens X) (hU : ∀ t : T, i t ∈ U)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' ({x} : Set X)).Finite)

/-- Canonical evaluation on a finite closed source is literally native constant-sheaf pullback
along the induced map to the open, after normalizing the ambient open class. -/
theorem canonicalConstantEvaluation_eq_intrinsicConstantPullback
    [LocallyConnectedSpace (TopCat.of U)]
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : CategoryTheory.Sheaf.H'.{u} (TopCat.ConstantSheaf.sheaf X A) n U) :
    canonicalConstantEvaluation i U hU hi hfinite A n x =
      intrinsicConstantPullback i U hU hi hfinite A n x := by
  let iU := induced i U hU
  let hiU := induced_isClosedMap i U hU hi
  let hfinU := induced_finite_fibres i U hU hfinite
  let cT := TopCat.ConstantSheaf.sheaf T A
  let aU := intrinsicOpenClass U A n x
  let e := canonicalConstantEvaluation i U hU hi hfinite A n x
  let p := TopCat.ConstantSheafCohomology.pullback iU hiU hfinU A n
  change e = p aU
  apply (TopCat.FiniteClosedPushforward.cohomologyForward_bijective
    iU hiU hfinU cT n).injective
  have heval := cohomologyEvaluation_forward_open i U hU hi hfinite A n x
  have hcoef := intrinsicOpenClass_coefficient i U hU A n x
  have hp := ConcreteCategory.congr_hom
    (TopCat.ConstantSheafCohomology.pullback_forward iU hiU hfinU A n) aU
  change TopCat.FiniteClosedPushforward.cohomologyForward
      iU hiU hfinU cT n e = _ at heval
  change _ = CategoryTheory.Sheaf.H.map
      (TopCat.ConstantSheaf.pushforwardHom A iU) n aU at hcoef
  change TopCat.FiniteClosedPushforward.cohomologyForward
      iU hiU hfinU cT n (p aU) =
    CategoryTheory.Sheaf.H.map
      (TopCat.ConstantSheaf.pushforwardHom A iU) n aU at hp
  exact heval.trans (hcoef.trans hp.symm)

end CategoryTheory.Sheaf.Leray.ConstantFibreEvaluationNormalization
