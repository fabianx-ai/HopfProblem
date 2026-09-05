/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularCochains.DualEvaluation.CoefficientNormalization
public import Lib.AlgebraicTopology.SingularCochains.PositivePrimitives

/-!
# Vanishing criteria for native singular cohomology

This FREE owner packages two standard transports of cohomological vanishing.  A homotopy
equivalence transports vanishing in either direction, while the integral local universal
coefficient theorem turns vanishing of two adjacent homology groups into vanishing of the
corresponding positive-degree cohomology group.

The statements are coefficient-generic where homotopy invariance is enough.  The universal
coefficient statements use the repository's coefficient convention `ULift ℤ`.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped ContinuousMap

namespace AlgebraicTopology.SingularCochains

/-- Vanishing of native singular cohomology transports backwards across a homotopy
equivalence. -/
theorem cohomology_subsingleton_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{0}) (e : X ≃ₕ Y) (n : ℕ)
    (hY : Subsingleton ((complex Y A).homology n)) :
    Subsingleton ((complex X A).homology n) := by
  let _ : Subsingleton ((complex Y A).homology n) := hY
  let E := homotopyEquivCohomologyIso A e n
  exact ((ConcreteCategory.isIso_iff_bijective E.inv).mp (by infer_instance)).1.subsingleton

/-- Native singular cohomology vanishes on one side of a homotopy equivalence exactly when it
vanishes on the other. -/
theorem cohomology_subsingleton_iff_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{0}) (e : X ≃ₕ Y) (n : ℕ) :
    Subsingleton ((complex X A).homology n) ↔
      Subsingleton ((complex Y A).homology n) := by
  constructor
  · exact cohomology_subsingleton_of_homotopyEquiv A e.symm n
  · exact cohomology_subsingleton_of_homotopyEquiv A e n

/-- Native singular cohomology vanishing is invariant under homeomorphism. -/
theorem cohomology_subsingleton_iff_of_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{0}) (e : X ≃ₜ Y) (n : ℕ) :
    Subsingleton ((complex X A).homology n) ↔
      Subsingleton ((complex Y A).homology n) :=
  cohomology_subsingleton_iff_of_homotopyEquiv A e.toHomotopyEquiv n

/-- Native singular cohomology of a point vanishes in every positive degree, for arbitrary
small abelian coefficients. -/
theorem pointCohomology_subsingleton (A : AddCommGrpCat.{0}) (n : ℕ) (hn : n ≠ 0) :
    Subsingleton ((complex Unit A).homology n) :=
  AddCommGrpCat.subsingleton_of_isZero
    (pointCochain_exactAt_positive A n hn).isZero_homology

/-- Native singular cohomology of a contractible space vanishes in every positive degree, for
arbitrary small abelian coefficients. -/
theorem contractibleCohomology_subsingleton
    (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (A : AddCommGrpCat.{0}) (n : ℕ) (hn : n ≠ 0) :
    Subsingleton ((complex X A).homology n) :=
  cohomology_subsingleton_of_homotopyEquiv A
    (Classical.choice (ContractibleSpace.hequiv_unit X)) n
    (pointCohomology_subsingleton A n hn)

open DualEvaluation.LocalUCT

/-- If degree-`n` integral homology is projective and degree-`n+1` integral homology vanishes,
then degree-`n+1` cohomology with the repository's `ULift ℤ` coefficients vanishes. -/
theorem uliftIntCohomology_subsingleton_of_projective_of_homology
    (X : Type) [TopologicalSpace X] (n : ℕ)
    [Module.Projective ℤ ((chains X).homology n)]
    (hnext : Subsingleton ((chains X).homology (n + 1))) :
    Subsingleton
      ((complex X (AddCommGrpCat.of (ULift.{0} ℤ))).homology (n + 1)) := by
  let _ : Subsingleton ((chains X).homology (n + 1)) := hnext
  let f := uliftIntCohomologyEvaluation (chains X) n
  let _ : IsIso f := singularUliftIntCohomologyEvaluation_isIso_of_projective X n
  exact ((ConcreteCategory.isIso_iff_bijective f).mp (by infer_instance)).1.subsingleton

/-- Vanishing of two adjacent integral homology groups forces vanishing of positive-degree
integral cohomology.  The lower homology group is projective because a subsingleton module is
free. -/
theorem uliftIntCohomology_subsingleton_of_adjacent_homology
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (hprev : Subsingleton ((chains X).homology n))
    (hnext : Subsingleton ((chains X).homology (n + 1))) :
    Subsingleton
      ((complex X (AddCommGrpCat.of (ULift.{0} ℤ))).homology (n + 1)) := by
  let _ : Subsingleton ((chains X).homology n) := hprev
  let _ : Module.Free ℤ ((chains X).homology n) :=
    Module.Free.of_subsingleton ℤ ((chains X).homology n)
  let _ : Module.Projective ℤ ((chains X).homology n) := Module.Projective.of_free
  exact uliftIntCohomology_subsingleton_of_projective_of_homology X n hnext

end AlgebraicTopology.SingularCochains
