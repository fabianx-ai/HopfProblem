/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularCochains.DualEvaluation.Free

/-!
# Kronecker coordinates and pullback

For the coefficient convention `ULift ℤ`, native singular `H¹` pullback preserves
Kronecker coordinates whenever the chosen source and target homology markings commute with the
induced homology map.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory
open AlgebraicTopology.SingularCochains
open AlgebraicTopology.SingularCochains.DualEvaluation
open AlgebraicTopology.SingularCochains.DualEvaluation.LocalUCT

namespace AlgebraicTopology.SingularCochains.DualEvaluation.HomeomorphCoordinates

/-- The lifted integral coefficient object used by the coordinate comparison. -/
abbrev A : AddCommGrpCat.{0} := AddCommGrpCat.of (ULift.{0} ℤ)

/-- Additive homomorphisms to lifted integers are canonically additive homomorphisms to
integers. -/
def uliftDownHomEquiv (H : Type) [AddCommGroup H] :
    (H →+ ULift.{0} ℤ) ≃+ (H →+ ℤ) where
  toFun phi := AddEquiv.ulift.toAddMonoidHom.comp phi
  invFun psi := AddEquiv.ulift.symm.toAddMonoidHom.comp psi
  left_inv phi := by ext x; rfl
  right_inv psi := by ext x; rfl
  map_add' phi psi := by ext x; rfl

/-- Transport the Kronecker-evaluation target through integral-linear homology coordinates. -/
def evaluationTargetEquiv
    {H L : Type} [AddCommGroup H] [AddCommGroup L] [Module ℤ H] [Module ℤ L]
    (e : H ≃ₗ[ℤ] L) :
    (H →+ ULift.{0} ℤ) ≃+ Module.Dual ℤ L :=
  (uliftDownHomEquiv H).trans
    ((addHomIntLinearEquiv H ℤ).trans e.dualMap.symm.toAddEquiv)

/-- Canonical `H¹` Kronecker evaluation, expressed in chosen integral-linear coordinates on
first homology. -/
def coordinateEvaluation
    (X L : Type) [TopologicalSpace X] [AddCommGroup L] [Module ℤ L]
    (e : (chains X).homology 1 ≃ₗ[ℤ] L) :
    (complex X A).homology 1 ⟶ AddCommGrpCat.of (Module.Dual ℤ L) :=
  cohomologyEvaluation A (chains X) 0 ≫
    AddCommGrpCat.ofHom (evaluationTargetEquiv e).toAddMonoidHom

/-- Pullback preserves Kronecker coordinates when the source and target homology markings commute
with the induced homology map. -/
theorem coordinateEvaluation_pullback
    {X Y L : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup L] [Module ℤ L]
    (g : C(X, Y))
    (eX : (chains X).homology 1 ≃ₗ[ℤ] L)
    (eY : (chains Y).homology 1 ≃ₗ[ℤ] L)
    (hcoord : ∀ c : L,
      (HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)) 1).hom (eX.symm c) = eY.symm c) :
    HomologicalComplex.homologyMap (pullback A g) 1 ≫
        coordinateEvaluation X L eX =
      coordinateEvaluation Y L eY := by
  let f : chains X ⟶ chains Y :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)
  have hnat := cohomologyEvaluation_natural A f 0
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply LinearMap.ext
  intro c
  have happ := ConcreteCategory.congr_hom hnat a
  have happc := congrArg (fun phi ↦ phi (eX.symm c)) happ
  change cohomologyEvaluation A (chains X) 0
      (HomologicalComplex.homologyMap (pullback A g) 1 a) (eX.symm c) =
    cohomologyEvaluation A (chains Y) 0 a
      ((HomologicalComplex.homologyMap f 1).hom (eX.symm c)) at happc
  have hraw := happc.trans
    (congrArg (cohomologyEvaluation A (chains Y) 0 a) (hcoord c))
  change AddEquiv.ulift _ = AddEquiv.ulift _
  exact congrArg AddEquiv.ulift hraw

end AlgebraicTopology.SingularCochains.DualEvaluation.HomeomorphCoordinates
