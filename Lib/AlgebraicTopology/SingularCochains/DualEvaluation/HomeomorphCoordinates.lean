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

With the small coefficient group `ULift ℤ`, native singular cohomology pullback preserves
Kronecker coordinates whenever the chosen source and target homology markings commute with the
induced homology map.  The degree-one statements are kept alongside the positive-degree ones.

## References

* [A. Hatcher, *Algebraic topology*][hatcher2002], §3.1 (naturality of the Kronecker pairing,
  `⟨f^*φ, c⟩ = ⟨φ, f_* c⟩`).
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

universe w

/-- The lifted integral coefficient object used by the coordinate comparison. -/
abbrev A : AddCommGrpCat.{w} := AddCommGrpCat.of (ULift.{w} ℤ)

/-- Additive homomorphisms to lifted integers are canonically additive homomorphisms to
integers. -/
def uliftDownHomEquiv (H : Type*) [AddCommGroup H] :
    (H →+ ULift.{w} ℤ) ≃+ (H →+ ℤ) where
  toFun phi := AddEquiv.ulift.toAddMonoidHom.comp phi
  invFun psi := AddEquiv.ulift.symm.toAddMonoidHom.comp psi
  left_inv phi := by ext x; rfl
  right_inv psi := by ext x; rfl
  map_add' phi psi := by ext x; rfl

/-- Transport the Kronecker-evaluation target through integral-linear homology coordinates. -/
def evaluationTargetEquiv
    {H : Type*} {L : Type w} [AddCommGroup H] [AddCommGroup L] [Module ℤ H] [Module ℤ L]
    (e : H ≃ₗ[ℤ] L) :
    (H →+ ULift.{w} ℤ) ≃+ Module.Dual ℤ L :=
  (uliftDownHomEquiv H).trans
    ((addHomIntLinearEquiv H ℤ).trans e.dualMap.symm.toAddEquiv)

/-- Canonical `H¹` Kronecker evaluation, expressed in chosen integral-linear coordinates on
first homology. -/
def coordinateEvaluation
    (X : Type) (L : Type w) [TopologicalSpace X] [AddCommGroup L] [Module ℤ L]
    (e : (chains X).homology 1 ≃ₗ[ℤ] L) :
    (complex X A).homology 1 ⟶ AddCommGrpCat.of (Module.Dual ℤ L) :=
  cohomologyEvaluation A (chains X) 0 ≫
    AddCommGrpCat.ofHom (evaluationTargetEquiv e).toAddMonoidHom

/-- Pullback preserves Kronecker coordinates when the source and target homology markings commute
with the induced homology map. -/
theorem coordinateEvaluation_pullback
    {X Y : Type} {L : Type w} [TopologicalSpace X] [TopologicalSpace Y]
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

/-- Positive-degree Kronecker evaluation, expressed in chosen integral-linear coordinates on
homology in degree `q + 1`. -/
def coordinateEvaluationPositive
    (q : ℕ) (X : Type) (L : Type w) [TopologicalSpace X]
    [AddCommGroup L] [Module ℤ L]
    (e : (chains X).homology (q + 1) ≃ₗ[ℤ] L) :
    (complex X A).homology (q + 1) ⟶ AddCommGrpCat.of (Module.Dual ℤ L) :=
  cohomologyEvaluation A (chains X) q ≫
    AddCommGrpCat.ofHom (evaluationTargetEquiv e).toAddMonoidHom

/-- Pullback preserves positive-degree Kronecker coordinates when the chosen homology markings
commute with the induced homology map. -/
theorem coordinateEvaluationPositive_pullback
    (q : ℕ) {X Y : Type} {L : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup L] [Module ℤ L]
    (g : C(X, Y))
    (eX : (chains X).homology (q + 1) ≃ₗ[ℤ] L)
    (eY : (chains Y).homology (q + 1) ≃ₗ[ℤ] L)
    (hcoord : ∀ c : L,
      (HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)) (q + 1)).hom (eX.symm c) =
        eY.symm c) :
    HomologicalComplex.homologyMap (pullback A g) (q + 1) ≫
        coordinateEvaluationPositive q X L eX =
      coordinateEvaluationPositive q Y L eY := by
  let f : chains X ⟶ chains Y :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)
  have hnat := cohomologyEvaluation_natural A f q
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply LinearMap.ext
  intro c
  have happ := ConcreteCategory.congr_hom hnat a
  have happc := congrArg (fun phi ↦ phi (eX.symm c)) happ
  change cohomologyEvaluation A (chains X) q
      (HomologicalComplex.homologyMap (pullback A g) (q + 1) a) (eX.symm c) =
    cohomologyEvaluation A (chains Y) q a
      ((HomologicalComplex.homologyMap f (q + 1)).hom (eX.symm c)) at happc
  have hraw := happc.trans
    (congrArg (cohomologyEvaluation A (chains Y) q a) (hcoord c))
  change AddEquiv.ulift _ = AddEquiv.ulift _
  exact congrArg AddEquiv.ulift hraw

/-- Two pullbacks have the same positive-degree Kronecker coordinates when their induced
integral homology maps agree in the evaluated degree. -/
theorem pullback_comp_coordinateEvaluationPositive_eq_of_homologyMap_eq
    (q : ℕ) {X Y : Type} {L : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup L] [Module ℤ L]
    (f g : C(X, Y))
    (eX : (chains X).homology (q + 1) ≃ₗ[ℤ] L)
    (hmap :
      (HomologicalComplex.homologyMap
          (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) (q + 1)).hom =
        (HomologicalComplex.homologyMap
          (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)) (q + 1)).hom) :
    HomologicalComplex.homologyMap (pullback A f) (q + 1) ≫
        coordinateEvaluationPositive q X L eX =
      HomologicalComplex.homologyMap (pullback A g) (q + 1) ≫
        coordinateEvaluationPositive q X L eX := by
  let F : chains X ⟶ chains Y :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)
  let G : chains X ⟶ chains Y :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)
  have hnatF := cohomologyEvaluation_natural A F q
  have hnatG := cohomologyEvaluation_natural A G q
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply LinearMap.ext
  intro c
  have hF := ConcreteCategory.congr_hom hnatF a
  have hG := ConcreteCategory.congr_hom hnatG a
  have hFc := congrArg (fun phi ↦ phi (eX.symm c)) hF
  have hGc := congrArg (fun phi ↦ phi (eX.symm c)) hG
  change cohomologyEvaluation A (chains X) q
      (HomologicalComplex.homologyMap (pullback A f) (q + 1) a) (eX.symm c) =
    cohomologyEvaluation A (chains Y) q a
      ((HomologicalComplex.homologyMap F (q + 1)).hom (eX.symm c)) at hFc
  change cohomologyEvaluation A (chains X) q
      (HomologicalComplex.homologyMap (pullback A g) (q + 1) a) (eX.symm c) =
    cohomologyEvaluation A (chains Y) q a
      ((HomologicalComplex.homologyMap G (q + 1)).hom (eX.symm c)) at hGc
  have hfg :
      (HomologicalComplex.homologyMap F (q + 1)).hom (eX.symm c) =
        (HomologicalComplex.homologyMap G (q + 1)).hom (eX.symm c) := by
    exact LinearMap.congr_fun hmap (eX.symm c)
  have hraw := hFc.trans
    ((congrArg (cohomologyEvaluation A (chains Y) q a) hfg).trans hGc.symm)
  change AddEquiv.ulift _ = AddEquiv.ulift _
  exact congrArg AddEquiv.ulift hraw

end AlgebraicTopology.SingularCochains.DualEvaluation.HomeomorphCoordinates
