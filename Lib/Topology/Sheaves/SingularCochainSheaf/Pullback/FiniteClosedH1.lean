/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.ConstantCohomologyPullback
public import Lib.Topology.Sheaves.Cohomology.AcyclicResolutionH1Naturality
public import Lib.Topology.Sheaves.FiniteClosedPushforward.AcyclicResolutionH1
public import Lib.Topology.Sheaves.SingularCochainSheaf.Pullback.ComparisonH1

/-!
# Finite closed pullback and the H¹ singular-cochain resolution

For a finite closed map, native Ext pullback commutes with the H¹ comparison supplied by the
singular-cochain sheaf resolution.  Only the degree-zero cochain sheaf is required to be acyclic.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace TopCat.SingularCochainSheaf

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' ({y} : Set Y)).Finite)
  (A : AddCommGrpCat.{0})

/-- Pullback of singular cochains as a map from the target resolution to the exact pushforward
of the source resolution. -/
def resolutionH1Pullback
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    CategoryTheory.Abelian.Ext.AcyclicResolutionH1.Hom (resolutionH1 Y A hY)
      (TopCat.FiniteClosedPushforward.mapResolution f hf hfinite
        (resolutionH1 X A hX)) where
  augmentation := TopCat.ConstantSheaf.pushforwardHom A f
  complex :=
    { τ₁ := cochainPullback f A 0
      τ₂ := cochainPullback f A 1
      τ₃ := cochainPullback f A 2
      comm₁₂ := cochainPullback_d f A 0 1
      comm₂₃ := cochainPullback_d f A 1 2 }
  comm := (cochainPullback_augmentation f A).symm

/-- On global sections, the resolution map is the three-term window of literal sheafified
cochain pullback. -/
private theorem resolutionH1Pullback_globalMap
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    (TopCat.SheafH1.AcyclicResolutionH1.Hom.globalMap
      (resolutionH1Pullback f hf hfinite A hX hY)).τ₁ =
        (globalSheafPullback f A).f 0 ∧
    (TopCat.SheafH1.AcyclicResolutionH1.Hom.globalMap
      (resolutionH1Pullback f hf hfinite A hX hY)).τ₂ =
        (globalSheafPullback f A).f 1 ∧
    (TopCat.SheafH1.AcyclicResolutionH1.Hom.globalMap
      (resolutionH1Pullback f hf hfinite A hX hY)).τ₃ =
        (globalSheafPullback f A).f 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The three-term global-window map and the full global cochain pullback induce the same H¹ map
after the canonical window identifications. -/
theorem globalWindowH1Iso_pullback
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    ShortComplex.homologyMap
        (TopCat.SheafH1.AcyclicResolutionH1.Hom.globalMap
          (resolutionH1Pullback f hf hfinite A hX hY)) ≫
      (globalWindowH1Iso X A).inv =
    (globalWindowH1Iso Y A).inv ≫
      HomologicalComplex.homologyMap (globalSheafPullback f A) 1 := by
  let e := HomologicalComplex.homologyFunctorIso' AddCommGrpCat.{0}
    (ComplexShape.up ℕ) 0 1 2 ((ComplexShape.up ℕ).prev_eq' (by rfl))
      ((ComplexShape.up ℕ).next_eq' (by rfl))
  have hn := e.hom.naturality (globalSheafPullback f A)
  have hshort :
      ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{0} (ComplexShape.up ℕ)
          0 1 2 ⋙ ShortComplex.homologyFunctor AddCommGrpCat.{0}).map
          (globalSheafPullback f A)) =
        ShortComplex.homologyMap
          (TopCat.SheafH1.AcyclicResolutionH1.Hom.globalMap
            (resolutionH1Pullback f hf hfinite A hX hY)) := by
    rfl
  rw [← hshort]
  change ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{0} (ComplexShape.up ℕ)
        0 1 2 ⋙ ShortComplex.homologyFunctor AddCommGrpCat.{0}).map
        (globalSheafPullback f A)) ≫
      (e.app (globalCochainComplex X A)).inv =
    (e.app (globalCochainComplex Y A)).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{0}
        (ComplexShape.up ℕ) 1).map (globalSheafPullback f A)
  apply (cancel_mono (e.hom.app (globalCochainComplex X A))).mp
  calc
    (_ ≫ (e.app (globalCochainComplex X A)).inv) ≫
        (e.app (globalCochainComplex X A)).hom =
      _ ≫ ((e.app (globalCochainComplex X A)).inv ≫
        (e.app (globalCochainComplex X A)).hom) := Category.assoc _ _ _
    _ = _ := by rw [Iso.inv_hom_id, Category.comp_id]
    _ = (e.app (globalCochainComplex Y A)).inv ≫
        ((e.app (globalCochainComplex Y A)).hom ≫ _) := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (e.app (globalCochainComplex Y A)).inv ≫
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{0}
            (ComplexShape.up ℕ) 1).map (globalSheafPullback f A) ≫
          (e.app (globalCochainComplex X A)).hom) :=
      congrArg (fun k => (e.app (globalCochainComplex Y A)).inv ≫ k) hn.symm
    _ = ((e.app (globalCochainComplex Y A)).inv ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{0}
          (ComplexShape.up ℕ) 1).map (globalSheafPullback f A)) ≫
          (e.app (globalCochainComplex X A)).hom := (Category.assoc _ _ _).symm

private theorem compose_squares {C : Type*} [Category C]
    {H K K' L L' M : C} (a : H ⟶ K) (b : K ⟶ L)
    (c : H ⟶ K') (d : K' ⟶ L) (e : L ⟶ M)
    (f : K' ⟶ L') (g : L' ⟶ M)
    (hab : a ≫ b = c ≫ d) (hde : d ≫ e = f ≫ g) :
    a ≫ (b ≫ e) = c ≫ (f ≫ g) := by
  rw [← Category.assoc, hab, Category.assoc, hde]

private theorem reassoc_eq {C : Type*} [Category C]
    {H K L M : C} (a : H ⟶ K) (b : K ⟶ L) (c : H ⟶ L)
    (d : L ⟶ M) (h : a ≫ b = c) : a ≫ (b ≫ d) = c ≫ d := by
  rw [← Category.assoc, h]

set_option maxHeartbeats 1000000 in
/-- Native finite-closed Ext pullback commutes with the actual resolution-to-global-cochain H¹
comparison. -/
theorem h1_global_naturality
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    TopCat.ConstantSheafCohomology.pullback f hf hfinite A 1 ≫
      (constantSheafGlobalH1Iso X A hX).hom =
    (constantSheafGlobalH1Iso Y A hY).hom ≫
      HomologicalComplex.homologyMap (globalSheafPullback f A) 1 := by
  let R := resolutionH1 X A hX
  let S := resolutionH1 Y A hY
  let P := TopCat.FiniteClosedPushforward.mapResolution f hf hfinite R
  let phi := resolutionH1Pullback f hf hfinite A hX hY
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1) :=
    zeroCochainSheaf_h1_subsingleton X A
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1) :=
    zeroCochainSheaf_h1_subsingleton Y A
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} P.complex.X₁ 1) :=
    TopCat.FiniteClosedPushforward.mapResolution_h1_subsingleton f hf hfinite R
  have hresolution := TopCat.SheafH1.AcyclicResolutionH1.Hom.h1GlobalIso_naturality phi
  have hwindow := globalWindowH1Iso_pullback f hf hfinite A hX hY
  have hnat :
      (CategoryTheory.Sheaf.functorH _ 1).map
          (TopCat.ConstantSheaf.pushforwardHom A f) ≫
        (TopCat.FiniteClosedPushforward.pushedH1GlobalIso f hf hfinite R).hom ≫
          (globalWindowH1Iso X A).inv =
      (constantSheafGlobalH1Iso Y A hY).hom ≫
        HomologicalComplex.homologyMap (globalSheafPullback f A) 1 := by
    change (CategoryTheory.Sheaf.functorH _ 1).map phi.augmentation ≫
        ((TopCat.SheafH1.AcyclicResolutionH1.h1GlobalIso P).hom ≫
          (globalWindowH1Iso X A).inv) = _
    have hsquare := compose_squares
      ((CategoryTheory.Sheaf.functorH _ 1).map phi.augmentation)
      (TopCat.SheafH1.AcyclicResolutionH1.h1GlobalIso P).hom
      (TopCat.SheafH1.AcyclicResolutionH1.h1GlobalIso S).hom
      (ShortComplex.homologyMap
        (TopCat.SheafH1.AcyclicResolutionH1.Hom.globalMap phi))
      (globalWindowH1Iso X A).inv (globalWindowH1Iso Y A).inv
      (HomologicalComplex.homologyMap (globalSheafPullback f A) 1)
      hresolution hwindow
    exact hsquare
  have hq := TopCat.FiniteClosedPushforward.h1Global_forward f hf hfinite R
  have hqglobal :
      AddCommGrpCat.ofHom
          (TopCat.FiniteClosedPushforward.cohomologyForward f hf hfinite R.F 1) ≫
        ((TopCat.FiniteClosedPushforward.pushedH1GlobalIso f hf hfinite R).hom ≫
          (globalWindowH1Iso X A).inv) =
      (constantSheafGlobalH1Iso X A hX).hom := by
    exact reassoc_eq _ _ _ _ hq
  have hpq := TopCat.ConstantSheafCohomology.pullback_forward f hf hfinite A 1
  exact (congrArg (fun k =>
    TopCat.ConstantSheafCohomology.pullback f hf hfinite A 1 ≫ k) hqglobal.symm).trans
      ((reassoc_eq
        (TopCat.ConstantSheafCohomology.pullback f hf hfinite A 1)
        (AddCommGrpCat.ofHom
          (TopCat.FiniteClosedPushforward.cohomologyForward f hf hfinite R.F 1))
        ((CategoryTheory.Sheaf.functorH _ 1).map
          (TopCat.ConstantSheaf.pushforwardHom A f))
        ((TopCat.FiniteClosedPushforward.pushedH1GlobalIso f hf hfinite R).hom ≫
          (globalWindowH1Iso X A).inv) hpq).trans hnat)

/-- Consequently native finite-closed Ext pullback commutes with the canonical singular H¹
comparison whenever the global sheafification-unit map is an isomorphism on H¹. -/
theorem h1Comparison_naturality
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y)
    [IsIso (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)]
    [IsIso (HomologicalComplex.homologyMap (globalCochainComparison Y A) 1)] :
    TopCat.ConstantSheafCohomology.pullback f hf hfinite A 1 ≫
      (h1Comparison X A hX).hom =
    (h1Comparison Y A hY).hom ≫
      HomologicalComplex.homologyMap
        (AlgebraicTopology.SingularCochains.pullback A f.hom) 1 :=
  h1Comparison_naturality_of_global f A hX hY
    (TopCat.ConstantSheafCohomology.pullback f hf hfinite A 1)
    (h1_global_naturality f hf hfinite A hX hY)

end TopCat.SingularCochainSheaf
