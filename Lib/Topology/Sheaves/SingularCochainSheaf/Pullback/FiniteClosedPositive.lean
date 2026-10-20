/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.ConstantCohomologyPullback
public import Lib.Topology.Sheaves.FiniteClosedPushforward.AcyclicResolution
public import Lib.Topology.Sheaves.SingularCochainSheaf.ComparisonPositive

/-!
# Naturality of the singular–sheaf comparison for finite closed maps

For a closed map with finite fibres, pullback on constant-sheaf cohomology commutes in every
positive degree with the comparison `H^{n}(X; A_X) ≅ H^{n}_sing(X; A)` (Bredon, *Sheaf Theory*
III.1; Warner, *Foundations of Differentiable Manifolds and Lie Groups* 5.32).  The proof uses
the cycle objects of the singular-cochain resolution and exactness of pushforward along such a
map.

## Main results

* `TopCat.SingularCochainSheaf.constantSheafCohomologyIsoSingular_naturality`
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' ({y} : Set Y)).Finite)
  (A : AddCommGrpCat.{0})

/-- Pullback on the degree-`n+1` cycle object of the resolution, followed by the inverse of the
kernel comparison for pushforward along a closed map with finite fibres. -/
def resolutionCyclePullback
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) (n : ℕ) :
    (resolution Y A hY).Z (n + 1) ⟶
      (TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
        (resolution X A hX)).Z (n + 1) := by
  let _ := (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
    f hf hfinite).1
  let _ := TopCat.FiniteClosedPushforward.pushforward_preservesFiniteColimits
    f hf hfinite
  let G := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
  exact
    kernel.map
        (sheafDifferential Y A (n + 1) (n + 2))
        (G.map (sheafDifferential X A (n + 1) (n + 2)))
        (cochainPullback f A (n + 1)) (cochainPullback f A (n + 2))
        (cochainPullback_d f A (n + 1) (n + 2)).symm ≫
      (PreservesKernel.iso G (sheafDifferential X A (n + 1) (n + 2))).inv

set_option backward.isDefEq.respectTransparency false in
/-- The pullback on cycle objects is compatible with their inclusions into the terms of the
resolution. -/
@[reassoc]
theorem resolutionCyclePullback_i
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) (n : ℕ) :
    resolutionCyclePullback f hf hfinite A hX hY n ≫
        (TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
          (resolution X A hX)).i (n + 1) =
      (resolution Y A hY).i (n + 1) ≫ cochainPullback f A (n + 1) := by
  let _ := (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
    f hf hfinite).1
  dsimp only [resolutionCyclePullback, TopCat.FiniteClosedPushforward.mapIndexedResolution,
    CategoryTheory.Abelian.Ext.AcyclicResolution.map_i, resolution,
    exactAugmentedComplex,
    CategoryTheory.Abelian.Ext.ExactAugmentedCochainComplex.toAcyclicResolution,
    CategoryTheory.Abelian.Ext.ExactAugmentedCochainComplex.i,
    CategoryTheory.Abelian.Ext.ExactAugmentedCochainComplex.Z]
  simp only [complexSheaf_d]
  rw [Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of sheafified singular cochains as a map from the resolution on `Y` to the
pushforward of the resolution on `X`. -/
def resolutionPullback
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    CategoryTheory.Abelian.Ext.AcyclicResolution.Hom (resolution Y A hY)
      (TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
        (resolution X A hX)) := by
  let _ := (TopCat.FiniteClosedPushforward.pushforward_preservesFiniteLimitsAndColimits
    f hf hfinite).1
  let _ := TopCat.FiniteClosedPushforward.pushforward_preservesFiniteColimits
    f hf hfinite
  refine
    { z := fun n ↦ match n with
        | 0 => TopCat.ConstantSheaf.pushforwardHom A f
        | n + 1 => resolutionCyclePullback f hf hfinite A hX hY n
      x := fun n ↦ cochainPullback f A n
      comm_i := ?_
      comm_p := ?_ }
  · intro n
    cases n with
    | zero => exact (cochainPullback_augmentation f A).symm
    | succ n => exact resolutionCyclePullback_i f hf hfinite A hX hY n
  · intro n
    let _ : Mono
        ((TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
          (resolution X A hX)).i (n + 1)) :=
      (TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
        (resolution X A hX)).shortExact (n + 1) |>.mono_f
    apply (cancel_mono
      ((TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
        (resolution X A hX)).i (n + 1))).mp
    calc
      (cochainPullback f A n ≫
          (TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
            (resolution X A hX)).p n) ≫
          (TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
            (resolution X A hX)).i (n + 1) =
        cochainPullback f A n ≫
          (TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
            (resolution X A hX)).d n := by
            exact Category.assoc _ _ _
      _ = (resolution Y A hY).d n ≫ cochainPullback f A (n + 1) := by
        rw [TopCat.FiniteClosedPushforward.mapIndexedResolution_d,
          resolution_d, resolution_d]
        exact cochainPullback_d f A n (n + 1)
      _ = ((resolution Y A hY).p n ≫
          resolutionCyclePullback f hf hfinite A hX hY n) ≫
          (TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
            (resolution X A hX)).i (n + 1) := by
        calc
          (resolution Y A hY).d n ≫ cochainPullback f A (n + 1) =
              ((resolution Y A hY).p n ≫ (resolution Y A hY).i (n + 1)) ≫
                cochainPullback f A (n + 1) := rfl
          _ = (resolution Y A hY).p n ≫
                ((resolution Y A hY).i (n + 1) ≫
                  cochainPullback f A (n + 1)) := Category.assoc _ _ _
          _ = (resolution Y A hY).p n ≫
                (resolutionCyclePullback f hf hfinite A hX hY n ≫
                  (TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
                    (resolution X A hX)).i (n + 1)) :=
              congrArg (fun k ↦ (resolution Y A hY).p n ≫ k)
                (resolutionCyclePullback_i f hf hfinite A hX hY n).symm
          _ = ((resolution Y A hY).p n ≫
                resolutionCyclePullback f hf hfinite A hX hY n) ≫
                  (TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite
                    (resolution X A hX)).i (n + 1) :=
              (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- On global sections, the map of resolutions is the pullback of sheafified singular cochains,
under the canonical identification of both resolution complexes. -/
theorem resolutionPullback_globalComplex
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    (TopCat.SheafCohomology.AcyclicResolution.Hom.globalComplexMap
        (resolutionPullback f hf hfinite A hX hY) ≫
      (TopCat.FiniteClosedPushforward.indexedGlobalComplexIso f hf hfinite
        (resolution X A hX)).hom) ≫
        (resolutionGlobalComplexIso X A hX).hom =
      (resolutionGlobalComplexIso Y A hY).hom ≫ globalSheafPullback f A := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

private theorem compose_squares {C : Type*} [Category C]
    {H K K' L L' M : C} (a : H ⟶ K) (b : K ⟶ L)
    (c : H ⟶ K') (d : K' ⟶ L) (e : L ⟶ M)
    (q : K' ⟶ L') (r : L' ⟶ M)
    (hab : a ≫ b = c ≫ d) (hde : d ≫ e = q ≫ r) :
    a ≫ (b ≫ e) = c ≫ (q ≫ r) := by
  rw [← Category.assoc, hab, Category.assoc, hde]

private theorem reassoc_eq {C : Type*} [Category C]
    {H K L M : C} (a : H ⟶ K) (b : K ⟶ L) (c : H ⟶ L)
    (d : L ⟶ M) (h : a ≫ b = c) : a ≫ (b ≫ d) = c ≫ d := by
  rw [← Category.assoc, h]

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback on constant-sheaf cohomology along a closed map with finite fibres commutes, in
every positive degree, with the identification of `H^•(·; A_·)` with the cohomology of
`Γ(·, 𝒮^•)`. -/
theorem constantSheafGlobalIso_naturality
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y)
    [MetrizableSpace X] [MetrizableSpace Y] (n : ℕ) :
    TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1) ≫
        (constantSheafGlobalIso X A hX n).hom =
      (constantSheafGlobalIso Y A hY n).hom ≫
        HomologicalComplex.homologyMap (globalSheafPullback f A) (n + 1) := by
  let R := resolution X A hX
  let S := resolution Y A hY
  let P := TopCat.FiniteClosedPushforward.mapIndexedResolution f hf hfinite R
  let phi := resolutionPullback f hf hfinite A hX hY
  let hR := resolution_isAcyclic X A hX
  let hS := resolution_isAcyclic Y A hY
  let hP := TopCat.FiniteClosedPushforward.mapIndexedResolution_isAcyclic
    f hf hfinite R hR
  have hresolution :=
    TopCat.SheafCohomology.AcyclicResolution.Hom.extIsoGlobalHomology_naturality
      phi hS hP n
  have hcomplex :
      HomologicalComplex.homologyMap
          (TopCat.SheafCohomology.AcyclicResolution.Hom.globalComplexMap phi) (n + 1) ≫
        (HomologicalComplex.homologyMapIso
          (TopCat.FiniteClosedPushforward.indexedGlobalComplexIso
            f hf hfinite R) (n + 1)).hom ≫
        (HomologicalComplex.homologyMapIso
          (resolutionGlobalComplexIso X A hX) (n + 1)).hom =
      (HomologicalComplex.homologyMapIso
          (resolutionGlobalComplexIso Y A hY) (n + 1)).hom ≫
        HomologicalComplex.homologyMap (globalSheafPullback f A) (n + 1) := by
    simpa only [phi, R, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMapIso_hom, Category.assoc] using
      congrArg (fun k ↦ HomologicalComplex.homologyMap k (n + 1))
        (resolutionPullback_globalComplex f hf hfinite A hX hY)
  have hnat :
      (CategoryTheory.Sheaf.functorH _ (n + 1)).map
          (TopCat.ConstantSheaf.pushforwardHom A f) ≫
        ((TopCat.FiniteClosedPushforward.pushedIndexedGlobalIso
          f hf hfinite R hR n).hom ≫
          (HomologicalComplex.homologyMapIso
            (resolutionGlobalComplexIso X A hX) (n + 1)).hom) =
      (constantSheafGlobalIso Y A hY n).hom ≫
        HomologicalComplex.homologyMap (globalSheafPullback f A) (n + 1) := by
    change (CategoryTheory.Sheaf.functorH _ (n + 1)).map (phi.z 0) ≫
        (((TopCat.SheafCohomology.AcyclicResolution.extIsoGlobalHomology P hP n).hom ≫
          (HomologicalComplex.homologyMapIso
            (TopCat.FiniteClosedPushforward.indexedGlobalComplexIso
              f hf hfinite R) (n + 1)).hom) ≫
          (HomologicalComplex.homologyMapIso
            (resolutionGlobalComplexIso X A hX) (n + 1)).hom) =
      ((TopCat.SheafCohomology.AcyclicResolution.extIsoGlobalHomology S hS n).hom ≫
        (HomologicalComplex.homologyMapIso
          (resolutionGlobalComplexIso Y A hY) (n + 1)).hom) ≫
        HomologicalComplex.homologyMap (globalSheafPullback f A) (n + 1)
    exact compose_squares
      ((CategoryTheory.Sheaf.functorH _ (n + 1)).map (phi.z 0))
      (TopCat.SheafCohomology.AcyclicResolution.extIsoGlobalHomology P hP n).hom
      (TopCat.SheafCohomology.AcyclicResolution.extIsoGlobalHomology S hS n).hom
      (HomologicalComplex.homologyMap
        (TopCat.SheafCohomology.AcyclicResolution.Hom.globalComplexMap phi) (n + 1))
      ((HomologicalComplex.homologyMapIso
          (TopCat.FiniteClosedPushforward.indexedGlobalComplexIso
            f hf hfinite R) (n + 1)).hom ≫
        (HomologicalComplex.homologyMapIso
          (resolutionGlobalComplexIso X A hX) (n + 1)).hom)
      (HomologicalComplex.homologyMapIso
        (resolutionGlobalComplexIso Y A hY) (n + 1)).hom
      (HomologicalComplex.homologyMap (globalSheafPullback f A) (n + 1))
      hresolution hcomplex
  have hq := TopCat.FiniteClosedPushforward.indexedGlobal_forward
    f hf hfinite R hR n
  have hqglobal :
      AddCommGrpCat.ofHom
          (TopCat.FiniteClosedPushforward.cohomologyForward
            f hf hfinite (R.Z 0) (n + 1)) ≫
        ((TopCat.FiniteClosedPushforward.pushedIndexedGlobalIso
          f hf hfinite R hR n).hom ≫
          (HomologicalComplex.homologyMapIso
            (resolutionGlobalComplexIso X A hX) (n + 1)).hom) =
      (constantSheafGlobalIso X A hX n).hom := by
    exact reassoc_eq _ _ _ _ hq
  have hpq := TopCat.ConstantSheafCohomology.pullback_forward
    f hf hfinite A (n + 1)
  exact (congrArg (fun k ↦
    TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1) ≫ k)
      hqglobal.symm).trans
    ((reassoc_eq
      (TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1))
      (AddCommGrpCat.ofHom
        (TopCat.FiniteClosedPushforward.cohomologyForward
          f hf hfinite (R.Z 0) (n + 1)))
      ((CategoryTheory.Sheaf.functorH _ (n + 1)).map
        (TopCat.ConstantSheaf.pushforwardHom A f))
      ((TopCat.FiniteClosedPushforward.pushedIndexedGlobalIso
        f hf hfinite R hR n).hom ≫
        (HomologicalComplex.homologyMapIso
          (resolutionGlobalComplexIso X A hX) (n + 1)).hom)
      hpq).trans hnat)

/-- Pullback on constant-sheaf cohomology along a closed map with finite fibres commutes, in
every positive degree, with the comparison `H^•(·; A_·) ≅ H^•_sing(·; A)`. -/
theorem constantSheafCohomologyIsoSingular_naturality
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y)
    [MetrizableSpace X] [MetrizableSpace Y] (n : ℕ) :
    TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1) ≫
        (constantSheafCohomologyIsoSingular X A hX n).hom =
      (constantSheafCohomologyIsoSingular Y A hY n).hom ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.SingularCochains.pullback A f.hom) (n + 1) :=
  constantSheafCohomologyIsoSingular_naturality_of_global
    f A hX hY n
      (TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1))
      (constantSheafGlobalIso_naturality f hf hfinite A hX hY n)

set_option backward.isDefEq.respectTransparency false in
/-- If pullback on singular cohomology is an isomorphism in a positive degree, then so is
pullback on constant-sheaf cohomology in that degree. -/
theorem constantSheafCohomology_pullback_isIso_of_singular
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y)
    [MetrizableSpace X] [MetrizableSpace Y] (n : ℕ)
    [IsIso (HomologicalComplex.homologyMap
      (AlgebraicTopology.SingularCochains.pullback A f.hom) (n + 1))] :
    IsIso (TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1)) := by
  let p := TopCat.ConstantSheafCohomology.pullback f hf hfinite A (n + 1)
  let eX := constantSheafCohomologyIsoSingular X A hX n
  let eY := constantSheafCohomologyIsoSingular Y A hY n
  let s := HomologicalComplex.homologyMap
    (AlgebraicTopology.SingularCochains.pullback A f.hom) (n + 1)
  have h := constantSheafCohomologyIsoSingular_naturality
    f hf hfinite A hX hY n
  have hp : p = eY.hom ≫ s ≫ eX.inv := by
    apply (cancel_mono eX.hom).mp
    simpa only [p, eX, eY, s, Category.assoc, Iso.inv_hom_id,
      Iso.inv_hom_id_assoc, Category.comp_id] using h
  change IsIso p
  rw [hp]
  infer_instance

end TopCat.SingularCochainSheaf
