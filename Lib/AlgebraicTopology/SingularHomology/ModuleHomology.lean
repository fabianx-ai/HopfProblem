/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains


set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
abbrev SingularMayerVietoris.ModuleHomology.Cycle (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) :=
  LinearMap.ker (K.d n ((ComplexShape.down ℕ).next n)).hom

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
instance SingularMayerVietoris.ModuleHomology.cycleModule (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) : Module ℤ (SingularMayerVietoris.ModuleHomology.Cycle K n) :=
  (SingularMayerVietoris.ModuleHomology.Cycle K n).module

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.next_nat (n : ℕ) :
    (ComplexShape.down ℕ).next n = n - 1 := by cases n <;> simp

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.cycle_condition
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) : (K.d n (n - 1)).hom c.1 = 0 := by
  rw [← next_nat n]
  exact c.2

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
def SingularMayerVietoris.ModuleHomology.mkCycle (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : K.X n) (hc : (K.d n (n - 1)).hom c = 0) :
    SingularMayerVietoris.ModuleHomology.Cycle K n :=
  ⟨c, by
    change (K.d n ((ComplexShape.down ℕ).next n)).hom c = 0
    rw [next_nat n]
    exact hc⟩

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
def SingularMayerVietoris.ModuleHomology.cycleClass (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] K.homology n :=
  FirstHurewicz.ChainHomology.shortCycleClass (K.sc n)

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.cycleClass_surjective
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) : Function.Surjective (cycleClass K n) :=
  FirstHurewicz.ChainHomology.shortCycleClass_surjective (K.sc n)

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    cycleClass K n c = 0 ↔ ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = c.1 := by
  refine (FirstHurewicz.ChainHomology.shortCycleClass_eq_zero_iff (K.sc n) c).trans ?_
  change
    (∃ b : K.X ((ComplexShape.down ℕ).prev n),
        (K.d ((ComplexShape.down ℕ).prev n) n).hom b = c.1) ↔
      _
  rw [ChainComplex.prev]

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c d : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    cycleClass K n c = cycleClass K n d ↔ ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = c.1 - d.1 := by
  simpa only [map_sub, sub_eq_zero, Submodule.coe_sub] using cycleClass_eq_zero_iff K n (c - d)

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
def SingularMayerVietoris.ModuleHomology.boundaryCycle (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) (b : K.X (n + 1)) : SingularMayerVietoris.ModuleHomology.Cycle K n :=
  mkCycle K n ((K.d (n + 1) n).hom b)
    (congrArg (fun f : K.X (n + 1) ⟶ K.X (n - 1) => f.hom b) (K.d_comp_d (n + 1) n (n - 1)))

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
abbrev SingularMayerVietoris.ModuleHomology.shortMap {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : L ⟶ K) (n : ℕ) : L.sc n ⟶ K.sc n :=
  (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map f

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
def SingularMayerVietoris.ModuleHomology.mapCycles {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : L ⟶ K) (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle L n →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle K n :=
  ((L.sc n).moduleCatCyclesIso.inv ≫
      CategoryTheory.ShortComplex.cyclesMap (shortMap f n) ≫ (K.sc n).moduleCatCyclesIso.hom).hom

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
@[simp]
theorem SingularMayerVietoris.ModuleHomology.mapCycles_val
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : L ⟶ K) (n : ℕ)
    (c : SingularMayerVietoris.ModuleHomology.Cycle L n) :
    (mapCycles f n c).1 = (f.f n).hom c.1 := by
  have hcat :
    (L.sc n).moduleCatCyclesIso.inv ≫
        CategoryTheory.ShortComplex.cyclesMap (shortMap f n) ≫
          (K.sc n).moduleCatCyclesIso.hom ≫ (K.sc n).moduleCatLeftHomologyData.i =
      (L.sc n).moduleCatLeftHomologyData.i ≫ (shortMap f n).τ₂ := by
    rw [(K.sc n).moduleCatCyclesIso_hom_i, CategoryTheory.ShortComplex.cyclesMap_i,
      (L.sc n).moduleCatCyclesIso_inv_iCycles_assoc]
  exact congrArg (fun g => g.hom c) hcat

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : L ⟶ K) (n : ℕ)
    (c : SingularMayerVietoris.ModuleHomology.Cycle L n) :
    (HomologicalComplex.homologyMap f n).hom (cycleClass L n c) =
      cycleClass K n (mapCycles f n c) := by
  have hcat :
    (L.sc n).moduleCatLeftHomologyData.π ≫
        (L.sc n).moduleCatHomologyIso.inv ≫
          CategoryTheory.ShortComplex.homologyMap (shortMap f n) =
      ((L.sc n).moduleCatCyclesIso.inv ≫
          CategoryTheory.ShortComplex.cyclesMap (shortMap f n) ≫
            (K.sc n).moduleCatCyclesIso.hom) ≫
        (K.sc n).moduleCatLeftHomologyData.π ≫ (K.sc n).moduleCatHomologyIso.inv := by
    simp only [CategoryTheory.Category.assoc, ← (L.sc n).moduleCatCyclesIso_inv_π_assoc,
      ← (K.sc n).moduleCatCyclesIso_inv_π, CategoryTheory.Iso.hom_inv_id_assoc]
    rw [CategoryTheory.ShortComplex.homologyπ_naturality]
  exact congrArg (fun g => g.hom c) hcat

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.homologyMap_surjective_of_cycle_lifting
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : L ⟶ K) (n : ℕ)
    (hlift :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle K n,
        ∃ z : SingularMayerVietoris.ModuleHomology.Cycle L n,
          ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = (c.1 : K.X n) - (f.f n).hom z.1) :
    Function.Surjective (HomologicalComplex.homologyMap f n).hom := by
  intro h
  obtain ⟨c, rfl⟩ := cycleClass_surjective K n h
  obtain ⟨z, b, hb⟩ := hlift c
  refine ⟨cycleClass L n z, ?_⟩
  rw [homologyMap_cycleClass]
  apply Eq.symm
  apply (cycleClass_eq_iff K n c (mapCycles f n z)).mpr
  exact ⟨b, by simpa only [mapCycles_val] using hb⟩

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.homologyMap_injective_of_boundary_lifting
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : L ⟶ K) (n : ℕ)
    (hlift :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle L n,
        ∀ b : K.X (n + 1),
          (K.d (n + 1) n).hom b = (f.f n).hom c.1 →
            ∃ a : L.X (n + 1), (L.d (n + 1) n).hom a = c.1) :
    Function.Injective (HomologicalComplex.homologyMap f n).hom := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := cycleClass_surjective L n x
  obtain ⟨d, rfl⟩ := cycleClass_surjective L n y
  have hz : (HomologicalComplex.homologyMap f n).hom (cycleClass L n (c - d)) = 0 := by
    simp only [map_sub]
    rw [hxy, sub_self]
  rw [homologyMap_cycleClass] at hz
  obtain ⟨b, hb⟩ := (cycleClass_eq_zero_iff K n (mapCycles f n (c - d))).mp hz
  apply (cycleClass_eq_iff L n c d).mpr
  exact hlift (c - d) b (hb.trans (mapCycles_val f n (c - d)))

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.quasiIsoAt_of_cycle_boundary_lifting
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : L ⟶ K) (n : ℕ)
    (hsurj :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle K n,
        ∃ z : SingularMayerVietoris.ModuleHomology.Cycle L n,
          ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = (c.1 : K.X n) - (f.f n).hom z.1)
    (hinj :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle L n,
        ∀ b : K.X (n + 1),
          (K.d (n + 1) n).hom b = (f.f n).hom c.1 →
            ∃ a : L.X (n + 1), (L.d (n + 1) n).hom a = c.1) :
    QuasiIsoAt f n := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr
  exact
    ⟨homologyMap_injective_of_boundary_lifting f n hinj,
      homologyMap_surjective_of_cycle_lifting f n hsurj⟩

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.quasiIso_of_cycle_boundary_lifting
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : L ⟶ K)
    (hsurj :
      ∀ n,
        ∀ c : SingularMayerVietoris.ModuleHomology.Cycle K n,
          ∃ z : SingularMayerVietoris.ModuleHomology.Cycle L n,
            ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = (c.1 : K.X n) - (f.f n).hom z.1)
    (hinj :
      ∀ n,
        ∀ c : SingularMayerVietoris.ModuleHomology.Cycle L n,
          ∀ b : K.X (n + 1),
            (K.d (n + 1) n).hom b = (f.f n).hom c.1 →
              ∃ a : L.X (n + 1), (L.d (n + 1) n).hom a = c.1) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  exact quasiIsoAt_of_cycle_boundary_lifting f n (hsurj n) (hinj n)

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.cycle_of_boundary_relation
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : L ⟶ K) (n : ℕ)
    (hf : Function.Injective (f.f (n - 1)).hom) (c : K.X n) (hc : (K.d n (n - 1)).hom c = 0)
    (z : L.X n) (b : K.X (n + 1)) (hb : (K.d (n + 1) n).hom b = c - (f.f n).hom z) :
    (L.d n (n - 1)).hom z = 0 := by
  have hdd : (K.d n (n - 1)).hom ((K.d (n + 1) n).hom b) = 0 :=
    congrArg (fun g : K.X (n + 1) ⟶ K.X (n - 1) => g.hom b) (K.d_comp_d (n + 1) n (n - 1))
  have he := congrArg (K.d n (n - 1)).hom hb
  rw [hdd, map_sub, hc, zero_sub] at he
  have hz : (K.d n (n - 1)).hom ((f.f n).hom z) = 0 := neg_eq_zero.mp he.symm
  apply hf
  rw [map_zero]
  exact (congrArg (fun g : L.X n ⟶ K.X (n - 1) => g.hom z) (f.comm n (n - 1))).symm.trans hz

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
theorem SingularMayerVietoris.ModuleHomology.quasiIso_of_injective_chain_conditions
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : L ⟶ K)
    (hf : ∀ n, Function.Injective (f.f n).hom)
    (hsurj :
      ∀ n,
        ∀ c : K.X n,
          (K.d n (n - 1)).hom c = 0 →
            ∃ z : L.X n, ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = c - (f.f n).hom z)
    (hinj :
      ∀ n,
        ∀ c : L.X n,
          (L.d n (n - 1)).hom c = 0 →
            ∀ b : K.X (n + 1),
              (K.d (n + 1) n).hom b = (f.f n).hom c →
                ∃ a : L.X (n + 1), (L.d (n + 1) n).hom a = c) :
    QuasiIso f := by
  apply quasiIso_of_cycle_boundary_lifting f
  · intro n c
    obtain ⟨z, b, hb⟩ := hsurj n c.1 (cycle_condition K n c)
    refine ⟨mkCycle L n z ?_, b, hb⟩
    exact cycle_of_boundary_relation f n (hf (n - 1)) c.1 (cycle_condition K n c) z b hb
  · intro n c b hb
    exact hinj n c.1 (cycle_condition L n c) b hb
end Mathoverflow1973
