/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology

open Set Function Filter Manifold Topology

open scoped BigOperators TensorProduct

/-!
# Descending a linear map on cycles to homology

For a chain complex `K` of `ℤ`-modules indexed by `ℕ` (any universe), a linear map on the
degree-`n` cycles that vanishes on boundaries descends to the homology `K.homology n`:
`SingularHomology.homologyDesc K n f hf`, computed on cycle classes by
`SingularHomology.homologyDesc_cycleClass`.  Two linear maps out of `K.homology n` that agree on
all cycle classes are equal (`SingularHomology.homologyLinearMap_ext`);
`SingularHomology.homologyBoundaries K n` is the submodule of boundary cycles and
`SingularHomology.homologyBoundaries_le_ker` its containment in the kernel of such an `f`.

This is the universal property of homology as cycles modulo boundaries (Hatcher, *Algebraic
Topology*, §2.1), stated through `SingularMayerVietoris.ModuleHomology.cycleClass`; the natural
home is `Lib.AlgebraicTopology.SingularHomology.ModuleHomology`, over any ring.
-/


@[expose] public noncomputable section

universe u


attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- The submodule of degree-`n` cycles of `K` consisting of boundaries, as a submodule
of the cycle module. -/
abbrev SingularHomology.homologyBoundaries (K : ChainComplex (ModuleCat.{u} ℤ) ℕ)
    (n : ℕ) : Submodule ℤ (SingularMayerVietoris.ModuleHomology.Cycle K n) :=
  SingularChains.ChainHomology.ShortBoundaries (K.sc n)

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- Two linear maps out of `K.homology n` agreeing on all cycle classes are equal. -/
theorem SingularHomology.homologyLinearMap_ext (K : ChainComplex (ModuleCat.{u} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M] {f g : K.homology n →ₗ[ℤ] M}
    (h :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle K n,
        f (SingularMayerVietoris.ModuleHomology.cycleClass K n c) =
          g (SingularMayerVietoris.ModuleHomology.cycleClass K n c)) :
    f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective K n x
  exact h c

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- If `f` vanishes on every boundary cycle, the boundary submodule is contained in
the kernel of `f`. -/
theorem SingularHomology.homologyBoundaries_le_ker (K : ChainComplex (ModuleCat.{u} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0) :
    SingularHomology.homologyBoundaries K n ≤ LinearMap.ker f := by
  rintro c ⟨b, hb⟩
  have hc : SingularMayerVietoris.ModuleHomology.cycleClass K n c = 0 :=
    (SingularChains.ChainHomology.shortCycleClass_eq_zero_iff (K.sc n) c).mpr
      ⟨b, congrArg Subtype.val hb⟩
  obtain ⟨b', hb'⟩ := (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff K n c).mp hc
  have he : SingularMayerVietoris.ModuleHomology.boundaryCycle K n b' = c := Subtype.ext hb'
  exact (congrArg f he).symm.trans (hf b')

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- A linear map on degree-`n` cycles of `K` vanishing on boundaries descends to a
linear map on `K.homology n`. -/
def SingularHomology.homologyDesc (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ)
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0) :
    K.homology n →ₗ[ℤ] M :=
  ((SingularHomology.homologyBoundaries K n).liftQ f (SingularHomology.homologyBoundaries_le_ker K n f hf)).comp
    (K.sc n).moduleCatHomologyIso.hom.hom

attribute [local instance] SingularChains.ChainHomology.shortCycleModule in
/-- `homologyDesc f hf` sends the class of a cycle `c` to `f c`. -/
@[simp]
theorem SingularHomology.homologyDesc_cycleClass (K : ChainComplex (ModuleCat.{u} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    SingularHomology.homologyDesc K n f hf (SingularMayerVietoris.ModuleHomology.cycleClass K n c) = f c := by
  have h :=
    congrArg (fun q => q.hom (Submodule.Quotient.mk c)) (K.sc n).moduleCatHomologyIso.inv_hom_id
  exact congrArg ((SingularHomology.homologyBoundaries K n).liftQ f (SingularHomology.homologyBoundaries_le_ker K n f hf)) h
