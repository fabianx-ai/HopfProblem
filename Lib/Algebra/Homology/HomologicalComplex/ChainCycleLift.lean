/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# A chain-complex quasi-isomorphism criterion from cycle and boundary lifts

This is the homological counterpart of the positive cochain cycle-lift criterion.  It works in
every natural degree, including degree zero, and talks only about elements of the original chain
complexes.

## References

* [A. Hatcher, *Algebraic topology*][hatcher2002], §2.1 (cycles modulo boundaries).
* [C. A. Weibel, *An introduction to homological algebra*][weibel1994], §1.1; compare
  `HomologicalComplex.quasiIso_iff` in Mathlib.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.HomologicalComplex

namespace ChainCycleLift

universe v

variable (K : ChainComplex (ModuleCat.{v} ℤ) ℕ)

/-- The concrete kernel of the outgoing differential. -/
abbrev Cycle (n : ℕ) := LinearMap.ker (K.d n ((ComplexShape.down ℕ).next n)).hom

/-- The cycles in degree `n` form a `ℤ`-module. -/
instance cycleModule (n : ℕ) : Module ℤ (Cycle K n) := (Cycle K n).module

/-- In the chain complex shape on `ℕ`, the degree after `n` is `n - 1`. -/
theorem next_nat (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  cases n <;> simp

/-- A cycle is killed by the ordinary `n` to `n - 1` differential. -/
theorem cycle_condition (n : ℕ) (c : Cycle K n) :
    (K.d n (n - 1)).hom c.1 = 0 := by
  rw [← next_nat n]
  exact c.2

/-- A cycle specified using the ordinary `n` to `n - 1` differential. -/
def mkCycle (n : ℕ) (c : K.X n) (hc : (K.d n (n - 1)).hom c = 0) : Cycle K n :=
  ⟨c, by
    change (K.d n ((ComplexShape.down ℕ).next n)).hom c = 0
    rw [next_nat n]
    exact hc⟩

/-- The underlying element of a cycle built by `mkCycle` is the given element. -/
@[simp]
theorem mkCycle_val (n : ℕ) (c : K.X n)
    (hc : (K.d n (n - 1)).hom c = 0) : (mkCycle K n c hc).1 = c := rfl

/-- The concrete kernel of the outgoing map of a short complex of modules. -/
abbrev ShortCycle (S : ShortComplex (ModuleCat.{v} ℤ)) :=
  LinearMap.ker S.g.hom

/-- The cycles of a short complex of modules form a `ℤ`-module. -/
instance shortCycleModule (S : ShortComplex (ModuleCat.{v} ℤ)) :
    Module ℤ (ShortCycle S) := (LinearMap.ker S.g.hom).module

/-- The submodule of cycles that are images of the incoming map. -/
abbrev ShortBoundaries (S : ShortComplex (ModuleCat.{v} ℤ)) :
    Submodule ℤ (ShortCycle S) :=
  LinearMap.range S.moduleCatToCycles

/-- The class in homology of a concrete cycle of a short complex. -/
def shortCycleClass (S : ShortComplex (ModuleCat.{v} ℤ)) :
    ShortCycle S →ₗ[ℤ] S.homology :=
  S.moduleCatHomologyIso.inv.hom.comp (ShortBoundaries S).mkQ

/-- Every homology class of a short complex of modules is the class of a concrete cycle. -/
theorem shortCycleClass_surjective (S : ShortComplex (ModuleCat.{v} ℤ)) :
    Function.Surjective (shortCycleClass S) :=
  ((ModuleCat.epi_iff_surjective S.moduleCatHomologyIso.inv).mp inferInstance).comp
    (ShortBoundaries S).mkQ_surjective

/-- A concrete cycle has vanishing homology class exactly when it is a boundary. -/
theorem shortCycleClass_eq_zero_iff (S : ShortComplex (ModuleCat.{v} ℤ))
    (c : ShortCycle S) :
    shortCycleClass S c = 0 ↔ ∃ b : S.X₁, S.f b = c.1 := by
  have hinj : Function.Injective S.moduleCatHomologyIso.inv :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  constructor
  · intro h
    have hq : (Submodule.Quotient.mk c : ShortCycle S ⧸ ShortBoundaries S) = 0 :=
      hinj (h.trans S.moduleCatHomologyIso.inv.hom.map_zero.symm)
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero (ShortBoundaries S)).mp hq
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hc : c ∈ ShortBoundaries S := ⟨b, Subtype.ext hb⟩
    have hq := (Submodule.Quotient.mk_eq_zero (ShortBoundaries S)).mpr hc
    exact (congrArg S.moduleCatHomologyIso.inv.hom hq).trans
      S.moduleCatHomologyIso.inv.hom.map_zero

/-- The canonical class of a concrete cycle. -/
def cycleClass (n : ℕ) : Cycle K n →ₗ[ℤ] K.homology n :=
  shortCycleClass (K.sc n)

/-- Every homology class of a chain complex of modules is the class of a concrete cycle. -/
theorem cycleClass_surjective (n : ℕ) : Function.Surjective (cycleClass K n) :=
  shortCycleClass_surjective (K.sc n)

/-- A concrete cycle has vanishing homology class exactly when it is a boundary. -/
theorem cycleClass_eq_zero_iff (n : ℕ) (c : Cycle K n) :
    cycleClass K n c = 0 ↔ ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = c.1 := by
  refine (shortCycleClass_eq_zero_iff (K.sc n) c).trans ?_
  change (∃ b : K.X ((ComplexShape.down ℕ).prev n),
    (K.d ((ComplexShape.down ℕ).prev n) n).hom b = c.1) ↔ _
  rw [ChainComplex.prev]

/-- Two concrete cycles have the same homology class exactly when they differ by a boundary. -/
theorem cycleClass_eq_iff (n : ℕ) (c d : Cycle K n) :
    cycleClass K n c = cycleClass K n d ↔
      ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = c.1 - d.1 := by
  simpa only [map_sub, sub_eq_zero, Submodule.coe_sub] using
    cycleClass_eq_zero_iff K n (c - d)

variable {K L : ChainComplex (ModuleCat.{v} ℤ) ℕ} (f : L ⟶ K)

/-- The map of short complexes in degree `n` induced by a chain map. -/
abbrev shortMap (n : ℕ) : L.sc n ⟶ K.sc n :=
  (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} ℤ)
    (ComplexShape.down ℕ) n).map f

/-- The actual cycle map through the concrete kernel descriptions. -/
def mapCycles (n : ℕ) : Cycle L n →ₗ[ℤ] Cycle K n :=
  ((L.sc n).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap f n) ≫
    (K.sc n).moduleCatCyclesIso.hom).hom

/-- The concrete cycle map is the restriction of the chain map in that degree. -/
@[simp]
theorem mapCycles_val (n : ℕ) (c : Cycle L n) :
    (mapCycles f n c).1 = (f.f n).hom c.1 := by
  have hcat : (L.sc n).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap f n) ≫
      (K.sc n).moduleCatCyclesIso.hom ≫ (K.sc n).moduleCatLeftHomologyData.i =
      (L.sc n).moduleCatLeftHomologyData.i ≫ (shortMap f n).τ₂ := by
    rw [(K.sc n).moduleCatCyclesIso_hom_i, ShortComplex.cyclesMap_i,
      (L.sc n).moduleCatCyclesIso_inv_iCycles_assoc]
  exact congrArg (fun g => g.hom c) hcat

/-- Concrete cycle representatives commute with the categorical homology map. -/
theorem homologyMap_cycleClass (n : ℕ) (c : Cycle L n) :
    (HomologicalComplex.homologyMap f n).hom (cycleClass L n c) =
      cycleClass K n (mapCycles f n c) := by
  have hcat : (L.sc n).moduleCatLeftHomologyData.π ≫
      (L.sc n).moduleCatHomologyIso.inv ≫ ShortComplex.homologyMap (shortMap f n) =
      ((L.sc n).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap f n) ≫
        (K.sc n).moduleCatCyclesIso.hom) ≫ (K.sc n).moduleCatLeftHomologyData.π ≫
          (K.sc n).moduleCatHomologyIso.inv := by
    simp only [Category.assoc, ← (L.sc n).moduleCatCyclesIso_inv_π_assoc,
      ← (K.sc n).moduleCatCyclesIso_inv_π, Iso.hom_inv_id_assoc]
    rw [ShortComplex.homologyπ_naturality]
  exact congrArg (fun g => g.hom c) hcat

private theorem homologyMap_surjective_of_cycle_lifting (n : ℕ)
    (hlift : ∀ c : Cycle K n, ∃ z : Cycle L n, ∃ b : K.X (n + 1),
      (K.d (n + 1) n).hom b = c.1 - (f.f n).hom z.1) :
    Function.Surjective (HomologicalComplex.homologyMap f n).hom := by
  intro h
  obtain ⟨c, rfl⟩ := cycleClass_surjective K n h
  obtain ⟨z, b, hb⟩ := hlift c
  refine ⟨cycleClass L n z, ?_⟩
  rw [homologyMap_cycleClass]
  apply Eq.symm
  exact (cycleClass_eq_iff K n c (mapCycles f n z)).mpr
    ⟨b, by simpa only [mapCycles_val] using hb⟩

private theorem homologyMap_injective_of_boundary_lifting (n : ℕ)
    (hlift : ∀ c : Cycle L n, ∀ b : K.X (n + 1),
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

private theorem cycle_of_boundary_relation (n : ℕ)
    (hf : Function.Injective (f.f (n - 1)).hom)
    (c : K.X n) (hc : (K.d n (n - 1)).hom c = 0)
    (z : L.X n) (b : K.X (n + 1))
    (hb : (K.d (n + 1) n).hom b = c - (f.f n).hom z) :
    (L.d n (n - 1)).hom z = 0 := by
  have hdd : (K.d n (n - 1)).hom ((K.d (n + 1) n).hom b) = 0 :=
    congrArg (fun g : K.X (n + 1) ⟶ K.X (n - 1) => g.hom b)
      (K.d_comp_d (n + 1) n (n - 1))
  have he := congrArg (K.d n (n - 1)).hom hb
  rw [hdd, map_sub, hc, zero_sub] at he
  have hz : (K.d n (n - 1)).hom ((f.f n).hom z) = 0 := neg_eq_zero.mp he.symm
  apply hf
  rw [map_zero]
  exact (congrArg (fun g : L.X n ⟶ K.X (n - 1) => g.hom z)
    (f.comm n (n - 1))).symm.trans hz

/-- An injective chain map is a quasi-isomorphism when cycles lift modulo actual boundaries and
actual boundaries of source cycles lift back to source boundaries. -/
theorem quasiIso_of_injective_chain_conditions
    (hf : ∀ n, Function.Injective (f.f n).hom)
    (hsurj : ∀ n, ∀ c : K.X n, (K.d n (n - 1)).hom c = 0 →
      ∃ z : L.X n, ∃ b : K.X (n + 1),
        (K.d (n + 1) n).hom b = c - (f.f n).hom z)
    (hinj : ∀ n, ∀ c : L.X n, (L.d n (n - 1)).hom c = 0 →
      ∀ b : K.X (n + 1), (K.d (n + 1) n).hom b = (f.f n).hom c →
        ∃ a : L.X (n + 1), (L.d (n + 1) n).hom a = c) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply homologyMap_injective_of_boundary_lifting f n
    intro c b hb
    exact hinj n c.1 (cycle_condition L n c) b hb
  · apply homologyMap_surjective_of_cycle_lifting f n
    intro c
    obtain ⟨z, b, hb⟩ := hsurj n c.1 (cycle_condition K n c)
    refine ⟨mkCycle L n z ?_, b, hb⟩
    exact cycle_of_boundary_relation f n (hf (n - 1)) c.1
      (cycle_condition K n c) z b hb

end ChainCycleLift

end CategoryTheory.HomologicalComplex
