/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.HomologicalComplex.ChainCycleLift
public import Lib.AlgebraicTopology.SingularCochains
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Evaluation of additive cohomology on integral homology

This file constructs the textbook Kronecker evaluation map from the homology of the additive
dual of an integral chain complex to additive homomorphisms on its integral homology.  The map is
defined on actual cycles, descends through actual boundaries, and is natural for chain maps.

No universal-coefficient isomorphism is asserted: evaluation exists without projectivity, while
bijectivity requires the usual extra hypotheses eliminating the `Ext` term.

## References

* [A. Hatcher, *Algebraic topology*][hatcher2002], §3.1 and Theorem 3.2 (the Kronecker
  pairing `⟨φ, z⟩` and the evaluation half of the universal coefficient theorem).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.SingularCochains

namespace DualEvaluation

universe v w

variable (A : AddCommGrpCat.{w})

/-! ## Concrete positive-degree cohomology classes -/

variable (C : CochainComplex AddCommGrpCat.{w} ℕ)

/-- Concrete cocycles in positive degree `n + 1`. -/
abbrev PositiveCocycle (n : ℕ) :=
  AddMonoidHom.ker (C.sc (n + 1)).g.hom

/-- The canonical class of a concrete positive-degree cocycle. -/
def positiveCocycleClass (n : ℕ) :
    PositiveCocycle C n →+ C.homology (n + 1) :=
  ((C.sc (n + 1)).abCyclesIso.inv ≫ (C.sc (n + 1)).homologyπ).hom

/-- Every positive-degree cohomology class has a concrete cocycle representative. -/
theorem positiveCocycleClass_surjective (n : ℕ) :
    Function.Surjective (positiveCocycleClass C n) := by
  exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance

variable {C D : CochainComplex AddCommGrpCat.{w} ℕ} (f : C ⟶ D)

/-- The concrete cocycle map induced by a cochain map. -/
def mapPositiveCocycles (n : ℕ) :
    PositiveCocycle C n →+ PositiveCocycle D n :=
  ((C.sc (n + 1)).abCyclesIso.inv ≫
      ShortComplex.cyclesMap
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{w}
          (ComplexShape.up ℕ) (n + 1)).map f) ≫
      (D.sc (n + 1)).abCyclesIso.hom).hom

/-- The induced cocycle map is the underlying cochain map in degree `n + 1`. -/
@[simp]
theorem mapPositiveCocycles_val (n : ℕ) (c : PositiveCocycle C n) :
    (mapPositiveCocycles (f := f) n c).1 = f.f (n + 1) c.1 := by
  change (D.sc (n + 1)).iCycles
      (ShortComplex.cyclesMap
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{w}
          (ComplexShape.up ℕ) (n + 1)).map f)
        ((C.sc (n + 1)).abCyclesIso.inv c)) = f.f (n + 1) c.1
  rw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i,
    ConcreteCategory.comp_apply,
    (C.sc (n + 1)).abCyclesIso_inv_apply_iCycles]
  rfl

/-- Homology maps send a concrete cocycle class to the class of its literal image. -/
theorem homologyMap_positiveCocycleClass (n : ℕ) (c : PositiveCocycle C n) :
    HomologicalComplex.homologyMap f (n + 1) (positiveCocycleClass C n c) =
      positiveCocycleClass D n (mapPositiveCocycles (f := f) n c) := by
  let φ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{w}
    (ComplexShape.up ℕ) (n + 1)).map f
  have hcat :
      (C.sc (n + 1)).abCyclesIso.inv ≫ (C.sc (n + 1)).homologyπ ≫
          ShortComplex.homologyMap φ =
        ((C.sc (n + 1)).abCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫
          (D.sc (n + 1)).abCyclesIso.hom) ≫
            (D.sc (n + 1)).abCyclesIso.inv ≫ (D.sc (n + 1)).homologyπ := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [ShortComplex.homologyπ_naturality]
  exact ConcreteCategory.congr_hom hcat c

/-! ## Evaluation of a closed functional -/

variable (K : ChainComplex (ModuleCat.{v} ℤ) ℕ) (n : ℕ)

/-- A linear functional is closed when it annihilates the incoming chain boundary. -/
def IsClosedFunctional (phi : K.X n →ₗ[ℤ] A) : Prop :=
  ∀ b : K.X (n + 1), phi ((K.d (n + 1) n).hom b) = 0

/-- A closed functional kills the boundary submodule in chains modulo boundaries. -/
theorem boundaryRange_le_ker (phi : K.X n →ₗ[ℤ] A)
    (hphi : IsClosedFunctional A K n phi) :
    LinearMap.range (K.sc n).f.hom ≤ LinearMap.ker phi := by
  change LinearMap.range (K.d ((ComplexShape.down ℕ).prev n) n).hom ≤ LinearMap.ker phi
  rw [ChainComplex.prev]
  rintro _ ⟨b, rfl⟩
  exact hphi b

/-- Chains modulo boundaries, in the degree selected by a short complex. -/
abbrev ChainClass (S : ShortComplex (ModuleCat.{v} ℤ)) :=
  S.X₂ ⧸ LinearMap.range S.f.hom

local instance chainClassModule (S : ShortComplex (ModuleCat.{v} ℤ)) :
    Module ℤ (ChainClass S) :=
  Submodule.Quotient.module (LinearMap.range S.f.hom)

/-- The canonical embedding of homology into chains modulo boundaries. -/
def homologyToChainClass (S : ShortComplex (ModuleCat.{v} ℤ)) :
    S.homology →ₗ[ℤ] ChainClass S :=
  (S.homologyι ≫ S.moduleCatOpcyclesIso.hom).hom

/-- Evaluation on actual homology by descending a closed chain functional. -/
def evaluationOfClosed (phi : K.X n →ₗ[ℤ] A)
    (hphi : IsClosedFunctional A K n phi) :
    K.homology n →ₗ[ℤ] A :=
  ((LinearMap.range (K.sc n).f.hom).liftQ phi
    (boundaryRange_le_ker A K n phi hphi)).comp
      (homologyToChainClass (K.sc n))

/-- Evaluation on a concrete cycle is literal evaluation on its chain representative. -/
@[simp]
theorem evaluationOfClosed_cycleClass (phi : K.X n →ₗ[ℤ] A)
    (hphi : IsClosedFunctional A K n phi)
    (c : HomologicalComplex.ChainCycleLift.Cycle K n) :
    evaluationOfClosed A K n phi hphi
        (HomologicalComplex.ChainCycleLift.cycleClass K n c) = phi c.1 := by
  have hcat :
      (K.sc n).moduleCatLeftHomologyData.π ≫ (K.sc n).moduleCatHomologyIso.inv ≫
          (K.sc n).homologyι ≫ (K.sc n).moduleCatOpcyclesIso.hom =
        (K.sc n).moduleCatLeftHomologyData.i ≫
          ModuleCat.ofHom (LinearMap.range (K.sc n).f.hom).mkQ := by
    rw [← (K.sc n).moduleCatCyclesIso_inv_π_assoc,
      (K.sc n).homology_π_ι_assoc,
      (K.sc n).moduleCatCyclesIso_inv_iCycles_assoc,
      (K.sc n).pOpcycles_comp_moduleCatOpcyclesIso_hom]
    rfl
  change ((LinearMap.range (K.sc n).f.hom).liftQ phi
      (boundaryRange_le_ker A K n phi hphi))
        (homologyToChainClass (K.sc n)
          (HomologicalComplex.ChainCycleLift.shortCycleClass (K.sc n) c)) = phi c.1
  rw [show homologyToChainClass (K.sc n)
      (HomologicalComplex.ChainCycleLift.shortCycleClass (K.sc n) c) =
        (Submodule.Quotient.mk c.1 : ChainClass (K.sc n)) by
    exact ConcreteCategory.congr_hom hcat c]
  rfl

/-! ## Kronecker evaluation on additive dual cohomology -/

/-- A term of the additive dual complex, exposed as its underlying additive functional. -/
def cochainAddHom (q : ℕ) (phi : (dualComplex A K).X q) : K.X q →+ A := by
  change (K.X q →+ A) at phi
  exact phi

/-- A term of the additive dual complex, regarded as an integral-linear functional. -/
def cochainLinear (q : ℕ) (phi : (dualComplex A K).X q) : K.X q →ₗ[ℤ] A :=
  { toFun := cochainAddHom A K q phi
    map_add' := (cochainAddHom A K q phi).map_add
    map_smul' := by
      intro z x
      change (cochainAddHom A K q phi)
          ((K.X q).isModule.smul z x) =
        (AddCommGroup.toIntModule A).smul z ((cochainAddHom A K q phi) x)
      rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
      exact (cochainAddHom A K q phi).map_zsmul z x }

/-- The canonical normalization of the short complex at positive degree. -/
noncomputable abbrev normalizedPositiveScIso
    (E : CochainComplex AddCommGrpCat.{w} ℕ) (m : ℕ) :
    E.sc (m + 1) ≅ E.sc' m (m + 1) (m + 1 + 1) :=
  E.isoSc' m (m + 1) (m + 1 + 1)
    (CochainComplex.prev_nat_succ m) (CochainComplex.next ℕ (m + 1))

/-- The underlying cochain represented by a concrete positive-degree cocycle.  This accessor goes
through the categorical cycle inclusion and the canonical normalized short complex, so its target
has the literal complex degree rather than the opaque middle object of the associated short
complex. -/
def positiveCocycleValue (m : ℕ) (c : PositiveCocycle C m) : C.X (m + 1) :=
  (normalizedPositiveScIso C m).hom.τ₂
    ((C.sc (m + 1)).iCycles ((C.sc (m + 1)).abCyclesIso.inv c))

/-- The cochain represented by a concrete cocycle is its underlying element, transported along
the normalization isomorphism. -/
@[simp]
theorem positiveCocycleValue_eq_val (m : ℕ) (c : PositiveCocycle C m) :
    positiveCocycleValue (C := C) m c =
      (normalizedPositiveScIso C m).hom.τ₂ c.1 := by
  exact congrArg (fun x ↦ (normalizedPositiveScIso C m).hom.τ₂ x)
    ((C.sc (m + 1)).abCyclesIso_inv_apply_iCycles c)

/-- The cochain represented by a concrete cocycle is literally its underlying element. -/
@[simp]
theorem positiveCocycleValue_eq_literal_val (m : ℕ) (c : PositiveCocycle C m) :
    positiveCocycleValue (C := C) m c = c.1 := by
  rw [positiveCocycleValue_eq_val]
  have hτ : (normalizedPositiveScIso C m).hom.τ₂ = 𝟙 (C.X (m + 1)) :=
    HomologicalComplex.natIsoSc'_hom_app_τ₂ AddCommGrpCat.{w}
      (ComplexShape.up ℕ) m (m + 1) (m + 1 + 1)
        (CochainComplex.prev_nat_succ m) (CochainComplex.next ℕ (m + 1)) C
  exact ConcreteCategory.congr_hom hτ c.1

/-- A literal integral-linear chain functional as a term of the additive dual complex. -/
def linearCochain (q : ℕ) (phi : K.X q →ₗ[ℤ] A) : (dualComplex A K).X q := by
  change K.X q →+ A
  exact phi.toAddMonoidHom

/-- Reading a linear functional back off the cochain it defines returns that functional. -/
@[simp]
theorem cochainLinear_linearCochain (q : ℕ) (phi : K.X q →ₗ[ℤ] A) :
    cochainLinear A K q (linearCochain A K q phi) = phi := by
  ext x
  rfl

/-- A literal chain functional placed in the normalized positive-degree short complex. -/
def normalizedLinearCochain (m : ℕ) (phi : K.X (m + 1) →ₗ[ℤ] A) :
    ((dualComplex A K).sc' m (m + 1) (m + 1 + 1)).X₂ := by
  change (dualComplex A K).X (m + 1)
  exact linearCochain A K (m + 1) phi

/-- A normalized linear cochain evaluates as the linear functional it comes from. -/
@[simp]
theorem normalizedLinearCochain_apply (m : ℕ) (phi : K.X (m + 1) →ₗ[ℤ] A)
    (x : K.X (m + 1)) :
    cochainAddHom A K (m + 1) (normalizedLinearCochain A K m phi) x = phi x := rfl

/-- A closed literal chain functional determines a concrete positive-degree cocycle. -/
def mkPositiveCocycleOfClosed (m : ℕ) (phi : K.X (m + 1) →ₗ[ℤ] A)
    (hphi : IsClosedFunctional A K (m + 1) phi) :
    PositiveCocycle (dualComplex A K) m := by
  let E := normalizedPositiveScIso (dualComplex A K) m
  let phi' := normalizedLinearCochain A K m phi
  refine ⟨E.inv.τ₂ phi', ?_⟩
  have hd : (dualComplex A K).d (m + 1) (m + 1 + 1) phi' = 0 := by
    apply AddMonoidHom.ext
    intro b
    exact hphi b
  have ht : ((dualComplex A K).sc' m (m + 1) (m + 1 + 1)).g phi' = 0 := by
    change (dualComplex A K).d (m + 1) (m + 1 + 1) phi' = 0
    exact hd
  have h := ConcreteCategory.congr_hom E.inv.comm₂₃ phi'
  change ((dualComplex A K).sc (m + 1)).g (E.inv.τ₂ phi') =
    E.inv.τ₃ (((dualComplex A K).sc' m (m + 1) (m + 1 + 1)).g phi') at h
  rw [ht, map_zero] at h
  exact h

/-- The underlying element of the cocycle attached to a closed functional is that functional,
transported along the normalization isomorphism. -/
@[simp]
theorem mkPositiveCocycleOfClosed_val (m : ℕ) (phi : K.X (m + 1) →ₗ[ℤ] A)
    (hphi : IsClosedFunctional A K (m + 1) phi) :
    (mkPositiveCocycleOfClosed A K m phi hphi).1 =
      (normalizedPositiveScIso (dualComplex A K) m).inv.τ₂
        (normalizedLinearCochain A K m phi) := rfl

/-- The cochain represented by the cocycle of a closed functional is that functional. -/
@[simp]
theorem positiveCocycleValue_mkPositiveCocycleOfClosed (m : ℕ)
    (phi : K.X (m + 1) →ₗ[ℤ] A) (hphi : IsClosedFunctional A K (m + 1) phi) :
    positiveCocycleValue (C := dualComplex A K) m
        (mkPositiveCocycleOfClosed A K m phi hphi) =
      normalizedLinearCochain A K m phi := by
  rw [positiveCocycleValue_eq_val]
  rw [mkPositiveCocycleOfClosed_val]
  let E := normalizedPositiveScIso (dualComplex A K) m
  have hτ := congrArg ShortComplex.Hom.τ₂ E.inv_hom_id
  have h := ConcreteCategory.congr_hom hτ (normalizedLinearCochain A K m phi)
  change E.hom.τ₂ (E.inv.τ₂ (normalizedLinearCochain A K m phi)) =
    normalizedLinearCochain A K m phi
  simpa only [ShortComplex.comp_τ₂, ShortComplex.id_τ₂,
    AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply] using h

/-- The zero cocycle represents the zero cochain. -/
@[simp]
theorem positiveCocycleValue_zero (m : ℕ) :
    positiveCocycleValue (C := C) m 0 = 0 := by
  change (normalizedPositiveScIso C m).hom.τ₂
    ((C.sc (m + 1)).iCycles ((C.sc (m + 1)).abCyclesIso.inv 0)) = 0
  simp only [map_zero]

/-- Passing from a cocycle to the cochain it represents is additive. -/
@[simp]
theorem positiveCocycleValue_add (m : ℕ) (c d : PositiveCocycle C m) :
    positiveCocycleValue (C := C) m (c + d) =
      positiveCocycleValue (C := C) m c + positiveCocycleValue (C := C) m d := by
  change (normalizedPositiveScIso C m).hom.τ₂
      ((C.sc (m + 1)).iCycles ((C.sc (m + 1)).abCyclesIso.inv (c + d))) =
    (normalizedPositiveScIso C m).hom.τ₂
        ((C.sc (m + 1)).iCycles ((C.sc (m + 1)).abCyclesIso.inv c)) +
      (normalizedPositiveScIso C m).hom.τ₂
        ((C.sc (m + 1)).iCycles ((C.sc (m + 1)).abCyclesIso.inv d))
  simp only [map_add]

/-- The differential of the dual complex is precomposition with the differential of the chain
complex: `(dφ)(x) = φ(∂x)`. -/
@[simp]
theorem dualComplex_d_apply_apply (i j : ℕ)
    (phi : (dualComplex A K).X i) (x : K.X j) :
    cochainAddHom A K j ((dualComplex A K).d i j phi) x =
      cochainAddHom A K i phi ((K.d j i).hom x) := rfl

/-- A cocycle in the additive dual complex is a closed linear functional on chains. -/
theorem positiveCocycle_isClosedFunctional (m : ℕ)
    (c : PositiveCocycle (dualComplex A K) m) :
    IsClosedFunctional A K (m + 1)
      (cochainLinear A K (m + 1)
        (positiveCocycleValue (C := dualComplex A K) m c)) := by
  intro b
  have hc : (dualComplex A K).d (m + 1) (m + 1 + 1)
      (positiveCocycleValue (C := dualComplex A K) m c) = 0 := by
    rw [positiveCocycleValue_eq_val]
    change ((dualComplex A K).sc' m (m + 1) (m + 1 + 1)).g
      ((normalizedPositiveScIso (dualComplex A K) m).hom.τ₂ c.1) = 0
    have h := ConcreteCategory.congr_hom
      (normalizedPositiveScIso (dualComplex A K) m).hom.comm₂₃ c.1
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    rw [c.2] at h
    simpa only [map_zero] using h
  change cochainAddHom A K (m + 1)
    (positiveCocycleValue (C := dualComplex A K) m c)
      ((K.d (m + 1 + 1) (m + 1)).hom b) = 0
  rw [← dualComplex_d_apply_apply]
  rw [hc]
  rfl

/-- Evaluation of one concrete positive-degree cocycle on integral homology. -/
def evaluationOfPositiveCocycle (m : ℕ)
    (c : PositiveCocycle (dualComplex A K) m) :
    K.homology (m + 1) →+ A :=
  (evaluationOfClosed A K (m + 1)
    (cochainLinear A K (m + 1) (positiveCocycleValue (C := dualComplex A K) m c))
    (positiveCocycle_isClosedFunctional A K m c)).toAddMonoidHom

/-- Evaluating the functional of a cocycle on the class of a cycle is the Kronecker pairing
`⟨φ, z⟩` of the represented cochain with the cycle. -/
@[simp]
theorem evaluationOfPositiveCocycle_cycleClass (m : ℕ)
    (c : PositiveCocycle (dualComplex A K) m)
    (z : HomologicalComplex.ChainCycleLift.Cycle K (m + 1)) :
    evaluationOfPositiveCocycle A K m c
        (HomologicalComplex.ChainCycleLift.cycleClass K (m + 1) z) =
      cochainAddHom A K (m + 1)
        (positiveCocycleValue (C := dualComplex A K) m c) z.1 := by
  change evaluationOfClosed A K (m + 1)
    (cochainLinear A K (m + 1) (positiveCocycleValue (C := dualComplex A K) m c))
      (positiveCocycle_isClosedFunctional A K m c)
        (HomologicalComplex.ChainCycleLift.cycleClass K (m + 1) z) = _
  rw [evaluationOfClosed_cycleClass]
  rfl

/-- The zero cocycle evaluates to the zero functional on homology. -/
theorem evaluationOfPositiveCocycle_zero (m : ℕ) :
    evaluationOfPositiveCocycle A K m 0 = 0 := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨z, rfl⟩ :=
    HomologicalComplex.ChainCycleLift.cycleClass_surjective K (m + 1) a
  rw [evaluationOfPositiveCocycle_cycleClass]
  simp only [positiveCocycleValue_zero, cochainAddHom, AddMonoidHom.zero_apply]
  rfl

/-- Evaluation on homology is additive in the cocycle. -/
theorem evaluationOfPositiveCocycle_add (m : ℕ)
    (c d : PositiveCocycle (dualComplex A K) m) :
    evaluationOfPositiveCocycle A K m (c + d) =
      evaluationOfPositiveCocycle A K m c + evaluationOfPositiveCocycle A K m d := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨z, rfl⟩ :=
    HomologicalComplex.ChainCycleLift.cycleClass_surjective K (m + 1) a
  change evaluationOfPositiveCocycle A K m (c + d)
      (HomologicalComplex.ChainCycleLift.cycleClass K (m + 1) z) =
    evaluationOfPositiveCocycle A K m c
        (HomologicalComplex.ChainCycleLift.cycleClass K (m + 1) z) +
      evaluationOfPositiveCocycle A K m d
        (HomologicalComplex.ChainCycleLift.cycleClass K (m + 1) z)
  rw [evaluationOfPositiveCocycle_cycleClass, evaluationOfPositiveCocycle_cycleClass,
    evaluationOfPositiveCocycle_cycleClass]
  simp only [positiveCocycleValue_add, cochainAddHom]
  rfl

/-- Evaluation of concrete positive-degree cocycles on integral homology is additive. -/
def positiveCocycleEvaluation (m : ℕ) :
    PositiveCocycle (dualComplex A K) m →+
      (K.homology (m + 1) →+ A) where
  toFun := evaluationOfPositiveCocycle A K m
  map_zero' := evaluationOfPositiveCocycle_zero A K m
  map_add' := evaluationOfPositiveCocycle_add A K m

/-- The bundled evaluation map agrees with the Kronecker pairing on classes of cycles. -/
@[simp]
theorem positiveCocycleEvaluation_cycleClass (m : ℕ)
    (c : PositiveCocycle (dualComplex A K) m)
    (z : HomologicalComplex.ChainCycleLift.Cycle K (m + 1)) :
    positiveCocycleEvaluation A K m c
        (HomologicalComplex.ChainCycleLift.cycleClass K (m + 1) z) =
      cochainAddHom A K (m + 1)
        (positiveCocycleValue (C := dualComplex A K) m c) z.1 := by
  exact evaluationOfPositiveCocycle_cycleClass A K m c z

/-- The preceding cochain in the short complex at positive degree, with its index normalized. -/
def previousCochainValue (m : ℕ)
    (b : ((dualComplex A K).sc (m + 1)).X₁) : (dualComplex A K).X m :=
  (normalizedPositiveScIso (dualComplex A K) m).hom.τ₁ b

/-- The incoming map of the normalized short complex agrees with the one of the native short
complex under the normalization isomorphism. -/
theorem positiveSc_f_apply (m : ℕ)
    (b : ((dualComplex A K).sc (m + 1)).X₁) :
    ((dualComplex A K).sc' m (m + 1) (m + 1 + 1)).f
        (previousCochainValue A K m b) =
      (normalizedPositiveScIso (dualComplex A K) m).hom.τ₂
        (((dualComplex A K).sc (m + 1)).f b) := by
  have h := ConcreteCategory.congr_hom
    (normalizedPositiveScIso (dualComplex A K) m).hom.comm₁₂ b
  simpa only [ConcreteCategory.comp_apply, previousCochainValue] using h

/-- Incoming coboundaries evaluate trivially on homology. -/
theorem positiveCocycleEvaluation_abToCycles (m : ℕ)
    (b : ((dualComplex A K).sc (m + 1)).X₁) :
    positiveCocycleEvaluation A K m
        (((dualComplex A K).sc (m + 1)).abToCycles b) = 0 := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨z, rfl⟩ :=
    HomologicalComplex.ChainCycleLift.cycleClass_surjective K (m + 1) a
  rw [positiveCocycleEvaluation_cycleClass]
  rw [positiveCocycleValue_eq_val]
  change cochainAddHom A K (m + 1)
    ((normalizedPositiveScIso (dualComplex A K) m).hom.τ₂
      (((dualComplex A K).sc (m + 1)).f b)) z.1 = 0
  rw [← positiveSc_f_apply]
  change cochainAddHom A K (m + 1)
    ((dualComplex A K).d m (m + 1) (previousCochainValue A K m b)) z.1 = 0
  rw [dualComplex_d_apply_apply]
  have hz : (K.d (m + 1) m).hom z.1 = 0 := by
    have hz' := z.2
    change (K.d (m + 1) ((ComplexShape.down ℕ).next (m + 1))).hom z.1 = 0 at hz'
    rw [ChainComplex.next_nat_succ] at hz'
    exact hz'
  rw [hz]
  exact (previousCochainValue A K m b).map_zero

/-- The incoming coboundary subgroup lies in the kernel of cocycle evaluation. -/
theorem positiveCoboundaryRange_le_ker (m : ℕ) :
    AddMonoidHom.range ((dualComplex A K).sc (m + 1)).abToCycles ≤
      AddMonoidHom.ker (positiveCocycleEvaluation A K m) := by
  rintro c ⟨b, rfl⟩
  exact positiveCocycleEvaluation_abToCycles A K m b

/-- Canonical Kronecker evaluation from positive-degree additive cohomology to the additive dual
of integral homology. -/
def cohomologyEvaluation (m : ℕ) :
    (dualComplex A K).homology (m + 1) ⟶
      AddCommGrpCat.of (K.homology (m + 1) →+ A) :=
  ((dualComplex A K).sc (m + 1)).abHomologyIso.hom ≫
    AddCommGrpCat.ofHom
      (QuotientAddGroup.lift
        (AddMonoidHom.range ((dualComplex A K).sc (m + 1)).abToCycles)
        (positiveCocycleEvaluation A K m)
        (positiveCoboundaryRange_le_ker A K m))

private theorem positiveCocycleClass_quotient (m : ℕ)
    (c : PositiveCocycle (dualComplex A K) m) :
    ((dualComplex A K).sc (m + 1)).abHomologyIso.hom
        (positiveCocycleClass (dualComplex A K) m c) =
      QuotientAddGroup.mk'
        (AddMonoidHom.range ((dualComplex A K).sc (m + 1)).abToCycles) c := by
  have h :
      ((dualComplex A K).sc (m + 1)).abCyclesIso.inv ≫
          ((dualComplex A K).sc (m + 1)).homologyπ ≫
          ((dualComplex A K).sc (m + 1)).abHomologyIso.hom =
        AddCommGrpCat.ofHom (QuotientAddGroup.mk'
          (AddMonoidHom.range ((dualComplex A K).sc (m + 1)).abToCycles)) := by
    change
      ((dualComplex A K).sc (m + 1)).abLeftHomologyData.cyclesIso.inv ≫
          ((dualComplex A K).sc (m + 1)).homologyπ ≫
          ((dualComplex A K).sc (m + 1)).abLeftHomologyData.homologyIso.hom =
        ((dualComplex A K).sc (m + 1)).abLeftHomologyData.π
    rw [((dualComplex A K).sc (m + 1)).abLeftHomologyData.homologyπ_comp_homologyIso_hom,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact ConcreteCategory.congr_hom h c

/-- A literal incoming coboundary represents the zero cohomology class. -/
@[simp]
theorem positiveCocycleClass_abToCycles (m : ℕ)
    (b : ((dualComplex A K).sc (m + 1)).X₁) :
    positiveCocycleClass (dualComplex A K) m
        (((dualComplex A K).sc (m + 1)).abToCycles b) = 0 := by
  let e : (dualComplex A K).homology (m + 1) ≅
      AddCommGrpCat.of
        (PositiveCocycle (dualComplex A K) m ⧸
          AddMonoidHom.range ((dualComplex A K).sc (m + 1)).abToCycles) :=
    ((dualComplex A K).sc (m + 1)).abHomologyIso
  apply (AddCommGrpCat.mono_iff_injective
    e.hom).mp inferInstance
  rw [map_zero]
  change ((dualComplex A K).sc (m + 1)).abHomologyIso.hom
      (positiveCocycleClass (dualComplex A K) m
        (((dualComplex A K).sc (m + 1)).abToCycles b)) = 0
  rw [positiveCocycleClass_quotient]
  exact (QuotientAddGroup.eq_zero_iff
    (((dualComplex A K).sc (m + 1)).abToCycles b)).mpr ⟨b, rfl⟩

/-- Evaluation of a cohomology class represented by a concrete cocycle is literal cycle
evaluation. -/
@[simp]
theorem cohomologyEvaluation_positiveCocycleClass (m : ℕ)
    (c : PositiveCocycle (dualComplex A K) m) :
    cohomologyEvaluation A K m (positiveCocycleClass (dualComplex A K) m c) =
      positiveCocycleEvaluation A K m c := by
  change QuotientAddGroup.lift
      (AddMonoidHom.range ((dualComplex A K).sc (m + 1)).abToCycles)
      (positiveCocycleEvaluation A K m)
      (positiveCoboundaryRange_le_ker A K m)
      (((dualComplex A K).sc (m + 1)).abHomologyIso.hom
        (positiveCocycleClass (dualComplex A K) m c)) = _
  rw [positiveCocycleClass_quotient]
  exact QuotientAddGroup.lift_mk'
    (AddMonoidHom.range ((dualComplex A K).sc (m + 1)).abToCycles)
    (positiveCoboundaryRange_le_ker A K m) c

/-- The Kronecker evaluation of the class of a cocycle on the class of a cycle is the value of
the cochain on the cycle. -/
@[simp]
theorem cohomologyEvaluation_cocycle_cycle (m : ℕ)
    (c : PositiveCocycle (dualComplex A K) m)
    (z : HomologicalComplex.ChainCycleLift.Cycle K (m + 1)) :
    cohomologyEvaluation A K m (positiveCocycleClass (dualComplex A K) m c)
        (HomologicalComplex.ChainCycleLift.cycleClass K (m + 1) z) =
      cochainAddHom A K (m + 1)
        (positiveCocycleValue (C := dualComplex A K) m c) z.1 := by
  rw [cohomologyEvaluation_positiveCocycleClass,
    positiveCocycleEvaluation_cycleClass]

/-! ## Naturality -/

variable {K L : ChainComplex (ModuleCat.{v} ℤ) ℕ}

/-- The dual of a chain map acts by literal precomposition in every degree. -/
@[simp]
theorem dualMap_cochainAddHom_apply (f : K ⟶ L) (q : ℕ)
    (phi : (dualComplex A L).X q) (x : K.X q) :
    cochainAddHom A K q ((dualMap A f).f q phi) x =
      cochainAddHom A L q phi ((f.f q).hom x) := rfl

/-- Concrete cocycle evaluation commutes with a chain map and its contravariant dual. -/
theorem positiveCocycleEvaluation_natural (f : K ⟶ L) (m : ℕ)
    (c : PositiveCocycle (dualComplex A L) m) :
    positiveCocycleEvaluation A K m
        (mapPositiveCocycles (f := dualMap A f) m c) =
      precompose A (HomologicalComplex.homologyMap f (m + 1)).hom.toAddMonoidHom
        (positiveCocycleEvaluation A L m c) := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨z, rfl⟩ :=
    HomologicalComplex.ChainCycleLift.cycleClass_surjective K (m + 1) a
  rw [positiveCocycleEvaluation_cycleClass]
  change cochainAddHom A K (m + 1)
      (positiveCocycleValue (C := dualComplex A K) m
        (mapPositiveCocycles (f := dualMap A f) m c)) z.1 =
    positiveCocycleEvaluation A L m c
      ((HomologicalComplex.homologyMap f (m + 1)).hom
        (HomologicalComplex.ChainCycleLift.cycleClass K (m + 1) z))
  rw [HomologicalComplex.ChainCycleLift.homologyMap_cycleClass,
    positiveCocycleEvaluation_cycleClass]
  simp only [positiveCocycleValue_eq_literal_val, mapPositiveCocycles_val,
    HomologicalComplex.ChainCycleLift.mapCycles_val]
  rw [← positiveCocycleValue_eq_literal_val (C := dualComplex A L) m c]
  exact dualMap_cochainAddHom_apply A f (m + 1)
    (positiveCocycleValue (C := dualComplex A L) m c) z.1

/-- Kronecker evaluation is contravariantly natural for chain maps. -/
theorem cohomologyEvaluation_natural (f : K ⟶ L) (m : ℕ) :
    HomologicalComplex.homologyMap (dualMap A f) (m + 1) ≫
        cohomologyEvaluation A K m =
      cohomologyEvaluation A L m ≫
        AddCommGrpCat.ofHom
          (precompose A
            (HomologicalComplex.homologyMap f (m + 1)).hom.toAddMonoidHom) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  obtain ⟨c, rfl⟩ := positiveCocycleClass_surjective (dualComplex A L) m a
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply,
    homologyMap_positiveCocycleClass, cohomologyEvaluation_positiveCocycleClass,
    cohomologyEvaluation_positiveCocycleClass]
  exact positiveCocycleEvaluation_natural A f m c

/-! ## Local universal-coefficient splittings -/

namespace LocalUCT

section Algebra

variable {R : Type*} [Ring R]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- A projective codomain supplies a linear section of a surjection. -/
theorem exists_section (q : M →ₗ[R] N) [Module.Projective R N]
    (hq : Function.Surjective q) :
    ∃ s : N →ₗ[R] M, ∀ y, q (s y) = y := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q
    (LinearMap.id : N →ₗ[R] N) hq
  exact ⟨s, fun y ↦ LinearMap.congr_fun hs y⟩

/-- Projectivity of the image of a map splits its kernel. -/
theorem exists_kernel_retraction (d : M →ₗ[R] N)
    [Module.Projective R (LinearMap.range d)] :
    ∃ r : M →ₗ[R] LinearMap.ker d,
      ∀ z : LinearMap.ker d, r z = z := by
  obtain ⟨s, hs⟩ := exists_section d.rangeRestrict d.surjective_rangeRestrict
  let r₀ : M →ₗ[R] M := LinearMap.id - s.comp d.rangeRestrict
  have hr₀ (x : M) : r₀ x ∈ LinearMap.ker d := by
    change d (x - s (d.rangeRestrict x)) = 0
    rw [map_sub]
    have h := congrArg Subtype.val (hs (d.rangeRestrict x))
    change d (s (d.rangeRestrict x)) = d x at h
    rw [h, sub_self]
  refine ⟨r₀.codRestrict (LinearMap.ker d) hr₀, ?_⟩
  intro z
  apply Subtype.ext
  change z.1 - s (d.rangeRestrict z.1) = z.1
  have hz : d.rangeRestrict z.1 = 0 := Subtype.ext z.2
  rw [hz, map_zero, sub_zero]

/-- Every linear functional on a split kernel extends to the ambient module. -/
theorem exists_extension_from_kernel (d : M →ₗ[R] N)
    [Module.Projective R (LinearMap.range d)]
    (phi : LinearMap.ker d →ₗ[R] P) :
    ∃ psi : M →ₗ[R] P, ∀ z : LinearMap.ker d, psi z = phi z := by
  obtain ⟨r, hr⟩ := exists_kernel_retraction d
  exact ⟨phi.comp r, fun z ↦ congrArg phi (hr z)⟩

/-- A functional annihilating a kernel factors through the actual image. -/
theorem exists_factor_through_range (d : M →ₗ[R] N) (phi : M →ₗ[R] P)
    (hphi : LinearMap.ker d ≤ LinearMap.ker phi) :
    ∃ psi : LinearMap.range d →ₗ[R] P, psi.comp d.rangeRestrict = phi := by
  let psi := ((LinearMap.ker d).liftQ phi hphi).comp d.quotKerEquivRange.symm.toLinearMap
  refine ⟨psi, ?_⟩
  ext x
  change (LinearMap.ker d).liftQ phi hphi
    (d.quotKerEquivRange.symm ⟨d x, LinearMap.mem_range_self d x⟩) = phi x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

end Algebra

/-- An additive homomorphism between integral modules is automatically integral-linear, even when
the displayed module structures are not definitionally the canonical ones. -/
def addHomToIntLinear {M P : Type*} [AddCommGroup M] [AddCommGroup P]
    [modM : Module ℤ M] [modP : Module ℤ P] (q : M →+ P) : M →ₗ[ℤ] P where
  toFun := q
  map_add' := q.map_add
  map_smul' z x := by
    change q (modM.smul z x) = modP.smul z (q x)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
    exact q.map_zsmul z x

/-- Additive homomorphisms between integral modules and integral-linear maps are canonically
additively equivalent.  The construction works for arbitrary displayed integral-module
structures, not only definitionally canonical ones. -/
def addHomIntLinearEquiv (M P : Type*) [AddCommGroup M] [AddCommGroup P]
    [Module ℤ M] [Module ℤ P] : (M →+ P) ≃+ (M →ₗ[ℤ] P) where
  toFun := fun q ↦ addHomToIntLinear (modM := inferInstance) (modP := inferInstance) q
  invFun := fun q ↦ q.toAddMonoidHom
  left_inv _ := rfl
  right_inv q := by
    apply LinearMap.ext
    intro x
    rfl
  map_add' q r := by ext; rfl

/-- The equivalence between additive maps and `ℤ`-linear maps does not change the underlying
function. -/
@[simp]
theorem addHomIntLinearEquiv_apply (M P : Type*) [AddCommGroup M] [AddCommGroup P]
    [Module ℤ M] [Module ℤ P] (q : M →+ P) (x : M) :
    addHomIntLinearEquiv M P q x = q x := by
  simp only [addHomIntLinearEquiv]
  rfl

open HomologicalComplex.ChainCycleLift

variable (J : ChainComplex (ModuleCat.{v} ℤ) ℕ) (n : ℕ)

/-- The image of the outgoing differential in degree `n`. -/
abbrev OutgoingImage :=
  LinearMap.range (J.d n ((ComplexShape.down ℕ).next n)).hom

local instance outgoingImageModule : Module ℤ (OutgoingImage J n) :=
  (OutgoingImage J n).module

/-- The image of the incoming differential in degree `n`. -/
abbrev IncomingImage := LinearMap.range (J.d (n + 1) n).hom

local instance incomingImageModule : Module ℤ (IncomingImage J n) :=
  (IncomingImage J n).module

/-- An incoming boundary as a concrete cycle. -/
def boundaryCycle (b : J.X (n + 1)) : Cycle J n :=
  ⟨(J.d (n + 1) n).hom b, by
    have hdd := J.d_comp_d (n + 1) n ((ComplexShape.down ℕ).next n)
    exact ConcreteCategory.congr_hom hdd b⟩

/-- The underlying element of the cycle attached to a boundary is that boundary. -/
@[simp]
theorem boundaryCycle_val (b : J.X (n + 1)) :
    (boundaryCycle J n b).1 = (J.d (n + 1) n).hom b := rfl

/-- A boundary has vanishing homology class. -/
@[simp]
theorem cycleClass_boundaryCycle (b : J.X (n + 1)) :
    cycleClass J n (boundaryCycle J n b) = 0 :=
  (cycleClass_eq_zero_iff J n (boundaryCycle J n b)).mpr ⟨b, rfl⟩

/-- A predecessor functional in the normalized positive-degree short complex. -/
def normalizedPreviousLinearCochain (A : AddCommGrpCat.{w})
    (psi : J.X n →ₗ[ℤ] A) :
    ((dualComplex A J).sc' n (n + 1) (n + 1 + 1)).X₁ := by
  change (dualComplex A J).X n
  exact linearCochain A J n psi

/-- The same predecessor functional transported to the native short complex. -/
def previousLinearCochain (A : AddCommGrpCat.{w}) (psi : J.X n →ₗ[ℤ] A) :
    ((dualComplex A J).sc (n + 1)).X₁ :=
  (normalizedPositiveScIso (dualComplex A J) n).inv.τ₁
    (normalizedPreviousLinearCochain J n A psi)

/-- The value of the coboundary represented by a predecessor functional. -/
theorem positiveCocycleValue_abToCycles_previousLinearCochain
    (A : AddCommGrpCat.{w}) (psi : J.X n →ₗ[ℤ] A) :
    positiveCocycleValue (C := dualComplex A J) n
        (((dualComplex A J).sc (n + 1)).abToCycles
          (previousLinearCochain J n A psi)) =
      ((dualComplex A J).sc' n (n + 1) (n + 1 + 1)).f
        (normalizedPreviousLinearCochain J n A psi) := by
  let E := normalizedPositiveScIso (dualComplex A J) n
  let psi' := normalizedPreviousLinearCochain J n A psi
  let b := previousLinearCochain J n A psi
  rw [positiveCocycleValue_eq_val]
  change E.hom.τ₂ (((dualComplex A J).sc (n + 1)).f b) =
    ((dualComplex A J).sc' n (n + 1) (n + 1 + 1)).f psi'
  have hcomm := ConcreteCategory.congr_hom E.hom.comm₁₂ b
  change ((dualComplex A J).sc' n (n + 1) (n + 1 + 1)).f (E.hom.τ₁ b) =
    E.hom.τ₂ (((dualComplex A J).sc (n + 1)).f b) at hcomm
  have hτ := congrArg ShortComplex.Hom.τ₁ E.inv_hom_id
  have hinv := ConcreteCategory.congr_hom hτ psi'
  change E.hom.τ₁ (E.inv.τ₁ psi') = psi' at hinv
  have hb : E.hom.τ₁ b = psi' := by
    exact hinv
  rw [hb] at hcomm
  exact hcomm.symm

/-- The coboundary of a functional `ψ` in degree `n` evaluates on a chain `x` as `ψ (∂x)`. -/
@[simp]
theorem positiveCocycleValue_abToCycles_previousLinearCochain_apply
    (A : AddCommGrpCat.{w}) (psi : J.X n →ₗ[ℤ] A) (x : J.X (n + 1)) :
    cochainAddHom A J (n + 1)
        (positiveCocycleValue (C := dualComplex A J) n
          (((dualComplex A J).sc (n + 1)).abToCycles
            (previousLinearCochain J n A psi))) x =
      psi ((J.d (n + 1) n).hom x) := by
  rw [positiveCocycleValue_abToCycles_previousLinearCochain]
  rfl

/-- The cycle inclusion splits when the outgoing image is projective. -/
theorem exists_cycle_retraction [Module.Projective ℤ (OutgoingImage J n)] :
    ∃ r : J.X n →ₗ[ℤ] Cycle J n, ∀ z : Cycle J n, r z = z :=
  exists_kernel_retraction (J.d n ((ComplexShape.down ℕ).next n)).hom

/-- A functional on cycles extends when the outgoing image is projective. -/
theorem exists_extension_from_cycles (A : AddCommGrpCat.{w})
    [Module.Projective ℤ (OutgoingImage J n)]
    (phi : Cycle J n →ₗ[ℤ] A) :
    ∃ psi : J.X n →ₗ[ℤ] A, ∀ z : Cycle J n, psi z = phi z :=
  exists_extension_from_kernel (J.d n ((ComplexShape.down ℕ).next n)).hom phi

/-- Every homology functional is represented by a genuine cocycle when the outgoing image in
that degree is projective. -/
theorem cohomologyEvaluation_surjective_of_outgoing_projective
    (A : AddCommGrpCat.{w}) [Module.Projective ℤ (OutgoingImage J (n + 1))] :
    Function.Surjective (cohomologyEvaluation A J n).hom := by
  intro phi
  let phiLin : J.homology (n + 1) →ₗ[ℤ] A := addHomToIntLinear phi
  obtain ⟨psi, hpsi⟩ := exists_extension_from_cycles J (n + 1) A
    (phiLin.comp (cycleClass J (n + 1)))
  have hclosed : IsClosedFunctional A J (n + 1) psi := by
    intro b
    have h := hpsi (boundaryCycle J (n + 1) b)
    simpa only [boundaryCycle_val, LinearMap.comp_apply, cycleClass_boundaryCycle,
      map_zero] using h
  let c := mkPositiveCocycleOfClosed A J n psi hclosed
  refine ⟨positiveCocycleClass (dualComplex A J) n c, ?_⟩
  apply AddMonoidHom.ext
  intro a
  obtain ⟨z, rfl⟩ := cycleClass_surjective J (n + 1) a
  rw [cohomologyEvaluation_positiveCocycleClass,
    positiveCocycleEvaluation_cycleClass,
    positiveCocycleValue_mkPositiveCocycleOfClosed]
  change psi z.1 = phi (cycleClass J (n + 1) z)
  rw [hpsi]
  rfl

/-- Projectivity of homology supplies a linear choice of cycle representatives. -/
theorem exists_cycle_section [Module.Projective ℤ (J.homology n)] :
    ∃ s : J.homology n →ₗ[ℤ] Cycle J n,
      ∀ a, cycleClass J n (s a) = a :=
  exists_section (cycleClass J n) (cycleClass_surjective J n)

/-- Under the two local projectivity hypotheses, boundaries split inside chains. -/
theorem exists_boundary_retraction [Module.Projective ℤ (OutgoingImage J n)]
    [Module.Projective ℤ (J.homology n)] :
    ∃ r : J.X n →ₗ[ℤ] IncomingImage J n,
      ∀ b : IncomingImage J n, r b = b := by
  obtain ⟨r, hr⟩ := exists_cycle_retraction J n
  obtain ⟨s, hs⟩ := exists_cycle_section J n
  let t : J.X n →ₗ[ℤ] Cycle J n := r - s.comp ((cycleClass J n).comp r)
  have ht (x : J.X n) : cycleClass J n (t x) = 0 := by
    change cycleClass J n (r x - s (cycleClass J n (r x))) = 0
    rw [map_sub, hs, sub_self]
  let t₀ : J.X n →ₗ[ℤ] J.X n := (Cycle J n).subtype.comp t
  have ht₀ (x : J.X n) : t₀ x ∈ IncomingImage J n := by
    obtain ⟨b, hb⟩ := (cycleClass_eq_zero_iff J n (t x)).mp (ht x)
    exact ⟨b, hb⟩
  refine ⟨t₀.codRestrict (IncomingImage J n) ht₀, ?_⟩
  rintro ⟨_, ⟨b, rfl⟩⟩
  apply Subtype.ext
  change (r ((J.d (n + 1) n).hom b) -
    s (cycleClass J n (r ((J.d (n + 1) n).hom b)))).1 = (J.d (n + 1) n).hom b
  let boundary : Cycle J n := ⟨(J.d (n + 1) n).hom b, by
    have hdd := J.d_comp_d (n + 1) n ((ComplexShape.down ℕ).next n)
    exact ConcreteCategory.congr_hom hdd b⟩
  have hrb := hr boundary
  have hclass : cycleClass J n boundary = 0 :=
    (cycleClass_eq_zero_iff J n boundary).mpr ⟨b, rfl⟩
  change r ((J.d (n + 1) n).hom b) = boundary at hrb
  rw [hrb, hclass, map_zero, sub_zero]

/-- A functional vanishing on all `(n+1)`-cycles is an actual coboundary when the preceding
outgoing image and homology are projective. -/
theorem exists_coboundary_of_vanishing_on_cycles (A : AddCommGrpCat.{w})
    [Module.Projective ℤ (OutgoingImage J n)] [Module.Projective ℤ (J.homology n)]
    (phi : J.X (n + 1) →ₗ[ℤ] A)
    (hphi : ∀ z : Cycle J (n + 1), phi z.1 = 0) :
    ∃ psi : J.X n →ₗ[ℤ] A, psi.comp (J.d (n + 1) n).hom = phi := by
  have hker : LinearMap.ker (J.d (n + 1) n).hom ≤ LinearMap.ker phi := by
    intro x hx
    exact hphi ⟨x, by
      change (J.d (n + 1) ((ComplexShape.down ℕ).next (n + 1))).hom x = 0
      rw [ChainComplex.next_nat_succ]
      exact hx⟩
  obtain ⟨psi₀, hpsi₀⟩ :=
    exists_factor_through_range (J.d (n + 1) n).hom phi hker
  obtain ⟨r, hr⟩ := exists_boundary_retraction J n
  refine ⟨psi₀.comp r, ?_⟩
  ext x
  change psi₀ (r ((J.d (n + 1) n).hom x)) = phi x
  have hrx := hr ((J.d (n + 1) n).hom.rangeRestrict x)
  change r ((J.d (n + 1) n).hom x) =
    (J.d (n + 1) n).hom.rangeRestrict x at hrx
  rw [hrx]
  exact LinearMap.congr_fun hpsi₀ x

/-- Evaluation in degree `n+1` is injective when the preceding outgoing image and homology are
projective.  This is the chain-level vanishing of the UCT `Ext¹(Hₙ, A)` term. -/
theorem cohomologyEvaluation_injective_of_local_projective
    (A : AddCommGrpCat.{w}) [Module.Projective ℤ (OutgoingImage J n)]
    [Module.Projective ℤ (J.homology n)] :
    Function.Injective (cohomologyEvaluation A J n).hom := by
  intro a b hab
  have hz : (cohomologyEvaluation A J n).hom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ :=
    positiveCocycleClass_surjective (dualComplex A J) n (a - b)
  have hvanish (z : Cycle J (n + 1)) :
      cochainAddHom A J (n + 1)
        (positiveCocycleValue (C := dualComplex A J) n c) z.1 = 0 := by
    have h := congrArg (fun q : J.homology (n + 1) →+ A ↦
      q (cycleClass J (n + 1) z)) hz
    rw [← hc, cohomologyEvaluation_cocycle_cycle] at h
    exact h
  obtain ⟨psi, hpsi⟩ := exists_coboundary_of_vanishing_on_cycles J n A
    (cochainLinear A J (n + 1)
      (positiveCocycleValue (C := dualComplex A J) n c)) (by
        intro z
        exact hvanish z)
  let b' := previousLinearCochain J n A psi
  let cb : PositiveCocycle (dualComplex A J) n :=
    ((dualComplex A J).sc (n + 1)).abToCycles b'
  have hvalues : positiveCocycleValue (C := dualComplex A J) n c =
      positiveCocycleValue (C := dualComplex A J) n cb := by
    apply AddMonoidHom.ext
    intro x
    change cochainAddHom A J (n + 1)
        (positiveCocycleValue (C := dualComplex A J) n c) x =
      cochainAddHom A J (n + 1)
        (positiveCocycleValue (C := dualComplex A J) n cb) x
    rw [show cochainAddHom A J (n + 1)
        (positiveCocycleValue (C := dualComplex A J) n cb) x =
          psi ((J.d (n + 1) n).hom x) by
      exact positiveCocycleValue_abToCycles_previousLinearCochain_apply J n A psi x]
    have hx := LinearMap.congr_fun hpsi x
    exact hx.symm
  have hc_eq : c = cb := by
    apply Subtype.ext
    apply (AddCommGrpCat.mono_iff_injective
      (normalizedPositiveScIso (dualComplex A J) n).hom.τ₂).mp inferInstance
    apply AddMonoidHom.ext
    intro x
    change cochainAddHom A J (n + 1)
        ((normalizedPositiveScIso (dualComplex A J) n).hom.τ₂ c.1) x =
      cochainAddHom A J (n + 1)
        ((normalizedPositiveScIso (dualComplex A J) n).hom.τ₂ cb.1) x
    have hx := congrArg (fun phi : (dualComplex A J).X (n + 1) ↦
      cochainAddHom A J (n + 1) phi x) hvalues
    simpa only [positiveCocycleValue_eq_val] using hx
  have hc_zero : positiveCocycleClass (dualComplex A J) n c = 0 := by
    rw [hc_eq]
    exact positiveCocycleClass_abToCycles A J n b'
  exact sub_eq_zero.mp (hc.symm.trans hc_zero)

/-- The local chain-level universal-coefficient theorem: the canonical evaluation is bijective
under precisely the two image-projectivity conditions used to extend cochains, together with
projectivity of the preceding homology that kills the `Ext¹` obstruction. -/
theorem cohomologyEvaluation_bijective_of_local_projective
    (A : AddCommGrpCat.{w}) [Module.Projective ℤ (OutgoingImage J n)]
    [Module.Projective ℤ (OutgoingImage J (n + 1))]
    [Module.Projective ℤ (J.homology n)] :
    Function.Bijective (cohomologyEvaluation A J n).hom :=
  ⟨cohomologyEvaluation_injective_of_local_projective J n A,
    cohomologyEvaluation_surjective_of_outgoing_projective J n A⟩

/-- Categorical form of the local UCT isomorphism. -/
theorem cohomologyEvaluation_isIso_of_local_projective
    (A : AddCommGrpCat.{w}) [Module.Projective ℤ (OutgoingImage J n)]
    [Module.Projective ℤ (OutgoingImage J (n + 1))]
    [Module.Projective ℤ (J.homology n)] :
    IsIso (cohomologyEvaluation A J n) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact cohomologyEvaluation_bijective_of_local_projective J n A

end LocalUCT

end DualEvaluation

end AlgebraicTopology.SingularCochains
