/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.Homotopy.CocycleEvaluation
public import Lib.AlgebraicTopology.SingularCochains
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Positive-degree primitives for singular cochains

The singular cochain complex of a point is exact in every positive degree: a point is
totally disconnected, so its singular chain complex is homotopy equivalent to the free
module on the point concentrated in degree `0`, and dualising an additive homotopy
equivalence gives one again.  Combining this with cochain homotopy shows that the pullback
of a positive-degree cocycle along a nullhomotopic map is a coboundary.  Everything is
stated for an arbitrary coefficient group.

## Main results

* `AlgebraicTopology.SingularCochains.pointCochain_exactAt_positive` : the cochain complex
  of a point is exact in every positive degree.
* `AlgebraicTopology.SingularCochains.pointCocycle_boundary` : a positive-degree cocycle on
  a point is a coboundary.
* `AlgebraicTopology.SingularCochains.nullhomotopic_pullback_closed_succ` : the pullback of a
  positive-degree cocycle along a nullhomotopic map is a coboundary.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.1 (the cohomology of a point vanishes
  in positive degrees)
* `Mathlib/Algebra/Homology/AlternatingConst.lean` for the chain complex of a point

## Tags

singular cohomology, cocycle, coboundary, nullhomotopic, contractible
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicTopology.SingularCochains

private abbrev pointFreeModule : ModuleCat.{0} ℤ :=
  ∐ fun _ : Unit ↦ ModuleCat.of ℤ ℤ

private noncomputable def pointChainHomotopyEquiv :
    HomotopyEquiv (chains Unit)
      ((ChainComplex.single₀ (ModuleCat.{0} ℤ)).obj pointFreeModule) :=
  (HomotopyEquiv.ofIso
      (AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
        (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) (TopCat.of Unit))).trans
    (ChainComplex.alternatingConstHomotopyEquiv pointFreeModule)

private noncomputable def dualHomotopyEquiv
    (A : AddCommGrpCat.{0}) {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (e : HomotopyEquiv K L) :
    HomotopyEquiv (dualComplex A L) (dualComplex A K) where
  hom := dualMap A e.hom
  inv := dualMap A e.inv
  homotopyHomInvId := by
    simpa only [dualMap_comp, dualMap_id] using dualHomotopy A e.homotopyInvHomId
  homotopyInvHomId := by
    simpa only [dualMap_comp, dualMap_id] using dualHomotopy A e.homotopyHomInvId

private noncomputable def pointCochainHomotopyEquiv (A : AddCommGrpCat.{0}) :
    HomotopyEquiv
      (dualComplex A ((ChainComplex.single₀ (ModuleCat.{0} ℤ)).obj pointFreeModule))
      (complex Unit A) :=
  dualHomotopyEquiv A pointChainHomotopyEquiv

private theorem dualPointSingle_exactAt (A : AddCommGrpCat.{0}) (n : ℕ)
    (hn : n ≠ 0) :
    (dualComplex A
      ((ChainComplex.single₀ (ModuleCat.{0} ℤ)).obj pointFreeModule)).ExactAt n := by
  apply HomologicalComplex.ExactAt.of_isZero
  let hzero := HomologicalComplex.isZero_single_obj_X
    (ComplexShape.down ℕ) 0 pointFreeModule n hn
  let _ : Subsingleton
      (((ChainComplex.single₀ (ModuleCat.{0} ℤ)).obj pointFreeModule).X n : Type) :=
    ModuleCat.subsingleton_of_isZero hzero
  change IsZero (AddCommGrpCat.of
    ((((ChainComplex.single₀ (ModuleCat.{0} ℤ)).obj pointFreeModule).X n : Type) →+ A))
  apply AddCommGrpCat.isZero_of_subsingleton

/-- Native singular cochains on a point are exact in every positive degree. -/
theorem pointCochain_exactAt_positive (A : AddCommGrpCat.{0}) (n : ℕ)
    (hn : n ≠ 0) : (complex Unit A).ExactAt n := by
  let E := pointCochainHomotopyEquiv A
  exact (quasiIsoAt_iff_exactAt E.hom n (dualPointSingle_exactAt A n hn)).mp
    (E.quasiIsoAt_hom n)

/-- Every positive-degree cocycle on a point has an actual primitive. -/
theorem pointCocycle_boundary (A : AddCommGrpCat.{0}) (n : ℕ)
    (c : (complex Unit A).X (n + 1))
    (hc : (complex Unit A).d (n + 1) (n + 2) c = 0) :
    ∃ b : (complex Unit A).X n, (complex Unit A).d n (n + 1) b = c := by
  have hexact := pointCochain_exactAt_positive A (n + 1) (by omega)
  rw [HomologicalComplex.exactAt_iff' (complex Unit A) n (n + 1) (n + 2)
      (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1)),
    ShortComplex.ab_exact_iff] at hexact
  exact hexact c hc

/-- A cochain map commutes with consecutive positive differentials on elements. -/
private theorem cochainMap_d_succ {K L : CochainComplex AddCommGrpCat.{u} ℕ}
    (f : K ⟶ L) (n : ℕ) (c : K.X (n + 1)) :
    L.d (n + 1) (n + 2) (f.f (n + 1) c) =
      f.f (n + 2) (K.d (n + 1) (n + 2) c) :=
  congrArg (fun k : K.X (n + 1) ⟶ L.X (n + 2) => k c) (f.comm (n + 1) (n + 2))

/-- Pullback preserves a native cocycle equation in consecutive degrees. -/
private theorem pullback_closed_succ {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{0}) (f : C(X, Y)) (n : ℕ)
    (c : (complex Y A).X (n + 1))
    (hc : (complex Y A).d (n + 1) (n + 2) c = 0) :
    (complex X A).d (n + 1) (n + 2) ((pullback A f).f (n + 1) c) = 0 := by
  rw [cochainMap_d_succ (pullback A f), hc, map_zero]

/-- Pullback along a nullhomotopic map sends every positive cocycle to an actual coboundary. -/
theorem nullhomotopic_pullback_closed_succ {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{0}) (f : C(X, Y)) (hf : f.Nullhomotopic)
    (n : ℕ) (c : (complex Y A).X (n + 1))
    (hc : (complex Y A).d (n + 1) (n + 2) c = 0) :
    ∃ b : (complex X A).X n,
      (complex X A).d n (n + 1) b = (pullback A f).f (n + 1) c := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  let p : C(X, Unit) := ContinuousMap.const X ()
  let q : C(Unit, Y) := ContinuousMap.const Unit y
  let cPoint := (pullback A q).f (n + 1) c
  have hcPoint : (complex Unit A).d (n + 1) (n + 2) cPoint = 0 :=
    pullback_closed_succ A q n c hc
  obtain ⟨bPoint, hbPoint⟩ := pointCocycle_boundary A n cPoint hcPoint
  let h := pullbackHomotopy A H
  refine ⟨h.hom (n + 1) n c + (pullback A p).f n bPoint, ?_⟩
  rw [map_add]
  have hd := congrArg
    (fun k : (complex Unit A).X n ⟶ (complex X A).X (n + 1) => k bPoint)
    ((pullback A p).comm n (n + 1))
  change (complex X A).d n (n + 1) ((pullback A p).f n bPoint) =
    (pullback A p).f (n + 1) ((complex Unit A).d n (n + 1) bPoint) at hd
  rw [hd, hbPoint]
  have hcomp := pullback_comp A p q
  have happ := ConcreteCategory.congr_hom
    (congrArg (fun t : complex Y A ⟶ complex X A => t.f (n + 1)) hcomp) c
  change (pullback A (ContinuousMap.const X y)).f (n + 1) c =
    (pullback A p).f (n + 1) cPoint at happ
  have he := CochainComplex.homotopy_on_cocycle_succ h n c hc
  rw [happ] at he
  exact he.symm

end AlgebraicTopology.SingularCochains
