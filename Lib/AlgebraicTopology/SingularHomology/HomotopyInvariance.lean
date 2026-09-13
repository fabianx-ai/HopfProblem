/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris

/-!
# Homotopy invariance of singular homology

Homotopic maps of spaces induce the same map on singular homology, so a homotopy equivalence
induces an isomorphism (Hatcher, Theorem 2.10):

* `SingularHomology.homotopic_homologyMap` — the headline statement: homotopic maps
  induce equal maps on singular homology.

Consequences: homotopy equivalences and homeomorphisms induce homology isomorphisms
(`homotopyEquivHomologyEquiv`, `homeomorphHomologyEquiv`), and homology vanishes on totally
disconnected, one-point, and contractible spaces, with the two null-homotopy lemmas
`Suspension.singularHomologyMap_const_eq_zero` and
`singularHomologyMap_eq_zero_of_nullhomotopic`.

## Outline of the proof

1. *Chain homotopy.*  `singularChainHomotopy f g H n` is a degree-`n+1` chain whose boundary
   is `g_# − f_#` on `n`-cycles; `homotopy_homologyMap` turns the identity into an equality
   of homology maps.
2. *Equivalences.*  `homotopyEquivHomologyEquiv` (a homotopy equivalence gives a homology
   equivalence), `homeomorphHomologyEquiv` (a homeomorphism gives a homology equivalence,
   functorial: `homeomorphHomologyEquiv_refl`, `_trans`, `_symm_apply`).
3. *Vanishing.*  `connectedHomologyZeroEquiv`, `pointHomologyZeroEquiv`,
   `contractibleHomologyEquivPoint` and the subsingleton corollaries
   (`totallyDisconnected_homology_subsingleton`, `point_homology_subsingleton`,
   `contractible_homology_subsingleton`).
4. *Null-homotopy.*  `Suspension.singularHomologyMap_const_eq_zero` and
   `singularHomologyMap_eq_zero_of_nullhomotopic`: a constant or null-homotopic map
   annihilates positive-degree homology maps.

## Main definitions and results

* `SingularHomology.homotopic_homologyMap` : homotopy invariance (Hatcher Thm 2.10).
* `SingularHomology.homotopyEquivHomologyEquiv`, `.homeomorphHomologyEquiv` :
  homology equivalences from equivalences.
* `Suspension.singularHomologyMap_eq_zero_of_nullhomotopic` : null-homotopy kills
  positive-degree homology maps.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorem 2.10

## Tags

homotopy invariance, chain homotopy, homology equivalence
-/



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

/-! ### Functoriality and homotopy invariance -/

/-- The identity map induces the identity on singular homology. -/
@[simp]
theorem SingularHomology.singularHomologyMap_id (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.id X) n = LinearMap.id := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map_id
      (TopCat.of X)
  exact congrArg ModuleCat.Hom.hom h

/-- Singular homology is functorial in continuous maps. -/
theorem SingularHomology.singularHomologyMap_comp {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (g.comp f) n =
      (SingularMayerVietoris.singularHomologyMap g n).comp
        (SingularMayerVietoris.singularHomologyMap f n) := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom f) (TopCat.ofHom g)
  exact congrArg ModuleCat.Hom.hom h

/-- A homotopy of maps induces a chain homotopy of singular chain maps. -/
def SingularHomology.singularChainHomotopy {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} (H : f.Homotopy g) :
    _root_.Homotopy (SingularChains.singularChainMap f) (SingularChains.singularChainMap g) :=
  TopCat.Homotopy.singularChainComplexFunctorObjMap (f := TopCat.ofHom f) (g := TopCat.ofHom g) H
    (ModuleCat.of ℤ ℤ)

/-- Homotopic maps induce the same map on singular homology. -/
theorem SingularHomology.homotopy_homologyMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} (H : f.Homotopy g) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap f n =
      SingularMayerVietoris.singularHomologyMap g n :=
  congrArg ModuleCat.Hom.hom ((singularChainHomotopy H).homologyMap_eq n)

/-- Maps related by a homotopy induce equal homology maps. -/
theorem SingularHomology.homotopic_homologyMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} (h : f.Homotopic g) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap f n =
      SingularMayerVietoris.singularHomologyMap g n := by
  obtain ⟨H⟩ := h
  exact homotopy_homologyMap H n

/-! ### Homology equivalences -/

/-- A homotopy inverse pair induces a linear equivalence of singular homology groups. -/
def SingularHomology.homotopyInverseHomologyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (g : C(Y, X))
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology Y n
    where
  toLinearMap := SingularMayerVietoris.singularHomologyMap f n
  invFun := SingularMayerVietoris.singularHomologyMap g n
  left_inv
    a := by
    have h := homotopic_homologyMap hgf n
    rw [singularHomologyMap_comp, singularHomologyMap_id] at h
    exact LinearMap.congr_fun h a
  right_inv
    a := by
    have h := homotopic_homologyMap hfg n
    rw [singularHomologyMap_comp, singularHomologyMap_id] at h
    exact LinearMap.congr_fun h a

/-- A homotopy equivalence induces a linear equivalence of singular homology groups. -/
def SingularHomology.homotopyEquivHomologyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology Y n :=
  homotopyInverseHomologyEquiv e.toFun e.invFun e.left_inv e.right_inv n

/-- The homology equivalence of a homotopy equivalence is the induced homology map. -/
@[simp]
theorem SingularHomology.homotopyEquivHomologyEquiv_toLinearMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ) :
    (homotopyEquivHomologyEquiv e n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap e.toFun n :=
  rfl

/-- The homology equivalence applies the induced homology map. -/
@[simp]
theorem SingularHomology.homotopyEquivHomologyEquiv_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    homotopyEquivHomologyEquiv e n a = SingularMayerVietoris.singularHomologyMap e.toFun n a :=
  rfl

/-- The inverse homology equivalence applies the inverse map's induced map. -/
@[simp]
theorem SingularHomology.homotopyEquivHomologyEquiv_symm_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology Y n) :
    (homotopyEquivHomologyEquiv e n).symm a =
      SingularMayerVietoris.singularHomologyMap e.symm.toFun n a :=
  rfl

/-- A homeomorphism induces a linear equivalence of singular homology groups. -/
def SingularHomology.homeomorphHomologyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology Y n :=
  homotopyEquivHomologyEquiv e.toHomotopyEquiv n

/-- The homology equivalence of a homeomorphism is its induced homology map. -/
@[simp]
theorem SingularHomology.homeomorphHomologyEquiv_toLinearMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) :
    (homeomorphHomologyEquiv e n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap (e : C(X, Y)) n :=
  rfl

/-- The homeomorphism-induced equivalence applies the induced homology map. -/
@[simp]
theorem SingularHomology.homeomorphHomologyEquiv_apply {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    homeomorphHomologyEquiv e n a = SingularMayerVietoris.singularHomologyMap (e : C(X, Y)) n a :=
  rfl

/-- The inverse homeomorphism-induced equivalence applies the inverse's induced map. -/
@[simp]
theorem SingularHomology.homeomorphHomologyEquiv_symm_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology Y n) :
    (homeomorphHomologyEquiv e n).symm a =
      SingularMayerVietoris.singularHomologyMap (e.symm : C(Y, X)) n a :=
  rfl

/-- The inverse of the induced equivalence is the equivalence of the inverse. -/
@[simp]
theorem SingularHomology.homeomorphHomologyEquiv_symm {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) :
    (homeomorphHomologyEquiv e n).symm = homeomorphHomologyEquiv e.symm n := by
  apply LinearEquiv.ext
  intro a
  rfl

/-- The identity homeomorphism induces the identity equivalence on homology. -/
@[simp]
theorem SingularHomology.homeomorphHomologyEquiv_refl (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    homeomorphHomologyEquiv (Homeomorph.refl X) n =
      LinearEquiv.refl ℤ (SingularMayerVietoris.SingularHomology X n) := by
  apply LinearEquiv.ext
  intro a
  change SingularMayerVietoris.singularHomologyMap (ContinuousMap.id X) n a = a
  rw [singularHomologyMap_id]
  rfl

/-- Induced homology equivalences compose with homeomorphism composition. -/
theorem SingularHomology.homeomorphHomologyEquiv_trans {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (e : X ≃ₜ Y) (f : Y ≃ₜ Z)
    (n : ℕ) :
    homeomorphHomologyEquiv (e.trans f) n =
      (homeomorphHomologyEquiv e n).trans (homeomorphHomologyEquiv f n) := by
  apply LinearEquiv.ext
  intro a
  change
    SingularMayerVietoris.singularHomologyMap ((f : C(Y, Z)).comp (e : C(X, Y))) n a =
      SingularMayerVietoris.singularHomologyMap (f : C(Y, Z)) n
        (SingularMayerVietoris.singularHomologyMap (e : C(X, Y)) n a)
  rw [singularHomologyMap_comp]
  rfl

/-! ### Elementary homology computations -/

/-- The zeroth singular homology of a path-connected space is `ℤ`. -/
def SingularHomology.connectedHomologyZeroEquiv (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : SingularMayerVietoris.SingularHomology X 0 ≃ₗ[ℤ] ℤ :=
  (CategoryTheory.asIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv

/-- Positive-degree singular homology of a totally disconnected space vanishes. -/
theorem SingularHomology.totallyDisconnected_homology_isZero (X : Type)
    [TopologicalSpace X] [TotallyDisconnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (SingularMayerVietoris.SingularHomology X n) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat ℤ) n
    (ModuleCat.of ℤ ℤ) (TopCat.of X) hn

/-- Positive-degree singular homology of a totally disconnected space is a subsingleton. -/
theorem SingularHomology.totallyDisconnected_homology_subsingleton (X : Type)
    [TopologicalSpace X] [TotallyDisconnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology X n) :=
  ModuleCat.subsingleton_of_isZero (totallyDisconnected_homology_isZero X n hn)

/-- The zeroth singular homology of a point is `ℤ`. -/
abbrev SingularHomology.pointHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology Unit 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv Unit

/-- Positive-degree singular homology of a point is a subsingleton. -/
theorem SingularHomology.point_homology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology Unit n) :=
  totallyDisconnected_homology_subsingleton Unit n hn

/-- A contractible space has the singular homology of a point. -/
def SingularHomology.contractibleHomologyEquivPoint (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology Unit n :=
  homotopyEquivHomologyEquiv (Classical.choice (ContractibleSpace.hequiv_unit X)) n

/-- Positive-degree singular homology of a contractible space is a subsingleton. -/
theorem SingularHomology.contractible_homology_subsingleton (X : Type)
    [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology X n) := by
  let := point_homology_subsingleton n hn
  exact (contractibleHomologyEquivPoint X n).injective.subsingleton

/-- A constant map induces zero on positive-degree singular homology. -/
theorem Suspension.singularHomologyMap_const_eq_zero {Y : Type} [TopologicalSpace Y]
    (X : Type) [TopologicalSpace X] (y : Y) (n : ℕ) (hn : n ≠ 0) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X y) n = 0 := by
  let := SingularHomology.point_homology_subsingleton n hn
  change
    SingularMayerVietoris.singularHomologyMap
        ((ContinuousMap.const Unit y).comp (ContinuousMap.const X ())) n =
      0
  rw [SingularHomology.singularHomologyMap_comp]
  ext a
  change
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.const Unit y) n
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X ()) n a) =
      0
  rw [Subsingleton.elim (SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X ()) n a)
      (0 : SingularMayerVietoris.SingularHomology Unit n),
    map_zero]

/-- A nullhomotopic map induces zero on positive-degree singular homology. -/
theorem Suspension.singularHomologyMap_eq_zero_of_nullhomotopic {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (hf : f.Nullhomotopic) (n : ℕ)
    (hn : n ≠ 0) : SingularMayerVietoris.singularHomologyMap f n = 0 := by
  obtain ⟨y, hy⟩ := hf
  rw [SingularHomology.homotopic_homologyMap hy n]
  exact singularHomologyMap_const_eq_zero X y n hn
end Mathoverflow1973
