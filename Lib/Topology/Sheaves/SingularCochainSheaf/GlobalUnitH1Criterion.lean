/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.Basic
public import Lib.Algebra.Homology.HomologicalComplex.CycleLift
public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnit

/-!
# A criterion for the degree-one singular-cochain comparison

The degree-one cohomology isomorphism for the comparison `S^•(X; A) → Γ(X, 𝒮^•(·; A))` is reduced
to two inputs, which are the two steps of the proof of Bredon, *Sheaf Theory* III Thm. 1.1: the
comparison map is surjective in degrees zero and one and its kernel is detected on a point-indexed
open cover; and the inclusion of the chains small with respect to such a cover is a
chain-homotopy equivalence (Hatcher, *Algebraic Topology* Prop. 2.21).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Set TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The comparison map `S^n(X; A) → Γ(X, 𝒮^n(·; A))` is surjective. -/
def GlobalUnitSurjective (n : ℕ) : Prop :=
  Function.Surjective (globalCochainUnit X A n)

/-- Every degree-`n` singular cochain killed by the comparison map vanishes on the chains small
with respect to some point-indexed open cover of `X`. -/
def GlobalKernelLocallySmall (n : ℕ) : Prop :=
  ∀ (phi : (AlgebraicTopology.SingularCochains.complex X A).X n),
    globalCochainUnit X A n phi = 0 →
      ∃ U : X → Opens X, (∀ x, x ∈ U x) ∧
        (TopCat.SingularSmallChains.cochainRestriction A
          (fun x => (U x : Set X))).f n phi = 0

/-- Conversely, a degree-one singular cochain vanishing on the chains small with respect to some
point-indexed open cover of `X` is killed by the comparison map. -/
def SmallKernelGlobalOne : Prop :=
  ∀ (U : X → Opens X), (∀ x, x ∈ U x) →
    ∀ (phi : (AlgebraicTopology.SingularCochains.complex X A).X 1),
      (TopCat.SingularSmallChains.cochainRestriction A
        (fun x => (U x : Set X))).f 1 phi = 0 →
        globalCochainUnit X A 1 phi = 0

/-- For every point-indexed open cover of `X` the inclusion of the small chains into all singular
chains is a chain-homotopy equivalence (Hatcher, *Algebraic Topology* Prop. 2.21). -/
def HasSmallChainEquivalences : Prop :=
  ∀ (U : X → Opens X), (∀ x, x ∈ U x) →
    ∃ e : HomotopyEquiv
        (TopCat.SingularSmallChains.complex (fun x => (U x : Set X)))
        (AlgebraicTopology.SingularCochains.chains X),
      e.hom = TopCat.SingularSmallChains.inclusion (fun x => (U x : Set X))

/-- Degree-one cocycle lifting for the comparison map: every cocycle in `Γ(X, 𝒮^1(·; A))` is the
image of a singular cocycle on `X`. -/
theorem globalCochainComparison_cycle_lift_one
    (hunitOne : GlobalUnitSurjective X A 1)
    (hkernelTwo : GlobalKernelLocallySmall X A 2)
    (hkernelReverseOne : SmallKernelGlobalOne X A)
    (hsmall : HasSmallChainEquivalences X) (s : (globalCochainComplex X A).X 1)
    (hs : (globalCochainComplex X A).d 1 2 s = 0) :
    ∃ phi : (AlgebraicTopology.SingularCochains.complex X A).X 1,
      (AlgebraicTopology.SingularCochains.complex X A).d 1 2 phi = 0 ∧
      globalCochainUnit X A 1 phi = s := by
  obtain ⟨alpha, rfl⟩ := hunitOne s
  have hdelta : globalCochainUnit X A 2
      ((AlgebraicTopology.SingularCochains.complex X A).d 1 2 alpha) = 0 := by
    exact (TopCat.SingularSmallChains.cochainMap_d
      (globalCochainComparison X A) 1 2 alpha).symm.trans hs
  obtain ⟨U, hxU, hU⟩ := hkernelTwo _ hdelta
  let r := TopCat.SingularSmallChains.cochainRestriction A (fun x => (U x : Set X))
  obtain ⟨e, he⟩ := hsmall U hxU
  have hsmallCocycle :
      (AlgebraicTopology.SingularCochains.dualComplex A
        (TopCat.SingularSmallChains.complex
          (fun x => (U x : Set X)))).d 1 2 (r.f 1 alpha) = 0 :=
    (TopCat.SingularSmallChains.cochainMap_d r 1 2 alpha).trans hU
  obtain ⟨phi, hphi, hphiRestriction⟩ :=
    TopCat.SingularSmallChains.smallCochain_cocycle_lift_exact_one A
      (fun x => (U x : Set X))
      e he (r.f 1 alpha) hsmallCocycle
  have hdiff : r.f 1 (phi - alpha) = 0 := by
    rw [map_sub, hphiRestriction, sub_self]
  have hunitDiff := hkernelReverseOne U hxU (phi - alpha) hdiff
  refine ⟨phi, hphi, ?_⟩
  exact sub_eq_zero.mp
    ((map_sub (globalCochainUnit X A 1).hom phi alpha).symm.trans hunitDiff)

/-- Degree-one boundary detection for the comparison map: a singular cocycle whose image in
`Γ(X, 𝒮^1(·; A))` is a coboundary is itself a coboundary. -/
theorem globalCochainComparison_boundary_detect_one
    (hunitZero : GlobalUnitSurjective X A 0)
    (hkernelOne : GlobalKernelLocallySmall X A 1)
    (hsmall : HasSmallChainEquivalences X)
    (phi : (AlgebraicTopology.SingularCochains.complex X A).X 1)
    (hphi : (AlgebraicTopology.SingularCochains.complex X A).d 1 2 phi = 0)
    (s : (globalCochainComplex X A).X 0)
    (hs : (globalCochainComplex X A).d 0 1 s = globalCochainUnit X A 1 phi) :
    ∃ psi : (AlgebraicTopology.SingularCochains.complex X A).X 0,
      (AlgebraicTopology.SingularCochains.complex X A).d 0 1 psi = phi := by
  obtain ⟨beta, rfl⟩ := hunitZero s
  have hdelta : globalCochainUnit X A 1
      ((AlgebraicTopology.SingularCochains.complex X A).d 0 1 beta) =
      globalCochainUnit X A 1 phi :=
    (TopCat.SingularSmallChains.cochainMap_d
      (globalCochainComparison X A) 0 1 beta).symm.trans hs
  have hdiff : globalCochainUnit X A 1
      (phi - (AlgebraicTopology.SingularCochains.complex X A).d 0 1 beta) = 0 := by
    rw [map_sub, hdelta, sub_self]
  obtain ⟨U, hxU, hU⟩ := hkernelOne _ hdiff
  let r := TopCat.SingularSmallChains.cochainRestriction A (fun x => (U x : Set X))
  obtain ⟨e, he⟩ := hsmall U hxU
  have hr : r.f 1 ((AlgebraicTopology.SingularCochains.complex X A).d 0 1 beta) =
      r.f 1 phi :=
    (sub_eq_zero.mp ((map_sub (r.f 1).hom phi
      ((AlgebraicTopology.SingularCochains.complex X A).d 0 1 beta)).symm.trans hU)).symm
  have hboundary :
      (AlgebraicTopology.SingularCochains.dualComplex A
        (TopCat.SingularSmallChains.complex
          (fun x => (U x : Set X)))).d 0 1 (r.f 0 beta) = r.f 1 phi :=
    (TopCat.SingularSmallChains.cochainMap_d r 0 1 beta).trans hr
  exact TopCat.SingularSmallChains.smallCochain_boundary_of_restriction_boundary_one A
    (fun x => (U x : Set X)) e he phi hphi (r.f 0 beta) hboundary

/-- The comparison `S^•(X; A) → Γ(X, 𝒮^•(·; A))` is an isomorphism on degree-one cohomology as
soon as it is surjective in degrees zero and one, its kernel in degrees one and two is detected on
point-indexed open covers, and the small-chain inclusions are chain-homotopy equivalences. -/
theorem globalCochainComparison_homology_isIso_one_of_small_chains
    (hunitZero : GlobalUnitSurjective X A 0)
    (hunitOne : GlobalUnitSurjective X A 1)
    (hkernelOne : GlobalKernelLocallySmall X A 1)
    (hkernelTwo : GlobalKernelLocallySmall X A 2)
    (hkernelReverseOne : SmallKernelGlobalOne X A)
    (hsmall : HasSmallChainEquivalences X) :
    IsIso (HomologicalComplex.homologyMap (globalCochainComparison X A) 1) := by
  apply HomologicalComplex.isIso_homologyMap_succ_of_cycle_lifts
    (globalCochainComparison X A) 0
  · intro s hs
    exact globalCochainComparison_cycle_lift_one X A hunitOne hkernelTwo
      hkernelReverseOne hsmall s hs
  · intro phi hphi hboundary
    obtain ⟨s, hs⟩ := hboundary
    exact globalCochainComparison_boundary_detect_one X A hunitZero hkernelOne
      hsmall phi hphi s hs

end TopCat.SingularCochainSheaf
