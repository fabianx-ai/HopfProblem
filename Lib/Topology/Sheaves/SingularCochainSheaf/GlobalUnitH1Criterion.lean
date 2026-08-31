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
# The exact H¹ seam for the global singular-cochain sheafification unit

This module reduces the degree-one homology isomorphism for the actual global unit to the two
textbook geometric inputs.  First, the global sheafification unit is surjective in degrees zero
and one and its kernel is detected on a point-indexed open cover.  Second, the inclusion of chains
small with respect to such a cover is a chain-homotopy equivalence.  No degree-two cohomology,
Mayer--Vietoris sequence, or Hurewicz comparison occurs.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Set TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The global unit is surjective in degree `n`. -/
def GlobalUnitSurjective (n : ℕ) : Prop :=
  Function.Surjective (globalCochainUnit X A n)

/-- A zero of the global unit in degree `n` vanishes on chains small with respect to some
point-indexed open cover. -/
def GlobalKernelLocallySmall (n : ℕ) : Prop :=
  ∀ (phi : (AlgebraicTopology.SingularCochains.complex X A).X n),
    globalCochainUnit X A n phi = 0 →
      ∃ U : X → Opens X, (∀ x, x ∈ U x) ∧
        (TopCat.SingularSmallChains.cochainRestriction A
          (fun x => (U x : Set X))).f n phi = 0

/-- Vanishing on a point-indexed cover-small complex implies vanishing under the degree-one
global unit. -/
def SmallKernelGlobalOne : Prop :=
  ∀ (U : X → Opens X), (∀ x, x ∈ U x) →
    ∀ (phi : (AlgebraicTopology.SingularCochains.complex X A).X 1),
      (TopCat.SingularSmallChains.cochainRestriction A
        (fun x => (U x : Set X))).f 1 phi = 0 →
        globalCochainUnit X A 1 phi = 0

/-- The cover-small inclusion is a literal chain-homotopy equivalence for every point-indexed
open cover. -/
def HasSmallChainEquivalences : Prop :=
  ∀ (U : X → Opens X), (∀ x, x ∈ U x) →
    ∃ e : HomotopyEquiv
        (TopCat.SingularSmallChains.complex (fun x => (U x : Set X)))
        (AlgebraicTopology.SingularCochains.chains X),
      e.hom = TopCat.SingularSmallChains.inclusion (fun x => (U x : Set X))

/-- Exact degree-one cocycle lifting for the actual global sheafification-unit comparison. -/
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

/-- Detection of actual degree-one boundaries for the actual global sheafification-unit
comparison. -/
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

/-- The degree-one homology map of the actual global unit is an isomorphism from exactly the
degree-zero/one global patching, degree-one/two kernel locality, and cover-small chain inputs. -/
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
