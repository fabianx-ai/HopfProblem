/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularSmallChains.CochainHomotopy
public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalKernelSmall

/-!
# The global singular-cochain sheafification unit in every positive degree

Closed locally finite patching, exact detection of the sheafification-unit kernel on cover-small
chains, and the classical small-chain homotopy equivalence imply that the actual global unit is a
quasi-isomorphism in every positive degree.  This is the degree-independent form of the existing
degree-one argument.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- Vanishing on a point-indexed cover-small complex forces vanishing under the global unit in
degree `n`. -/
def SmallKernelGlobal (n : ℕ) : Prop :=
  ∀ (U : X → Opens X), (∀ x, x ∈ U x) →
    ∀ (phi : (AlgebraicTopology.SingularCochains.complex X A).X n),
      (TopCat.SingularSmallChains.cochainRestriction A
        (fun x => (U x : Set X))).f n phi = 0 →
        globalCochainUnit X A n phi = 0

/-- Exact positive-degree cocycle lifting for the actual global sheafification-unit map. -/
theorem globalCochainComparison_cycle_lift_succ (n : ℕ)
    (hunit : GlobalUnitSurjective X A (n + 1))
    (hkernelNext : GlobalKernelLocallySmall X A (n + 2))
    (hkernelReverse : SmallKernelGlobal X A (n + 1))
    (hsmall : HasSmallChainEquivalences X)
    (s : (globalCochainComplex X A).X (n + 1))
    (hs : (globalCochainComplex X A).d (n + 1) (n + 2) s = 0) :
    ∃ phi : (AlgebraicTopology.SingularCochains.complex X A).X (n + 1),
      (AlgebraicTopology.SingularCochains.complex X A).d
        (n + 1) (n + 2) phi = 0 ∧
      globalCochainUnit X A (n + 1) phi = s := by
  obtain ⟨alpha, rfl⟩ := hunit s
  have hdelta : globalCochainUnit X A (n + 2)
      ((AlgebraicTopology.SingularCochains.complex X A).d
        (n + 1) (n + 2) alpha) = 0 := by
    exact (TopCat.SingularSmallChains.cochainMap_d
      (globalCochainComparison X A) (n + 1) (n + 2) alpha).symm.trans hs
  obtain ⟨U, hxU, hU⟩ := hkernelNext _ hdelta
  let r := TopCat.SingularSmallChains.cochainRestriction A (fun x => (U x : Set X))
  obtain ⟨e, he⟩ := hsmall U hxU
  have hsmallCocycle :
      (AlgebraicTopology.SingularCochains.dualComplex A
        (TopCat.SingularSmallChains.complex
          (fun x => (U x : Set X)))).d (n + 1) (n + 2) (r.f (n + 1) alpha) = 0 :=
    (TopCat.SingularSmallChains.cochainMap_d r (n + 1) (n + 2) alpha).trans hU
  obtain ⟨phi, hphi, hphiRestriction⟩ :=
    TopCat.SingularSmallChains.smallCochain_cocycle_lift_exact_succ A
      (fun x => (U x : Set X)) e he n (r.f (n + 1) alpha) hsmallCocycle
  have hdiff : r.f (n + 1) (phi - alpha) = 0 := by
    rw [map_sub, hphiRestriction, sub_self]
  have hunitDiff := hkernelReverse U hxU (phi - alpha) hdiff
  refine ⟨phi, hphi, ?_⟩
  exact sub_eq_zero.mp
    ((map_sub (globalCochainUnit X A (n + 1)).hom phi alpha).symm.trans hunitDiff)

/-- Detection of actual positive-degree boundaries for the global sheafification-unit map. -/
theorem globalCochainComparison_boundary_detect_succ (n : ℕ)
    (hunitPrev : GlobalUnitSurjective X A n)
    (hkernel : GlobalKernelLocallySmall X A (n + 1))
    (hsmall : HasSmallChainEquivalences X)
    (phi : (AlgebraicTopology.SingularCochains.complex X A).X (n + 1))
    (hphi : (AlgebraicTopology.SingularCochains.complex X A).d
      (n + 1) (n + 2) phi = 0)
    (s : (globalCochainComplex X A).X n)
    (hs : (globalCochainComplex X A).d n (n + 1) s =
      globalCochainUnit X A (n + 1) phi) :
    ∃ psi : (AlgebraicTopology.SingularCochains.complex X A).X n,
      (AlgebraicTopology.SingularCochains.complex X A).d n (n + 1) psi = phi := by
  obtain ⟨beta, rfl⟩ := hunitPrev s
  have hdelta : globalCochainUnit X A (n + 1)
      ((AlgebraicTopology.SingularCochains.complex X A).d n (n + 1) beta) =
      globalCochainUnit X A (n + 1) phi :=
    (TopCat.SingularSmallChains.cochainMap_d
      (globalCochainComparison X A) n (n + 1) beta).symm.trans hs
  have hdiff : globalCochainUnit X A (n + 1)
      (phi - (AlgebraicTopology.SingularCochains.complex X A).d n (n + 1) beta) = 0 := by
    rw [map_sub, hdelta, sub_self]
  obtain ⟨U, hxU, hU⟩ := hkernel _ hdiff
  let r := TopCat.SingularSmallChains.cochainRestriction A (fun x => (U x : Set X))
  obtain ⟨e, he⟩ := hsmall U hxU
  have hr : r.f (n + 1)
      ((AlgebraicTopology.SingularCochains.complex X A).d n (n + 1) beta) =
      r.f (n + 1) phi :=
    (sub_eq_zero.mp ((map_sub (r.f (n + 1)).hom phi
      ((AlgebraicTopology.SingularCochains.complex X A).d n (n + 1) beta)).symm.trans hU)).symm
  have hboundary :
      (AlgebraicTopology.SingularCochains.dualComplex A
        (TopCat.SingularSmallChains.complex (fun x => (U x : Set X)))).d
          n (n + 1) (r.f n beta) = r.f (n + 1) phi :=
    (TopCat.SingularSmallChains.cochainMap_d r n (n + 1) beta).trans hr
  exact TopCat.SingularSmallChains.smallCochain_boundary_of_restriction_boundary_succ A
    (fun x => (U x : Set X)) e he n phi hphi (r.f n beta) hboundary

/-- The positive-degree homology map of the actual global unit is an isomorphism from the
degree-independent patching, kernel-locality, and small-chain hypotheses. -/
theorem globalCochainComparison_homology_isIso_succ_of_small_chains (n : ℕ)
    (hunitPrev : GlobalUnitSurjective X A n)
    (hunit : GlobalUnitSurjective X A (n + 1))
    (hkernel : GlobalKernelLocallySmall X A (n + 1))
    (hkernelNext : GlobalKernelLocallySmall X A (n + 2))
    (hkernelReverse : SmallKernelGlobal X A (n + 1))
    (hsmall : HasSmallChainEquivalences X) :
    IsIso (HomologicalComplex.homologyMap (globalCochainComparison X A) (n + 1)) := by
  apply HomologicalComplex.isIso_homologyMap_succ_of_cycle_lifts
    (globalCochainComparison X A) n
  · exact globalCochainComparison_cycle_lift_succ X A n hunit hkernelNext
      hkernelReverse hsmall
  · intro phi hphi hboundary
    obtain ⟨s, hs⟩ := hboundary
    exact globalCochainComparison_boundary_detect_succ X A n hunitPrev hkernel
      hsmall phi hphi s hs

/-- The concrete global-unit kernel supplies the reverse cover-small implication in every
degree. -/
theorem smallKernelGlobal (n : ℕ) : SmallKernelGlobal X A n := by
  intro U hxU phi hphi
  exact globalCochainUnit_eq_zero_of_smallRestriction X A n U
    (fun x => ⟨x, hxU x⟩) phi hphi

/-- On a normal paracompact space, the actual global sheafification unit is an isomorphism on
every positive-degree cohomology group once the textbook small-chain equivalences are supplied. -/
theorem globalCochainComparison_homology_isIso_succ
    [NormalSpace X] [ParacompactSpace X]
    (hsmall : HasSmallChainEquivalences X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (globalCochainComparison X A) (n + 1)) :=
  globalCochainComparison_homology_isIso_succ_of_small_chains X A n
    (globalCochainUnit_surjective X A n)
    (globalCochainUnit_surjective X A (n + 1))
    (globalKernelLocallySmall X A (n + 1))
    (globalKernelLocallySmall X A (n + 2))
    (smallKernelGlobal X A (n + 1)) hsmall

end TopCat.SingularCochainSheaf
