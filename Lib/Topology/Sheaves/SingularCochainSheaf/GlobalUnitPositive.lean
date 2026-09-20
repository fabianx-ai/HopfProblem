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
# The singular-cochain comparison in every positive degree

On a normal paracompact space the comparison map `S^•(X; A) → Γ(X, 𝒮^•(·; A))` is an isomorphism
on cohomology in every positive degree.  This is Bredon, *Sheaf Theory* III Thm. 1.1 (see also
Warner, *Foundations of Differentiable Manifolds and Lie Groups* 5.31); the ingredients are
surjectivity of the comparison map, detection of its kernel on the chains small for an open cover,
and the small-chain homotopy equivalence (Hatcher, *Algebraic Topology* Prop. 2.21).

## Main results

* `TopCat.SingularCochainSheaf.globalCochainComparison_homology_isIso_succ`
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.SingularCochainSheaf

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- Cocycle lifting in degree `n + 1`: every cocycle in `Γ(X, 𝒮^{n+1}(·; A))` is the image of a
singular cocycle on `X`. -/
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

/-- Boundary detection in degree `n + 1`: a singular cocycle whose image in `Γ(X, 𝒮^{n+1}(·; A))`
is a coboundary is itself a coboundary. -/
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

/-- The comparison `S^•(X; A) → Γ(X, 𝒮^•(·; A))` is an isomorphism on cohomology in degree
`n + 1` as soon as it is surjective, its kernel is detected on point-indexed open covers, and the
small-chain inclusions are chain-homotopy equivalences. -/
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

/-- On a normal paracompact space the comparison `S^•(X; A) → Γ(X, 𝒮^•(·; A))` is an isomorphism
on cohomology in every positive degree, given the small-chain homotopy equivalences for open
covers of `X` (Bredon, *Sheaf Theory* III Thm. 1.1). -/
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
