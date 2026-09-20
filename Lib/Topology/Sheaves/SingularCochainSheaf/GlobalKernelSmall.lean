/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalKernelLocal
public import Lib.Topology.Sheaves.SingularCochainSheaf.GlobalUnitPredicates

/-!
# The global-unit kernel and cover-small chains

A global singular cochain is killed by the sheafification unit exactly when it vanishes on the
chains that are small with respect to some open cover, equivalently when it restricts to zero on
each member of that cover (Bredon, *Sheaf Theory*, III §1; Hatcher, *Algebraic Topology*,
Prop. 2.21).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Set TopologicalSpace

namespace TopCat.SingularCochainSheaf

open AlgebraicTopology.SingularCochains

/-- A cochain restricts to zero on the cover-small chains exactly when it vanishes on every
simplex carried by a member of the cover. -/
theorem cochainRestriction_eq_zero_iff {X : Type} [TopologicalSpace X]
    {ι : Type} (A : AddCommGrpCat.{0}) (U : ι → Set X) (n : ℕ)
    (phi : Cochains X A n) :
    (TopCat.SingularSmallChains.cochainRestriction A U).f n phi = 0 ↔
      ∀ sigma : TopCat.SingularSmallChains.SingularSimplex X n,
        TopCat.SingularSmallChains.IsSmallSimplex U sigma →
          phi (TopCat.SingularSmallChains.simplexChain X n sigma) = 0 := by
  constructor
  · intro h sigma hsigma
    have hv := congrArg
      (fun chi : (AlgebraicTopology.SingularCochains.dualComplex A
          (TopCat.SingularSmallChains.complex U)).X n =>
        (show (((TopCat.SingularSmallChains.complex U).X n : Type) →+ A) from chi)
          ⟨TopCat.SingularSmallChains.simplexChain X n sigma,
            TopCat.SingularSmallChains.simplexChain_mem U n sigma hsigma⟩) h
    exact hv
  · intro h
    let r := (TopCat.SingularSmallChains.cochainRestriction A U).f n phi
    have he : TopCat.SingularSmallChains.addHomToIntLinearMap r = 0 := by
      apply (TopCat.SingularSmallChains.smallChainBasis U n).ext
      intro sigma
      change phi (TopCat.SingularSmallChains.smallChainBasis U n sigma).1 = 0
      rw [TopCat.SingularSmallChains.smallChainBasis_apply_val]
      exact h sigma.1 sigma.2
    change r = 0
    exact congrArg LinearMap.toAddMonoidHom he

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ)

/-- A cochain restricts to zero on the cover-small chains exactly when its restriction to each
member of the open cover is zero. -/
theorem cochainRestriction_eq_zero_iff_open_restrictions
    {ι : Type} (U : ι → Opens X) (phi : Cochains X A n) :
    (TopCat.SingularSmallChains.cochainRestriction A
      (fun i => (U i : Set X))).f n phi = 0 ↔
      ∀ i, restrictGlobalCochain A n phi (U i) = 0 := by
  constructor
  · intro h i
    apply cochain_ext A n
    intro sigma
    let tau : TopCat.SingularSmallChains.SingularSimplex X n :=
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X)).comp sigma
    have htau : TopCat.SingularSmallChains.IsSmallSimplex
        (fun j => (U j : Set X)) tau := by
      refine ⟨i, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact (sigma z).property
    exact (restrictGlobalCochain_simplex A n phi (U i) sigma).trans
      ((cochainRestriction_eq_zero_iff A (fun j => (U j : Set X)) n phi).mp
        h tau htau)
  · intro h
    apply (cochainRestriction_eq_zero_iff A (fun i => (U i : Set X)) n phi).mpr
    intro sigma hsigma
    obtain ⟨i, hi⟩ := hsigma
    let sigma' := simplexInOpen n sigma (U i) hi
    have hv := congrArg
      (fun psi : Cochains (U i) A n =>
        psi (TopCat.SingularSmallChains.simplexChain (U i) n sigma')) (h i)
    exact (restrictGlobalCochain_simplex A n phi (U i) sigma').symm.trans hv

/-- A cochain vanishing on the chains small for an open cover is killed by the global
sheafification unit. -/
theorem globalCochainUnit_eq_zero_of_smallRestriction
    {ι : Type} (U : ι → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (phi : Cochains X A n)
    (hphi : (TopCat.SingularSmallChains.cochainRestriction A
      (fun i => (U i : Set X))).f n phi = 0) :
    globalCochainUnit X A n phi = 0 := by
  apply globalCochainUnit_eq_zero_of_local X A n phi
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨U i, hi,
    (cochainRestriction_eq_zero_iff_open_restrictions X A n U phi).mp hphi i⟩

/-- A cochain killed by the global sheafification unit vanishes on the chains small for some
open cover indexed by the points of `X`. -/
theorem exists_cover_cochainRestriction_eq_zero (phi : Cochains X A n)
    (hphi : globalCochainUnit X A n phi = 0) :
    ∃ U : X → Opens X, (∀ x : X, x ∈ U x) ∧
      (TopCat.SingularSmallChains.cochainRestriction A
        (fun x => (U x : Set X))).f n phi = 0 := by
  classical
  choose U hxU hU using globalCochainUnit_locally_zero X A n phi hphi
  exact ⟨U, hxU,
    (cochainRestriction_eq_zero_iff_open_restrictions X A n U phi).mpr hU⟩

/-- The kernel of the global sheafification unit consists exactly of the cochains vanishing on
the chains small for some point-indexed open cover (Bredon III §1). -/
theorem globalCochainUnit_eq_zero_iff_smallCover (phi : Cochains X A n) :
    globalCochainUnit X A n phi = 0 ↔
      ∃ U : X → Opens X, (∀ x : X, x ∈ U x) ∧
        (TopCat.SingularSmallChains.cochainRestriction A
          (fun x => (U x : Set X))).f n phi = 0 := by
  constructor
  · exact exists_cover_cochainRestriction_eq_zero X A n phi
  · rintro ⟨U, hxU, hU⟩
    exact globalCochainUnit_eq_zero_of_smallRestriction X A n U
      (fun x => ⟨x, hxU x⟩) phi hU

/-- The singular-cochain presheaf satisfies the locally-small-kernel condition: every cochain in
the kernel of the global unit is small for some cover. -/
theorem globalKernelLocallySmall (n : ℕ) : GlobalKernelLocallySmall X A n :=
  exists_cover_cochainRestriction_eq_zero X A n

/-- A singular cochain vanishing on the chains small for a point-indexed open cover is killed by
the comparison map, in every degree. -/
theorem smallKernelGlobal (n : ℕ) : SmallKernelGlobal X A n := by
  intro U hxU phi hphi
  exact globalCochainUnit_eq_zero_of_smallRestriction X A n U
    (fun x => ⟨x, hxU x⟩) phi hphi

end TopCat.SingularCochainSheaf
