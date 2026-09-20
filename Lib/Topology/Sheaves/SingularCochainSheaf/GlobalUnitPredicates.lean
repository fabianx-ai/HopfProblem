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
# The inputs of the singular-cochain comparison theorem

The cohomology isomorphism for the comparison `S^•(X; A) → Γ(X, 𝒮^•(·; A))` is reduced to the two
steps of the proof of Bredon, *Sheaf Theory* III Thm. 1.1: the comparison map is surjective and
its kernel is exactly the cochains vanishing on the chains small for a point-indexed open cover;
and the inclusion of those small chains is a chain-homotopy equivalence (Hatcher, *Algebraic
Topology* Prop. 2.21).  This module names those four conditions.  `GlobalUnitSurjective` is
discharged by `globalCochainUnit_surjective` in `GlobalSections.lean`;
`GlobalKernelLocallySmall` and `SmallKernelGlobal` by `globalKernelLocallySmall` and
`smallKernelGlobal` in `GlobalKernelSmall.lean`; `HasSmallChainEquivalences` by
`hasSmallChainEquivalences_barycentric` in `BarycentricSmallChains.lean`.  All four are consumed
in `GlobalUnitPositive.lean`.

## Main definitions

* `TopCat.SingularCochainSheaf.GlobalUnitSurjective`
* `TopCat.SingularCochainSheaf.GlobalKernelLocallySmall`
* `TopCat.SingularCochainSheaf.SmallKernelGlobal`
* `TopCat.SingularCochainSheaf.HasSmallChainEquivalences`
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

/-- Conversely, a degree-`n` singular cochain vanishing on the chains small with respect to some
point-indexed open cover of `X` is killed by the comparison map in degree `n`. -/
def SmallKernelGlobal (n : ℕ) : Prop :=
  ∀ (U : X → Opens X), (∀ x, x ∈ U x) →
    ∀ (phi : (AlgebraicTopology.SingularCochains.complex X A).X n),
      (TopCat.SingularSmallChains.cochainRestriction A
        (fun x => (U x : Set X))).f n phi = 0 →
        globalCochainUnit X A n phi = 0

/-- For every point-indexed open cover of `X` the inclusion of the small chains into all singular
chains is a chain-homotopy equivalence (Hatcher, *Algebraic Topology* Prop. 2.21). -/
def HasSmallChainEquivalences : Prop :=
  ∀ (U : X → Opens X), (∀ x, x ∈ U x) →
    ∃ e : HomotopyEquiv
        (TopCat.SingularSmallChains.complex (fun x => (U x : Set X)))
        (AlgebraicTopology.SingularCochains.chains X),
      e.hom = TopCat.SingularSmallChains.inclusion (fun x => (U x : Set X))

end TopCat.SingularCochainSheaf
