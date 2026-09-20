/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularCochains
public import Lib.Topology.Sheaves.ConstantCohomologyPullback
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Constant-product degree-one adapters

Projection from a product `S × X` with `S` contractible is a homotopy equivalence with inverse
the inclusion of the fibre over a chosen point `s : S`.  The point-set and singular-cohomology
consequences of this are collected here; the corresponding statement for constant-sheaf
cohomology is homotopy invariance (Bredon, *Sheaf Theory*, II.11) and needs the comparison with
singular cohomology.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory ContinuousMap

namespace TopCat.ConstantProductH1

variable (S X : Type) [TopologicalSpace S] [TopologicalSpace X]
  [CompactSpace S] [T2Space S] [ContractibleSpace S]
  [CompactSpace X] [T2Space X]

omit [CompactSpace S] [T2Space S] in
/-- Any chosen point of a contractible space gives a contraction based at that point. -/
theorem basedContraction_homotopic (s : S) :
    (ContinuousMap.const S s).Homotopic (ContinuousMap.id S) := by
  obtain ⟨p, hp⟩ := id_nullhomotopic S
  have hsp : (ContinuousMap.const S s).Homotopic (ContinuousMap.const S p) :=
    (ContinuousMap.homotopic_const_iff).2 (PathConnectedSpace.joined s p)
  exact hsp.trans hp.symm

/-- Projection from a contractible product, with inverse based at `s`. -/
def basedProductHomotopyEquiv (s : S) : (S × X) ≃ₕ X where
  toFun := ContinuousMap.snd
  invFun := (ContinuousMap.const X s).prodMk (ContinuousMap.id X)
  left_inv := (basedContraction_homotopic S s).prodMap
    (.refl (ContinuousMap.id X))
  right_inv := .refl (ContinuousMap.id X)

/-- Inclusion of the fibre based at `s`. -/
def basedFibreInclusion (s : S) : TopCat.of X ⟶ TopCat.of (S × X) :=
  TopCat.ofHom (basedProductHomotopyEquiv S X s).symm.toFun

omit [CompactSpace S] [T2Space S] [CompactSpace X] [T2Space X] in
/-- The fibre inclusion based at `s` sends `x` to `(s, x)`. -/
@[simp]
theorem basedFibreInclusion_apply (s : S) (x : X) :
    basedFibreInclusion S X s x = (s, x) := rfl

omit [CompactSpace S] [T2Space S] [CompactSpace X] [T2Space X] in
/-- The fibre inclusion based at `s` is injective. -/
theorem basedFibreInclusion_injective (s : S) :
    Function.Injective (basedFibreInclusion S X s) := by
  intro x y h
  exact congrArg Prod.snd h

omit [CompactSpace S] in
/-- The fibre inclusion based at `s` is a closed map when the product is compact Hausdorff. -/
theorem basedFibreInclusion_isClosedMap (s : S) :
    IsClosedMap (basedFibreInclusion S X s) :=
  (basedFibreInclusion S X s).hom.continuous.isClosedMap

omit [CompactSpace S] [T2Space S] [CompactSpace X] [T2Space X] in
/-- The fibre inclusion based at `s` has finite (indeed at most singleton) fibres. -/
theorem basedFibreInclusion_finite_fibres (s : S) (p : S × X) :
    ((basedFibreInclusion S X s) ⁻¹' ({p} : Set (S × X))).Finite :=
  Set.Finite.preimage (basedFibreInclusion_injective S X s).injOn
    (Set.finite_singleton p)

/-- Pullback to a based fibre is an isomorphism on the native singular-cochain cohomology in
every degree and for every small abelian coefficient group. -/
instance singularPullback_basedFibreInclusion_isIso
    (A : AddCommGrpCat.{0}) (s : S) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (AlgebraicTopology.SingularCochains.pullback A
        (basedFibreInclusion S X s).hom) n) := by
  change IsIso
    (AlgebraicTopology.SingularCochains.homotopyEquivCohomologyIso A
      (basedProductHomotopyEquiv S X s) n).inv
  infer_instance

/-- If comparison isomorphisms intertwine a native constant-sheaf pullback with singular
pullback, then the native pullback is an isomorphism.  This isolates exactly how the missing
comparison theorem is consumed. -/
theorem nativePullback_isIso_of_comparison
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space Z]
    (f : TopCat.of Z ⟶ TopCat.of Y) (hf : IsClosedMap f)
    (hfinite : ∀ y : Y, (f ⁻¹' ({y} : Set Y)).Finite)
    (A : AddCommGrpCat.{0})
    (cY : @AddCommGrpCat.of
        (CategoryTheory.Sheaf.H.{0}
          (TopCat.ConstantSheaf.sheaf (TopCat.of Y) A) 1)
        (CategoryTheory.Sheaf.instAddCommGroupH
          (TopCat.ConstantSheaf.sheaf (TopCat.of Y) A) 1) ≅
      (AlgebraicTopology.SingularCochains.complex Y A).homology 1)
    (cZ : @AddCommGrpCat.of
        (CategoryTheory.Sheaf.H.{0}
          (TopCat.ConstantSheaf.sheaf (TopCat.of Z) A) 1)
        (CategoryTheory.Sheaf.instAddCommGroupH
          (TopCat.ConstantSheaf.sheaf (TopCat.of Z) A) 1) ≅
      (AlgebraicTopology.SingularCochains.complex Z A).homology 1)
    (hcomm : TopCat.ConstantSheafCohomology.pullback f hf hfinite A 1 ≫ cZ.hom =
      cY.hom ≫ HomologicalComplex.homologyMap
        (AlgebraicTopology.SingularCochains.pullback A f.hom) 1)
    [IsIso (HomologicalComplex.homologyMap
      (AlgebraicTopology.SingularCochains.pullback A f.hom) 1)] :
    IsIso (TopCat.ConstantSheafCohomology.pullback f hf hfinite A 1) := by
  have : IsIso
      (TopCat.ConstantSheafCohomology.pullback f hf hfinite A 1 ≫ cZ.hom) := by
    rw [hcomm]
    infer_instance
  exact (isIso_comp_right_iff
    (TopCat.ConstantSheafCohomology.pullback f hf hfinite A 1) cZ.hom).mp this

end TopCat.ConstantProductH1
