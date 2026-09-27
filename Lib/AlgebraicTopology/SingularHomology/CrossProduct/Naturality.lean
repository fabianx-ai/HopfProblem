/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
public import Lib.AlgebraicTopology.SingularHomology.CrossInsert
public import Lib.AlgebraicTopology.SingularHomology.CircleProduct
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Homology

open Set Function Filter Manifold Topology

open scoped BigOperators TensorProduct

/-!
# Naturality of the homology cross product

For continuous `f : X → X'` and `g : Y → Y'`, `(f × g)_#(a × b) = f_# a × g_# b` on cycles
(`PeriodTorusHigherHomology.crossProductCycles_natural`) and on homology
(`PeriodTorusHigherHomology.crossProductHomology_natural`), for `a ∈ H₁(X)`, `b ∈ Hₙ(Y)`.  As a
consequence the projection to the second factor kills every cross product with a `1`-class,
`(pr₂)_#(a × b) = 0` (`PeriodTorusHigherHomology.crossProductHomology_snd`), since `H₁` of a point
vanishes.

Naturality of the cross product: Hatcher, *Algebraic Topology*, §3.B.
-/


@[expose] public noncomputable section


section

open SingularHomology


attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cycle-level cross product is natural under maps of both factors. -/
theorem PeriodTorusHigherHomology.crossProductCycles_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    SingularMayerVietoris.ModuleHomology.mapCycles (SingularChains.singularChainMap (f.prodMap g))
        (n + 1) (crossProductCycles X Y n a b) =
      crossProductCycles X' Y' n
        (SingularMayerVietoris.ModuleHomology.mapCycles (SingularChains.singularChainMap f) 1 a)
        (SingularMayerVietoris.ModuleHomology.mapCycles (SingularChains.singularChainMap g) n b) :=
  by
  apply Subtype.ext
  simp only [SingularMayerVietoris.ModuleHomology.mapCycles_val, crossProductCycles_val]
  exact crossProductEdge_natural f g n a.1 b.1

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The homology cross product is natural: it commutes with the maps induced by `f.prodMap g`. -/
theorem PeriodTorusHigherHomology.crossProductHomology_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (a : (SingularChains.singularComplex X).homology 1)
    (b : (SingularChains.singularComplex Y).homology n) :
    (HomologicalComplex.homologyMap (SingularChains.singularChainMap (f.prodMap g)) (n + 1)).hom
        (crossProductHomology X Y n a b) =
      crossProductHomology X' Y' n
        ((HomologicalComplex.homologyMap (SingularChains.singularChainMap f) 1).hom a)
        ((HomologicalComplex.homologyMap (SingularChains.singularChainMap g) n).hom b) := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex Y) n
      b
  rw [crossProductHomology_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, crossProductHomology_cycleClass,
    crossProductCycles_natural]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product maps to zero under the second projection: `H_*` of a product pushed to a factor kills mixed classes, the Künneth projection identity. -/
theorem PeriodTorusHigherHomology.crossProductHomology_snd {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y n) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.snd : C(X × Y, Y)) (n + 1)
        (crossProductHomology X Y n a b) =
      0 := by
  let : Subsingleton (SingularMayerVietoris.SingularHomology Unit 1) :=
    point_homology_subsingleton 1 (by decide)
  let f : C(X, Unit) := ContinuousMap.const X ()
  have hz : SingularMayerVietoris.singularHomologyMap f 1 a = 0 := Subsingleton.elim _ _
  have hn := crossProductHomology_natural f (ContinuousMap.id Y) n a b
  change
    SingularMayerVietoris.singularHomologyMap (f.prodMap (ContinuousMap.id Y)) (n + 1)
        (crossProductHomology X Y n a b) =
      crossProductHomology Unit Y n (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id Y) n b) at hn
  rw [hz, map_zero, LinearMap.zero_apply] at hn
  calc
    _ =
        SingularMayerVietoris.singularHomologyMap (ContinuousMap.snd : C(Unit × Y, Y)) (n + 1)
          (SingularMayerVietoris.singularHomologyMap (f.prodMap (ContinuousMap.id Y)) (n + 1)
            (crossProductHomology X Y n a b)) := by
      exact
        LinearMap.congr_fun
          (singularHomologyMap_comp (f.prodMap (ContinuousMap.id Y))
            (ContinuousMap.snd : C(Unit × Y, Y)) (n + 1))
          (crossProductHomology X Y n a b)
    _ = 0 := by rw [hn, map_zero]

end
