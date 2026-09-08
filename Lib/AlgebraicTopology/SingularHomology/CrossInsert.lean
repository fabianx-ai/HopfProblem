/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.CircleProduct


set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

def SingularHomology.crossInsertLeft {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) : C(Y, X × Y) :=
  ⟨fun y => (x, y), continuous_const.prodMk continuous_id⟩

theorem SingularHomology.crossInsertLeft_natural {X Y X' Y' : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X')) (g : C(Y, Y'))
    (x : X) : (f.prodMap g).comp (crossInsertLeft x) = (crossInsertLeft (f x)).comp g :=
  rfl

theorem SingularHomology.inducedChain_crossInsertLeft {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (x : X) (n : ℕ) (c : SingularChains.Chains Y n) :
    SingularChains.inducedChain (f.prodMap g) n
        (SingularChains.inducedChain (crossInsertLeft x) n c) =
      SingularChains.inducedChain (crossInsertLeft (f x)) n (SingularChains.inducedChain g n c) := by
  have h :=
    congrArg (fun h : C(Y, X' × Y') => SingularChains.inducedChain h n c)
      (crossInsertLeft_natural f g x)
  simpa only [SingularChains.inducedChain_comp, LinearMap.comp_apply] using h
end Mathoverflow1973
