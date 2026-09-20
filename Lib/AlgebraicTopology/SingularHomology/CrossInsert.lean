/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.CircleProduct
/-!
# Cross-insertion chains and their naturality

  Cross-insertion: the chain map inserting a point of `X` as a degenerate
  `Y`-factor in the singular chains of `X x Y`, its naturality in both factors,
  and the induced map on homology (Eilenberg-Steenrod, Foundations of Algebraic
  Topology, VIII.6, chain-level precursor of cross products).
-/



open Set Function Filter Manifold Topology

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Inserting a basepoint into a product factor -/

/-- The map `Y → X × Y` inserting the point `x` in the first factor. -/
def SingularHomology.crossInsertLeft {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) : C(Y, X × Y) :=
  ⟨fun y => (x, y), continuous_const.prodMk continuous_id⟩

/-- Point insertion commutes with the product of two continuous maps. -/
theorem SingularHomology.crossInsertLeft_natural {X Y X' Y' : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X')) (g : C(Y, Y'))
    (x : X) : (f.prodMap g).comp (crossInsertLeft x) = (crossInsertLeft (f x)).comp g :=
  rfl

/-- Chains induced by a product map through a point insertion equal insertion into the induced chains. -/
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
