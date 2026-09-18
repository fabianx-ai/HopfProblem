/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.Topology.Homotopy.CellFilling
import Lib.Geometry.Manifold.Morse.CellStructure

/-!
# Relative disk lifting from homotopy-group vanishing

For path-connected spaces, uniform source vanishing below `d` and target
vanishing below `d + 1` give relative disk lifting through dimension `d`.
The supplied side homotopy is retained exactly. Dimension zero is included;
no surjectivity assumption on an induced homotopy-group map is needed.
-/

set_option autoImplicit false
open Set Topology
noncomputable section

/-- Homotopy-group vanishing gives relative disk lifting with an exact
prescribed side.

## Proof

Fix a disk of dimension m ≤ d, its boundary map a into X, target disk map u,
and compatible boundary homotopy H. Boundary extension in X, using source
vanishing in degrees 0 < k < d and path connectivity, gives a disk map v
extending a and taking the chosen value x at the center. Only its boundary
equation is needed below.

Set f = F ∘ v. On the boundary, H(0,s) = F(a(s)) = F(v(s)); at time one,
H(1,s) = u(s). These are precisely the two corner compatibilities for filling
the disk cylinder. Its dimension is m + 1 ≤ d + 1. Target vanishing in
degrees 0 < k < d + 1 and path connectivity therefore allow cylinder filling,
with chosen target point F(x). The resulting G has endpoints F ∘ v and u
and side exactly H. Together with v extending a, this is the required lifting
property for every disk of dimension at most d.

For d = 0, the disk is a point and its sphere is empty. The constant map at x
and a path in Y from F(x) to u's value give the conclusion. Both positive-degree
vanishing ranges are empty. The same extension and filling suppliers include
this case; source path connectivity is retained as a uniform hypothesis.
-/
theorem LowCellLifting.relativeDiskLifting_of_pi_vanishing
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] {d : ℕ}
    (F : C(X, Y)) (x : X)
    (hX : ∀ k, 0 < k → k < d → ∀ x : X, Subsingleton (π_ k X x))
    (hY : ∀ k, 0 < k → k < d + 1 → ∀ y : Y, Subsingleton (π_ k Y y)) :
    FiniteCells.RelativeDiskLifting F d := by
  intro V _ _ _ hd a u H h0 h1
  obtain ⟨v, hv, _⟩ := Sphere.exists_boundary_extension_of_pi hX hd a x
  have h0' : ∀ s, H (0, s) = (F.comp v) (DiskCylinder.boundaryToDisk s) :=
    fun s => (h0 s).trans (congrArg F (hv s).symm)
  obtain ⟨G, hG0, hG1, hGside⟩ :=
    CylinderFilling.exists_filling hY (Nat.add_le_add_right hd 1)
      (F.comp v) u H h0' h1 (F x)
  exact ⟨v, G, hv, hG0, hG1, hGside⟩
