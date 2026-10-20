/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.Topology.Homotopy.CellFilling
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Topology.Homotopy.BasedDiskLifting

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

/-- Lower homotopy vanishing and top homotopy surjectivity give relative disk
lifting through a positive dimension, retaining the prescribed side exactly.

## Proof

Fix a disk of dimension m ≤ n and compatible boundary data a, u, H. Split
into m < n and m = n. In the first case put d = n - 1. Positivity gives
d + 1 = n and m ≤ d. Source vanishing below n restricts to vanishing below d;
target vanishing below n is exactly vanishing below d + 1. The lower-dimensional
lifting theorem gives the required disk map and homotopy with exact side H.

In the second case, equality of finite dimensions gives a continuous linear
equivalence from the disk's normed vector space to real n-space. Source path
connectivity and homotopy vanishing below n supply a nullhomotopy of a to the
constant map at the chosen source point x. Apply prescribed-side top-disk
lifting with this nullhomotopy, the coordinate equivalence and surjectivity
on the nth homotopy group at x. Its conclusion is precisely the required
boundary equation, both endpoint equations and exact side H.

These cases exhaust m ≤ n. When n = 1 the low case has d = 0, hence point
disks and empty boundary; target path connectivity suffices there. For the
one-dimensional top case, source path connectivity gives the boundary
nullhomotopy and pi-one surjectivity supplies the lift. No positive-degree
vanishing condition is omitted. Dimension n = 0 is excluded.
-/
theorem TopCellLifting.relativeDiskLifting_of_pi_vanishing_of_surjective
    {n : ℕ} [Nonempty (Fin n)]
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (F : C(X, Y)) (x : X)
    (hX : ∀ k, 0 < k → k < n → ∀ x : X, Subsingleton (π_ k X x))
    (hY : ∀ k, 0 < k → k < n → ∀ y : Y, Subsingleton (π_ k Y y))
    (hsurj : Function.Surjective (Hurewicz.homotopyMap (n := n) F x)) :
    FiniteCells.RelativeDiskLifting F n := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  intro V _ _ _ hd a u H h0 h1
  by_cases hlow : Module.finrank ℝ V < n
  · have hdlow : Module.finrank ℝ V ≤ n - 1 := by omega
    have hXlow : ∀ k, 0 < k → k < n - 1 → ∀ x : X, Subsingleton (π_ k X x) :=
      fun k hk hkn => hX k hk (by omega)
    have hYlow : ∀ k, 0 < k → k < (n - 1) + 1 → ∀ y : Y, Subsingleton (π_ k Y y) :=
      fun k hk hkn => hY k hk (by omega)
    exact LowCellLifting.relativeDiskLifting_of_pi_vanishing F x hXlow hYlow
      V hdlow a u H h0 h1
  · have heq : Module.finrank ℝ V = n := by omega
    obtain ⟨L⟩ :=
      FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
        (show Module.finrank ℝ V = Module.finrank ℝ (Fin n → ℝ) by simpa using heq)
    have ha : a.Homotopic (ContinuousMap.const _ x) :=
      Sphere.boundary_homotopic_const_of_pi hX hd a x
    exact TopCellLifting.exists_disk_lift_of_boundary_nullhomotopic
      F x hsurj L a ha u H h0 h1
