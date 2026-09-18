/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.Naturality
import Lib.Topology.Homeomorph.DiskCube

/-!
# Based disk lifting from surjectivity on a homotopy group

A continuous map surjective on the based `n`th homotopy group lifts a map of an
`n`-disk, constant on its boundary, up to homotopy relative to that boundary.
The source and target are arbitrary topological spaces. No sphere, manifold,
connectivity or homology hypothesis is needed. This is not an exact lifting
theorem, nor a statement for arbitrary nonconstant boundary data.

The disk is the closed unit ball of a finite-dimensional real normed space,
with a supplied continuous linear identification with real `n`-space. The
positive-dimension hypothesis is expressed by `Nonempty (Fin n)`, as required
by the existing induced homotopy-group map.
-/

set_option autoImplicit false
open scoped Topology
noncomputable section
universe u

/-- A based disk map lifts up to relative homotopy when the induced map on its
homotopy group is surjective.

## Proof

Let `D` be the closed unit disk and `S` its norm-one boundary. Choose the
boundary-preserving disk–cube homeomorphism `e : D → Iⁿ` supplied by the
linear identification. Define `q(w) = u(e⁻¹(w))`. It is continuous and equals
`F(x)` on the cube boundary, since the inverse homeomorphism carries that
boundary into `S`. Hence it represents a based homotopy class.

Surjectivity gives a preimage class. Choose a representative `p : Iⁿ → X`,
equal to `x` on the cube boundary. Equality of the image class with `[q]`
means that there is a continuous homotopy `H` from `F ∘ p` to `q`, keeping
the entire cube boundary at `F(x)` throughout.

Set `v(z) = p(e(z))`. This is continuous and equals `x` on `S`. Pull back
the homotopy by defining `K(t,z) = H(t,e(z))`. Continuity follows from
continuity of `H` and the product map `(t,z) ↦ (t,e(z))`. At time zero this
is `F(v(z))`; at time one it is `u(e⁻¹(e(z))) = u(z)`. For `z ∈ S`, the
point `e(z)` lies on the cube boundary, so `K(t,z) = F(x)` at every time.
Thus `K` is the required homotopy relative to `S`.
-/
theorem BasedDiskLifting.exists_based_disk_lift_of_surjective
    {n : ℕ} [Nonempty (Fin n)]
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (F : C(X, Y)) (x : X)
    (hsurj : Function.Surjective (Hurewicz.homotopyMap (n := n) F x))
    (L : V ≃L[ℝ] (Fin n → ℝ))
    (u : C(DiskCylinder.Disk (E := V), Y))
    (hu : ∀ z : DiskCylinder.Disk (E := V),
      ‖(z : V)‖ = 1 → u z = F x) :
    ∃ v : C(DiskCylinder.Disk (E := V), X),
      (∀ z : DiskCylinder.Disk (E := V),
        ‖(z : V)‖ = 1 → v z = x) ∧
      (F.comp v).HomotopicRel u
        {z : DiskCylinder.Disk (E := V) | ‖(z : V)‖ = 1} := by
  let e := DiskCube.homeomorph L
  let q : GenLoop (Fin n) Y (F x) :=
    ⟨u.comp (e.symm : C(_, _)), fun z hz =>
      hu (e.symm z) ((DiskCube.symm_boundary_iff L z).mpr hz)⟩
  obtain ⟨a, ha⟩ := hsurj ⟦q⟧
  obtain ⟨p, hp⟩ := Quotient.exists_rep a
  have he : Hurewicz.homotopyMap (n := n) F x ⟦p⟧ = ⟦q⟧ :=
    (congrArg (Hurewicz.homotopyMap (n := n) F x) hp).trans ha
  have hh : GenLoop.Homotopic (Hurewicz.DegreeTwo.mapGenLoop F x p) q :=
    Quotient.exact he
  obtain ⟨H⟩ := hh
  let v : C(DiskCylinder.Disk (E := V), X) := p.val.comp (e : C(_, _))
  refine
    ⟨v, ?_,
      ⟨{ toFun := fun z => H (z.1, e z.2)
         continuous_toFun :=
           H.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd))
         map_zero_left := ?_
         map_one_left := ?_
         prop' := ?_ }⟩⟩
  · intro z hz
    exact p.property (e z) ((DiskCube.boundary_iff L z).mpr hz)
  · intro z
    exact H.apply_zero (e z)
  · intro z
    exact (H.apply_one (e z)).trans (congrArg u (e.symm_apply_apply z))
  · intro t z hz
    exact H.eq_fst t ((DiskCube.boundary_iff L z).mpr hz)
