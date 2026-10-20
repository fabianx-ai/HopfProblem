/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.Naturality
import Lib.Topology.Homeomorph.DiskCube
import Lib.Topology.Homotopy.CylinderHEP

/-!
# Based disk lifting from surjectivity on a homotopy group

A continuous map surjective on the based `n`th homotopy group lifts a map of an
`n`-disk, constant on its boundary, up to homotopy relative to that boundary.
The source and target are arbitrary topological spaces. No sphere, manifold,
connectivity or homology hypothesis is needed. This is not an exact lifting
theorem. For nonconstant boundary data with a supplied source nullhomotopy,
the second theorem retains an exact prescribed boundary homotopy.

This is the disk-lifting step used in the proof of the Whitehead theorem and in cellular
approximation: a map which is surjective on `π_n` lets one push a cell of the target back into
the source, up to a homotopy fixing the attaching map.

The disk is the closed unit ball of a finite-dimensional real normed space,
with a supplied continuous linear identification with real `n`-space. The
positive-dimension hypothesis is expressed by `Nonempty (Fin n)`, as required
by the existing induced homotopy-group map.

## Main results

* `BasedDiskLifting.exists_based_disk_lift_of_surjective`: lifting of a disk with constant
  boundary data.
* `TopCellLifting.exists_disk_lift_of_boundary_nullhomotopic`: lifting with a prescribed
  boundary homotopy.

## References

* A. Hatcher, *Algebraic Topology*, §4.1 (the compression lemma and the Whitehead theorem)
-/

set_option autoImplicit false
open scoped Topology
open Set Topology
noncomputable section
universe u

/-- If `F : X → Y` is surjective on `π_n(X, x)`, then every map `u` of the `n`-disk into `Y`
which is constant equal to `F x` on the boundary sphere lifts to a map `v` of the disk into `X`,
constant equal to `x` on the boundary, with `F ∘ v` homotopic to `u` relative to the boundary
(Hatcher, *Algebraic Topology*, §4.1). -/
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
  -- Let `D` be the closed unit disk and `S` its norm-one boundary. Choose the
  -- boundary-preserving disk-cube homeomorphism `e : D → Iⁿ` supplied by the linear
  -- identification. Define `q(w) = u(e⁻¹(w))`. It is continuous and equals `F(x)` on the cube
  -- boundary, since the inverse homeomorphism carries that boundary into `S`. Hence it
  -- represents a based homotopy class.
  --
  -- Surjectivity gives a preimage class. Choose a representative `p : Iⁿ → X`, equal to `x` on
  -- the cube boundary. Equality of the image class with `[q]` means that there is a continuous
  -- homotopy `H` from `F ∘ p` to `q`, keeping the entire cube boundary at `F(x)` throughout.
  --
  -- Set `v(z) = p(e(z))`. This is continuous and equals `x` on `S`. Pull back the homotopy by
  -- defining `K(t,z) = H(t,e(z))`. At time zero this is `F(v(z))`; at time one it is
  -- `u(e⁻¹(e(z))) = u(z)`. For `z ∈ S`, the point `e(z)` lies on the cube boundary, so
  -- `K(t,z) = F(x)` at every time. Thus `K` is the required homotopy relative to `S`.
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

/-- If `F : X → Y` is surjective on `π_n(X, x)`, `a` is a map of the boundary sphere into `X`
which is nullhomotopic, and `H` is a homotopy from `F ∘ a` to the boundary restriction of a disk
map `u`, then `u` lifts to a disk map `v` of the disk into `X` with boundary exactly `a`,
together with a homotopy from `F ∘ v` to `u` whose boundary restriction is exactly `H`
(Hatcher, *Algebraic Topology*, §4.1). -/
theorem TopCellLifting.exists_disk_lift_of_boundary_nullhomotopic
    {n : ℕ} [Nonempty (Fin n)]
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : C(X, Y)) (x : X)
    (hsurj : Function.Surjective (Hurewicz.homotopyMap (n := n) F x))
    (L : V ≃L[ℝ] (Fin n → ℝ))
    (a : C(DiskCylinder.Sphere (E := V), X))
    (ha : a.Homotopic (ContinuousMap.const _ x))
    (u : C(DiskCylinder.Disk (E := V), Y))
    (H : C(unitInterval × DiskCylinder.Sphere (E := V), Y))
    (h0 : ∀ s, H (0, s) = F (a s))
    (h1 : ∀ s, H (1, s) = u (DiskCylinder.boundaryToDisk s)) :
    ∃ (v : C(DiskCylinder.Disk (E := V), X))
      (G : C(unitInterval × DiskCylinder.Disk (E := V), Y)),
      (∀ s, v (DiskCylinder.boundaryToDisk s) = a s) ∧
      (∀ z, G (0, z) = F (v z)) ∧
      (∀ z, G (1, z) = u z) ∧
      ∀ t s, G (t, DiskCylinder.boundaryToDisk s) = H (t, s) := by
  -- Write `D` for the disk and `S` for its boundary, and `c` for the constant map at `x`.
  -- Reverse the supplied nullhomotopy to get a mapping-space path `A` from `c` to `a`.
  -- Postcompose to get `FA` from `F ∘ c` to `F ∘ a`. The prescribed `H` gives a path `HP` from
  -- `F ∘ a` to `u|S`. Then `K = HP⁻¹ · FA⁻¹` runs from `u|S` to `F ∘ c`.
  --
  -- Boundary transport extends `K` to a path `E` from `u` to a disk map `u₀` whose boundary is
  -- `F(x)`. The based-disk theorem gives `p` with boundary `x` and a homotopy `B` from `F ∘ p`
  -- to `u₀` fixed on `S`. Viewed as a mapping-space path, `B` restricts to the constant path at
  -- `F ∘ c`.
  --
  -- Transport `p` along `A` to obtain `v` with boundary `a` and a path `P` from `p` to `v`
  -- restricting to `A`. Its postcomposition `FP` restricts to `FA`. Thus
  -- `R = FP⁻¹ · (B · E⁻¹)` runs from `F ∘ v` to `u`, and its exact restriction is
  -- `Q = FA⁻¹ · (const · K⁻¹)`.
  --
  -- Path normalization gives an endpoint-fixed homotopy from `Q` to `HP`: reverse the inner
  -- concatenation, remove the constant segment, reassociate and cancel `FA⁻¹ · FA`. Cylinder
  -- side rectification extends this change of side while fixing both end faces. Its final slice
  -- `G` therefore has endpoints `F ∘ v` and `u` and side exactly `HP(t)(s) = H(t,s)`.
  let c : C(DiskCylinder.Sphere (E := V), X) :=
    ContinuousMap.const _ x
  obtain ⟨Ac⟩ := ha.symm
  let A : Path c a := MappingPaths.ofHomotopy Ac
  let FA : Path (F.comp c) (F.comp a) := A.map (ContinuousMap.continuous_postcomp F)
  let HP : Path (F.comp a) (u.comp DiskCylinder.boundaryToDisk) :=
    { toContinuousMap := H.curry
      source' := ContinuousMap.ext h0
      target' := ContinuousMap.ext h1 }
  let K := HP.symm.trans FA.symm
  obtain ⟨u₀, E, hE, hu₀⟩ := BoundaryPathTransport.exists_transport u K rfl
  have hu₀' :
    ∀ z : DiskCylinder.Disk (E := V),
      ‖(z : V)‖ = 1 → u₀ z = F x := by
    intro z hz
    exact ContinuousMap.congr_fun hu₀ ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨p, hp, ⟨B⟩⟩ := BasedDiskLifting.exists_based_disk_lift_of_surjective F x hsurj L u₀ hu₀'
  have hp' : p.comp DiskCylinder.boundaryToDisk = c := by
    apply ContinuousMap.ext
    intro s
    exact hp (DiskCylinder.boundaryToDisk s) (mem_sphere_zero_iff_norm.mp s.property)
  obtain ⟨v, P, hP, hv⟩ := BoundaryPathTransport.exists_transport p A hp'
  let FP : Path (F.comp p) (F.comp v) := P.map (ContinuousMap.continuous_postcomp F)
  let BP := MappingPaths.ofHomotopy B.toHomotopy
  have hFP :
    MappingPaths.Over
      (fun w : C(DiskCylinder.Disk (E := V), Y) =>
        w.comp DiskCylinder.boundaryToDisk)
      FP FA := by
    intro t
    apply ContinuousMap.ext
    intro s
    exact congrArg F (ContinuousMap.congr_fun (hP t) s)
  have hBP :
    MappingPaths.Over
      (fun w : C(DiskCylinder.Disk (E := V), Y) =>
        w.comp DiskCylinder.boundaryToDisk)
      BP (Path.refl (F.comp c)) := by
    intro t
    apply ContinuousMap.ext
    intro s
    have hs : ‖(DiskCylinder.boundaryToDisk s : V)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp s.property
    exact (B.eq_fst t hs).trans (congrArg F (hp (DiskCylinder.boundaryToDisk s) hs))
  let R := FP.symm.trans (BP.trans E.symm)
  let Q := FA.symm.trans ((Path.refl (F.comp c)).trans K.symm)
  have hR :
    MappingPaths.Over
      (fun w : C(DiskCylinder.Disk (E := V), Y) =>
        w.comp DiskCylinder.boundaryToDisk)
      R Q :=
    hFP.symm.trans (hBP.trans hE.symm)
  have hQ : Q.Homotopic HP := MappingPaths.normalization_cancellation FA HP
  obtain ⟨G, hG0, hG1, hGside⟩ := SideRectification.exists_rectification R Q HP hR hQ
  exact ⟨v, G, fun s => ContinuousMap.congr_fun hv s, hG0, hG1, hGside⟩
