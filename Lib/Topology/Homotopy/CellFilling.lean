/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Topology.Homotopy.CylinderHEP
import Lib.AlgebraicTopology.Hurewicz.CubeSphere

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973

theorem Sphere.homotopic_const_discrete {Z X : Type} [TopologicalSpace Z]
    [DiscreteTopology Z] [TopologicalSpace X] [PathConnectedSpace X] (u : C(Z, X)) (x : X) :
    u.Homotopic (ContinuousMap.const Z x) := by
  refine
    ⟨{  toFun := fun p => (PathConnectedSpace.somePath (u p.2) x) p.1
        continuous_toFun :=
          continuous_prod_of_discrete_right.mpr
            (fun z => (PathConnectedSpace.somePath (u z) x).continuous)
        map_zero_left := fun z => (PathConnectedSpace.somePath (u z) x).source
        map_one_left := fun z => (PathConnectedSpace.somePath (u z) x).target }⟩

theorem Sphere.real_unitSphere_finite : (Metric.sphere (0 : ℝ) 1).Finite := by
  apply (Set.toFinite ({1, -1} : Set ℝ)).subset
  intro x hx
  have h : |x| = |(1 : ℝ)| := by simpa using mem_sphere_zero_iff_norm.mp hx
  rcases abs_eq_abs.mp h with h | h <;> simp [h]

theorem Sphere.homotopic_const_of_homeomorph {Z W X : Type} [TopologicalSpace Z]
    [TopologicalSpace W] [TopologicalSpace X] (e : Z ≃ₜ W) (u : C(Z, X)) (x : X)
    (h : (u.comp (e.symm : C(W, Z))).Homotopic (ContinuousMap.const W x)) :
    u.Homotopic (ContinuousMap.const Z x) := by
  have hh := h.comp (ContinuousMap.Homotopic.refl (e : C(Z, W)))
  convert hh using 1
  · apply ContinuousMap.ext
    intro z
    exact (congrArg u (e.symm_apply_apply z)).symm
  · rfl

theorem Sphere.boundary_homotopic_const_of_pi {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] {d : ℕ} (hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))
    (hd : Module.finrank ℝ V ≤ d) (u : C(DiskCylinder.Sphere (E := V), X)) (x : X) :
    u.Homotopic (ContinuousMap.const _ x) := by
  classical
    cases subsingleton_or_nontrivial V with
  | inl
    h =>
    have hempty (s : DiskCylinder.Sphere (E := V)) : False :=
      UnitSphereEquiv.vector_ne_zero s (Subsingleton.elim _ _)
    have he : u = ContinuousMap.const _ x := ContinuousMap.ext (fun s => (hempty s).elim)
    rw [he]
  | inr h =>
    by_cases hd1 : Module.finrank ℝ V = 1
    · obtain ⟨L⟩ :=
        FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
          (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hd1)
      let e := UnitSphereEquiv.homeomorph L
      let : Finite (DiskCylinder.Sphere (E := ℝ)) := real_unitSphere_finite.to_subtype
      let : Finite (DiskCylinder.Sphere (E := V)) := Finite.of_injective e e.injective
      exact homotopic_const_discrete u x
    · have hdpos : 0 < Module.finrank ℝ V := Module.finrank_pos
      let n := Module.finrank ℝ V - 1
      have hn : 0 < n := by dsimp [n]; omega
      have hnd : n < d := by dsimp [n]; omega
      obtain ⟨L⟩ :=
        FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
          (show Module.finrank ℝ V = Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
            by
            simp only [finrank_euclideanSpace, Fintype.card_fin]
            dsimp [n]
            omega)
      let e := UnitSphereEquiv.homeomorph L
      let v : C(SphereCube.Sphere n, X) := u.comp (e.symm : C(_, _))
      let := hpi n hn hnd (v (SphereCube.point n))
      obtain ⟨H⟩ := SphereCube.homotopicRel_const_of_subsingleton hn v
      have hstart : v.Homotopic (ContinuousMap.const _ (v (SphereCube.point n))) :=
        ⟨H.toHomotopy⟩
      have hv : v.Homotopic (ContinuousMap.const _ x) :=
        hstart.trans
          ⟨(PathConnectedSpace.somePath (v (SphereCube.point n)) x).toHomotopyConst⟩
      exact homotopic_const_of_homeomorph e u x hv

theorem Sphere.exists_boundary_extension_of_pi {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] {d : ℕ} (hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))
    (hd : Module.finrank ℝ V ≤ d) (u : C(DiskCylinder.Sphere (E := V), X)) (x : X) :
    ∃ v : C(DiskCylinder.Disk (E := V), X),
      (∀ s, v (DiskCylinder.boundaryToDisk s) = u s) ∧ v ⟨0, by simp⟩ = x := by
  classical
    cases isEmpty_or_nonempty (DiskCylinder.Sphere (E := V)) with
  | inl h => exact ⟨ContinuousMap.const _ x, fun s => isEmptyElim s, rfl⟩
  | inr h =>
    let s0 : DiskCylinder.Sphere (E := V) := Classical.choice h
    obtain ⟨H⟩ := (boundary_homotopic_const_of_pi hpi hd u x).symm
    let G := H.toContinuousMap
    have h0 : ∀ s, G (0, s) = x := H.map_zero_left
    refine ⟨DiskCone.extension s0 G x h0, ?_, DiskCone.extension_center s0 G x h0⟩
    intro s
    exact (DiskCone.extension_boundary s0 G x h0 s).trans (H.map_one_left s)

theorem CylinderFilling.exists_filling {V X : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace X] [PathConnectedSpace X] {d : ℕ}
    (hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))
    (hd : Module.finrank ℝ V + 1 ≤ d) (f g : C(DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (DiskCylinder.boundaryToDisk s)) (x : X) :
    ∃ G : C((unitInterval) × DiskCylinder.Disk (E := V), X),
      (∀ z, G (0, z) = f z) ∧
        (∀ z, G (1, z) = g z) ∧ ∀ t s, G (t, DiskCylinder.boundaryToDisk s) = H (t, s) := by
  let b := CylinderBoundary.glued f g H h0 h1
  let e := CylinderBall.boundaryHomeomorph (V := V)
  let u :=
    b.comp
      (e.symm : C(DiskCylinder.Sphere (E := ℝ × V), CylinderBall.boundary (V := V)))
  have hdim : Module.finrank ℝ (ℝ × V) ≤ d := by
    simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using hd
  obtain ⟨v, hv, _⟩ := Sphere.exists_boundary_extension_of_pi hpi hdim u x
  let G : C((unitInterval) × DiskCylinder.Disk (E := V), X) :=
    v.comp (CylinderBall.homeomorph (V := V) : C(_, _))
  have hb (p : CylinderBall.boundary (V := V)) : G p.val = b p := by
    change v (DiskCylinder.boundaryToDisk (CylinderBall.boundaryHomeomorph p)) = b p
    exact
      (hv (CylinderBall.boundaryHomeomorph p)).trans
        (congrArg b (CylinderBall.boundaryHomeomorph.symm_apply_apply p))
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z
    exact
      (hb (CylinderBoundary.lower (DiskCylinder.bottomMap z))).trans
        (CylinderBoundary.glued_bottom f g H h0 h1 z)
  · intro z
    exact
      (hb (CylinderBoundary.top z)).trans (CylinderBoundary.glued_top f g H h0 h1 z)
  · intro t s
    exact
      (hb (CylinderBoundary.lower (DiskCylinder.sideMap (t, s)))).trans
        (CylinderBoundary.glued_side f g H h0 h1 t s)

end Mathoverflow1973
