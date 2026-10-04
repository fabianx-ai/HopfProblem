/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.PuncturedBall

/-!
# The connecting homomorphism at a point of a manifold and its naturality

For a point `x` of a manifold `M` with a chart neighbourhood `U` (`LocalDegree.NeighborhoodData`),
Mayer–Vietoris for the cover `{M ∖ x, U}` gives the connecting homomorphism
`H_{k+1}(M) → H_k(S(E))` to the homology of the unit sphere of the model space
(`LocalDegree.NativeNeighborhood.sphereConnecting`), independent of the chart radius
(`sphereConnecting_eq`) and an isomorphism `H_{k+2}(M) ≅ H_{k+1}(S(E))` when `M ∖ x` is
contractible (`sphereHomologyEquiv`).  Under a homeomorphism `e` with `e x = y` the connecting maps
correspond through the sphere map of the derivative of the chart transition
(`LocalDegree.PointTransition.connecting_naturality`, `pointConnecting_diffeomorph`); a linear
isomorphism `B` acts on sphere homology through `LinearSphereAction.homologyEquiv`, and the
normalised boundary map of a `BoundaryData` acts by the sign of the relative determinant
(`LocalDegree.BoundaryData.normalized_homology_eq_sign_smul`).  Cf. Hatcher, *Algebraic
Topology*, §2.2 (local degree).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- The homotopy equivalence `S(E) ≃ₕ {x}ᶜ ∩ openSet x d` from the unit sphere of the model space
to the punctured chart neighbourhood of `x`, through the inner boundary sphere of `d`. -/
def LocalDegree.NativeNeighborhood.overlapSphereEquiv {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Metric.sphere (0 : E) 1 ≃ₕ ↥({ x }ᶜ ∩ openSet x d) :=
  (PuncturedBall.sphereHomotopyEquiv d.radius d.innerBoundary.radius
        d.innerBoundary.radius_pos
        (by
          rw [d.innerBoundary_radius]
          exact half_lt_self d.radius_pos)).trans
    (puncturedHomeomorph x d).toHomotopyEquiv

/-- For separated neighbourhoods `D` of the finite set `P`, the homotopy equivalence
`S(E) ≃ₕ Pᶜ ∩ D.neighborhood x` at `x ∈ P`. -/
def LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    Metric.sphere (0 : E) 1 ≃ₕ ↥(Pᶜ ∩ D.neighborhood x) :=
  (LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).trans
    (Homeomorph.setCongr (D.overlap_eq x).symm).toHomotopyEquiv

/-- `D.overlapSphereEquiv x u` is the chart image of `innerBoundary.radius • u` centred at `x`. -/
theorem LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv_apply {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P)
    (u : Metric.sphere (0 : E) 1) :
    (D.overlapSphereEquiv x u).val =
      NativeParametrization.centered (x : M) ((D.data x).innerBoundary.radius • (u : E)) :=
  rfl

/-- `D.overlapMap x ∘ D.overlapSphereEquiv x` is the inner boundary map
`(D.data x).innerBoundary.map`. -/
theorem LocalDegree.SeparatedNeighborhoods.overlapMap_sphereEquiv {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    (D.overlapMap x).comp (D.overlapSphereEquiv x).toFun = (D.data x).innerBoundary.map := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, overlapMap_coe, overlapSphereEquiv_apply,
    LocalDegree.BoundaryData.map_coe]
  rfl

/-- The homotopy equivalence `S(E) ≃ₕ S(F)` induced by a linear isomorphism `B : E ≃L[ℝ] F`
(through the punctured space). -/
def LinearSphereAction.sphereHomotopyEquiv {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) :
    Metric.sphere (0 : E) 1 ≃ₕ Metric.sphere (0 : F) 1 :=
  (LocalDegree.linearSphereEquiv B 1 zero_lt_one).trans
    (PuncturedRadial.sphereHomotopyEquiv 1 zero_lt_one).symm

/-- The forward map of `sphereHomotopyEquiv B` is the normalised sphere map `sphereMap B`. -/
theorem LinearSphereAction.sphereHomotopyEquiv_toFun {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) :
    (sphereHomotopyEquiv B).toFun = sphereMap B.toContinuousLinearMap B.injective :=
  normalized_linearSphereMap B 1 zero_lt_one

/-- The homology isomorphism `H_k(S(E)) ≃ H_k(S(F))` induced by `B : E ≃L[ℝ] F`. -/
def LinearSphereAction.homologyEquiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : F) 1) k :=
  SingularHomology.homotopyEquivHomologyEquiv (sphereHomotopyEquiv B) k

/-- `homologyEquiv B k a = H_k(sphereMap B) a`. -/
theorem LinearSphereAction.homologyEquiv_apply {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k) :
    homologyEquiv B k a =
      SingularMayerVietoris.singularHomologyMap (sphereMap B.toContinuousLinearMap B.injective) k
        a := by
  change SingularMayerVietoris.singularHomologyMap (sphereHomotopyEquiv B).toFun k a = _
  rw [sphereHomotopyEquiv_toFun]

/-- The connecting homomorphism `H_{k+1}(M) → H_k(S(E))` at the point `x` of `M`: the
Mayer–Vietoris connecting map of the cover `({x}ᶜ, openSet x d)` followed by the inverse of the
overlap sphere equivalence. -/
def LocalDegree.NativeNeighborhood.sphereConnecting {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] (k : ℕ) :
    SingularMayerVietoris.SingularHomology M (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k :=
  (SingularHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv x d)
        k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism { x }ᶜ (openSet x d)
      isClosed_singleton.isOpen_compl (isOpen_openSet x d) (singlePoint_cover x d) k)

/-- If `M ∖ {x}` is contractible, the connecting map is an isomorphism
`H_{k+2}(M) ≃ H_{k+1}(S(E))`. -/
def LocalDegree.NativeNeighborhood.sphereHomologyEquiv {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] [ContractibleSpace ({ x }ᶜ : Set M)] (k : ℕ) :
    SingularMayerVietoris.SingularHomology M (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) (k + 1) := by
  let : ContractibleSpace (openSet x d) := openSet_contractible x d
  exact
    (Suspension.contractibleCoverHomologyHigherEquiv { x }ᶜ (openSet x d)
          isClosed_singleton.isOpen_compl (isOpen_openSet x d) (singlePoint_cover x d) k).trans
      (SingularHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv x d) (k + 1)).symm

/-- On homology, the normalised boundary map `b.normalizedMap` of `b : BoundaryData f L s` agrees
with the sphere map of `L`. -/
theorem LocalDegree.BoundaryData.normalized_homology_compare {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {L : E ≃L[ℝ] F} {s : Set E} (b : LocalDegree.BoundaryData f L s) (k : ℕ) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap k =
      SingularMayerVietoris.singularHomologyMap
        (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) k := by
  change
    SingularMayerVietoris.singularHomologyMap (PuncturedRadial.toSphere.comp b.map) k = _
  rw [SingularHomology.singularHomologyMap_comp, b.homology_compare, ←
    SingularHomology.singularHomologyMap_comp,
    LinearSphereAction.normalized_linearSphereMap]

/-- For `b : BoundaryData f L s` on `ℝⁿ⁺²` and a second isomorphism `B`, `H_{k+1}(b.normalizedMap)`
is `sign det (B⁻¹ ∘ L)` times `H_{k+1}(sphereMap B)`. -/
theorem LocalDegree.BoundaryData.normalized_homology_eq_sign_smul {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) {f : EuclideanSpace ℝ (Fin (n + 2)) → F}
    {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F} {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (b : LocalDegree.BoundaryData f L s) (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap (k + 1) a =
      (SignType.sign (L.trans B.symm).toLinearEquiv.toLinearMap.det : ℤ) •
        SingularMayerVietoris.singularHomologyMap
          (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
  rw [b.normalized_homology_compare]
  exact LinearSphereAction.homology_relative_sign n L B k a

/-- The map `S(E) → S(E)` induced by a homeomorphism `e` with `e x = y` mapping the chart
neighbourhood of `x` into that of `y`, through the overlap sphere equivalences at `x` and `y`. -/
def LocalDegree.PointTransition.coordinateMap {E F G M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G} {Wx Wy : Set M}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered (D := E) x) Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy)) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1) :=
  CoverNaturality.overlapCoordinateMap { x }ᶜ
    (LocalDegree.NativeNeighborhood.openSet x dx) { y }ᶜ
    (LocalDegree.NativeNeighborhood.openSet y dy) e.toHomotopyEquiv.toFun
    (maps_point_complement e x y he) hV
    (LocalDegree.NativeNeighborhood.overlapSphereEquiv x dx)
    (LocalDegree.NativeNeighborhood.overlapSphereEquiv y dy)

/-- `coordinateMap x y dx dy e he hV u` is the normalisation of the chart coordinate at `y` of
`e` applied to the chart point `innerBoundary.radius • u` at `x`. -/
theorem LocalDegree.PointTransition.coordinateMap_coe {E F G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G}
    {Wx Wy : Set M}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered (D := E) x) Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy))
    (u : Metric.sphere (0 : E) 1) :
    (coordinateMap x y dx dy e he hV u).val =
      ‖(NativeParametrization.centered (D := E) y).symm
              (e
                (NativeParametrization.centered (D := E) x
                  (dx.innerBoundary.radius • (u : E))))‖⁻¹ •
        (NativeParametrization.centered (D := E) y).symm
          (e
            (NativeParametrization.centered (D := E) x
              (dx.innerBoundary.radius • (u : E)))) :=
  rfl

/-- Naturality of the point connecting map under `e`: `H_k(coordinateMap) ∘ sphereConnecting x dx`
equals `sphereConnecting y dy ∘ H_{k+1}(e)`. -/
theorem LocalDegree.PointTransition.connecting_naturality {E F G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G}
    {Wx Wy : Set M}
    (dx :
      LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered (D := E) x) Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy))
    [T1Space M] (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (coordinateMap x y dx dy e he hV) k
        (LocalDegree.NativeNeighborhood.sphereConnecting x dx k a) =
      LocalDegree.NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomotopyEquiv.toFun (k + 1) a) :=
  CoverNaturality.normalized_connecting_naturality { x }ᶜ
    (LocalDegree.NativeNeighborhood.openSet x dx) { y }ᶜ
    (LocalDegree.NativeNeighborhood.openSet y dy) e.toHomotopyEquiv.toFun
    (maps_point_complement e x y he) hV
    (LocalDegree.NativeNeighborhood.overlapSphereEquiv x dx)
    (LocalDegree.NativeNeighborhood.overlapSphereEquiv y dy) isClosed_singleton.isOpen_compl
    (LocalDegree.NativeNeighborhood.isOpen_openSet x dx)
    (LocalDegree.NativeNeighborhood.singlePoint_cover x dx) isClosed_singleton.isOpen_compl
    (LocalDegree.NativeNeighborhood.isOpen_openSet y dy)
    (LocalDegree.NativeNeighborhood.singlePoint_cover y dy) k a

/-- The coordinate map of the identity between `d.restrictRadius r` and `d` is the identity of the
sphere. -/
theorem LocalDegree.NativeNeighborhood.coordinateMap_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    LocalDegree.PointTransition.coordinateMap x x (d.restrictRadius r hr hrR) d
        (Homeomorph.refl M) (identity_center x) (mapsTo_restrictRadius x d r hr hrR) =
      ContinuousMap.id (Metric.sphere (0 : E) 1) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [LocalDegree.PointTransition.coordinateMap_coe]
  let ds := d.restrictRadius r hr hrR
  change
    ‖(NativeParametrization.centered (D := E) x).symm
              (NativeParametrization.centered (D := E) x
                (ds.innerBoundary.radius • (u : E)))‖⁻¹ •
        (NativeParametrization.centered (D := E) x).symm
          (NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E))) =
      (u : E)
  have hu : ds.innerBoundary.radius • (u : E) ∈ (NativeParametrization.centered x).source :=
    closedBall_subset_source x ds (Metric.ball_subset_closedBall (ds.innerBoundary_mem_ball u))
  have hleft :
    (NativeParametrization.centered (D := E) x).symm
        (NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E))) =
      ds.innerBoundary.radius • (u : E) :=
    (NativeParametrization.centered x).left_inv' hu
  rw [hleft, LocalDegree.norm_radius_smul _ ds.innerBoundary.radius_pos,
    inv_smul_smul₀ ds.innerBoundary.radius_pos.ne']

/-- `sphereConnecting x (d.restrictRadius r hr hrR) k = sphereConnecting x d k`. -/
theorem LocalDegree.NativeNeighborhood.sphereConnecting_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) [T1Space M] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    sphereConnecting x (d.restrictRadius r hr hrR) k a = sphereConnecting x d k a := by
  have h :=
    LocalDegree.PointTransition.connecting_naturality x x (d.restrictRadius r hr hrR) d
      (Homeomorph.refl M) (identity_center x) (mapsTo_restrictRadius x d r hr hrR) k a
  rw [coordinateMap_restrictRadius, SingularHomology.singularHomologyMap_id,
    LinearMap.id_apply] at h
  change
    sphereConnecting x (d.restrictRadius r hr hrR) k a =
      sphereConnecting x d k
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id M) (k + 1) a) at h
  rwa [SingularHomology.singularHomologyMap_id, LinearMap.id_apply] at h

/-- The point connecting map at `x` does not depend on the neighbourhood datum:
`sphereConnecting x d k a = sphereConnecting x d' k a`. -/
theorem LocalDegree.NativeNeighborhood.sphereConnecting_eq {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {f' : M → F'}
    {L' : E ≃L[ℝ] F'} {W' : Set M}
    (d' :
      LocalDegree.NeighborhoodData (f' ∘ NativeParametrization.centered (D := E) x) L'
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W'))
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    sphereConnecting x d k a = sphereConnecting x d' k a := by
  let ρ := Min.min d.radius d'.radius
  have hρ : 0 < ρ := lt_min d.radius_pos d'.radius_pos
  rw [← sphereConnecting_restrictRadius x d ρ hρ (min_le_left _ _) k a, ←
    sphereConnecting_restrictRadius x d' ρ hρ (min_le_right _ _) k a]
  rfl

/-- When `dx` is a neighbourhood datum for the chart transition `chart_y⁻¹ ∘ e ∘ chart_x` itself,
the coordinate map is the normalised inner boundary map of `dx`. -/
theorem LocalDegree.PointTransition.coordinateMap_eq_boundary {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      LocalDegree.NeighborhoodData
        (((NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          NativeParametrization.centered (D := E) x)
        Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy)) :
    coordinateMap x y dx dy e he hV = dx.innerBoundary.normalizedMap :=
  rfl

/-- In the situation of `coordinateMap_eq_boundary`, `H_k(coordinateMap)` is `H_k(sphereMap Lx)`
for the linear part `Lx` of the chart transition. -/
theorem LocalDegree.PointTransition.coordinateMap_homology {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      LocalDegree.NeighborhoodData
        (((NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          NativeParametrization.centered (D := E) x)
        Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy))
    (k : ℕ) :
    SingularMayerVietoris.singularHomologyMap (coordinateMap x y dx dy e he hV) k =
      SingularMayerVietoris.singularHomologyMap
        (LinearSphereAction.sphereMap Lx.toContinuousLinearMap Lx.injective) k := by
  rw [coordinateMap_eq_boundary]
  exact dx.innerBoundary.normalized_homology_compare k

/-- In the situation of `coordinateMap_eq_boundary`: `sphereConnecting y dy k ∘ H_{k+1}(e)` equals
`H_k(sphereMap Lx) ∘ sphereConnecting x d₀ k` for any neighbourhood datum `d₀` at `x`. -/
theorem LocalDegree.PointTransition.connecting_derivative_naturality {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      LocalDegree.NeighborhoodData
        (((NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          NativeParametrization.centered (D := E) x)
        Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (LocalDegree.NativeNeighborhood.openSet x dx)
        (LocalDegree.NativeNeighborhood.openSet y dy))
    [T1Space M] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f₀ : M → F} {L₀ : E ≃L[ℝ] F}
    {W₀ : Set M}
    (d₀ :
      LocalDegree.NeighborhoodData (f₀ ∘ NativeParametrization.centered (D := E) x) L₀
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W₀))
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    LocalDegree.NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomotopyEquiv.toFun (k + 1) a) =
      SingularMayerVietoris.singularHomologyMap
        (LinearSphereAction.sphereMap Lx.toContinuousLinearMap Lx.injective) k
        (LocalDegree.NativeNeighborhood.sphereConnecting x d₀ k a) := by
  have h := connecting_naturality x y dx dy e he hV k a
  rw [coordinateMap_homology x y e he dy dx hV k,
    LocalDegree.NativeNeighborhood.sphereConnecting_eq x dx d₀ k a] at h
  exact h.symm

/-- For a diffeomorphism `e` of `M` with `e x = y`, `sphereConnecting y dy k ∘ H_{k+1}(e)` equals
`H_k(sphereMap (NativeChartTransition.linear x y e he)) ∘ sphereConnecting x dx k`. -/
theorem LocalDegree.pointConnecting_diffeomorph {E F G M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F}
    {Ly : E ≃L[ℝ] G} {Wx Wy : Set M}
    (dx :
      NeighborhoodData (fx ∘ NativeParametrization.centered (D := E) x) Lx
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      NeighborhoodData (fy ∘ NativeParametrization.centered (D := E) y) Ly
        ((NativeParametrization.centered (D := E) y).source ∩
          NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomeomorph.toHomotopyEquiv.toFun (k + 1)
          a) =
      SingularMayerVietoris.singularHomologyMap
        (LinearSphereAction.sphereMap
          (NativeChartTransition.linear x y e he).toContinuousLinearMap
          (NativeChartTransition.linear x y e he).injective)
        k (NativeNeighborhood.sphereConnecting x dx k a) := by
  let W := e.toHomeomorph ⁻¹' NativeNeighborhood.openSet y dy
  have hW : W ∈ 𝓝 x := by
    apply e.toHomeomorph.continuous.continuousAt
    have hy :=
      (NativeNeighborhood.isOpen_openSet y dy).mem_nhds
        (NativeNeighborhood.center_mem_openSet y dy)
    exact he.symm ▸ hy
  obtain ⟨b⟩ := NativeChartTransition.nonempty_neighborhoodData x y e he W hW
  have hV :
    Set.MapsTo e.toHomeomorph (NativeNeighborhood.openSet x b)
      (NativeNeighborhood.openSet y dy) :=
    NativeNeighborhood.openSet_subset x b
  exact PointTransition.connecting_derivative_naturality x y e.toHomeomorph he dy b hV dx k a

end
