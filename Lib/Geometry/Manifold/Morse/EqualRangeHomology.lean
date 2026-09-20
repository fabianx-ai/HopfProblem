/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.LocalContributionsNaturality
import Lib.Geometry.Manifold.Morse.AdaptedWindows
import Lib.Geometry.Manifold.Morse.BeltCancellation
import Lib.Geometry.Manifold.Morse.CutTransport

/-!
# Homology of maps with equal range, and separated neighbourhoods

Two comparison lemmas kept in `Lib` after the round-7 audit split
`Lib.Geometry.Manifold.Morse.MiddleBlocks` (the rest of that module was the
project's dimension-6 index-2/3 bookkeeping and now lives under `Hopf/Proof/`):

* `SingularHomology.homologyMap_unit_smul_of_range_eq`: two topological
  embeddings of the `2`-sphere into a space with the same range induce degree-`2`
  singular homology maps that differ by a unit of `ℤ`; the homeomorphism they
  determine is a self-map of the sphere, and a self-map of `S²` acts on `H₂` by
  `±1`.  `MorseCancellation.middleSectionClass_unit_smul_of_range_eq` is the
  same statement for the classes of two sections of a regular level in the
  homology of the sublevel set.
* `LocalDegree.SeparatedNeighborhoods.pointComplementInclusion` and
  `componentConnecting_singlePoint`: over a separated family of neighbourhoods
  of a finite set `P`, the local contribution at a point `x ∈ P` computed on
  `Pᶜ` agrees with the Mayer–Vietoris connecting homomorphism of the cover
  `{xᶜ, D.neighborhood x}`.

## References

* [Allen Hatcher, *Algebraic topology*][hatcher02], §2.2 (degree of a self-map
  of a sphere and local degrees).

## Tags

singular homology, degree, local degree, sphere, Mayer-Vietoris
-/
open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section


/-- Two embeddings of the `2`-sphere into a space with the same range induce degree-`2`
singular homology maps that differ by a unit of `ℤ`: the homeomorphism of `S²` they determine
acts on `H₂(S²) ≃ ℤ` by `±1`. -/
theorem SingularHomology.homologyMap_unit_smul_of_range_eq {Y : Type} [TopologicalSpace Y]
    (α β : C((Hemisphere.Sphere 2), Y)) (hα : Topology.IsEmbedding α)
    (hβ : Topology.IsEmbedding β) (hrange : Set.range β = Set.range α) :
    ∃ k : ℤ,
      (k = 1 ∨ k = -1) ∧
        SingularMayerVietoris.singularHomologyMap β 2 =
          k • SingularMayerVietoris.singularHomologyMap α 2 := by
  let e : (Hemisphere.Sphere 2) ≃ₜ (Hemisphere.Sphere 2) :=
    hβ.toHomeomorph.trans ((Homeomorph.setCongr hrange).trans hα.toHomeomorph.symm)
  have heq : α.comp (e : C((Hemisphere.Sphere 2), (Hemisphere.Sphere 2))) = β := by
    apply ContinuousMap.ext
    intro x
    have hh :=
      congrArg Subtype.val
        (hα.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr hrange) (hβ.toHomeomorph x)))
    exact hh
  have hbij :
    Function.Bijective
      (SingularMayerVietoris.singularHomologyMap
        (e : C((Hemisphere.Sphere 2), (Hemisphere.Sphere 2))) 2) :=
    (SingularHomology.homeomorphHomologyEquiv e 2).bijective
  obtain ⟨k, hk, hu⟩ :=
    MorseCancellation.two_sphere_map_unit_of_homology_bijective (Homeomorph.refl (Hemisphere.Sphere 2))
      (e : C((Hemisphere.Sphere 2), (Hemisphere.Sphere 2))) hbij
  rcases hk with rfl | rfl
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp only [one_smul] at hu ⊢
    rw [← heq, SingularHomology.singularHomologyMap_comp, hu]
    change
      (SingularMayerVietoris.singularHomologyMap α 2).comp
          (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.id (Hemisphere.Sphere 2)) 2) =
        _
    rw [SingularHomology.singularHomologyMap_id, LinearMap.comp_id]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [neg_one_zsmul] at hu ⊢
    rw [← heq, SingularHomology.singularHomologyMap_comp, hu, LinearMap.comp_neg]
    change
      -((SingularMayerVietoris.singularHomologyMap α 2).comp
            (SingularMayerVietoris.singularHomologyMap
              (ContinuousMap.id (Hemisphere.Sphere 2)) 2)) =
        _
    rw [SingularHomology.singularHomologyMap_id, LinearMap.comp_id]

/-- Two embedded `2`-sphere sections of the level set `f ⁻¹' {a}` with the same range have
homology classes in the sublevel set `{f ≤ a}` that differ by a unit of `ℤ`. -/
theorem MorseCancellation.middleSectionClass_unit_smul_of_range_eq {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} {a : ℝ}
    (α β : C((Hemisphere.Sphere 2), { y : M // f y = a })) (hα : Topology.IsEmbedding α)
    (hβ : Topology.IsEmbedding β) (hrange : Set.range β = Set.range α) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ middleSectionClass β = k • middleSectionClass α := by
  obtain ⟨k, hk, hm⟩ := SingularHomology.homologyMap_unit_smul_of_range_eq α β hα hβ hrange
  have heval :
    (k • SingularMayerVietoris.singularHomologyMap α 2) (SphereHomology.unitSphereTopClass 1) =
      k • SingularMayerVietoris.singularHomologyMap α 2 (SphereHomology.unitSphereTopClass 1) :=
    map_zsmul (LinearMap.evalAddMonoidHom (SphereHomology.unitSphereTopClass 1)) k
      (SingularMayerVietoris.singularHomologyMap α 2)
  refine ⟨k, hk, ?_⟩
  simp only [middleSectionClass, SingularHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, hm, heval, map_zsmul]


/-- For a separated family of neighbourhoods of a finite set `P`, the inclusion of
`Pᶜ ∩ D.neighborhood x` into `{x}ᶜ ∩ D.neighborhood x`: on the neighbourhood of `x` the two
complements agree. -/
def LocalDegree.SeparatedNeighborhoods.pointComplementInclusion {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    C(↥(Pᶜ ∩ D.neighborhood x), ↥({(x : M)}ᶜ ∩ D.neighborhood x)) :=
  (Homeomorph.setCongr (D.overlap_eq x)).toHomotopyEquiv.toFun

/-- The local contribution at `x ∈ P` of the cover by the neighbourhoods of a separated family
agrees with the Mayer-Vietoris connecting homomorphism of the two-set cover `{xᶜ, D.neighborhood x}`,
under the inclusion `pointComplementInclusion`. -/
theorem LocalDegree.SeparatedNeighborhoods.componentConnecting_singlePoint {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] {P : Set M}
    {f : M → F} {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) [Fintype P]
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) (x : P) :
    SingularMayerVietoris.singularHomologyMap (D.pointComplementInclusion x) k
        (CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
          (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint
          D.open_cover k a x) =
      SingularMayerVietoris.connectingHomomorphism {(x : M)}ᶜ (D.neighborhood x)
        isClosed_singleton.isOpen_compl (D.isOpen_neighborhood x)
        (LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a := by
  have hsub : Pᶜ ⊆ {(x : M)}ᶜ := by
    intro y hy hxy
    exact hy (hxy ▸ x.property)
  exact
    CoverLocalContributions.componentConnecting_enlarge Pᶜ {(x : M)}ᶜ D.neighborhood
      (Set.toFinite P).isClosed.isOpen_compl isClosed_singleton.isOpen_compl D.isOpen_neighborhood
      D.pairwise_disjoint D.open_cover hsub x
      (LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a


end
