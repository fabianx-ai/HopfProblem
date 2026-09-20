/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Topology.MappingTorus.Basic
import Lib.Topology.MappingTorus.HomologyCover
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.CrossInsert
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.PathClass
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.Topology.Homotopy.Suspension
import Lib.Topology.Homotopy.CellAttachment
import Lib.Topology.Homotopy.SublevelRetraction
import Lib.Topology.Homotopy.LocalCollapse
import Lib.Topology.OnePointCollapse
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.AlgebraicTopology.SingularHomology.CirclePaths
/-!
# Chain-level input for the Wang sequence of a mapping torus

For a homeomorphism `f` of `X` of finite order `m`, the mapping torus `T_f` is covered by two
open pieces whose intersection is homotopy equivalent to two copies of `X`.  This file builds,
at chain level, the cycles which compute the Mayer--Vietoris connecting map of that cover: a
cycle `b` of `X` is swept along the two families of strips joining the sections at times `1/4`
and `3/4`, and the resulting `(n+1)`-cycle of `T_f` has connecting image `(-N b, N b)`, where
`N = 1 + f_* + ⋯ + f_*^{m-1}` is the norm operator.  This is the computation behind the Wang
exact sequence of a mapping torus.

The file also records the subdivision of the fundamental cycle of the circle used to present the
cross product, and the polar-coordinate description of a punctured normed space as a cylinder,
with the homology relation between the two ends of a once-punctured cylinder.

## References

* A. Hatcher, *Algebraic Topology*, Example 2.48 (the Wang sequence of a mapping torus)
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- Translating the time coordinate by an integer `k` in the mapping torus is the same as
applying the `k`-th power of the gluing homeomorphism to the fibre coordinate. -/
theorem MappingTorusHomology.Covering.mk_add_int {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (t : ℝ) (k : ℤ) (x : X) :
    MappingTorus.mk f (t + (k : ℝ), x) = MappingTorus.mk f (t, (f ^ k) x) := by
  apply (MappingTorus.mk_eq_mk_iff f _ _).mpr
  exact ⟨-k, by simp, by simp⟩

/-- The affine path from `a` to `b` in the reals. -/
def MappingTorusHomology.Covering.affineRealArc (a b : ℝ) : Path a b
    where
  toFun t := a + (b - a) * (t : ℝ)
  continuous_toFun := continuous_const.add (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by simp

/-- The norm operator `1 + B_* + ⋯ + B_*^{m-1}` on singular homology: the sum of the first `m`
powers of the map induced by a homeomorphism. -/
def MappingTorusHomology.Covering.homologyNorm {X : Type} [TopologicalSpace X] (m : ℕ)
    (B : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n :=
  ∑ k ∈ Finset.range m, SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n

/-- The norm operator evaluates to the sum of the images of a class under the first `m` powers of
the induced map. -/
@[simp]
theorem MappingTorusHomology.Covering.homologyNorm_apply {X : Type} [TopologicalSpace X] (m : ℕ)
    (B : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    homologyNorm m B n a =
      ∑ k ∈ Finset.range m,
        SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n a := by
  simp only [homologyNorm, LinearMap.sum_apply]

/-- If `B ^ m = 1`, then `B⁻¹ ^ k = B ^ (m - k)` for `k ≤ m`. -/
theorem MappingTorusHomology.Covering.homeomorph_symm_pow_eq {X : Type} [TopologicalSpace X]
    (m : ℕ) (B : X ≃ₜ X) (hB : B ^ m = 1) (k : ℕ) (hk : k ≤ m) : B.symm ^ k = B ^ (m - k) := by
  change B⁻¹ ^ k = B ^ (m - k)
  rw [pow_sub B hk, hB, one_mul, inv_pow]

/-- Every point of the mapping torus is represented by a point of the cylinder `[0,1] × X`. -/
theorem MappingTorus.mk_unitCylinder_surjective {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    MappingTorus.mk f '' ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ : Set X)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective f q
  refine ⟨deck f (-⌊t⌋) (t, x), ?_, mk_deck f (-⌊t⌋) (t, x)⟩
  change (0 ≤ t + ((-⌊t⌋ : ℤ) : ℝ) ∧ t + ((-⌊t⌋ : ℤ) : ℝ) ≤ 1) ∧ True
  push_cast
  exact ⟨⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩, trivial⟩

/-- The mapping torus of a homeomorphism of a compact space is compact. -/
instance MappingTorus.compactSpace {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X ≃ₜ X) : CompactSpace (Torus f) where
  isCompact_univ := by
    rw [← mk_unitCylinder_surjective f]
    exact (CompactIccSpace.isCompact_Icc.prod isCompact_univ).image (mk_continuous f)

/-- Polar coordinates on a punctured normed space: `E ∖ {0}` is homeomorphic to the cylinder
`ℝ × S(E)` by `(t, u) ↦ exp t • u`. -/
def PassageHomology.radialCylinderHomeomorph (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : (ℝ × Metric.sphere (0 : E) 1) ≃ₜ ({0}ᶜ : Set E) :=
  ((Homeomorph.prodComm ℝ (Metric.sphere (0 : E) 1)).trans
        ((Homeomorph.refl (Metric.sphere (0 : E) 1)).prodCongr
          Real.expOrderIso.toHomeomorph)).trans
    (homeomorphUnitSphereProd E).symm

/-- Removing one point from the cylinder `ℝ × S(E)` gives a space homeomorphic to `E` with the
origin and the corresponding point removed. -/
def PassageHomology.puncturedCylinderHomeomorph {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (τ : ℝ) (u : Metric.sphere (0 : E) 1) :
    ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)) ≃ₜ twoPunctureSet 0 (PassageHomology.cylinderPuncture τ u)
    where
  toFun
    p := by
    refine
      ⟨(radialCylinderHomeomorph E p.val).val, (radialCylinderHomeomorph E p.val).property, ?_⟩
    intro h
    have he : radialCylinderHomeomorph E p.val = radialCylinderHomeomorph E (τ, u) :=
      Subtype.ext h
    exact p.property ((radialCylinderHomeomorph E).injective he)
  invFun
    z :=
    ⟨(radialCylinderHomeomorph E).symm ⟨z.val, z.property.1⟩,
      by
      intro h
      have hh := congrArg (radialCylinderHomeomorph E) h
      rw [(radialCylinderHomeomorph E).apply_symm_apply] at hh
      exact z.property.2 (congrArg Subtype.val hh)⟩
  left_inv
    p := by
    apply Subtype.ext
    change (radialCylinderHomeomorph E).symm (radialCylinderHomeomorph E p.val) = p.val
    exact (radialCylinderHomeomorph E).symm_apply_apply p.val
  right_inv
    z := by
    apply Subtype.ext
    change
      ((radialCylinderHomeomorph E)
            ((radialCylinderHomeomorph E).symm ⟨z.val, z.property.1⟩)).val =
        z.val
    exact
      congrArg (fun w : ({0}ᶜ : Set E) => w.val)
        ((radialCylinderHomeomorph E).apply_symm_apply ⟨z.val, z.property.1⟩)
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((radialCylinderHomeomorph E).continuous.comp continuous_subtype_val)).subtype_mk
      _
  continuous_invFun := by
    have hc :
      Continuous
        (fun z : twoPunctureSet 0 (PassageHomology.cylinderPuncture τ u) =>
          (⟨z.val, z.property.1⟩ : ({0}ᶜ : Set E))) :=
      continuous_subtype_val.subtype_mk _
    exact ((radialCylinderHomeomorph E).symm.continuous.comp hc).subtype_mk _

/-- The link of the removed point of the cylinder: the sphere of radius `ε` around that point,
parametrised by the unit sphere of `E`. -/
def PassageHomology.cylinderLink {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : ℝ) (u : Metric.sphere (0 : E) 1) (ε : ℝ) (hε : 0 < ε) (hεu : ε < Real.exp τ) :
    C(Metric.sphere (0 : E) 1, ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1))) :=
  ((PassageHomology.puncturedCylinderHomeomorph τ u).symm : C(_, _)).comp
    (PassageHomology.linkingSphere (PassageHomology.cylinderPuncture τ u) ε hε (by rwa [norm_cylinderPuncture]))

/-- In the once-punctured cylinder, the class of the slice at time `1` is the sum of the class of
the slice at time `0` and the class of the link of the puncture, in every positive degree. -/
theorem PassageHomology.punctured_cylinder_endpoint_relation {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (u : Metric.sphere (0 : E) 1) {ε : ℝ} (hε : 0 < ε) (hεu : ε < Real.exp τ) (n : ℕ)
    (hn : n ≠ 0) :
    SingularMayerVietoris.singularHomologyMap (cylinderSlice τ u 1 hτ.2.ne') n =
      SingularMayerVietoris.singularHomologyMap (cylinderSlice τ u 0 hτ.1.ne) n +
        SingularMayerVietoris.singularHomologyMap (cylinderLink τ u ε hε hεu) n := by
  let b := PassageHomology.cylinderPuncture τ u
  have hrb : (1 : ℝ) < ‖b‖ := by
    rw [norm_cylinderPuncture]
    exact Real.one_lt_exp_iff.mpr hτ.1
  have hbR : ‖b‖ < Real.exp 1 := by
    rw [norm_cylinderPuncture]
    exact Real.exp_lt_exp.mpr hτ.2
  have hεb : ε < ‖b‖ := by rwa [norm_cylinderPuncture]
  let inner := innerSphere b 1 zero_lt_one hrb
  let outer := outerSphere b (Real.exp 1) hbR
  let link := PassageHomology.linkingSphere b ε hε hεb
  let e := PassageHomology.puncturedCylinderHomeomorph τ u
  let e' : C(twoPunctureSet 0 b, ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1))) := e.symm
  have hinner : e'.comp inner = cylinderSlice τ u 0 hτ.1.ne := by
    apply ContinuousMap.ext
    intro v
    apply e.injective
    change e (e.symm (inner v)) = e (cylinderSlice τ u 0 hτ.1.ne v)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (0 : E) + 1 • v.val = Real.exp 0 • v.val
    rw [Real.exp_zero, one_smul, zero_add]
  have houter : e'.comp outer = cylinderSlice τ u 1 hτ.2.ne' := by
    apply ContinuousMap.ext
    intro v
    apply e.injective
    change e (e.symm (outer v)) = e (cylinderSlice τ u 1 hτ.2.ne' v)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (0 : E) + Real.exp 1 • v.val = Real.exp 1 • v.val
    rw [zero_add]
  have H :
    SingularMayerVietoris.singularHomologyMap (e'.comp outer) n =
      SingularMayerVietoris.singularHomologyMap (e'.comp inner) n +
        SingularMayerVietoris.singularHomologyMap (e'.comp link) n := by
    rw [SingularHomology.singularHomologyMap_comp,
      SingularHomology.singularHomologyMap_comp,
      SingularHomology.singularHomologyMap_comp]
    have hrel := radial_sphere_homology_relation b zero_lt_one hrb hbR hε hεb n hn
    change
      (SingularMayerVietoris.singularHomologyMap e' n).comp
          (SingularMayerVietoris.singularHomologyMap outer n) =
        _
    rw [hrel, LinearMap.comp_add]
  rw [hinner, houter] at H
  exact H

/-- The same relation after pushing forward along any continuous map out of the punctured
cylinder: the top slice contributes the bottom slice plus the link. -/
theorem PassageHomology.punctured_cylinder_trace_relation {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Y : Type} [TopologicalSpace Y] {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (u : Metric.sphere (0 : E) 1) {ε : ℝ} (hε : 0 < ε) (hεu : ε < Real.exp τ)
    (F : C(({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)), Y)) (n : ℕ) (hn : n ≠ 0) :
    SingularMayerVietoris.singularHomologyMap (F.comp (cylinderSlice τ u 1 hτ.2.ne')) n =
      SingularMayerVietoris.singularHomologyMap (F.comp (cylinderSlice τ u 0 hτ.1.ne)) n +
        SingularMayerVietoris.singularHomologyMap (F.comp (cylinderLink τ u ε hε hεu)) n := by
  rw [SingularHomology.singularHomologyMap_comp,
    SingularHomology.singularHomologyMap_comp,
    SingularHomology.singularHomologyMap_comp,
    punctured_cylinder_endpoint_relation hτ u hε hεu n hn, LinearMap.comp_add]

/-- The inclusion of an open subset of a charted space, as a partial diffeomorphism. -/
def PartialChart.openInclusion {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    (U : TopologicalSpace.Opens X) [Nonempty U] : PartialDiffeomorph I I U X ∞ := by
  let h : OpenPartialHomeomorph U X := U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  refine
    { toPartialEquiv := h.toPartialEquiv
      open_source := h.open_source
      open_target := h.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := ?_ }
  change ContMDiffOn I I ∞ h.symm h.target
  intro x hx
  apply (ContMDiffWithinAt.subtypeVal_comp_iff U h.symm h.target x).mp
  apply contMDiffWithinAt_id.congr_of_mem (fun y hy => ?_) hx
  exact h.right_inv hy

/-- The inclusion of an open subset has that open subset as its target. -/
theorem PartialChart.openInclusion_target {E H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X]
    [ChartedSpace H X] (U : TopologicalSpace.Opens X) [Nonempty U] :
    (openInclusion (I := I) U).target = U := by
  change U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.target = U
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact Subtype.range_coe

/-- The inverse of the inclusion of an open subset is the identity on points of that subset. -/
theorem PartialChart.openInclusion_symm_coe {E H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X]
    [ChartedSpace H X] (U : TopologicalSpace.Opens X) [Nonempty U] {x : X} (hx : x ∈ U) :
    ((openInclusion (I := I) U).symm x).val = x := by
  have h :=
    (openInclusion (I := I) U).right_inv
      (show x ∈ (openInclusion (I := I) U).target by rw [openInclusion_target]; exact hx)
  exact h

/-- The first (radial) coordinate of a point in polar coordinates is the logarithm of its norm. -/
theorem PassageHomology.radialCylinderHomeomorph_symm_fst (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ({0}ᶜ : Set E)) :
    ((radialCylinderHomeomorph E).symm x).1 = Real.log ‖x.val‖ := by
  have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property
  change Real.expOrderIso.symm ((homeomorphUnitSphereProd E) x).2 = _
  rw [Real.log_of_pos hn]
  congr 1
  apply Subtype.ext
  exact homeomorphUnitSphereProd_apply_snd_coe E x

/-- The second (spherical) coordinate of a point in polar coordinates is its normalisation. -/
theorem PassageHomology.radialCylinderHomeomorph_symm_snd_coe (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : ({0}ᶜ : Set E)) :
    (((radialCylinderHomeomorph E).symm x).2 : E) = ‖x.val‖⁻¹ • x.val := by
  change (((homeomorphUnitSphereProd E) x).1 : E) = _
  exact homeomorphUnitSphereProd_apply_fst_coe E x

/-- Polar coordinates are a diffeomorphism from the cylinder `ℝ × Sⁿ` onto the punctured
finite-dimensional inner product space. -/
def PassageHomology.radialCylinderDiffeomorph (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)] :
    Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (ℝ × Metric.sphere (0 : E) 1)
      (PassageHomology.puncturedVectorSpace E) ∞
    where
  toEquiv := (radialCylinderHomeomorph E).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (PassageHomology.puncturedVectorSpace E) _).mp
    change
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) ∞
        (fun p : ℝ × Metric.sphere (0 : E) 1 => Real.exp p.1 • p.2.val)
    exact
      (Real.contDiff_exp.contMDiff.comp contMDiff_fst).smul
        ((contMDiff_coe_sphere (n := n)).comp contMDiff_snd)
  contMDiff_invFun := by
    have hn : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : PassageHomology.puncturedVectorSpace E => ‖x.val‖) := by
      intro x
      exact (contDiffAt_norm ℝ x.property).contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt
    have hl : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : PassageHomology.puncturedVectorSpace E => Real.log ‖x.val‖) := by
      intro x
      exact
        (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr x.property)).contMDiffAt.comp x
          hn.contMDiffAt
    have hraw :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : PassageHomology.puncturedVectorSpace E => ‖x.val‖⁻¹ • x.val) :=
      (hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul contMDiff_subtype_val
    have hfst :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        (fun x : PassageHomology.puncturedVectorSpace E => ((radialCylinderHomeomorph E).symm x).1) := by
      have heq :
        (fun x : PassageHomology.puncturedVectorSpace E => ((radialCylinderHomeomorph E).symm x).1) =
          (fun x => Real.log ‖x.val‖) :=
        funext (fun x => radialCylinderHomeomorph_symm_fst E x)
      rw [heq]
      exact hl
    have hval :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun x : PassageHomology.puncturedVectorSpace E => (((radialCylinderHomeomorph E).symm x).2 : E)) := by
      have heq :
        (fun x : PassageHomology.puncturedVectorSpace E => (((radialCylinderHomeomorph E).symm x).2 : E)) =
          (fun x => ‖x.val‖⁻¹ • x.val) :=
        funext (fun x => radialCylinderHomeomorph_symm_snd_coe E x)
      rw [heq]
      exact hraw
    have hsnd :
      ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞
        (fun x : PassageHomology.puncturedVectorSpace E => ((radialCylinderHomeomorph E).symm x).2) :=
      hval.codRestrict_sphere (fun x => ((radialCylinderHomeomorph E).symm x).2.property)
    exact hfst.prodMk hsnd

/-- Polar coordinates, read as a partial diffeomorphism from the cylinder into `E` itself. -/
def PassageHomology.radialCylinderChart (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : Metric.sphere (0 : E) 1) :
    PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (ℝ × Metric.sphere (0 : E) 1) E ∞ := by
  let _ : Nonempty (PassageHomology.puncturedVectorSpace E) :=
    ⟨⟨u.val, Metric.ne_of_mem_sphere u.property one_ne_zero⟩⟩
  exact
    (PassageHomology.radialCylinderDiffeomorph E n).toPartialDiffeomorph.trans
      (PartialChart.openInclusion (I := 𝓘(ℝ, E)) (PassageHomology.puncturedVectorSpace E))

/-- The polar-coordinate chart is defined on the whole cylinder. -/
theorem PassageHomology.radialCylinderChart_mem_source (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : Metric.sphere (0 : E) 1) (p : ℝ × Metric.sphere (0 : E) 1) :
    p ∈ (radialCylinderChart E n u).source :=
  ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- The image of the polar-coordinate chart is exactly the complement of the origin. -/
theorem PassageHomology.radialCylinderChart_mem_target (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : Metric.sphere (0 : E) 1) (z : E) : z ∈ (radialCylinderChart E n u).target ↔ z ≠ 0 := by
  let _ : Nonempty (PassageHomology.puncturedVectorSpace E) :=
    ⟨⟨u.val, Metric.ne_of_mem_sphere u.property one_ne_zero⟩⟩
  change
    (z ∈ (PartialChart.openInclusion (I := 𝓘(ℝ, E)) (PassageHomology.puncturedVectorSpace E)).target ∧
        (PartialChart.openInclusion (I := 𝓘(ℝ, E)) (PassageHomology.puncturedVectorSpace E)).symm z ∈
          Set.univ) ↔
      z ≠ 0
  rw [PartialChart.openInclusion_target]
  exact ⟨fun h => h.1, fun h => ⟨h, Set.mem_univ _⟩⟩

/-- On nonzero vectors, the inverse of the polar-coordinate chart is the inverse of the polar
homeomorphism. -/
theorem PassageHomology.radialCylinderChart_symm_eq (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : Metric.sphere (0 : E) 1) (z : E) (hz : z ≠ 0) :
    (radialCylinderChart E n u).symm z = (radialCylinderHomeomorph E).symm ⟨z, hz⟩ := by
  let _ : Nonempty (PassageHomology.puncturedVectorSpace E) :=
    ⟨⟨u.val, Metric.ne_of_mem_sphere u.property one_ne_zero⟩⟩
  change
    (PassageHomology.radialCylinderDiffeomorph E n).symm
        ((PartialChart.openInclusion (I := 𝓘(ℝ, E)) (PassageHomology.puncturedVectorSpace E)).symm z) =
      _
  have heq :
    (PartialChart.openInclusion (I := 𝓘(ℝ, E)) (PassageHomology.puncturedVectorSpace E)).symm z =
      (⟨z, hz⟩ : PassageHomology.puncturedVectorSpace E) :=
    Subtype.ext
      (PartialChart.openInclusion_symm_coe (I := 𝓘(ℝ, E)) (PassageHomology.puncturedVectorSpace E) hz)
  rw [heq]
  rfl

private theorem MappingTorusHomology.Covering.sum_range_shift_of_endpoints_eq
    {A : Type*} [AddCommGroup A] (F : ℕ → A) (m : ℕ) (hF : F m = F 0) :
    ∑ k ∈ Finset.range m, F (k + 1) = ∑ k ∈ Finset.range m, F k := by
  apply add_right_cancel (b := F 0)
  calc
    (∑ k ∈ Finset.range m, F (k + 1)) + F 0 = ∑ k ∈ Finset.range (m + 1), F k :=
      (Finset.sum_range_succ' F m).symm
    _ = (∑ k ∈ Finset.range m, F k) + F 0 := by rw [Finset.sum_range_succ, hF]

/-- For a homeomorphism of finite order `m`, the norm operator of the inverse agrees with the norm
operator of the homeomorphism itself. -/
theorem MappingTorusHomology.Covering.homologyNorm_symm {X : Type} [TopologicalSpace X] (m : ℕ)
    (B : X ≃ₜ X) (n : ℕ) (hB : B ^ m = 1) : homologyNorm m B.symm n = homologyNorm m B n := by
  unfold homologyNorm
  calc
    (∑ k ∈ Finset.range m,
          SingularMayerVietoris.singularHomologyMap ((B.symm ^ k : X ≃ₜ X) : C(X, X)) n) =
        ∑ k ∈ Finset.range m,
          SingularMayerVietoris.singularHomologyMap ((B ^ (m - 1 - k + 1) : X ≃ₜ X) : C(X, X))
            n := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k < m := Finset.mem_range.mp hk
      have hexp : m - k = m - 1 - k + 1 := by omega
      rw [homeomorph_symm_pow_eq m B hB k hkm.le, hexp]
    _ =
        ∑ k ∈ Finset.range m,
          SingularMayerVietoris.singularHomologyMap ((B ^ (k + 1) : X ≃ₜ X) : C(X, X)) n :=
      (Finset.sum_range_reflect
        (fun k => SingularMayerVietoris.singularHomologyMap ((B ^ (k + 1) : X ≃ₜ X) : C(X, X)) n)
        m)
    _ =
        ∑ k ∈ Finset.range m,
          SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n := by
      apply
        MappingTorusHomology.Covering.sum_range_shift_of_endpoints_eq
          (fun k => SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n) m
      rw [hB, pow_zero]

/-- The once-around loop of the circle, based at the point `a` instead of at the origin. -/
def MappingTorusHomology.Covering.translatedPositiveLoop (a : ℝ) :
    Path (a : (SingularHomology.CircleTopology.Circle))
      (a : (SingularHomology.CircleTopology.Circle)) :=
  ((PeriodTorusHigherHomology.CirclePaths.positiveLoop.map
        (PeriodTorusHigherHomology.CirclePaths.circleTranslation a).continuous).cast
    (by simp) (by simp))

/-- The translated loop runs from `a` once around the circle. -/
@[simp]
theorem MappingTorusHomology.Covering.translatedPositiveLoop_apply (a : ℝ) (t : unitInterval) :
    translatedPositiveLoop a t =
      ((a + (t : ℝ) : ℝ) : (SingularHomology.CircleTopology.Circle)) := by
  change
    (a : (SingularHomology.CircleTopology.Circle)) +
        ((t : ℝ) : (SingularHomology.CircleTopology.Circle)) =
      ((a + (t : ℝ) : ℝ) : (SingularHomology.CircleTopology.Circle))
  exact (AddCircle.coe_add (1 : ℝ) a (t : ℝ)).symm

/-- The translated loop carries the same homology class as the standard positive loop. -/
theorem MappingTorusHomology.Covering.translatedPositiveLoop_class (a : ℝ) :
    SingularChains.loopHomologyClass (translatedPositiveLoop a) =
      SingularChains.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  have hc :
    SingularChains.loopHomologyClass (translatedPositiveLoop a) =
      SingularChains.loopHomologyClass
        (PeriodTorusHigherHomology.CirclePaths.positiveLoop.map
          (PeriodTorusHigherHomology.CirclePaths.circleTranslation a).continuous) := by
    apply
      SingularChains.homologyToChainClass_injective
        (SingularHomology.CircleTopology.Circle)
    rw [SingularChains.homologyToChainClass_loopHomologyClass,
      SingularChains.homologyToChainClass_loopHomologyClass]
    rfl
  exact
    hc.trans (PeriodTorusHigherHomology.CirclePaths.loopHomologyClass_map_circleTranslation a _)

/-- The inverse of a homeomorphism of finite order `m` again has order dividing `m`. -/
theorem MappingTorusHomology.Covering.inverseMonodromy_period {X : Type}
    [TopologicalSpace X] (m : ℕ) (B : X ≃ₜ X) (h : B ^ m = 1) : B.symm ^ m = 1 := by
  rw [homeomorph_symm_pow_eq m B h m le_rfl, Nat.sub_self, pow_zero]

/-- The section of the intersection of the two mapping-torus cover pieces at time `1/4`, composed
with the `k`-th power of the gluing homeomorphism. -/
def MappingTorusHomology.Covering.lowerSection {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) : C(X, ↥(MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f))
    where
  toFun
    x :=
    (MappingTorus.HomologyCover.intersectionHomeomorph f).symm
      (Sum.inl (⟨(1 / 4 : ℝ), by norm_num⟩, (f ^ k) x))
  continuous_toFun :=
    (MappingTorus.HomologyCover.intersectionHomeomorph f).symm.continuous.comp
      (continuous_inl.comp (continuous_const.prodMk (f ^ k).continuous))

/-- The section of the intersection of the two mapping-torus cover pieces at time `3/4`, composed
with the `k`-th power of the gluing homeomorphism. -/
def MappingTorusHomology.Covering.upperSection {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) : C(X, ↥(MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f))
    where
  toFun
    x :=
    (MappingTorus.HomologyCover.intersectionHomeomorph f).symm
      (Sum.inr (⟨(3 / 4 : ℝ), by norm_num⟩, (f ^ k) x))
  continuous_toFun :=
    (MappingTorus.HomologyCover.intersectionHomeomorph f).symm.continuous.comp
      (continuous_inr.comp (continuous_const.prodMk (f ^ k).continuous))

/-- The lower section sends `x` to the class of `(1/4, f^k x)`. -/
@[simp]
theorem MappingTorusHomology.Covering.lowerSection_val {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k : ℕ) (x : X) :
    (lowerSection f k x : MappingTorus.Torus f) = MappingTorus.mk f (1 / 4, (f ^ k) x) :=
  MappingTorus.HomologyCover.intersectionHomeomorph_symm_inl_coe f _

/-- The upper section sends `x` to the class of `(3/4, f^k x)`. -/
@[simp]
theorem MappingTorusHomology.Covering.upperSection_val {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k : ℕ) (x : X) :
    (upperSection f k x : MappingTorus.Torus f) = MappingTorus.mk f (3 / 4, (f ^ k) x) :=
  MappingTorus.HomologyCover.intersectionHomeomorph_symm_inr_coe f _

/-- The reparametrisation of the unit interval onto the time interval `(1/4, 3/4)`. -/
def MappingTorusHomology.Covering.uTime (t : unitInterval) : Set.Ioo (0 : ℝ) 1 :=
  ⟨(1 / 4 : ℝ) + (t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

/-- The time reparametrisation of the first strip is continuous. -/
theorem MappingTorusHomology.Covering.uTime_continuous : Continuous uTime :=
  (continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk _

/-- The reparametrisation of the unit interval onto the time interval `(-1/4, 1/4)`. -/
def MappingTorusHomology.Covering.vTime (t : unitInterval) : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
  ⟨-(1 / 4 : ℝ) + (t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

/-- The time reparametrisation of the second strip is continuous. -/
theorem MappingTorusHomology.Covering.vTime_continuous : Continuous vTime :=
  (continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk _

/-- The strip in the first cover piece running from the lower to the upper section, at the `k`-th
power of the gluing homeomorphism. -/
def MappingTorusHomology.Covering.uStrip {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (k : ℕ) :
    C(unitInterval × X, MappingTorus.HomologyCover.U f)
    where
  toFun p := (MappingTorus.HomologyCover.chartU f).symm (uTime p.1, (f ^ k) p.2)
  continuous_toFun :=
    (MappingTorus.HomologyCover.chartU f).symm.continuous.comp
      ((uTime_continuous.comp continuous_fst).prodMk ((f ^ k).continuous.comp continuous_snd))

/-- The strip in the second cover piece running from the upper section to the next lower section,
at the `k`-th power of the gluing homeomorphism. -/
def MappingTorusHomology.Covering.vStrip {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (k : ℕ) :
    C(unitInterval × X, MappingTorus.HomologyCover.V f)
    where
  toFun p := (MappingTorus.HomologyCover.chartV f).symm (vTime p.1, (f ^ (k + 1)) p.2)
  continuous_toFun :=
    (MappingTorus.HomologyCover.chartV f).symm.continuous.comp
      ((vTime_continuous.comp continuous_fst).prodMk
        ((f ^ (k + 1)).continuous.comp continuous_snd))

/-- The first strip sends `(t, x)` to the class of `(1/4 + t/2, f^k x)`. -/
@[simp]
theorem MappingTorusHomology.Covering.uStrip_val {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) (p : unitInterval × X) :
    (uStrip f k p : MappingTorus.Torus f) =
      MappingTorus.mk f ((1 / 4 : ℝ) + (p.1 : ℝ) / 2, (f ^ k) p.2) :=
  MappingTorus.HomologyCover.chartU_symm_coe f _

/-- The second strip sends `(t, x)` to the class of `(-1/4 + t/2, f^{k+1} x)`. -/
@[simp]
theorem MappingTorusHomology.Covering.vStrip_val {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) (p : unitInterval × X) :
    (vStrip f k p : MappingTorus.Torus f) =
      MappingTorus.mk f (-(1 / 4 : ℝ) + (p.1 : ℝ) / 2, (f ^ (k + 1)) p.2) :=
  MappingTorus.HomologyCover.chartV_symm_coe f _

/-- The first strip starts at the `k`-th lower section. -/
theorem MappingTorusHomology.Covering.uStrip_zero {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) :
    (uStrip f k).comp (SingularHomology.crossInsertLeft (0 : unitInterval)) =
      (MappingTorus.HomologyCover.intersectionToU f).comp (lowerSection f k) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (uStrip f k (0, x) : MappingTorus.Torus f) = (lowerSection f k x : MappingTorus.Torus f)
  rw [uStrip_val, lowerSection_val]
  simp

/-- The first strip ends at the `k`-th upper section. -/
theorem MappingTorusHomology.Covering.uStrip_one {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) :
    (uStrip f k).comp (SingularHomology.crossInsertLeft (1 : unitInterval)) =
      (MappingTorus.HomologyCover.intersectionToU f).comp (upperSection f k) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (uStrip f k (1, x) : MappingTorus.Torus f) = (upperSection f k x : MappingTorus.Torus f)
  rw [uStrip_val, upperSection_val]
  norm_num

/-- The second strip starts at the `k`-th upper section. -/
theorem MappingTorusHomology.Covering.vStrip_zero {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) :
    (vStrip f k).comp (SingularHomology.crossInsertLeft (0 : unitInterval)) =
      (MappingTorus.HomologyCover.intersectionToV f).comp (upperSection f k) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (vStrip f k (0, x) : MappingTorus.Torus f) = (upperSection f k x : MappingTorus.Torus f)
  rw [vStrip_val, upperSection_val]
  have hpow : (f ^ (k + 1)) x = f ((f ^ k) x) := by rw [pow_succ', Homeomorph.mul_apply]
  rw [hpow]
  convert MappingTorus.mk_sub_one f (3 / 4) ((f ^ k) x) using 1
  norm_num

/-- The second strip ends at the `(k+1)`-st lower section. -/
theorem MappingTorusHomology.Covering.vStrip_one {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k : ℕ) :
    (vStrip f k).comp (SingularHomology.crossInsertLeft (1 : unitInterval)) =
      (MappingTorus.HomologyCover.intersectionToV f).comp (lowerSection f (k + 1)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    (vStrip f k (1, x) : MappingTorus.Torus f) = (lowerSection f (k + 1) x : MappingTorus.Torus f)
  rw [vStrip_val, lowerSection_val]
  norm_num

/-- If the gluing homeomorphism has order `m`, the `m`-th lower section is the zeroth one. -/
theorem MappingTorusHomology.Covering.lowerSection_period {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) : lowerSection f m = lowerSection f 0 := by
  apply ContinuousMap.ext
  intro x
  change
    (MappingTorus.HomologyCover.intersectionHomeomorph f).symm (Sum.inl (_, (f ^ m) x)) =
      (MappingTorus.HomologyCover.intersectionHomeomorph f).symm (Sum.inl (_, (f ^ 0) x))
  rw [hf, pow_zero]

/-- Under the homotopy equivalence of the intersection with two copies of `X`, the `k`-th lower
section is the first copy composed with `f^k`. -/
theorem MappingTorusHomology.Covering.lowerSection_component {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k : ℕ) :
    (MappingTorus.HomologyCover.intersectionHomotopyEquiv f).toFun.comp (lowerSection f k) =
      (⟨Sum.inl, continuous_inl⟩ : C(X, X ⊕ X)).comp ((f ^ k : X ≃ₜ X) : C(X, X)) := by
  apply ContinuousMap.ext
  intro x
  exact MappingTorus.HomologyCover.intersectionHomotopyEquiv_inl f _

/-- Under the homotopy equivalence of the intersection with two copies of `X`, the `k`-th upper
section is the second copy composed with `f^k`. -/
theorem MappingTorusHomology.Covering.upperSection_component {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k : ℕ) :
    (MappingTorus.HomologyCover.intersectionHomotopyEquiv f).toFun.comp (upperSection f k) =
      (⟨Sum.inr, continuous_inr⟩ : C(X, X ⊕ X)).comp ((f ^ k : X ≃ₜ X) : C(X, X)) := by
  apply ContinuousMap.ext
  intro x
  exact MappingTorus.HomologyCover.intersectionHomotopyEquiv_inr f _

/-- In the two homology coordinates of the intersection, the `k`-th lower section contributes
`(f^k)_*` in the first coordinate and zero in the second. -/
theorem MappingTorusHomology.Covering.lowerSection_homology_coordinates {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (k n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    MappingTorusHomology.intersectionHomologyEquiv f n
        (SingularMayerVietoris.singularHomologyMap (lowerSection f k) n a) =
      (SingularMayerVietoris.singularHomologyMap ((f ^ k : X ≃ₜ X) : C(X, X)) n a, 0) := by
  rw [MappingTorusHomology.intersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    SingularHomology.singularHomologyMap_comp, lowerSection_component,
    SingularHomology.singularHomologyMap_comp]
  exact SingularHomology.sumHomologyEquiv_inl X X n _

/-- In the two homology coordinates of the intersection, the `k`-th upper section contributes zero
in the first coordinate and `(f^k)_*` in the second. -/
theorem MappingTorusHomology.Covering.upperSection_homology_coordinates {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (k n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    MappingTorusHomology.intersectionHomologyEquiv f n
        (SingularMayerVietoris.singularHomologyMap (upperSection f k) n a) =
      (0, SingularMayerVietoris.singularHomologyMap ((f ^ k : X ≃ₜ X) : C(X, X)) n a) := by
  rw [MappingTorusHomology.intersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    SingularHomology.singularHomologyMap_comp, upperSection_component,
    SingularHomology.singularHomologyMap_comp]
  exact SingularHomology.sumHomologyEquiv_inr X X n _

/-- The affine arc from `a` to `b` in the circle `ℝ / ℤ`. -/
def MappingTorusHomology.Covering.affineCircleArc (a b : ℝ) :
    Path (a : (SingularHomology.CircleTopology.Circle))
      (b : (SingularHomology.CircleTopology.Circle)) :=
  (affineRealArc a b).map (AddCircle.continuous_mk' (1 : ℝ))

/-- The affine circle arc is the image of the affine real interpolation. -/
@[simp]
theorem MappingTorusHomology.Covering.affineCircleArc_apply (a b : ℝ) (t : unitInterval) :
    affineCircleArc a b t =
      ((a + (b - a) * (t : ℝ) : ℝ) : (SingularHomology.CircleTopology.Circle)) :=
  rfl

/-- The affine arc from a point to itself is the constant path. -/
@[simp]
theorem MappingTorusHomology.Covering.affineCircleArc_self (a : ℝ) :
    affineCircleArc a a = Path.refl (a : (SingularHomology.CircleTopology.Circle)) := by
  apply Path.ext
  funext t
  simp

/-- Two consecutive affine circle arcs are homotopic to the single arc over the whole interval. -/
theorem MappingTorusHomology.Covering.affineCircleArc_trans_homotopic (a b c : ℝ) :
    ((affineCircleArc a b).trans (affineCircleArc b c)).Homotopic (affineCircleArc a c) := by
  have h :=
    SimplyConnectedSpace.paths_homotopic ((affineRealArc a b).trans (affineRealArc b c))
      (affineRealArc a c)
  have hmap :=
    h.map
      (⟨fun x : ℝ => (x : (SingularHomology.CircleTopology.Circle)),
          AddCircle.continuous_mk' (1 : ℝ)⟩ :
        C(ℝ, (SingularHomology.CircleTopology.Circle)))
  rw [Path.map_trans] at hmap
  exact hmap

/-- Path classes of consecutive affine circle arcs add. -/
theorem MappingTorusHomology.Covering.pathClass_affineCircleArc_add (a b c : ℝ) :
    SingularChains.pathClass (affineCircleArc a b) +
        SingularChains.pathClass (affineCircleArc b c) =
      SingularChains.pathClass (affineCircleArc a c) := by
  rw [← SingularChains.pathClass_trans]
  exact SingularChains.pathClass_homotopic (affineCircleArc_trans_homotopic a b c)

/-- The lift of the time `1/4` of the `k`-th of `m` equal subintervals of the circle. -/
def MappingTorusHomology.Covering.quarterLift (m k : ℕ) : ℝ :=
  ((k : ℝ) + 1 / 4) / m

/-- The lift of the time `3/4` of the `k`-th of `m` equal subintervals of the circle. -/
def MappingTorusHomology.Covering.threeQuarterLift (m k : ℕ) : ℝ :=
  ((k : ℝ) + 3 / 4) / m

/-- The first half of the `k`-th subinterval arc, from the quarter point to the three-quarter
point. -/
def MappingTorusHomology.Covering.uPath (m k : ℕ) :
    Path (quarterLift m k : (SingularHomology.CircleTopology.Circle))
      (threeQuarterLift m k : (SingularHomology.CircleTopology.Circle)) :=
  affineCircleArc (quarterLift m k) (threeQuarterLift m k)

/-- The second half of the `k`-th subinterval arc, from the three-quarter point to the next
quarter point. -/
def MappingTorusHomology.Covering.vPath (m k : ℕ) :
    Path (threeQuarterLift m k : (SingularHomology.CircleTopology.Circle))
      (quarterLift m (k + 1) : (SingularHomology.CircleTopology.Circle)) :=
  affineCircleArc (threeQuarterLift m k) (quarterLift m (k + 1))

/-- The first half-arc runs affinely from `(k + 1/4)/m` to `(k + 3/4)/m`. -/
@[simp]
theorem MappingTorusHomology.Covering.uPath_apply (m k : ℕ) (t : unitInterval) :
    uPath m k t =
      ((((k : ℝ) + 1 / 4 + (t : ℝ) / 2) / m : ℝ) :
        (SingularHomology.CircleTopology.Circle)) := by
  change
    (((quarterLift m k + (threeQuarterLift m k - quarterLift m k) * (t : ℝ)) : ℝ) :
        (SingularHomology.CircleTopology.Circle)) =
      _
  congr 1
  unfold quarterLift threeQuarterLift
  ring

/-- The second half-arc runs affinely from `(k + 3/4)/m` to `(k + 5/4)/m`. -/
@[simp]
theorem MappingTorusHomology.Covering.vPath_apply (m k : ℕ) (t : unitInterval) :
    vPath m k t =
      ((((k : ℝ) + 3 / 4 + (t : ℝ) / 2) / m : ℝ) :
        (SingularHomology.CircleTopology.Circle)) := by
  change
    (((threeQuarterLift m k + (quarterLift m (k + 1) - threeQuarterLift m k) * (t : ℝ)) : ℝ) :
        (SingularHomology.CircleTopology.Circle)) =
      _
  congr 1
  unfold quarterLift threeQuarterLift
  push_cast
  ring

/-- The two half-arcs of one subinterval add up to the arc over the whole subinterval. -/
theorem MappingTorusHomology.Covering.pathClass_uPath_add_vPath (m k : ℕ) :
    SingularChains.pathClass (uPath m k) + SingularChains.pathClass (vPath m k) =
      SingularChains.pathClass (affineCircleArc (quarterLift m k) (quarterLift m (k + 1))) :=
  pathClass_affineCircleArc_add _ _ _

/-- After `m` steps the quarter points have advanced by exactly one full turn. -/
theorem MappingTorusHomology.Covering.quarterLift_period (m : ℕ) [NeZero m] :
    quarterLift m m = quarterLift m 0 + 1 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [quarterLift, Nat.cast_zero, zero_add]
  field_simp
  ring

/-- After `m` steps the quarter points return to their starting point on the circle. -/
theorem MappingTorusHomology.Covering.quarterLift_circle_period (m : ℕ) [NeZero m] :
    (quarterLift m m : (SingularHomology.CircleTopology.Circle)) =
      (quarterLift m 0 : (SingularHomology.CircleTopology.Circle)) := by
  rw [quarterLift_period]
  exact AddCircle.coe_add_period (1 : ℝ) _

/-- The boundary of the first `n` subdivision arcs is the difference of their endpoints. -/
theorem MappingTorusHomology.Covering.boundaryOne_arcPrefix (m n : ℕ) :
    SingularChains.boundaryOne (SingularHomology.CircleTopology.Circle)
        (∑ k ∈ Finset.range n,
          (SingularChains.pathChain (uPath m k) + SingularChains.pathChain (vPath m k))) =
      SingularChains.pointChain
          (quarterLift m n : (SingularHomology.CircleTopology.Circle)) -
        SingularChains.pointChain
          (quarterLift m 0 : (SingularHomology.CircleTopology.Circle)) := by
  induction n with
  | zero => simp
  | succ n
    ih =>
    rw [Finset.sum_range_succ, map_add, ih, map_add, SingularChains.boundaryOne_pathChain,
      SingularChains.boundaryOne_pathChain]
    abel

/-- The class of the first `n` subdivision arcs is the class of the single arc joining their
endpoints. -/
theorem MappingTorusHomology.Covering.chainClass_arcPrefix (m n : ℕ) :
    SingularChains.chainClass (SingularHomology.CircleTopology.Circle)
        (∑ k ∈ Finset.range n,
          (SingularChains.pathChain (uPath m k) + SingularChains.pathChain (vPath m k))) =
      SingularChains.pathClass (affineCircleArc (quarterLift m 0) (quarterLift m n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, map_add, ih, map_add]
    change
      SingularChains.pathClass (affineCircleArc (quarterLift m 0) (quarterLift m n)) +
          (SingularChains.pathClass (uPath m n) + SingularChains.pathClass (vPath m n)) =
        _
    rw [pathClass_uPath_add_vPath, pathClass_affineCircleArc_add]

/-- The one-chain formed by all `2m` half-arcs of the `m`-fold subdivision of the circle. -/
def MappingTorusHomology.Covering.arcSumChain (m : ℕ) :
    SingularChains.Chains (SingularHomology.CircleTopology.Circle) 1 :=
  ∑ k ∈ Finset.range m,
    (SingularChains.pathChain (uPath m k) + SingularChains.pathChain (vPath m k))

/-- The subdivision chain is a cycle: its endpoints cancel around the circle. -/
theorem MappingTorusHomology.Covering.boundaryOne_arcSumChain (m : ℕ) [NeZero m] :
    SingularChains.boundaryOne (SingularHomology.CircleTopology.Circle) (arcSumChain m) =
      0 := by rw [arcSumChain, boundaryOne_arcPrefix, quarterLift_circle_period, sub_self]

/-- The subdivision chain, as a one-cycle of the circle. -/
def MappingTorusHomology.Covering.arcSumCycle (m : ℕ) [NeZero m] :
    SingularChains.Cycles1 (SingularHomology.CircleTopology.Circle) :=
  SingularChains.mkCycle1 (SingularHomology.CircleTopology.Circle) (arcSumChain m)
    (boundaryOne_arcSumChain m)

/-- The underlying chain of the subdivision cycle is the subdivision chain. -/
@[simp]
theorem MappingTorusHomology.Covering.arcSumCycle_val (m : ℕ) [NeZero m] :
    (arcSumCycle m).1 = arcSumChain m :=
  rfl

/-- The class of the subdivision chain is the class of the arc from the first to the last quarter
point. -/
theorem MappingTorusHomology.Covering.chainClass_arcSumChain (m : ℕ) :
    SingularChains.chainClass (SingularHomology.CircleTopology.Circle) (arcSumChain m) =
      SingularChains.pathClass (affineCircleArc (quarterLift m 0) (quarterLift m m)) :=
  chainClass_arcPrefix m m

/-- An affine arc which advances by exactly one turn has the class of the positive loop based at
its starting point. -/
theorem MappingTorusHomology.Covering.pathClass_affineCircleArc_period (a : ℝ) :
    SingularChains.pathClass (affineCircleArc a (a + 1)) =
      SingularChains.pathClass (translatedPositiveLoop a) := by
  have hp :
    (affineCircleArc a (a + 1)).cast rfl (AddCircle.coe_add_period (1 : ℝ) a).symm =
      translatedPositiveLoop a := by
    apply Path.ext
    funext t
    simp only [Path.cast_coe, affineCircleArc_apply, translatedPositiveLoop_apply]
    congr 1
    ring
  rw [← hp, SingularChains.pathClass_cast]

/-- The subdivision cycle represents the fundamental class of the circle, the class of the
positive loop. -/
theorem MappingTorusHomology.Covering.arcSumCycle_positiveLoop_class (m : ℕ) [NeZero m] :
    SingularChains.cycleClass (SingularHomology.CircleTopology.Circle) (arcSumCycle m) =
      SingularChains.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  rw [← translatedPositiveLoop_class (quarterLift m 0)]
  apply
    SingularChains.homologyToChainClass_injective (SingularHomology.CircleTopology.Circle)
  rw [SingularChains.homologyToChainClass_cycleClass,
    SingularChains.homologyToChainClass_loopHomologyClass, arcSumCycle_val, chainClass_arcSumChain,
    quarterLift_period, pathClass_affineCircleArc_period]

/-- The first half-arc of the `k`-th subinterval, as a map of the unit interval. -/
def MappingTorusHomology.Covering.uCircleMap (m k : ℕ) : C(unitInterval, (MappingTorus.Circle)) :=
  ⟨uPath m k, (uPath m k).continuous⟩

/-- The second half-arc of the `k`-th subinterval, as a map of the unit interval. -/
def MappingTorusHomology.Covering.vCircleMap (m k : ℕ) : C(unitInterval, (MappingTorus.Circle)) :=
  ⟨vPath m k, (vPath m k).continuous⟩

/-- The chain induced by the first half-arc map on the identity path is the chain of that
half-arc. -/
@[simp]
theorem MappingTorusHomology.Covering.uCircleMap_pathChain (m k : ℕ) :
    SingularChains.inducedChain (uCircleMap m k) 1 (SingularChains.pathChain Path.id) =
      SingularChains.pathChain (uPath m k) := by
  rw [SingularChains.inducedChain_pathChain]
  rfl

/-- The chain induced by the second half-arc map on the identity path is the chain of that
half-arc. -/
@[simp]
theorem MappingTorusHomology.Covering.vCircleMap_pathChain (m k : ℕ) :
    SingularChains.inducedChain (vCircleMap m k) 1 (SingularChains.pathChain Path.id) =
      SingularChains.pathChain (vPath m k) := by
  rw [SingularChains.inducedChain_pathChain]
  rfl

/-- The cross product with the fundamental class of the circle can be computed with the
`m`-fold subdivision cycle as the circle representative. -/
theorem MappingTorusHomology.Covering.positiveCircleCross_subdivision_cycleClass {X : Type}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    PeriodTorusHigherHomology.positiveCircleCross X n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex ((MappingTorus.Circle) × X)) (n + 1)
        (SingularHomology.crossProductCycles (MappingTorus.Circle) X n (arcSumCycle m)
          b) := by
  have h :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex (MappingTorus.Circle)) 1 (arcSumCycle m) =
      SingularChains.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop :=
    arcSumCycle_positiveLoop_class m
  change
    SingularHomology.crossProductHomology (MappingTorus.Circle) X n
        (SingularChains.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n b) =
      _
  rw [← h]
  exact
    SingularHomology.crossProductHomology_cycleClass (MappingTorus.Circle) X n
      (arcSumCycle m) b

/-- The action of homeomorphisms of `X` on degree-`n` singular homology, as a monoid
homomorphism into the endomorphisms of that homology. -/
def MappingTorusHomology.Covering.monodromyHomologyMonoidHom {X : Type} [TopologicalSpace X]
    (n : ℕ) : (X ≃ₜ X) →* Module.End ℤ (SingularMayerVietoris.SingularHomology X n)
    where
  toFun B := MappingTorusHomology.monodromyHomologyMap B n
  map_one' := SingularHomology.singularHomologyMap_id X n
  map_mul' B D := SingularHomology.singularHomologyMap_comp (D : C(X, X)) (B : C(X, X)) n

/-- The monodromy map of a power of a homeomorphism is the corresponding power of its monodromy
map. -/
@[simp]
theorem MappingTorusHomology.Covering.monodromyHomologyMap_pow {X : Type} [TopologicalSpace X]
    (B : X ≃ₜ X) (n k : ℕ) :
    MappingTorusHomology.monodromyHomologyMap (B ^ k) n =
      (MappingTorusHomology.monodromyHomologyMap B n) ^ k :=
  map_pow (monodromyHomologyMonoidHom (X := X) n) B k

/-- The norm operator is the sum of the first `m` powers of the monodromy endomorphism. -/
theorem MappingTorusHomology.Covering.homologyNorm_eq_sum_powers {X : Type} [TopologicalSpace X]
    (m : ℕ) (B : X ≃ₜ X) (n : ℕ) :
    homologyNorm m B n =
      ∑ k ∈ Finset.range m, (MappingTorusHomology.monodromyHomologyMap B n) ^ k := by
  apply Finset.sum_congr rfl
  intro k _
  exact monodromyHomologyMap_pow B n k

/-- The `(n+1)`-chain in the first cover piece obtained by sweeping a cycle `b` of `X` along the
`k`-th strip. -/
def MappingTorusHomology.Covering.uCrossChain {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.Chains (MappingTorus.HomologyCover.U f) (n + 1) :=
  SingularChains.inducedChain (uStrip f k) (n + 1)
    (SingularHomology.crossProductEdge unitInterval X n (SingularChains.pathChain Path.id)
      b.1)

/-- The `(n+1)`-chain in the second cover piece obtained by sweeping a cycle `b` of `X` along the
`k`-th strip. -/
def MappingTorusHomology.Covering.vCrossChain {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (k n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.Chains (MappingTorus.HomologyCover.V f) (n + 1) :=
  SingularChains.inducedChain (vStrip f k) (n + 1)
    (SingularHomology.crossProductEdge unitInterval X n (SingularChains.pathChain Path.id)
      b.1)

/-- The boundary of the `k`-th first-piece sweep is the difference of the upper and the lower
section of the cycle. -/
theorem MappingTorusHomology.Covering.uCrossChain_boundary {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    ((SingularChains.singularComplex (MappingTorus.HomologyCover.U f)).d (n + 1) n).hom
        (uCrossChain f k n b) =
      SingularChains.inducedChain (MappingTorus.HomologyCover.intersectionToU f) n
        (SingularChains.inducedChain (upperSection f k) n b.1 -
          SingularChains.inducedChain (lowerSection f k) n b.1) := by
  rw [uCrossChain, ← SingularChains.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_path_boundary, map_sub, map_sub]
  congr 1
  · have h := congrArg (fun g => SingularChains.inducedChain g n b.1) (uStrip_one f k)
    simpa only [SingularChains.inducedChain_comp, LinearMap.comp_apply] using h
  · have h := congrArg (fun g => SingularChains.inducedChain g n b.1) (uStrip_zero f k)
    simpa only [SingularChains.inducedChain_comp, LinearMap.comp_apply] using h

/-- The boundary of the `k`-th second-piece sweep is the difference of the next lower section and
the upper section of the cycle. -/
theorem MappingTorusHomology.Covering.vCrossChain_boundary {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (k n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    ((SingularChains.singularComplex (MappingTorus.HomologyCover.V f)).d (n + 1) n).hom
        (vCrossChain f k n b) =
      SingularChains.inducedChain (MappingTorus.HomologyCover.intersectionToV f) n
        (SingularChains.inducedChain (lowerSection f (k + 1)) n b.1 -
          SingularChains.inducedChain (upperSection f k) n b.1) := by
  rw [vCrossChain, ← SingularChains.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_path_boundary, map_sub, map_sub]
  congr 1
  · have h := congrArg (fun g => SingularChains.inducedChain g n b.1) (vStrip_one f k)
    simpa only [SingularChains.inducedChain_comp, LinearMap.comp_apply] using h
  · have h := congrArg (fun g => SingularChains.inducedChain g n b.1) (vStrip_zero f k)
    simpa only [SingularChains.inducedChain_comp, LinearMap.comp_apply] using h

/-- The sum over `k < m` of the sweeps in the first cover piece. -/
def MappingTorusHomology.Covering.uCrossChainSum {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.Chains (MappingTorus.HomologyCover.U f) (n + 1) :=
  ∑ k ∈ Finset.range m, uCrossChain f k n b

/-- The sum over `k < m` of the sweeps in the second cover piece. -/
def MappingTorusHomology.Covering.vCrossChainSum {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.Chains (MappingTorus.HomologyCover.V f) (n + 1) :=
  ∑ k ∈ Finset.range m, vCrossChain f k n b

/-- The cycle of the intersection given by the sum over `k < m` of the differences of the upper
and lower sections of a cycle `b`. -/
def MappingTorusHomology.Covering.differenceCycle {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.Cycle
      (SingularChains.singularComplex
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f)))
      n :=
  ∑ k ∈ Finset.range m,
    (SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularChains.singularChainMap (upperSection f k)) n b -
      SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularChains.singularChainMap (lowerSection f k)) n b)

/-- The underlying chain of the difference cycle is the sum of the section differences. -/
@[simp]
theorem MappingTorusHomology.Covering.differenceCycle_val {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    (differenceCycle f m n b).1 =
      ∑ k ∈ Finset.range m,
        (SingularChains.inducedChain (upperSection f k) n b.1 -
          SingularChains.inducedChain (lowerSection f k) n b.1) := by
  simp only [differenceCycle, Submodule.coe_sum, Submodule.coe_sub,
    SingularMayerVietoris.ModuleHomology.mapCycles_val]

/-- If the gluing homeomorphism has order `m`, shifting the index of the lower sections by one
does not change their sum. -/
theorem MappingTorusHomology.Covering.lowerSection_chain_sum_shift {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    (∑ k ∈ Finset.range m, SingularChains.inducedChain (lowerSection f (k + 1)) n b.1) =
      ∑ k ∈ Finset.range m, SingularChains.inducedChain (lowerSection f k) n b.1 := by
  apply add_right_cancel (b := SingularChains.inducedChain (lowerSection f 0) n b.1)
  calc
    _ = ∑ k ∈ Finset.range (m + 1), SingularChains.inducedChain (lowerSection f k) n b.1 :=
      (Finset.sum_range_succ' (fun k => SingularChains.inducedChain (lowerSection f k) n b.1)
          m).symm
    _ = _ := by rw [Finset.sum_range_succ, lowerSection_period f m hf]

/-- The boundary of the first-piece sweep sum is the difference cycle, pushed into the first
piece. -/
theorem MappingTorusHomology.Covering.uCrossChainSum_boundary {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    ((SingularChains.singularComplex (MappingTorus.HomologyCover.U f)).d (n + 1) n).hom
        (uCrossChainSum f m n b) =
      SingularChains.inducedChain (MappingTorus.HomologyCover.intersectionToU f) n
        (differenceCycle f m n b).1 := by
  simp only [uCrossChainSum, differenceCycle_val, map_sum, uCrossChain_boundary]

/-- The boundary of the second-piece sweep sum is the negative of the difference cycle, pushed
into the second piece. -/
theorem MappingTorusHomology.Covering.vCrossChainSum_boundary {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    ((SingularChains.singularComplex (MappingTorus.HomologyCover.V f)).d (n + 1) n).hom
        (vCrossChainSum f m n b) =
      -SingularChains.inducedChain (MappingTorus.HomologyCover.intersectionToV f) n
          (differenceCycle f m n b).1 := by
  calc
    _ =
        SingularChains.inducedChain (MappingTorus.HomologyCover.intersectionToV f) n
          (∑ k ∈ Finset.range m,
            (SingularChains.inducedChain (lowerSection f (k + 1)) n b.1 -
              SingularChains.inducedChain (upperSection f k) n b.1)) := by
      simp only [vCrossChainSum, map_sum, vCrossChain_boundary]
    _ = _ := by
      rw [differenceCycle_val]
      simp only [Finset.sum_sub_distrib]
      rw [lowerSection_chain_sum_shift f m hf]
      simp only [map_sub]
      abel

/-- The class of the difference cycle is the sum over `k < m` of the differences of the classes of
the upper and the lower sections. -/
theorem MappingTorusHomology.Covering.differenceCycle_class {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex
          (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
            Set (MappingTorus.Torus f)))
        n (differenceCycle f m n b) =
      ∑ k ∈ Finset.range m,
        (SingularMayerVietoris.singularHomologyMap (upperSection f k) n
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
              b) -
          SingularMayerVietoris.singularHomologyMap (lowerSection f k) n
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
              b)) := by
  simp only [differenceCycle, map_sum, map_sub,
    ← SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]

/-- In the two homology coordinates of the intersection, the class of the difference cycle is
`(-N b, N b)`, where `N` is the norm operator. -/
theorem MappingTorusHomology.Covering.differenceCycle_class_coordinates {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (m n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    MappingTorusHomology.intersectionHomologyEquiv f n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (SingularChains.singularComplex
            (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
              Set (MappingTorus.Torus f)))
          n (differenceCycle f m n b)) =
      (-homologyNorm m f n
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
              b),
        homologyNorm m f n
          (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
            b)) := by
  rw [differenceCycle_class, map_sum]
  simp only [map_sub, upperSection_homology_coordinates, lowerSection_homology_coordinates,
    Prod.mk_sub_mk, zero_sub, sub_zero, ← prod_mk_sum, Finset.sum_neg_distrib, homologyNorm_apply]

/-- The Mayer--Vietoris small cycle of degree `n + 1` in the mapping torus built from the two
sweep sums and their common boundary. -/
def MappingTorusHomology.Covering.coverSmallCycle {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.Cycle
      (SingularMayerVietoris.smallComplex (MappingTorus.HomologyCover.U f)
        (MappingTorus.HomologyCover.V f))
      (n + 1) :=
  PeriodTorusHigherHomology.twoChainSmallCycle (MappingTorus.HomologyCover.U f)
    (MappingTorus.HomologyCover.V f) n (uCrossChainSum f m n b) (vCrossChainSum f m n b)
    (differenceCycle f m n b) (uCrossChainSum_boundary f m n b)
    (vCrossChainSum_boundary f m hf n b)

/-- The ambient chain of the small cycle is the sum of the two sweep sums. -/
theorem MappingTorusHomology.Covering.coverSmallCycle_ambient_val {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (MappingTorus.HomologyCover.U f)
            (MappingTorus.HomologyCover.V f))
          (n + 1) (coverSmallCycle f m hf n b)).1 =
      SingularChains.inducedChain (MappingTorus.HomologyCover.inclusionU f) (n + 1)
          (uCrossChainSum f m n b) +
        SingularChains.inducedChain (MappingTorus.HomologyCover.inclusionV f) (n + 1)
          (vCrossChainSum f m n b) :=
  PeriodTorusHigherHomology.twoChainSmallCycle_ambient_val (MappingTorus.HomologyCover.U f)
    (MappingTorus.HomologyCover.V f) n (uCrossChainSum f m n b) (vCrossChainSum f m n b)
    (differenceCycle f m n b) (uCrossChainSum_boundary f m n b)
    (vCrossChainSum_boundary f m hf n b)

/-- The ambient chain of the small cycle is also the sum over `k < m` of the two individual
sweeps. -/
theorem MappingTorusHomology.Covering.coverSmallCycle_ambient_sum_val {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (MappingTorus.HomologyCover.U f)
            (MappingTorus.HomologyCover.V f))
          (n + 1) (coverSmallCycle f m hf n b)).1 =
      ∑ k ∈ Finset.range m,
        (SingularChains.inducedChain (MappingTorus.HomologyCover.inclusionU f) (n + 1)
            (uCrossChain f k n b) +
          SingularChains.inducedChain (MappingTorus.HomologyCover.inclusionV f) (n + 1)
            (vCrossChain f k n b)) := by
  simp only [coverSmallCycle_ambient_val, uCrossChainSum, vCrossChainSum, map_sum,
    Finset.sum_add_distrib]

/-- The Mayer--Vietoris connecting homomorphism sends the class of the small cycle to the class of
the difference cycle. -/
theorem MappingTorusHomology.Covering.coverSmallCycle_connecting {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    MappingTorusHomology.mayerVietorisConnecting f n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (SingularChains.singularComplex (MappingTorus.Torus f)) (n + 1)
          (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularMayerVietoris.smallInclusion (MappingTorus.HomologyCover.U f)
              (MappingTorus.HomologyCover.V f))
            (n + 1) (coverSmallCycle f m hf n b))) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex
          (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
            Set (MappingTorus.Torus f)))
        n (differenceCycle f m n b) :=
  PeriodTorusHigherHomology.connectingHomomorphism_twoChain (MappingTorus.HomologyCover.U f)
    (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
    (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f) n
    (uCrossChainSum f m n b) (vCrossChainSum f m n b) (differenceCycle f m n b)
    (uCrossChainSum_boundary f m n b) (vCrossChainSum_boundary f m hf n b)

/-- In the two boundary coordinates, the class of the small cycle is `(-N b, N b)` with `N` the
norm operator: this is the Wang relation. -/
theorem MappingTorusHomology.Covering.coverSmallCycle_boundaryCoordinates {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (m : ℕ) (hf : f ^ m = 1) (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    MappingTorusHomology.boundaryCoordinates f n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (SingularChains.singularComplex (MappingTorus.Torus f)) (n + 1)
          (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularMayerVietoris.smallInclusion (MappingTorus.HomologyCover.U f)
              (MappingTorus.HomologyCover.V f))
            (n + 1) (coverSmallCycle f m hf n b))) =
      (-homologyNorm m f n
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
              b),
        homologyNorm m f n
          (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
            b)) := by
  rw [MappingTorusHomology.boundaryCoordinates_apply, coverSmallCycle_connecting]
  exact differenceCycle_class_coordinates f m n b

/-- Any class of `S¹ × X` differs from the cross product with its circle boundary by an element in
the image of the circle section. -/
theorem MappingTorusHomology.Covering.sub_cross_boundary_mem_range_circleSection {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((SingularHomology.CircleTopology.Circle) × X) (n + 1)) :
    a -
        PeriodTorusHigherHomology.positiveCircleCross X n
          (SingularHomology.circleBoundary X n a) ∈
      LinearMap.range (SingularHomology.circleSectionHomology X (n + 1)) := by
  rw [SingularHomology.circleBoundary_exact]
  change
    SingularHomology.circleBoundary X n
        (a -
          PeriodTorusHigherHomology.positiveCircleCross X n
            (SingularHomology.circleBoundary X n a)) =
      0
  rw [map_sub, PeriodTorusHigherHomology.circleBoundary_positiveCircleCross, sub_self]

/-- A linear map on the homology of `S¹ × X` which kills the circle section and agrees with `N` on
cross products is `N` composed with the circle boundary, evaluated at any class. -/
theorem MappingTorusHomology.Covering.eq_comp_circleBoundary_of_section_cross_apply {X : Type}
    [TopologicalSpace X] {A : Type*} [AddCommGroup A] [Module ℤ A] (n : ℕ)
    (L :
      SingularMayerVietoris.SingularHomology
          ((SingularHomology.CircleTopology.Circle) × X) (n + 1) →ₗ[ℤ]
        A)
    (N : SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] A)
    (hsec : ∀ b, L (SingularHomology.circleSectionHomology X (n + 1) b) = 0)
    (hcross : ∀ b, L (PeriodTorusHigherHomology.positiveCircleCross X n b) = N b)
    (a :
      SingularMayerVietoris.SingularHomology
        ((SingularHomology.CircleTopology.Circle) × X) (n + 1)) :
    L a = N (SingularHomology.circleBoundary X n a) := by
  obtain ⟨b, hb⟩ := sub_cross_boundary_mem_range_circleSection n a
  have h := hsec b
  rw [hb, map_sub, hcross] at h
  exact sub_eq_zero.mp h

/-- A linear map on the homology of `S¹ × X` which kills the circle section and agrees with `N` on
cross products equals `N` composed with the circle boundary. -/
theorem MappingTorusHomology.Covering.eq_comp_circleBoundary_of_section_cross {X : Type}
    [TopologicalSpace X] {A : Type*} [AddCommGroup A] [Module ℤ A] (n : ℕ)
    (L :
      SingularMayerVietoris.SingularHomology
          ((SingularHomology.CircleTopology.Circle) × X) (n + 1) →ₗ[ℤ]
        A)
    (N : SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] A)
    (hsec : ∀ b, L (SingularHomology.circleSectionHomology X (n + 1) b) = 0)
    (hcross : ∀ b, L (PeriodTorusHigherHomology.positiveCircleCross X n b) = N b) :
    L = N.comp (SingularHomology.circleBoundary X n) := by
  ext a
  exact eq_comp_circleBoundary_of_section_cross_apply n L N hsec hcross a
