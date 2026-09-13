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
/-!
# Wang-family rows: torus circle cross-product and covering cycles

  Circle translations and their induced homology maps, the positive circle
  cross-product, the two-chain small-cycle assembly, the two-open-cover
  covering chains of the mapping torus, and the punctured-cylinder
  homeomorphisms (Hatcher, Algebraic Topology, Example 2.48).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v w

noncomputable section

namespace Mathoverflow1973



def PeriodTorusHigherHomology.CirclePaths.circleTranslation (a : ℝ) :
    C((SingularHomology.CircleTopology.Circle),
      (SingularHomology.CircleTopology.Circle)) :=
  ⟨fun z => (a : (SingularHomology.CircleTopology.Circle)) + z, by
    exact
      (continuous_const :
            Continuous
              (fun _ : (SingularHomology.CircleTopology.Circle) =>
                (a : (SingularHomology.CircleTopology.Circle)))).add
        continuous_id⟩



def PeriodTorusHigherHomology.CirclePaths.positiveLoop :
    Path (0 : (SingularHomology.CircleTopology.Circle)) 0
    where
  toFun t := ((t : ℝ) : (SingularHomology.CircleTopology.Circle))
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  source' := AddCircle.coe_zero (1 : ℝ)
  target' := AddCircle.coe_period (1 : ℝ)



def PeriodTorusHigherHomology.positiveCircleCross (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((SingularHomology.CircleTopology.Circle) × X) (n + 1) :=
  SingularHomology.crossProductHomology (SingularHomology.CircleTopology.Circle) X n
    (SingularChains.loopHomologyClass CirclePaths.positiveLoop)



theorem PeriodTorusHigherHomology.crossProductEdge_boundary_of_right_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    ((SingularChains.singularComplex (X × Y)).d (n + 1) n).hom (SingularHomology.crossProductEdge X Y n a b.1) =
      SingularHomology.crossProductZeroLeft X Y n (((SingularChains.singularComplex X).d 1 0).hom a) b.1 := by
  cases n with
  | zero => exact SingularHomology.crossProductEdge_boundary_zero a b.1
  | succ
    n =>
    have hb : ((SingularChains.singularComplex Y).d (n + 1) n).hom b.1 = 0 := by
      simpa only [Nat.succ_sub_one] using
        SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex Y)
          (n + 1) b
    simp only [SingularHomology.crossProductEdge_boundary, hb, map_zero, sub_zero]


theorem PeriodTorusHigherHomology.crossProductEdge_path_boundary {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) {x y : X} (p : Path x y)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    ((SingularChains.singularComplex (X × Y)).d (n + 1) n).hom
        (SingularHomology.crossProductEdge X Y n (SingularChains.pathChain p) b.1) =
      SingularChains.inducedChain (SingularHomology.crossInsertLeft y) n b.1 -
        SingularChains.inducedChain (SingularHomology.crossInsertLeft x) n b.1 := by
  rw [crossProductEdge_boundary_of_right_cycle]
  change
    SingularHomology.crossProductZeroLeft X Y n (SingularChains.boundaryOne X (SingularChains.pathChain p)) b.1 = _
  rw [SingularChains.boundaryOne_pathChain, map_sub, LinearMap.sub_apply]
  simp only [SingularChains.pointChain, SingularHomology.crossProductZeroLeft_simplex_left]
  rfl



theorem MappingTorusHomology.Covering.mk_add_int {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (t : ℝ) (k : ℤ) (x : X) :
    MappingTorus.mk f (t + (k : ℝ), x) = MappingTorus.mk f (t, (f ^ k) x) := by
  apply (MappingTorus.mk_eq_mk_iff f _ _).mpr
  exact ⟨-k, by simp, by simp⟩



def MappingTorusHomology.Covering.affineRealArc (a b : ℝ) : Path a b
    where
  toFun t := a + (b - a) * (t : ℝ)
  continuous_toFun := continuous_const.add (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by simp



def MappingTorusHomology.Covering.homologyNorm {X : Type} [TopologicalSpace X] (m : ℕ)
    (B : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n :=
  ∑ k ∈ Finset.range m, SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n


@[simp]
theorem MappingTorusHomology.Covering.homologyNorm_apply {X : Type} [TopologicalSpace X] (m : ℕ)
    (B : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    homologyNorm m B n a =
      ∑ k ∈ Finset.range m,
        SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n a := by
  simp only [homologyNorm, LinearMap.sum_apply]


theorem MappingTorusHomology.Covering.homeomorph_symm_pow_eq {X : Type} [TopologicalSpace X]
    (m : ℕ) (B : X ≃ₜ X) (hB : B ^ m = 1) (k : ℕ) (hk : k ≤ m) : B.symm ^ k = B ^ (m - k) := by
  change B⁻¹ ^ k = B ^ (m - k)
  rw [pow_sub B hk, hB, one_mul, inv_pow]



theorem MappingTorus.mk_unitCylinder_surjective {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    MappingTorus.mk f '' ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ : Set X)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective f q
  refine ⟨deck f (-⌊t⌋) (t, x), ?_, mk_deck f (-⌊t⌋) (t, x)⟩
  change (0 ≤ t + ((-⌊t⌋ : ℤ) : ℝ) ∧ t + ((-⌊t⌋ : ℤ) : ℝ) ≤ 1) ∧ True
  push_cast
  exact ⟨⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩, trivial⟩


instance MappingTorus.compactSpace {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X ≃ₜ X) : CompactSpace (Torus f) where
  isCompact_univ := by
    rw [← mk_unitCylinder_surjective f]
    exact (CompactIccSpace.isCompact_Icc.prod isCompact_univ).image (mk_continuous f)



def PassageHomology.radialCylinderHomeomorph (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : (ℝ × Metric.sphere (0 : E) 1) ≃ₜ ({0}ᶜ : Set E) :=
  ((Homeomorph.prodComm ℝ (Metric.sphere (0 : E) 1)).trans
        ((Homeomorph.refl (Metric.sphere (0 : E) 1)).prodCongr
          Real.expOrderIso.toHomeomorph)).trans
    (homeomorphUnitSphereProd E).symm


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


def PassageHomology.cylinderLink {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : ℝ) (u : Metric.sphere (0 : E) 1) (ε : ℝ) (hε : 0 < ε) (hεu : ε < Real.exp τ) :
    C(Metric.sphere (0 : E) 1, ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1))) :=
  ((PassageHomology.puncturedCylinderHomeomorph τ u).symm : C(_, _)).comp
    (PassageHomology.linkingSphere (PassageHomology.cylinderPuncture τ u) ε hε (by rwa [norm_cylinderPuncture]))


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


theorem PartialChart.openInclusion_target {E H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X]
    [ChartedSpace H X] (U : TopologicalSpace.Opens X) [Nonempty U] :
    (openInclusion (I := I) U).target = U := by
  change U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.target = U
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact Subtype.range_coe


theorem PartialChart.openInclusion_symm_coe {E H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X]
    [ChartedSpace H X] (U : TopologicalSpace.Opens X) [Nonempty U] {x : X} (hx : x ∈ U) :
    ((openInclusion (I := I) U).symm x).val = x := by
  have h :=
    (openInclusion (I := I) U).right_inv
      (show x ∈ (openInclusion (I := I) U).target by rw [openInclusion_target]; exact hx)
  exact h


theorem PassageHomology.radialCylinderHomeomorph_symm_fst (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ({0}ᶜ : Set E)) :
    ((radialCylinderHomeomorph E).symm x).1 = Real.log ‖x.val‖ := by
  have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property
  change Real.expOrderIso.symm ((homeomorphUnitSphereProd E) x).2 = _
  rw [Real.log_of_pos hn]
  congr 1
  apply Subtype.ext
  exact homeomorphUnitSphereProd_apply_snd_coe E x


theorem PassageHomology.radialCylinderHomeomorph_symm_snd_coe (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : ({0}ᶜ : Set E)) :
    (((radialCylinderHomeomorph E).symm x).2 : E) = ‖x.val‖⁻¹ • x.val := by
  change (((homeomorphUnitSphereProd E) x).1 : E) = _
  exact homeomorphUnitSphereProd_apply_fst_coe E x


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


def PassageHomology.radialCylinderChart (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : Metric.sphere (0 : E) 1) :
    PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (ℝ × Metric.sphere (0 : E) 1) E ∞ := by
  let _ : Nonempty (PassageHomology.puncturedVectorSpace E) :=
    ⟨⟨u.val, Metric.ne_of_mem_sphere u.property one_ne_zero⟩⟩
  exact
    (PassageHomology.radialCylinderDiffeomorph E n).toPartialDiffeomorph.trans
      (PartialChart.openInclusion (I := 𝓘(ℝ, E)) (PassageHomology.puncturedVectorSpace E))


theorem PassageHomology.radialCylinderChart_mem_source (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : Metric.sphere (0 : E) 1) (p : ℝ × Metric.sphere (0 : E) 1) :
    p ∈ (radialCylinderChart E n u).source :=
  ⟨Set.mem_univ _, Set.mem_univ _⟩


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



private def PeriodTorusHigherHomology.biprodElement_mo1973_12801
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : K.X n) (b : L.X n) : (K ⊞ L).X n :=
  ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom a +
    ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom b


def PeriodTorusHigherHomology.twoChainMiddle {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ)
    (a : SingularChains.Chains U (n + 1)) (b : SingularChains.Chains V (n + 1)) :
    (SingularMayerVietoris.middleComplex U V).X (n + 1) :=
  PeriodTorusHigherHomology.biprodElement_mo1973_12801 (SingularChains.singularComplex U) (SingularChains.singularComplex V)
    (n + 1) a b


private theorem PeriodTorusHigherHomology.biprod_lift_f_apply_mo1973_12802
    {J K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : J ⟶ K) (g : J ⟶ L) (n : ℕ) (z : J.X n) :
    ((CategoryTheory.Limits.biprod.lift f g).f n).hom z =
      ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom ((f.f n).hom z) +
        ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom ((g.f n).hom z) := by
  have htotal :=
    congrArg (fun h => h.hom (((CategoryTheory.Limits.biprod.lift f g).f n).hom z))
      (HomologicalComplex.biprod_total_f K L n)
  have hfst := congrArg (fun h => h.hom z) (HomologicalComplex.biprod_lift_fst_f f g n)
  have hsnd := congrArg (fun h => h.hom z) (HomologicalComplex.biprod_lift_snd_f f g n)
  change
    ((CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K).f n).hom
        (((CategoryTheory.Limits.biprod.lift f g).f n).hom z) =
      (f.f n).hom z at hfst
  change
    ((CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L).f n).hom
        (((CategoryTheory.Limits.biprod.lift f g).f n).hom z) =
      (g.f n).hom z at hsnd
  change
    ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom
          (((CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K).f n).hom
            (((CategoryTheory.Limits.biprod.lift f g).f n).hom z)) +
        ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom
          (((CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L).f n).hom
            (((CategoryTheory.Limits.biprod.lift f g).f n).hom z)) =
      ((CategoryTheory.Limits.biprod.lift f g).f n).hom z at htotal
  rw [hfst, hsnd] at htotal
  exact htotal.symm


private def PeriodTorusHigherHomology.biprodElement_desc_mo1973_12803
    {K L T : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ T) (g : L ⟶ T) (n : ℕ) (a : K.X n)
    (b : L.X n) :
    ((CategoryTheory.Limits.biprod.desc f g).f n).hom (PeriodTorusHigherHomology.biprodElement_mo1973_12801 K L n a b) =
      (f.f n).hom a + (g.f n).hom b := by
  change
    ((CategoryTheory.Limits.biprod.desc f g).f n).hom
        (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom a +
          ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom b) =
      _
  rw [map_add]
  congr 1
  · exact congrArg (fun h => h.hom a) (HomologicalComplex.biprod_inl_desc_f f g n)
  · exact congrArg (fun h => h.hom b) (HomologicalComplex.biprod_inr_desc_f f g n)


theorem PeriodTorusHigherHomology.twoChainMiddle_rightMap {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularChains.Chains U (n + 1))
    (b : SingularChains.Chains V (n + 1)) :
    ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b) =
      ((SingularMayerVietoris.toSmallLeft U V).f (n + 1)).hom a +
        ((SingularMayerVietoris.toSmallRight U V).f (n + 1)).hom b :=
  PeriodTorusHigherHomology.biprodElement_desc_mo1973_12803 (SingularMayerVietoris.toSmallLeft U V)
    (SingularMayerVietoris.toSmallRight U V) (n + 1) a b


private theorem PeriodTorusHigherHomology.biprodElement_boundary_mo1973_12804
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i j : ℕ) (a : K.X i) (b : L.X i) :
    ((K ⊞ L).d i j).hom (PeriodTorusHigherHomology.biprodElement_mo1973_12801 K L i a b) =
      PeriodTorusHigherHomology.biprodElement_mo1973_12801 K L j ((K.d i j).hom a) ((L.d i j).hom b) := by
  have hK := congrArg (fun f => f.hom a) ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).comm i j)
  have hL := congrArg (fun f => f.hom b) ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).comm i j)
  change
    ((K ⊞ L).d i j).hom (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f i).hom a) =
      ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f j).hom ((K.d i j).hom a) at hK
  change
    ((K ⊞ L).d i j).hom (((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f i).hom b) =
      ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f j).hom ((L.d i j).hom b) at hL
  change
    ((K ⊞ L).d i j).hom
        (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f i).hom a +
          ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f i).hom b) =
      _
  rw [map_add, hK, hL]
  rfl


private theorem PeriodTorusHigherHomology.biprod_lift_eq_boundary_mo1973_12805
    {J K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : J ⟶ K) (g : J ⟶ L) (i j : ℕ) (a : K.X i)
    (b : L.X i) (z : J.X j) (ha : (K.d i j).hom a = (f.f j).hom z)
    (hb : (L.d i j).hom b = (g.f j).hom z) :
    ((CategoryTheory.Limits.biprod.lift f g).f j).hom z =
      ((K ⊞ L).d i j).hom (PeriodTorusHigherHomology.biprodElement_mo1973_12801 K L i a b) := by
  have hlift := PeriodTorusHigherHomology.biprod_lift_f_apply_mo1973_12802 f g j z
  have hboundary := PeriodTorusHigherHomology.biprodElement_boundary_mo1973_12804 K L i j a b
  have hab := congrArg₂ (PeriodTorusHigherHomology.biprodElement_mo1973_12801 K L j) ha hb
  exact hlift.trans (hab.symm.trans hboundary.symm)


theorem PeriodTorusHigherHomology.twoChainMiddle_boundary {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularChains.Chains U (n + 1))
    (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    ((SingularMayerVietoris.leftMap U V).f n).hom z.1 =
      ((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom (twoChainMiddle U V n a b) :=
  PeriodTorusHigherHomology.biprod_lift_eq_boundary_mo1973_12805 (SingularMayerVietoris.intersectionToLeft U V)
    (-(SingularMayerVietoris.intersectionToRight U V)) (n + 1) n a b z.1 ha hb


theorem PeriodTorusHigherHomology.twoChainSmallCycle_condition {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularChains.Chains U (n + 1))
    (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    ((SingularMayerVietoris.smallComplex U V).d (n + 1) n).hom
        (((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b)) =
      0 := by
  have hcomm :=
    congrArg (fun f => f.hom (twoChainMiddle U V n a b))
      ((SingularMayerVietoris.rightMap U V).comm (n + 1) n)
  have hzero := congrArg (fun f => (f.f n).hom z.1) (SingularMayerVietoris.leftMap_rightMap U V)
  calc
    _ =
        ((SingularMayerVietoris.rightMap U V).f n).hom
          (((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom
            (twoChainMiddle U V n a b)) :=
      hcomm
    _ =
        ((SingularMayerVietoris.rightMap U V).f n).hom
          (((SingularMayerVietoris.leftMap U V).f n).hom z.1) :=
      (congrArg ((SingularMayerVietoris.rightMap U V).f n).hom
        (twoChainMiddle_boundary U V n a b z ha hb).symm)
    _ = 0 := hzero


def PeriodTorusHigherHomology.twoChainSmallCycle {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : SingularChains.Chains U (n + 1)) (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularMayerVietoris.smallComplex U V) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularMayerVietoris.smallComplex U V) (n + 1)
    (((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b))
    (by
      rw [Nat.add_sub_cancel]
      exact twoChainSmallCycle_condition U V n a b z ha hb)


@[simp]
theorem PeriodTorusHigherHomology.twoChainSmallCycle_val {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularChains.Chains U (n + 1))
    (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    (twoChainSmallCycle U V n a b z ha hb).1 =
      ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b) :=
  rfl


theorem PeriodTorusHigherHomology.twoChainSmallCycle_ambient_val {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularChains.Chains U (n + 1))
    (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    (SingularMayerVietoris.ModuleHomology.mapCycles (SingularMayerVietoris.smallInclusion U V)
          (n + 1) (twoChainSmallCycle U V n a b z ha hb)).1 =
      SingularChains.inducedChain (SingularMayerVietoris.subtypeInclusion U) (n + 1) a +
        SingularChains.inducedChain (SingularMayerVietoris.subtypeInclusion V) (n + 1) b := by
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, twoChainSmallCycle_val,
    twoChainMiddle_rightMap, map_add]
  have hU :=
    congrArg (fun f => (f.f (n + 1)).hom a) (SingularMayerVietoris.toSmallLeft_inclusion U V)
  have hV :=
    congrArg (fun f => (f.f (n + 1)).hom b) (SingularMayerVietoris.toSmallRight_inclusion U V)
  exact congrArg₂ (· + ·) hU hV


theorem PeriodTorusHigherHomology.connectingHomomorphism_twoChain {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (a : SingularChains.Chains U (n + 1)) (b : SingularChains.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((SingularChains.singularComplex U).d (n + 1) n).hom a =
        SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((SingularChains.singularComplex V).d (n + 1) n).hom b =
        -SingularChains.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (n + 1)
          (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularMayerVietoris.smallInclusion U V) (n + 1)
            (twoChainSmallCycle U V n a b z ha hb))) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex (U ∩ V : Set X)) n z :=
  SingularHomology.connectingHomomorphism_cycleClass U V hU hV hcover n (twoChainSmallCycle U V n a b z ha hb)
    (twoChainMiddle U V n a b) rfl z (twoChainMiddle_boundary U V n a b z ha hb)



private theorem MappingTorusHomology.Covering.sum_range_shift_of_endpoints_mo1973_27356
    {A : Type*} [AddCommGroup A] (F : ℕ → A) (m : ℕ) (hF : F m = F 0) :
    ∑ k ∈ Finset.range m, F (k + 1) = ∑ k ∈ Finset.range m, F k := by
  apply add_right_cancel (b := F 0)
  calc
    (∑ k ∈ Finset.range m, F (k + 1)) + F 0 = ∑ k ∈ Finset.range (m + 1), F k :=
      (Finset.sum_range_succ' F m).symm
    _ = (∑ k ∈ Finset.range m, F k) + F 0 := by rw [Finset.sum_range_succ, hF]


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
        MappingTorusHomology.Covering.sum_range_shift_of_endpoints_mo1973_27356
          (fun k => SingularMayerVietoris.singularHomologyMap ((B ^ k : X ≃ₜ X) : C(X, X)) n) m
      rw [hB, pow_zero]


@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_apply (a : ℝ)
    (z : (SingularHomology.CircleTopology.Circle)) :
    circleTranslation a z = (a : (SingularHomology.CircleTopology.Circle)) + z :=
  rfl


def PeriodTorusHigherHomology.CirclePaths.circleTranslationHomotopy (a : ℝ) :
    (circleTranslation a).Homotopy
      (ContinuousMap.id (SingularHomology.CircleTopology.Circle))
    where
  toFun
    p := ((((1 - (p.1 : ℝ)) * a : ℝ) : (SingularHomology.CircleTopology.Circle)) + p.2)
  continuous_toFun :=
    ((AddCircle.continuous_mk' (1 : ℝ)).comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            continuous_const)).add
      continuous_snd
  map_zero_left z := by simp
  map_one_left z := by simp


@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_singularHomologyMap (a : ℝ)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (circleTranslation a) n = LinearMap.id := by
  rw [SingularHomology.homotopy_homologyMap (circleTranslationHomotopy a) n,
    SingularHomology.singularHomologyMap_id]


@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_inducedHomology (a : ℝ) :
    SingularChains.inducedHomology (circleTranslation a) = LinearMap.id :=
  circleTranslation_singularHomologyMap a 1


theorem PeriodTorusHigherHomology.CirclePaths.loopHomologyClass_map_circleTranslation (a : ℝ)
    {x : (SingularHomology.CircleTopology.Circle)} (p : Path x x) :
    SingularChains.loopHomologyClass (p.map (circleTranslation a).continuous) =
      SingularChains.loopHomologyClass p := by
  rw [← SingularChains.inducedHomology_loopHomologyClass (circleTranslation a) x p,
    circleTranslation_inducedHomology]
  rfl



def MappingTorusHomology.Covering.translatedPositiveLoop (a : ℝ) :
    Path (a : (SingularHomology.CircleTopology.Circle))
      (a : (SingularHomology.CircleTopology.Circle)) :=
  ((PeriodTorusHigherHomology.CirclePaths.positiveLoop.map
        (PeriodTorusHigherHomology.CirclePaths.circleTranslation a).continuous).cast
    (by simp) (by simp))


@[simp]
theorem MappingTorusHomology.Covering.translatedPositiveLoop_apply (a : ℝ) (t : unitInterval) :
    translatedPositiveLoop a t =
      ((a + (t : ℝ) : ℝ) : (SingularHomology.CircleTopology.Circle)) := by
  change
    (a : (SingularHomology.CircleTopology.Circle)) +
        ((t : ℝ) : (SingularHomology.CircleTopology.Circle)) =
      ((a + (t : ℝ) : ℝ) : (SingularHomology.CircleTopology.Circle))
  exact (AddCircle.coe_add (1 : ℝ) a (t : ℝ)).symm



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

end Mathoverflow1973
