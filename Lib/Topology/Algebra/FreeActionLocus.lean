/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
/-!
# The free-action locus of a group action

  The free-action locus: the largest invariant open subset on which a group acts
  freely, closed under restriction, with the induced quotient map properties
  (Forster, Lectures on Riemann Surfaces, Section 1).
-/



open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### The free-action locus -/

/-- The points with trivial stabilizer. -/
def FreeActionLocus.locus (G X : Type*) [Group G] [MulAction G X] : Set X :=
  {x | ∀ g : G, g • x = x → g = 1}

/-- The free-action locus as a subtype. -/
abbrev FreeActionLocus.Space (G X : Type*) [Group G] [MulAction G X] :=
  { x : X // x ∈ locus G X }

/-- The free locus is `G`-invariant. -/
theorem FreeActionLocus.smul_mem_locus (G X : Type*) [Group G] [MulAction G X] (g : G) {x : X}
    (hx : x ∈ locus G X) : g • x ∈ locus G X := by
  intro h hh
  have he : g⁻¹ * h * g = 1 :=
    hx _
      (by
        simpa only [SemigroupAction.mul_smul, inv_smul_smul] using congrArg (fun y => g⁻¹ • y) hh)
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left, inv_mul_cancel,
    one_mul] using congrArg (fun k : G => g * k * g⁻¹) he

/-- A translate lies in the free locus exactly when the point does. -/
theorem FreeActionLocus.smul_mem_locus_iff (G X : Type*) [Group G] [MulAction G X] (g : G)
    (x : X) : g • x ∈ locus G X ↔ x ∈ locus G X := by
  refine ⟨fun hx => ?_, smul_mem_locus G X g⟩
  simpa only [inv_smul_smul] using smul_mem_locus G X g⁻¹ hx

/-- The `G`-action on the free locus. -/
instance FreeActionLocus.mulAction (G X : Type*) [Group G] [MulAction G X] :
    MulAction G (Space G X)
    where
  smul g x := ⟨g • x.val, smul_mem_locus G X g x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (SemigroupAction.mul_smul g h x.val)

/-- The action on the free locus is free (cancellative). -/
instance FreeActionLocus.isCancelSMul (G X : Type*) [Group G] [MulAction G X] :
    IsCancelSMul G (Space G X) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  exact x.property g (congrArg Subtype.val hx)

/-- The action on the free locus is continuous in each element. -/
instance FreeActionLocus.continuousConstSMul (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace X] [ContinuousConstSMul G X] : ContinuousConstSMul G (Space G X) where
  continuous_const_smul
    g := ((ContinuousConstSMul.continuous_const_smul g).comp continuous_subtype_val).subtype_mk _

/-- The action on the free locus stays properly discontinuous. -/
instance FreeActionLocus.properlyDiscontinuousSMul (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace X] [ProperlyDiscontinuousSMul G X] : ProperlyDiscontinuousSMul G (Space G X)
    where
  finite_disjoint_inter_image {K L} hK
    hL := by
    apply
      (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G)
          (hK.image continuous_subtype_val) (hL.image continuous_subtype_val)).subset
    rintro g ⟨y, ⟨x, hx, hxy⟩, hy⟩
    exact ⟨y.val, ⟨x.val, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩, ⟨y, hy, rfl⟩⟩

/-- A proper action element fixing a point has finite order. -/
theorem FreeActionLocus.isOfFinOrder_of_smul_eq (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace X] [ProperlyDiscontinuousSMul G X] (g : G) (x : X) (hg : g • x = x) :
    IsOfFinOrder g := by
  let := (ProperlyDiscontinuousSMul.finite_stabilizer (Γ := G) x).fintype
  exact
    (MulAction.stabilizer G x).subtype.isOfFinOrder
      (isOfFinOrder_of_finite (⟨g, hg⟩ : MulAction.stabilizer G x))

/-- For a properly discontinuous action on a locally compact Hausdorff space the free locus is open. -/
theorem FreeActionLocus.isOpen_locus (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] : IsOpen (locus G X) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hdis⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  apply Filter.mem_of_superset hU
  intro y hy g hgy
  exact hx g (hdis g ⟨y, ⟨y, hy, hgy⟩, hy⟩)

/-- The free locus as an open set. -/
def FreeActionLocus.opens (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X] :
    TopologicalSpace.Opens X :=
  ⟨locus G X, isOpen_locus G X⟩

/-- The free locus inherits the charted-space structure. -/
instance FreeActionLocus.chartedSpace (G X E : Type*) [Group G] [TopologicalSpace X]
    [MulAction G X] [T2Space X] [LocallyCompactSpace X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] [NormedAddCommGroup E] [ChartedSpace E X] :
    ChartedSpace E (Space G X) :=
  inferInstanceAs (ChartedSpace E (opens G X))

/-- Group elements act smoothly on the free locus. -/
theorem FreeActionLocus.smul_contMDiff (G X E : Type*) [Group G] [TopologicalSpace X]
    [MulAction G X] [T2Space X] [LocallyCompactSpace X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E X]
    (n : ℕ∞ω)
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : X => g • x))
    (g : G) :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun x : Space G X => g • x) := by
  intro x
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
        (fun y : Space G X => ((g • y : Space G X) : X)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
        (fun y : Space G X => g • y) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := opens G X)
      (fun y : Space G X => g • y) Set.univ x
  exact he.mp (((hG g).comp (contMDiff_subtype_val (U := opens G X))) x)
