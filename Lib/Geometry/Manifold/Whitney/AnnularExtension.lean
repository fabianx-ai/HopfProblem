/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.CleanStrips

/-!
# Annular extensions and sphere nullhomotopies

Sphere cones, annular extensions of circle maps, smooth sphere representatives and the nullhomotopy of sphere maps omitting a point or of low dimension, extension of circle nullhomotopies to bigon neighbourhoods, and the `TubularBigon` structure.

Moved verbatim from the project stock file `Hopf/SingularHomology.lean` (integration 4,
`Lib/reports/integration-4/singhom-moves.md`); the families here are
`SphereCone`, `AnnularExtension`, `ClosedHemisphere`, `WhitneyPairModel`, `TubularBigon`. The declarations keep their historical dotted names
and their order; the file order is the dependency order.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6.

## Twin

No Mathlib counterpart exists.

## Tags

Morse theory, Whitney trick, handle cancellation
-/

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

def SphereCone.point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : unitInterval × Metric.sphere (0 : E) 1) : Metric.closedBall (0 : E) 1 :=
  ⟨(1 - (p.1 : ℝ)) • (p.2 : E),
    by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr p.1.2.2), mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
    linarith [p.1.2.1]⟩

theorem SphereCone.norm_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : unitInterval × Metric.sphere (0 : E) 1) : ‖(point p : E)‖ = 1 - (p.1 : ℝ) := by
  change ‖(1 - (p.1 : ℝ)) • (p.2 : E)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.1.2.2),
    mem_sphere_zero_iff_norm.mp p.2.property, mul_one]

theorem SphereCone.continuous_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (point (E := E)) := by
  apply Continuous.subtype_mk
  exact
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)

theorem SphereCone.point_fibers {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : unitInterval × Metric.sphere (0 : E) 1} (hpq : point p = point q) :
    p = q ∨ (p.1 = 1 ∧ q.1 = 1) := by
  have hnorm := congrArg (fun x : Metric.closedBall (0 : E) 1 => ‖(x : E)‖) hpq
  rw [norm_point, norm_point] at hnorm
  have ht : p.1 = q.1 := Subtype.ext (by linarith)
  rcases p with ⟨t, x⟩
  rcases q with ⟨s, y⟩
  dsimp only at ht
  subst s
  by_cases htop : t = 1
  · exact Or.inr ⟨htop, htop⟩
  · have htval : (t : ℝ) ≠ 1 := fun heq => htop (Subtype.ext heq)
    have hnonzero : 1 - (t : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm htval)
    have hvec : (1 - (t : ℝ)) • (x : E) = (1 - (t : ℝ)) • (y : E) := congrArg Subtype.val hpq
    have hxy : x = y := Subtype.ext ((smul_right_injective E hnonzero) hvec)
    exact Or.inl (congrArg (fun z => (t, z)) hxy)

theorem SphereCone.surjective_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nonempty (Metric.sphere (0 : E) 1)] : Function.Surjective (point (E := E)) := by
  intro x
  by_cases hx : (x : E) = 0
  · refine ⟨(1, Classical.choice inferInstance), ?_⟩
    apply Subtype.ext
    change (1 - (1 : ℝ)) • _ = (x : E)
    rw [sub_self, zero_smul, hx]
  · have hxnorm : ‖(x : E)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
    let t : unitInterval :=
      ⟨1 - ‖(x : E)‖, sub_nonneg.mpr hxnorm, by linarith [norm_nonneg (x : E)]⟩
    refine ⟨(t, RadialExtension.direction (x : E) hx), ?_⟩
    apply Subtype.ext
    change (1 - (1 - ‖(x : E)‖)) • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
    rw [sub_sub_cancel, smul_inv_smul₀ (norm_ne_zero_iff.mpr hx)]

theorem SphereCone.isQuotientMap_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nonempty (Metric.sphere (0 : E) 1)] [FiniteDimensional ℝ E] :
    Topology.IsQuotientMap (point (E := E)) := by
  let : CompactSpace (Metric.sphere (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  exact .of_surjective_continuous surjective_point continuous_point

theorem SphereCone.homotopy_eq_of_point_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] (f : C(Metric.sphere (0 : E) 1, M)) (c : M)
    (H : f.Homotopy (ContinuousMap.const _ c)) {p q : unitInterval × Metric.sphere (0 : E) 1}
    (hpq : point p = point q) : H p = H q := by
  rcases point_fibers hpq with h | ⟨hp, hq⟩
  · exact congrArg H h
  · have hp' : p = (1, p.2) := Prod.ext hp rfl
    have hq' : q = (1, q.2) := Prod.ext hq rfl
    rw [hp', hq', H.apply_one, H.apply_one]
    rfl

def SphereCone.extensionFun {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) (x : Metric.closedBall (0 : E) 1) : M :=
  H (Function.surjInv surjective_point x)

theorem SphereCone.extensionFun_point {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c))
    (p : unitInterval × Metric.sphere (0 : E) 1) : extensionFun f c H (point p) = H p :=
  homotopy_eq_of_point_eq f c H (Function.surjInv_eq surjective_point (point p))

def SphereCone.extension {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) [FiniteDimensional ℝ E] :
    C(Metric.closedBall (0 : E) 1, M)
    where
  toFun := extensionFun f c H
  continuous_toFun := by
    apply isQuotientMap_point.continuous_iff.mpr
    have heq : extensionFun f c H ∘ point = H := funext (extensionFun_point f c H)
    rw [heq]
    exact H.continuous

theorem SphereCone.extension_boundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) [FiniteDimensional ℝ E]
    (x : Metric.sphere (0 : E) 1) :
    extension f c H ⟨x, Metric.sphere_subset_closedBall x.property⟩ = f x := by
  have heq :
    (⟨(x : E), Metric.sphere_subset_closedBall x.property⟩ : Metric.closedBall (0 : E) 1) =
      point (0, x) := by
    apply Subtype.ext
    change (x : E) = (1 - (0 : ℝ)) • (x : E)
    rw [sub_zero, one_smul]
  change extensionFun f c H _ = f x
  rw [heq, extensionFun_point, H.apply_zero]

theorem SphereCone.extension_zero {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [Nonempty (Metric.sphere (0 : E) 1)] (f : C(Metric.sphere (0 : E) 1, M))
    (c : M) (H : f.Homotopy (ContinuousMap.const _ c)) [FiniteDimensional ℝ E] :
    extension f c H ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = c := by
  let x : Metric.sphere (0 : E) 1 := Classical.choice inferInstance
  have heq :
    (⟨0, Metric.mem_closedBall_self zero_le_one⟩ : Metric.closedBall (0 : E) 1) = point (1, x) := by
    apply Subtype.ext
    change (0 : E) = (1 - (1 : ℝ)) • (x : E)
    rw [sub_self, zero_smul]
  change extensionFun f c H _ = c
  rw [heq, extensionFun_point, H.apply_one]
  rfl

def AnnularExtension.unitClamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (x : E) : E :=
  (Max.max a ‖x‖)⁻¹ • x

theorem AnnularExtension.max_radius_pos {E : Type*} [NormedAddCommGroup E] {a : ℝ}
    (ha : 0 < a) (x : E) : 0 < Max.max a ‖x‖ :=
  ha.trans_le (le_max_left _ _)

theorem AnnularExtension.continuous_unitClamp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) : Continuous (unitClamp (E := E) a) :=
  ((continuous_const.max continuous_norm).inv₀ (fun x => (max_radius_pos ha x).ne')).smul
    continuous_id

theorem AnnularExtension.norm_unitClamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (x : E) : ‖unitClamp a x‖ = ‖x‖ / Max.max a ‖x‖ := by
  rw [unitClamp, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (max_radius_pos ha x)),
    div_eq_mul_inv, mul_comm]

theorem AnnularExtension.norm_unitClamp_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) (x : E) : ‖unitClamp a x‖ ≤ 1 := by
  rw [norm_unitClamp ha]
  exact (div_le_one (max_radius_pos ha x)).mpr (le_max_right _ _)

def AnnularExtension.innerDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ}
    (ha : 0 < a) : C(E, Metric.closedBall (0 : E) 1)
    where
  toFun x := ⟨unitClamp a x, mem_closedBall_zero_iff.mpr (norm_unitClamp_le ha x)⟩
  continuous_toFun := (continuous_unitClamp ha).subtype_mk _

theorem AnnularExtension.unitClamp_of_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} {x : E} (hx : ‖x‖ ≤ a) : unitClamp a x = a⁻¹ • x := by
  rw [unitClamp, max_eq_left hx]

def AnnularExtension.clamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (x : E) : E :=
  a • unitClamp a x

theorem AnnularExtension.continuous_clamp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) : Continuous (clamp (E := E) a) :=
  continuous_const.smul (continuous_unitClamp ha)

theorem AnnularExtension.clamp_of_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) {x : E} (hx : ‖x‖ ≤ a) : clamp a x = x := by
  rw [clamp, unitClamp_of_norm_le hx, smul_inv_smul₀ ha.ne']

theorem AnnularExtension.norm_clamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (x : E) : ‖clamp a x‖ = Min.min a ‖x‖ := by
  by_cases hx : ‖x‖ ≤ a
  · rw [clamp_of_norm_le ha hx, min_eq_right hx]
  · have hx' : a ≤ ‖x‖ := le_of_not_ge hx
    have hnorm : ‖x‖ ≠ 0 := (ha.trans_le hx').ne'
    rw [clamp, norm_smul, Real.norm_eq_abs, abs_of_pos ha, norm_unitClamp ha, max_eq_right hx',
      div_self hnorm, mul_one, min_eq_left hx']

theorem AnnularExtension.clamp_mem_annulus {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} (hb : 0 < b) (hab : a ≤ b) {x : E} (hx : a ≤ ‖x‖) :
    a ≤ ‖clamp b x‖ ∧ ‖clamp b x‖ ≤ b := by
  rw [norm_clamp hb]
  exact ⟨le_min hab hx, min_le_left _ _⟩

def AnnularExtension.exteriorFactor {E : Type*} [NormedAddCommGroup E] (a : ℝ) (x : E) :
    ℝ :=
  Min.min 1 (Max.max 0 (2 - ‖x‖ / a))

theorem AnnularExtension.exteriorFactor_nonneg {E : Type*} [NormedAddCommGroup E] (a : ℝ)
    (x : E) : 0 ≤ exteriorFactor a x :=
  le_min zero_le_one (le_max_left _ _)

theorem AnnularExtension.exteriorFactor_le_one {E : Type*} [NormedAddCommGroup E] (a : ℝ)
    (x : E) : exteriorFactor a x ≤ 1 :=
  min_le_left _ _

def AnnularExtension.exteriorVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (x : E) : E :=
  exteriorFactor a x • unitClamp a x

theorem AnnularExtension.continuous_exteriorVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) : Continuous (exteriorVector (E := E) a) := by
  have hf : Continuous (exteriorFactor (E := E) a) := by unfold exteriorFactor; fun_prop
  exact hf.smul (continuous_unitClamp ha)

theorem AnnularExtension.norm_exteriorVector_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) (x : E) : ‖exteriorVector a x‖ ≤ 1 := by
  rw [exteriorVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (exteriorFactor_nonneg a x)]
  calc
    _ ≤ 1 * 1 :=
      mul_le_mul (exteriorFactor_le_one a x) (norm_unitClamp_le ha x) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

def AnnularExtension.exteriorDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) : C(E, Metric.closedBall (0 : E) 1)
    where
  toFun x := ⟨exteriorVector a x, mem_closedBall_zero_iff.mpr (norm_exteriorVector_le ha x)⟩
  continuous_toFun := (continuous_exteriorVector ha).subtype_mk _

theorem AnnularExtension.exteriorVector_on_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) {x : E} (hx : ‖x‖ = a) :
    exteriorVector a x = unitClamp a x := by
  have hf : exteriorFactor a x = 1 := by
    unfold exteriorFactor
    rw [hx, div_self ha.ne']
    norm_num
  rw [exteriorVector, hf, one_smul]

theorem AnnularExtension.exteriorVector_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) {x : E} (hx : 2 * a ≤ ‖x‖) : exteriorVector a x = 0 := by
  have hdiv : 2 ≤ ‖x‖ / a := (le_div_iff₀ ha).mpr hx
  have hf : exteriorFactor a x = 0 := by
    unfold exteriorFactor
    rw [max_eq_left (by linarith : 2 - ‖x‖ / a ≤ 0), min_eq_right zero_le_one]
  rw [exteriorVector, hf, zero_smul]

theorem AnnularExtension.disk_extension_on_radius {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] {a : ℝ} (ha : 0 < a) {g : E → M}
    (F : C(Metric.closedBall (0 : E) 1, M))
    (hF :
      ∀ v : Metric.sphere (0 : E) 1,
        F ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    {x : E} (hx : ‖x‖ = a) : F (innerDisk ha x) = g x := by
  let v : Metric.sphere (0 : E) 1 :=
    ⟨unitClamp a x, by
      rw [mem_sphere_zero_iff_norm, norm_unitClamp ha, hx, max_self, div_self ha.ne']⟩
  have heq : innerDisk ha x = ⟨(v : E), Metric.sphere_subset_closedBall v.property⟩ := rfl
  rw [heq, hF]
  change g (clamp a x) = g x
  rw [clamp_of_norm_le ha hx.le]

theorem AnnularExtension.exterior_extension_on_radius {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] {a : ℝ} (ha : 0 < a) {g : E → M}
    (F : C(Metric.closedBall (0 : E) 1, M))
    (hF :
      ∀ v : Metric.sphere (0 : E) 1,
        F ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    {x : E} (hx : ‖x‖ = a) : F (exteriorDisk ha x) = g x := by
  have heq : exteriorDisk ha x = innerDisk ha x := Subtype.ext (exteriorVector_on_sphere ha hx)
  rw [heq]
  exact disk_extension_on_radius ha F hF hx

theorem AnnularExtension.exists_continuous_annular_extension {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {g : E → M} (hg : ContinuousOn g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b})
    (F₀ F₁ : C(Metric.closedBall (0 : E) 1, M))
    (hF₀ :
      ∀ v : Metric.sphere (0 : E) 1,
        F₀ ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (a • (v : E)))
    (hF₁ :
      ∀ v : Metric.sphere (0 : E) 1,
        F₁ ⟨v, Metric.sphere_subset_closedBall v.property⟩ = g (b • (v : E))) :
    ∃ G : C(E, M),
      Set.EqOn G g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ∧
        ∀ x, 2 * b ≤ ‖x‖ → G x = F₁ ⟨0, Metric.mem_closedBall_self zero_le_one⟩ := by
  classical
  have hb : 0 < b := ha.trans hab
  let inner : C(E, M) := F₀.comp (innerDisk ha)
  let outer : C(E, M) := F₁.comp (exteriorDisk hb)
  let middle : E → M := g ∘ clamp b
  have houtside : closure (Metric.closedBall (0 : E) a)ᶜ ⊆ {x : E | a ≤ ‖x‖} := by
    apply closure_minimal
    · intro x hx
      have hn : ¬‖x‖ ≤ a := by simpa only [Set.mem_compl_iff, mem_closedBall_zero_iff] using hx
      exact le_of_lt (lt_of_not_ge hn)
    · exact isClosed_le continuous_const continuous_norm
  have hmiddle : ContinuousOn middle (closure (Metric.closedBall (0 : E) a)ᶜ) :=
    hg.comp (continuous_clamp hb).continuousOn
      (fun _ hx => clamp_mem_annulus hb hab.le (houtside hx))
  have hjoin₀ : ∀ x ∈ frontier (Metric.closedBall (0 : E) a), inner x = middle x := by
    intro x hx
    rw [frontier_closedBall _ ha.ne'] at hx
    have hnorm : ‖x‖ = a := mem_sphere_zero_iff_norm.mp hx
    change F₀ (innerDisk ha x) = g (clamp b x)
    rw [disk_extension_on_radius ha F₀ hF₀ hnorm, clamp_of_norm_le hb (hnorm.le.trans hab.le)]
  let G₀ : E → M := (Metric.closedBall (0 : E) a).piecewise inner middle
  have hG₀ : Continuous G₀ := continuous_piecewise hjoin₀ inner.continuous.continuousOn hmiddle
  have hG₀eq : Set.EqOn G₀ g {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
    intro x hx
    by_cases hxa : x ∈ Metric.closedBall (0 : E) a
    · have hnorm : ‖x‖ = a := le_antisymm (mem_closedBall_zero_iff.mp hxa) hx.1
      change ((Metric.closedBall (0 : E) a).piecewise inner middle) x = g x
      rw [Set.piecewise_eq_of_mem _ _ _ hxa]
      exact disk_extension_on_radius ha F₀ hF₀ hnorm
    · change ((Metric.closedBall (0 : E) a).piecewise inner middle) x = g x
      rw [Set.piecewise_eq_of_notMem _ _ _ hxa]
      change g (clamp b x) = g x
      rw [clamp_of_norm_le hb hx.2]
  have hjoin₁ : ∀ x ∈ frontier (Metric.closedBall (0 : E) b), G₀ x = outer x := by
    intro x hx
    rw [frontier_closedBall _ hb.ne'] at hx
    have hnorm : ‖x‖ = b := mem_sphere_zero_iff_norm.mp hx
    rw [hG₀eq (show a ≤ ‖x‖ ∧ ‖x‖ ≤ b by rw [hnorm]; exact ⟨hab.le, le_rfl⟩)]
    exact (exterior_extension_on_radius hb F₁ hF₁ hnorm).symm
  let G : C(E, M) :=
    ⟨(Metric.closedBall (0 : E) b).piecewise G₀ outer, hG₀.piecewise hjoin₁ outer.continuous⟩
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    change ((Metric.closedBall (0 : E) b).piecewise G₀ outer) x = g x
    rw [Set.piecewise_eq_of_mem _ _ _ (mem_closedBall_zero_iff.mpr hx.2)]
    exact hG₀eq hx
  · intro x hx
    have hxb : x ∉ Metric.closedBall (0 : E) b := by
      rw [mem_closedBall_zero_iff]
      linarith
    change ((Metric.closedBall (0 : E) b).piecewise G₀ outer) x = _
    rw [Set.piecewise_eq_of_notMem _ _ _ hxb]
    change F₁ (exteriorDisk hb x) = F₁ ⟨0, Metric.mem_closedBall_self zero_le_one⟩
    apply congrArg F₁
    exact Subtype.ext (exteriorVector_eq_zero hb hx)

theorem AnnularExtension.dist_direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) : Dist.dist x (RadialExtension.direction x hx : E) = |‖x‖ - 1| := by
  let v := RadialExtension.direction x hx
  have hvec : ‖x‖ • (v : E) = x := smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) x
  have hn : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  change Dist.dist x (v : E) = _
  calc
    _ = ‖(‖x‖ - 1) • (v : E)‖ := by rw [dist_eq_norm, sub_smul, one_smul, hvec]
    _ = |‖x‖ - 1| := by rw [norm_smul, Real.norm_eq_abs, hn, mul_one]

theorem AnnularExtension.exists_closed_annulus_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {W : Set E} (hW : IsOpen W)
    (hSW : Metric.sphere (0 : E) 1 ⊆ W) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧ {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ⊆ W := by
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_sphere (0 : E) 1).exists_cthickening_subset_open hW hSW
  let ε := Min.min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεsmall : ε ≤ 1 / 2 := min_le_right _ _
  have hεδ : ε ≤ δ := (min_le_left _ _).trans (by linarith)
  refine ⟨1 - ε, 1 + ε, by linarith, by linarith, by linarith, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro heq
    have hxlo := hx.1
    rw [heq, norm_zero] at hxlo
    linarith
  have hdist : Dist.dist x (RadialExtension.direction x hx0 : E) ≤ δ := by
    rw [dist_direction]
    apply le_trans (abs_le.mpr ?_) hεδ
    constructor <;> linarith [hx.1, hx.2]
  exact
    hδW
      (Metric.mem_cthickening_of_dist_le x (RadialExtension.direction x hx0) δ
        (Metric.sphere (0 : E) 1) (RadialExtension.direction x hx0).property hdist)

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

theorem ClosedHemisphere.unit_norm {E : Type*} [NormedAddCommGroup E]
    (x : UnitSphere E) : ‖(x : E)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

abbrev Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

noncomputable def normalizedSphereMap {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (g : C(X, E)) (hg : ∀ x, g x ≠ 0) :
    C(X, UnitSphere E) := by
  let gN : X → E := fun x ↦ NormedSpace.normalize (g x)
  have hm : ∀ x, gN x ∈ UnitSphere E := by
    intro x
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize (hg x)
  have hc : Continuous gN :=
    (g.continuous.norm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr (hg x))).smul g.continuous
  exact ⟨fun x ↦ ⟨gN x, hm x⟩, hc.subtype_mk hm⟩

theorem nearby_unit_ne_zero {E : Type*} [NormedAddCommGroup E] (a : UnitSphere E) (b : E)
    (h : Dist.dist b (a : E) < 1) : b ≠ 0 := by
  intro hb
  rw [hb, dist_zero_left, ClosedHemisphere.unit_norm] at h
  exact (lt_irrefl 1) h

theorem nearby_segment_dist_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : UnitSphere E) (b : E) (h : Dist.dist b (a : E) < 1) (t : (unitInterval)) :
    Dist.dist ((a : E) + (t : ℝ) • (b - (a : E))) (a : E) < 1 := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  calc
    (t : ℝ) * ‖b - (a : E)‖ ≤ ‖b - (a : E)‖ := mul_le_of_le_one_left (norm_nonneg _) t.2.2
    _ < 1 := by simpa only [dist_eq_norm] using h

theorem nearby_segment_ne_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : UnitSphere E) (b : E) (h : Dist.dist b (a : E) < 1) (t : (unitInterval)) :
    (a : E) + (t : ℝ) • (b - (a : E)) ≠ 0 :=
  nearby_unit_ne_zero a _ (nearby_segment_dist_lt a b h t)

noncomputable def nearbyNormalizationHomotopy {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : C(X, UnitSphere E)) (g : C(X, E))
    (h : ∀ x, Dist.dist (g x) (f x : E) < 1) :
    f.Homotopy (normalizedSphereMap g (fun x ↦ nearby_unit_ne_zero (f x) (g x) (h x)))
    where
  toFun
    p :=
    ⟨NormedSpace.normalize ((f p.2 : E) + (p.1 : ℝ) • (g p.2 - (f p.2 : E))), by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        NormedSpace.norm_normalize (nearby_segment_ne_zero (f p.2) (g p.2) (h p.2) p.1)⟩
  continuous_toFun := by
    have hf : Continuous (fun p : (unitInterval) × X ↦ (f p.2 : E)) :=
      continuous_subtype_val.comp (f.continuous.comp continuous_snd)
    have hg := g.continuous.comp (continuous_snd : Continuous (Prod.snd : (unitInterval) × X → X))
    have ht : Continuous (fun p : (unitInterval) × X ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hb := hf.add (ht.smul (hg.sub hf))
    exact
      ((hb.norm.inv₀
                (fun p ↦
                  norm_ne_zero_iff.mpr (nearby_segment_ne_zero (f p.2) (g p.2) (h p.2) p.1))).smul
            hb).subtype_mk
        _
  map_zero_left
    x := by
    apply Subtype.ext
    change NormedSpace.normalize ((f x : E) + (0 : ℝ) • (g x - (f x : E))) = (f x : E)
    simpa only [zero_smul, add_zero] using
      NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (f x))
  map_one_left
    x := by
    apply Subtype.ext
    change
      NormedSpace.normalize ((f x : E) + (1 : ℝ) • (g x - (f x : E))) =
        NormedSpace.normalize (g x)
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]

theorem contMDiff_normalize {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M] {g : M → E}
    (hg : ContMDiff I 𝓘(ℝ, E) ∞ g) (hn : ∀ x, g x ≠ 0) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun x ↦ NormedSpace.normalize (g x)) := by
  intro x
  have hN : ContDiffAt ℝ ∞ (NormedSpace.normalize : E → E) (g x) :=
    ((contDiffAt_norm ℝ (hn x)).inv (norm_ne_zero_iff.mpr (hn x))).smul contDiffAt_id
  exact hN.comp_contMDiffAt (f := g) (x := x) (hg x)

theorem exists_smoothSphereRepresentative {B H M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M]
    [ChartedSpace H M] [FiniteDimensional ℝ B] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] (n : ℕ) (f : C(M, Sphere n)) :
    ∃ g : C(M, Sphere n), ContMDiff I (𝓡 n) ∞ g ∧ f.Homotopic g := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hf : Continuous (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) :=
    continuous_subtype_val.comp f.continuous
  obtain ⟨g, hg, _⟩ :=
    hf.exists_contMDiff_approx I (⊤ : ℕ∞) (ε := fun _ ↦ 1) continuous_const (fun _ ↦ zero_lt_one)
  let gC : C(M, EuclideanSpace ℝ (Fin (n + 1))) := ⟨g, g.contMDiff.continuous⟩
  have hn : ∀ x, gC x ≠ 0 := fun x ↦ nearby_unit_ne_zero (f x) (gC x) (hg x)
  refine ⟨normalizedSphereMap gC hn, ?_, ⟨nearbyNormalizationHomotopy f gC hg⟩⟩
  exact
    (contMDiff_normalize g.contMDiff hn).codRestrict_sphere (n := n)
      (fun x ↦ (normalizedSphereMap gC hn x).2)

noncomputable def chartContractionHomotopy {X Y E : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (f : C(X, Y))
    (c : OpenPartialHomeomorph Y E) (ht : c.target = Set.univ) (hf : ∀ x, f x ∈ c.source) :
    f.Homotopy (ContinuousMap.const _ (c.symm 0))
    where
  toFun p := c.symm ((1 - (p.1 : ℝ)) • c (f p.2))
  continuous_toFun := by
    have hc : Continuous (fun x ↦ c (f x)) := c.continuousOn.comp_continuous f.continuous hf
    have hci : Continuous c.symm := by
      apply continuousOn_univ.mp
      rw [← ht]
      exact c.symm.continuousOn
    exact
      hci.comp
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (hc.comp continuous_snd))
  map_zero_left
    x := by
    change c.symm ((1 - (0 : ℝ)) • c (f x)) = f x
    rw [sub_zero, one_smul]
    exact c.left_inv (hf x)
  map_one_left
    x := by
    change c.symm ((1 - (1 : ℝ)) • c (f x)) = c.symm 0
    rw [sub_self, zero_smul]

theorem sphereMap_nullhomotopic_of_omitted_point {X : Type*} [TopologicalSpace X] (n : ℕ)
    (f : C(X, Sphere n)) (p : Sphere n) (hp : ∀ x, f x ≠ p) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let c := stereographic' n p
  have hf : ∀ x, f x ∈ c.source := by
    intro x
    simpa only [c, stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using hp x
  exact ⟨c.symm 0, ⟨chartContractionHomotopy f c (stereographic'_target (n := n) p) hf⟩⟩

theorem sphereMap_nullhomotopic_of_dim_lt {B H M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    [T2Space M] (n : ℕ) (f : C(M, Sphere n)) (hd : Module.finrank ℝ B < n) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  classical
  obtain ⟨g, hg, hfg⟩ := exists_smoothSphereRepresentative (I := I) n f
  let : Nonempty (Sphere n) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  have hn : ¬Function.Surjective g :=
    not_surjective_contMDiff_of_dim_lt hg (by simpa only [finrank_euclideanSpace_fin] using hd)
  obtain ⟨p, hp⟩ : ∃ p, ∀ x, g x ≠ p := by
    simpa only [Function.Surjective, Classical.not_forall, not_exists] using hn
  obtain ⟨c, hgc⟩ := sphereMap_nullhomotopic_of_omitted_point n g p hp
  exact ⟨c, hfg.trans hgc⟩

theorem sphere_sphere_nullhomotopic {m n : ℕ} (hmn : m < n) (f : C(Sphere m, Sphere n)) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) :=
  sphereMap_nullhomotopic_of_dim_lt (I := 𝓡 m) n f
    (by simpa only [finrank_euclideanSpace_fin] using hmn)

theorem exists_circle_neighborhood_extension_of_circle_nullhomotopies {M : Type*}
    [TopologicalSpace M]
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (ContinuousMap.const _ c))
    {g : Hemisphere.Ambient 2 → M} {W : Set (Hemisphere.Ambient 2)} (hW : IsOpen W)
    (hg : ContinuousOn g W) (hSW : Metric.sphere (0 : Hemisphere.Ambient 2) 1 ⊆ W) :
    ∃ G : C(Hemisphere.Ambient 2, M),
      ∃ c : M,
        ∃ K : Set (Hemisphere.Ambient 2),
          IsCompact K ∧
            (∀ x ∉ K, G x = c) ∧
              ∃ U : Set (Hemisphere.Ambient 2),
                IsOpen U ∧
                  Metric.sphere (0 : Hemisphere.Ambient 2) 1 ⊆ U ∧ U ⊆ W ∧ Set.EqOn G g U := by
  obtain ⟨a, b, ha, ha1, h1b, hAW⟩ := AnnularExtension.exists_closed_annulus_subset hW hSW
  have hab : a < b := ha1.trans h1b
  have hb : 0 < b := ha.trans hab
  let A : Set (Hemisphere.Ambient 2) := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  have hgA : ContinuousOn g A := hg.mono hAW
  have hscale (r : ℝ) (hr : r ∈ Set.Icc a b) (v : Hemisphere.Sphere 1) :
    r • (v : Hemisphere.Ambient 2) ∈ A := by
    have hr0 : 0 < r := ha.trans_le hr.1
    have hnorm : ‖r • (v : Hemisphere.Ambient 2)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, mem_sphere_zero_iff_norm.mp v.property,
        mul_one]
    change a ≤ ‖r • (v : Hemisphere.Ambient 2)‖ ∧ ‖r • (v : Hemisphere.Ambient 2)‖ ≤ b
    rw [hnorm]
    exact hr
  have hcontinuous (r : ℝ) :
    Continuous (fun v : Hemisphere.Sphere 1 => r • (v : Hemisphere.Ambient 2)) := by fun_prop
  let f₀ : C(Hemisphere.Sphere 1, M) :=
    ⟨fun v => g (a • (v : Hemisphere.Ambient 2)),
      hgA.comp_continuous (hcontinuous a) (hscale a ⟨le_rfl, hab.le⟩)⟩
  let f₁ : C(Hemisphere.Sphere 1, M) :=
    ⟨fun v => g (b • (v : Hemisphere.Ambient 2)),
      hgA.comp_continuous (hcontinuous b) (hscale b ⟨hab.le, le_rfl⟩)⟩
  obtain ⟨c₀, ⟨H₀⟩⟩ := hnull f₀
  obtain ⟨c₁, ⟨H₁⟩⟩ := hnull f₁
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let : Nonempty (Metric.sphere (0 : Hemisphere.Ambient 2) 1) := ⟨⟨v, hv⟩⟩
  let F₀ := SphereCone.extension f₀ c₀ H₀
  let F₁ := SphereCone.extension f₁ c₁ H₁
  obtain ⟨G, hGeq, hGconst⟩ :=
    AnnularExtension.exists_continuous_annular_extension ha hab hgA F₀ F₁
      (SphereCone.extension_boundary f₀ c₀ H₀) (SphereCone.extension_boundary f₁ c₁ H₁)
  let U : Set (Hemisphere.Ambient 2) := {x | a < ‖x‖ ∧ ‖x‖ < b}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hUA : U ⊆ A := fun _ hx => ⟨hx.1.le, hx.2.le⟩
  refine
    ⟨G, c₁, Metric.closedBall 0 (2 * b), ProperSpace.isCompact_closedBall _ _, ?_, U, hU, ?_,
      hUA.trans hAW, hGeq.mono hUA⟩
  · intro x hx
    have hn : 2 * b < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hx
    rw [hGconst x hn.le]
    exact SphereCone.extension_zero f₁ c₁ H₁
  · intro x hx
    have hn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    change a < ‖x‖ ∧ ‖x‖ < b
    rw [hn]
    exact ⟨ha1, h1b⟩

theorem WhitneyPairModel.convex_bigon {h : ℝ} (hh : 0 ≤ h) : Convex ℝ (bigon h) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x.2 + b * y.2 ∧ h * (a * x.1 + b * y.1) ^ 2 + (a * x.2 + b * y.2) ≤ h
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_⟩
  have hsq : (a * x.1 + b * y.1) ^ 2 = a * x.1 ^ 2 + b * y.1 ^ 2 - a * b * (x.1 - y.1) ^ 2 := by
    calc
      _ = (a + b) * (a * x.1 ^ 2 + b * y.1 ^ 2) - a * b * (x.1 - y.1) ^ 2 := by ring
      _ = _ := by rw [hab, one_mul]
  calc
    _ = a * (h * x.1 ^ 2 + x.2) + b * (h * y.1 ^ 2 + y.2) - h * a * b * (x.1 - y.1) ^ 2 := by
      rw [hsq]; ring
    _ ≤ a * (h * x.1 ^ 2 + x.2) + b * (h * y.1 ^ 2 + y.2) :=
      (sub_le_self _ (mul_nonneg (mul_nonneg (mul_nonneg hh ha) hb) (sq_nonneg _)))
    _ ≤ a * h + b * h :=
      (add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb))
    _ = h := by rw [← add_mul, hab, one_mul]

theorem WhitneyPairModel.bigon_center_mem_interior {h : ℝ} (hh : 0 < h) :
    (0, h / 2) ∈ interior (bigon h) := by
  apply (mem_interior_bigon_iff h _).mpr
  change 0 < h / 2 ∧ h / 2 < h * (1 - 0 ^ 2)
  norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one]
  constructor <;> linarith

theorem WhitneyPairModel.interior_bigon_nonempty {h : ℝ} (hh : 0 < h) :
    (interior (bigon h)).Nonempty :=
  ⟨(0, h / 2), bigon_center_mem_interior hh⟩

theorem WhitneyPairModel.exists_bigon_disk_homeomorph {h : ℝ} (hh : 0 < h) :
    ∃ e : (ℝ × ℝ) ≃ₜ Hemisphere.Ambient 2,
      e '' bigon h = Metric.closedBall 0 1 ∧
        e '' interior (bigon h) = Metric.ball 0 1 ∧ e '' frontier (bigon h) = Metric.sphere 0 1 :=
  by
  let L : (ℝ × ℝ) ≃L[ℝ] Hemisphere.Ambient 2 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Hemisphere.Ambient, Module.finrank_prod])
  let K : Set (Hemisphere.Ambient 2) := L '' bigon h
  have hK : IsCompact K := (isCompact_bigon hh).image L.continuous
  have hc : Convex ℝ K := (convex_bigon hh.le).linear_image L.toLinearEquiv.toLinearMap
  have hLint : L '' interior (bigon h) = interior K := L.toHomeomorph.image_interior (bigon h)
  have hLfront : L '' frontier (bigon h) = frontier K := L.toHomeomorph.image_frontier (bigon h)
  have hne : (interior K).Nonempty := by
    rw [← hLint]
    exact (interior_bigon_nonempty hh).image L
  obtain ⟨e, heint, heclosed, hefront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hK.isBounded
  refine ⟨L.toHomeomorph.trans e, ?_, ?_, ?_⟩
  · calc
      _ = e '' (L '' bigon h) := (Set.image_image e L (bigon h)).symm
      _ = Metric.closedBall 0 1 := by
        change e '' K = _
        rwa [hK.isClosed.closure_eq] at heclosed
  · calc
      _ = e '' (L '' interior (bigon h)) := (Set.image_image e L (interior (bigon h))).symm
      _ = Metric.ball 0 1 := by rw [hLint]; exact heint
  · calc
      _ = e '' (L '' frontier (bigon h)) := (Set.image_image e L (frontier (bigon h))).symm
      _ = Metric.sphere 0 1 := by rw [hLfront]; exact hefront

theorem exists_bigon_neighborhood_extension_of_circle_nullhomotopies {M : Type*}
    [TopologicalSpace M]
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (ContinuousMap.const _ c)) {h : ℝ}
    (hh : 0 < h) {f : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hf : ContinuousOn f W)
    (hfrontW : frontier (WhitneyPairModel.bigon h) ⊆ W) :
    ∃ F : C(ℝ × ℝ, M),
      ∃ c : M,
        ∃ K : Set (ℝ × ℝ),
          IsCompact K ∧
            (∀ x ∉ K, F x = c) ∧
              ∃ U : Set (ℝ × ℝ),
                IsOpen U ∧ frontier (WhitneyPairModel.bigon h) ⊆ U ∧ U ⊆ W ∧ Set.EqOn F f U := by
  obtain ⟨φ, _, _, hφfront⟩ := WhitneyPairModel.exists_bigon_disk_homeomorph hh
  let W' : Set (Hemisphere.Ambient 2) := φ.symm ⁻¹' W
  let g : Hemisphere.Ambient 2 → M := f ∘ φ.symm
  have hW' : IsOpen W' := hW.preimage φ.symm.continuous
  have hg : ContinuousOn g W' := hf.comp φ.symm.continuous.continuousOn (fun _ hx => hx)
  have hSW : Metric.sphere (0 : Hemisphere.Ambient 2) 1 ⊆ W' := by
    intro y hy
    have hy' : y ∈ φ '' frontier (WhitneyPairModel.bigon h) := by rw [hφfront]; exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    change φ.symm (φ x) ∈ W
    rw [φ.symm_apply_apply]
    exact hfrontW hx
  obtain ⟨G, c, K', hK', hconst, U', hU', hSU', hU'W', heq⟩ :=
    exists_circle_neighborhood_extension_of_circle_nullhomotopies hnull hW' hg hSW
  let F : C(ℝ × ℝ, M) := G.comp ⟨φ, φ.continuous⟩
  let K := φ.symm '' K'
  let U := φ ⁻¹' U'
  refine ⟨F, c, K, hK'.image φ.symm.continuous, ?_, U, hU'.preimage φ.continuous, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : φ x ∉ K' := fun hmem => hx ⟨φ x, hmem, φ.symm_apply_apply x⟩
    exact hconst (φ x) hx'
  · intro x hx
    apply hSU'
    rw [← hφfront]
    exact Set.mem_image_of_mem φ hx
  · intro x hx
    have hx' : φ.symm (φ x) ∈ W := hU'W' hx
    rwa [φ.symm_apply_apply] at hx'
  · intro x hx
    change G (φ x) = f x
    rw [heq hx]
    change f (φ.symm (φ x)) = f x
    rw [φ.symm_apply_apply]

theorem exists_smooth_bigon_neighborhood_extension_of_circle_nullhomotopies {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (ContinuousMap.const _ c)) {h : ℝ}
    (hh : 0 < h) {f : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f W)
    (hfrontW : frontier (WhitneyPairModel.bigon h) ⊆ W) :
    ∃ F : C(ℝ × ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧ frontier (WhitneyPairModel.bigon h) ⊆ U ∧ U ⊆ W ∧ Set.EqOn F f U := by
  obtain ⟨G, c, K, hK, hconst, V, hV, hfrontV, hVW, hGeq⟩ :=
    exists_bigon_neighborhood_extension_of_circle_nullhomotopies hnull hh hW hf.continuousOn
      hfrontW
  have hfrontCompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, _, hC, hfrontC, hCV⟩ := exists_compact_closed_between hfrontCompact hV hfrontV
  have hGV : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G V := (hf.mono hVW).congr (fun _ hx => hGeq hx)
  have hGK : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G Kᶜ :=
    (contMDiff_const (c := c)).contMDiffOn.congr (fun x hx => hconst x hx)
  obtain ⟨F, hF, hrel⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact G hK hC hV hCV hGV hGK
  refine ⟨F, hF, interior C, isOpen_interior, hfrontC, interior_subset.trans (hCV.trans hVW), ?_⟩
  intro x hx
  exact (hrel.fst_eq_snd (interior_subset hx)).symm.trans (hGeq (hCV (interior_subset hx)))

structure TubularBigon {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) (k l : (ℝ × ℝ) → M)
    (h : ℝ) (n : ℕ := 4) where
  height_pos : 0 < h
  map : C(ℝ × ℝ, M)
  smooth : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map
  closed_embedding : Topology.IsClosedEmbedding (fun p : WhitneyPairModel.bigon h => map p)
  derivative_injective :
    ∀ p ∈ WhitneyPairModel.bigon h, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  interior_avoids : ∀ p ∈ interior (WhitneyPairModel.bigon h), map p ∉ S ∪ T
  lower : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, 0) = a t
  upper : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t
  lower_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, map =ᶠ[𝓝 (2 * t - 1, 0)] k ∘ WhitneyPairModel.lowerStripCoordinates h
  upper_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      map =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
        l ∘ WhitneyPairModel.upperStripCoordinates h
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
      ((ℝ × ℝ) × EuclideanSpace ℝ (Fin n)) M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = map p

end
