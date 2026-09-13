/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Handle

/-!
# The handle retraction onto its core

`Handle.Space` and the retraction of a handle onto its core cell with the
unit-sphere equivalences — the topological half of "attaching a handle is attaching a cell"
(Hatcher, Prop 0.16 / §2.3's matrix rows).

## Main definitions and results

* `Handle.Space` : the handle space.
* `UnitSphereEquiv.*` : the unit-sphere equivalences of the core retraction.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Prop 0.16, §2.3

## Tags

handle, core retraction, unit sphere
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### The handle retraction -/

/-- The handle space `Dⁿ × Dᵖ` as a product of unit disks. -/
abbrev Handle.Space {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P] :=
  MorseHandle.UnitDisk N × MorseHandle.UnitDisk P

/-- The normalization `max(1/2, ‖u‖, ‖v‖)`-type denominator of the retraction. -/
def Handle.denominator {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    (z : Space (N := N) (P := P)) : ℝ :=
  Max.max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)

/-- The denominator is at least `1/2`. -/
theorem Handle.half_le_denominator {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Space (N := N) (P := P)) : (1 / 2 : ℝ) ≤ denominator z := by
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
  have hd := le_max_right ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
  change (1 / 2 : ℝ) ≤ Max.max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
  linarith

/-- The denominator is positive. -/
theorem Handle.denominator_pos {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    (z : Space (N := N) (P := P)) : 0 < denominator z :=
  lt_of_lt_of_le (by norm_num) (half_le_denominator z)

/-- The denominator is at most one. -/
theorem Handle.denominator_le_one {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Space (N := N) (P := P)) : denominator z ≤ 1 := by
  apply max_le (mem_closedBall_zero_iff.mp z.1.property)
  linarith [norm_nonneg (z.2 : P)]

/-- The multiplier shrinking the positive component. -/
def Handle.positiveMultiplier {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    (z : Space (N := N) (P := P)) : ℝ :=
  (2 * denominator z + ‖(z.2 : P)‖ - 2) / (‖(z.2 : P)‖ * denominator z)

/-- The positive multiplier is nonnegative. -/
theorem Handle.positiveMultiplier_nonneg {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Space (N := N) (P := P)) : 0 ≤ positiveMultiplier z := by
  apply div_nonneg
  · have hd := le_max_right ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
    change 0 ≤ 2 * Max.max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2) + ‖(z.2 : P)‖ - 2
    linarith
  · exact mul_nonneg (norm_nonneg _) (denominator_pos z).le

/-- The positive multiplier is at most one. -/
theorem Handle.positiveMultiplier_le_one {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Space (N := N) (P := P)) : positiveMultiplier z ≤ 1 := by
  by_cases hv : (z.2 : P) = 0
  · simp [positiveMultiplier, hv]
  · apply (div_le_one (mul_pos (norm_pos_iff.mpr hv) (denominator_pos z))).mpr
    have hb : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
    have hprod :=
      mul_nonneg (sub_nonneg.mpr (denominator_le_one z)) (show 0 ≤ 2 - ‖(z.2 : P)‖ by linarith)
    nlinarith

/-- The negative component of the handle retraction. -/
def Handle.negative {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    [NormedSpace ℝ N] (z : Space (N := N) (P := P)) : N :=
  (denominator z)⁻¹ • (z.1 : N)

/-- The positive component of the handle retraction. -/
def Handle.positive {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    [NormedSpace ℝ P] (z : Space (N := N) (P := P)) : P :=
  positiveMultiplier z • (z.2 : P)

/-- The retracted negative component stays in the disk. -/
theorem Handle.norm_negative_le_one {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [NormedSpace ℝ N] (z : Space (N := N) (P := P)) : ‖negative z‖ ≤ 1 := by
  rw [negative, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (denominator_pos z).le)]
  have h :=
    mul_le_mul_of_nonneg_left (le_max_left ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2))
      (inv_nonneg.mpr (denominator_pos z).le)
  exact h.trans_eq (inv_mul_cancel₀ (denominator_pos z).ne')

/-- The retracted positive component stays in the disk. -/
theorem Handle.norm_positive_le {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    [NormedSpace ℝ P] (z : Space (N := N) (P := P)) : ‖positive z‖ ≤ ‖(z.2 : P)‖ := by
  rw [positive, norm_smul, Real.norm_of_nonneg (positiveMultiplier_nonneg z)]
  exact
    (mul_le_mul_of_nonneg_right (positiveMultiplier_le_one z) (norm_nonneg _)).trans_eq
      (one_mul _)

/-- A zero positive component retracts to zero. -/
theorem Handle.positive_eq_zero_of_snd_eq_zero {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Space (N := N) (P := P)) (hz : (z.2 : P) = 0) :
    positive z = 0 := by simp only [positive, hz, smul_zero]

/-- With zero positive component the denominator is one. -/
theorem Handle.denominator_eq_one_of_snd_eq_zero {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Space (N := N) (P := P)) (hz : (z.2 : P) = 0) :
    denominator z = 1 := by
  simp only [denominator, hz, norm_zero, zero_div, sub_zero]
  exact max_eq_right (mem_closedBall_zero_iff.mp z.1.property)

/-- The denominator is continuous. -/
theorem Handle.continuous_denominator {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] : Continuous (denominator (N := N) (P := P)) := by
  unfold denominator
  fun_prop

/-- The negative component is continuous. -/
theorem Handle.continuous_negative {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] : Continuous (negative (N := N) (P := P)) :=
  (continuous_denominator.inv₀ (fun z => (denominator_pos z).ne')).smul
    (continuous_subtype_val.comp continuous_fst)

/-- The positive component is continuous. -/
theorem Handle.continuous_positive {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] : Continuous (positive (N := N) (P := P)) := by
  have hv : Continuous (fun z : Space (N := N) (P := P) => (z.2 : P)) :=
    continuous_subtype_val.comp continuous_snd
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : (z.2 : P) = 0
  · change Filter.Tendsto positive (𝓝 z) (𝓝 (positive z))
    rw [positive_eq_zero_of_snd_eq_zero z hz]
    apply squeeze_zero_norm norm_positive_le
    simpa only [hz, norm_zero] using hv.norm.continuousAt.tendsto (x := z)
  · have hn :
      Continuous (fun w : Space (N := N) (P := P) => 2 * denominator w + ‖(w.2 : P)‖ - 2) :=
      ((continuous_const.mul continuous_denominator).add hv.norm).sub continuous_const
    have hd : Continuous (fun w : Space (N := N) (P := P) => ‖(w.2 : P)‖ * denominator w) :=
      hv.norm.mul continuous_denominator
    exact
      (hn.continuousAt.div hd.continuousAt
            (mul_ne_zero (norm_ne_zero_iff.mpr hz) (denominator_pos z).ne')).smul
        hv.continuousAt

/-- The retraction of the handle onto its core union lower face. -/
def Handle.retraction {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] : C(Space (N := N) (P := P), Space (N := N) (P := P))
    where
  toFun
    z :=
    (⟨negative z, mem_closedBall_zero_iff.mpr (norm_negative_le_one z)⟩,
      ⟨positive z,
        mem_closedBall_zero_iff.mpr
          ((norm_positive_le z).trans (mem_closedBall_zero_iff.mp z.2.property))⟩)
  continuous_toFun := (continuous_negative.subtype_mk _).prodMk (continuous_positive.subtype_mk _)

/-- The face-core: the lower face union the core disk. -/
def Handle.faceCore {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P] :
    Set (Space (N := N) (P := P)) :=
  {z | ‖(z.1 : N)‖ = 1 ∨ (z.2 : P) = 0}

/-- The retraction lands in the face-core. -/
theorem Handle.retraction_mem_faceCore {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Space (N := N) (P := P)) :
    retraction z ∈ faceCore := by
  by_cases hz : 1 - ‖(z.2 : P)‖ / 2 ≤ ‖(z.1 : N)‖
  · left
    change ‖negative z‖ = 1
    have hd : denominator z = ‖(z.1 : N)‖ := max_eq_left hz
    rw [negative, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (denominator_pos z).le)]
    rw [← hd, inv_mul_cancel₀ (denominator_pos z).ne']
  · right
    change positive z = 0
    have hd : denominator z = 1 - ‖(z.2 : P)‖ / 2 := max_eq_right (le_of_not_ge hz)
    have hn : 2 * denominator z + ‖(z.2 : P)‖ - 2 = 0 := by rw [hd]; ring
    simp only [positive, positiveMultiplier, hn, zero_div, zero_smul]

/-- The retraction fixes the face-core. -/
theorem Handle.retraction_eq_self {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Space (N := N) (P := P)) (hz : z ∈ faceCore) :
    retraction z = z := by
  have hd : denominator z = 1 := by
    rcases hz with hu | hv
    · unfold denominator
      rw [hu]
      apply max_eq_left
      linarith [norm_nonneg (z.2 : P)]
    · exact denominator_eq_one_of_snd_eq_zero z hv
  apply Prod.ext
  · apply Subtype.ext
    change negative z = (z.1 : N)
    simp only [negative, hd, inv_one, one_smul]
  · apply Subtype.ext
    change positive z = (z.2 : P)
    by_cases hv : (z.2 : P) = 0
    · simp only [positive, hv, smul_zero]
    · have hm : positiveMultiplier z = 1 := by
        unfold positiveMultiplier
        rw [hd]
        field_simp
        ring
      rw [positive, hm, one_smul]

/-! ### Retraction of the disk cylinder -/

/-- The closed unit disk of a normed space. -/
abbrev DiskCylinder.Disk {E : Type*} [NormedAddCommGroup E] :=
  Metric.closedBall (0 : E) 1

/-- The unit sphere of a normed space. -/
abbrev DiskCylinder.Sphere {E : Type*} [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

/-- The disk cylinder viewed inside the handle space. -/
def DiskCylinder.toHandle {E : Type*} [NormedAddCommGroup E] :
    C((unitInterval) × Disk (E := E), Handle.Space (N := E) (P := ℝ))
    where
  toFun
    p :=
    (p.2,
      ⟨p.1.val,
        mem_closedBall_zero_iff.mpr
          (by
            rw [Real.norm_of_nonneg p.1.property.1]
            exact p.1.property.2)⟩)
  continuous_toFun :=
    continuous_snd.prodMk ((continuous_subtype_val.comp continuous_fst).subtype_mk _)

/-- The time coordinate of the cylinder retraction. -/
def DiskCylinder.retractedTime {E : Type*} [NormedAddCommGroup E]
    (p : (unitInterval) × Disk (E := E)) : (unitInterval) :=
  ⟨Handle.positiveMultiplier (toHandle p) * p.1.val,
    mul_nonneg (Handle.positiveMultiplier_nonneg _) p.1.property.1,
    (by
      have h :=
        mul_le_mul_of_nonneg_right (Handle.positiveMultiplier_le_one (toHandle p))
          p.1.property.1
      exact (h.trans_eq (one_mul p.1.val)).trans p.1.property.2)⟩

/-- The retracted time is continuous. -/
theorem DiskCylinder.continuous_retractedTime {E : Type*} [NormedAddCommGroup E] :
    Continuous (retractedTime (E := E)) :=
  (Handle.continuous_positive.comp toHandle.continuous).subtype_mk _

/-- The disk coordinate of the cylinder retraction. -/
def DiskCylinder.retractedDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : (unitInterval) × Disk (E := E)) : Disk (E := E) :=
  (Handle.retraction (toHandle p)).1

/-- The retracted disk coordinate is continuous. -/
theorem DiskCylinder.continuous_retractedDisk {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Continuous (retractedDisk (E := E)) :=
  continuous_fst.comp (Handle.retraction.continuous.comp toHandle.continuous)

/-! ### Bottom-and-side gluing -/

/-- The bottom disk union the lateral side of the cylinder. -/
def DiskCylinder.bottomOrSide {E : Type*} [NormedAddCommGroup E] :
    Set ((unitInterval) × Disk (E := E)) :=
  {p | p.1 = 0 ∨ ‖(p.2 : E)‖ = 1}

/-- The cylinder retraction lands in bottom-or-side. -/
theorem DiskCylinder.retracted_mem_bottomOrSide {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : (unitInterval) × Disk (E := E)) :
    (retractedTime p, retractedDisk p) ∈ bottomOrSide := by
  rcases Handle.retraction_mem_faceCore (toHandle p) with hp | hp
  · exact Or.inr hp
  · apply Or.inl
    apply Subtype.ext
    exact hp

/-- The retraction of the disk cylinder onto bottom-or-side. -/
def DiskCylinder.retraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C((unitInterval) × Disk (E := E), bottomOrSide (E := E)) :=
  ⟨fun p => ⟨(retractedTime p, retractedDisk p), retracted_mem_bottomOrSide p⟩,
    (continuous_retractedTime.prodMk continuous_retractedDisk).subtype_mk _⟩

/-- The retraction fixes bottom-or-side. -/
theorem DiskCylinder.retraction_fixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : (unitInterval) × Disk (E := E)) (hp : p ∈ bottomOrSide) : (retraction p).val = p := by
  have hh : toHandle p ∈ Handle.faceCore := by
    rcases hp with ht | hx
    · exact Or.inr (congrArg Subtype.val ht)
    · exact Or.inl hx
  have hr := Handle.retraction_eq_self (toHandle p) hh
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : Handle.Space (N := E) (P := ℝ) => (z.2 : ℝ)) hr
  · exact congrArg Prod.fst hr

/-- A boundary sphere point rescaled into the disk. -/
def DiskCylinder.boundaryToDisk {E : Type*} [NormedAddCommGroup E] :
    C(Sphere (E := E), Disk (E := E)) :=
  ⟨fun u => ⟨u.val, Metric.sphere_subset_closedBall u.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The bottom disk inclusion into bottom-or-side. -/
def DiskCylinder.bottomMap {E : Type*} [NormedAddCommGroup E] :
    C(Disk (E := E), bottomOrSide (E := E)) :=
  ⟨fun u => ⟨(0, u), Or.inl rfl⟩, (continuous_const.prodMk continuous_id).subtype_mk _⟩

/-- The side inclusion into bottom-or-side. -/
def DiskCylinder.sideMap {E : Type*} [NormedAddCommGroup E] :
    C((unitInterval) × Sphere (E := E), bottomOrSide (E := E)) :=
  ⟨fun p => ⟨(p.1, boundaryToDisk p.2), Or.inr (mem_sphere_zero_iff_norm.mp p.2.property)⟩,
    (continuous_fst.prodMk (boundaryToDisk.continuous.comp continuous_snd)).subtype_mk _⟩

/-- The quotient map presenting bottom-or-side. -/
def DiskCylinder.bottomSideQuotient {E : Type*} [NormedAddCommGroup E] :
    C(Disk (E := E) ⊕ ((unitInterval) × Sphere (E := E)), bottomOrSide (E := E)) :=
  ⟨Sum.elim bottomMap sideMap, bottomMap.continuous.sumElim sideMap.continuous⟩

/-- The bottom-side quotient map is surjective. -/
theorem DiskCylinder.bottomSideQuotient_surjective {E : Type*} [NormedAddCommGroup E] :
    Function.Surjective (bottomSideQuotient (E := E)) := by
  rintro ⟨⟨t, u⟩, ht | hu⟩
  · change t = 0 at ht
    subst t
    exact ⟨.inl u, rfl⟩
  · exact ⟨.inr (t, ⟨u.val, mem_sphere_zero_iff_norm.mpr hu⟩), rfl⟩

/-- The bottom-side presentation is a quotient map. -/
theorem DiskCylinder.bottomSideQuotient_isQuotientMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Topology.IsQuotientMap (bottomSideQuotient (E := E)) :=
  .of_surjective_continuous bottomSideQuotient_surjective bottomSideQuotient.continuous

/-- Maps on the bottom and side agreeing on the sphere. -/
def DiskCylinder.bottomSideData {E : Type*} [NormedAddCommGroup E] {X : Type*}
    [TopologicalSpace X] (f : C(Disk (E := E), X)) (G : C((unitInterval) × Sphere (E := E), X)) :
    C(Disk (E := E) ⊕ ((unitInterval) × Sphere (E := E)), X) :=
  ⟨Sum.elim f G, f.continuous.sumElim G.continuous⟩

/-- Compatible bottom-side data is constant on quotient fibers. -/
theorem DiskCylinder.bottomSideData_constant_on_fibres {E : Type*} [NormedAddCommGroup E]
    {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u))
    (a b : Disk (E := E) ⊕ ((unitInterval) × Sphere (E := E)))
    (h : bottomSideQuotient a = bottomSideQuotient b) :
    bottomSideData f G a = bottomSideData f G b := by
  have he := congrArg Subtype.val h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg f (congrArg Prod.snd he)
    | inr b =>
      have ht : (0 : (unitInterval)) = b.1 := congrArg Prod.fst he
      have hu : a = boundaryToDisk b.2 := congrArg Prod.snd he
      exact (congrArg f hu).trans ((h0 b.2).symm.trans (congrArg G (Prod.ext ht rfl)))
  | inr a =>
    cases b with
    | inl b =>
      change G a = f b
      have ht : a.1 = (0 : (unitInterval)) := congrArg Prod.fst he
      have hu : boundaryToDisk a.2 = b := congrArg Prod.snd he
      have ha : a = (0, a.2) := Prod.ext ht rfl
      exact (congrArg G ha).trans ((h0 a.2).trans (congrArg f hu))
    | inr b =>
      change G a = G b
      have ht : a.1 = b.1 := congrArg (fun p : (unitInterval) × Disk (E := E) => p.1) he
      have hu : a.2.val = b.2.val :=
        congrArg (fun p : (unitInterval) × Disk (E := E) => p.2.val) he
      exact congrArg G (Prod.ext ht (Subtype.ext hu))

/-- The map on bottom-or-side glued from bottom and side data. -/
def DiskCylinder.gluedBottomSide {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) :
    C(bottomOrSide (E := E), X) :=
  bottomSideQuotient_isQuotientMap.lift (bottomSideData f G)
    (bottomSideData_constant_on_fibres f G h0)

/-- The glued map computes through the quotient. -/
@[simp]
theorem DiskCylinder.gluedBottomSide_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (f : C(Disk (E := E), X)) (G : C((unitInterval) × Sphere (E := E), X))
    (h0 : ∀ u, G (0, u) = f (boundaryToDisk u))
    (z : Disk (E := E) ⊕ ((unitInterval) × Sphere (E := E))) :
    gluedBottomSide f G h0 (bottomSideQuotient z) = bottomSideData f G z :=
  ContinuousMap.congr_fun
    (bottomSideQuotient_isQuotientMap.lift_comp (bottomSideData f G)
      (bottomSideData_constant_on_fibres f G h0))
    z

/-- The glued map on the bottom is the bottom map. -/
@[simp]
theorem DiskCylinder.gluedBottomSide_bottom {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (f : C(Disk (E := E), X)) (G : C((unitInterval) × Sphere (E := E), X))
    (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) (u : Disk (E := E)) :
    gluedBottomSide f G h0 (bottomMap u) = f u :=
  gluedBottomSide_apply f G h0 (.inl u)

/-- The glued map on the side is the side map. -/
@[simp]
theorem DiskCylinder.gluedBottomSide_side {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (f : C(Disk (E := E), X)) (G : C((unitInterval) × Sphere (E := E), X))
    (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) (p : (unitInterval) × Sphere (E := E)) :
    gluedBottomSide f G h0 (sideMap p) = G p :=
  gluedBottomSide_apply f G h0 (.inr p)

/-- The retraction computes on the bottom. -/
theorem DiskCylinder.retraction_bottom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Disk (E := E)) : retraction (0, u) = bottomMap u :=
  Subtype.ext (retraction_fixed (0, u) (Or.inl rfl))

/-- The retraction computes on the side. -/
theorem DiskCylinder.retraction_side {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : (unitInterval) × Sphere (E := E)) : retraction (p.1, boundaryToDisk p.2) = sideMap p :=
  Subtype.ext
    (retraction_fixed (p.1, boundaryToDisk p.2)
      (Or.inr (mem_sphere_zero_iff_norm.mp p.2.property)))

/-- A bottom-side map extended to the cylinder via the retraction. -/
def DiskCylinder.extend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) :
    C((unitInterval) × Disk (E := E), X) :=
  (gluedBottomSide f G h0).comp retraction

/-- The extension restricts to the bottom map. -/
@[simp]
theorem DiskCylinder.extend_bottom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u))
    (u : Disk (E := E)) : DiskCylinder.extend f G h0 (0, u) = f u := by
  change gluedBottomSide f G h0 (retraction (0, u)) = f u
  rw [retraction_bottom, gluedBottomSide_bottom]

/-- The extension restricts to the side map. -/
@[simp]
theorem DiskCylinder.extend_side {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u))
    (t : (unitInterval)) (u : Sphere (E := E)) :
    DiskCylinder.extend f G h0 (t, boundaryToDisk u) = G (t, u) := by
  change gluedBottomSide f G h0 (retraction (t, boundaryToDisk u)) = G (t, u)
  rw [retraction_side (t, u), gluedBottomSide_side]

/-- The endpoint map of the cylinder extension. -/
def DiskCylinder.extensionEndpoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) :
    C(Disk (E := E), X) :=
  (DiskCylinder.extend f G h0).comp
    ⟨fun u => (1, u), continuous_const.prodMk continuous_id⟩

/-- The extension as a homotopy to the endpoint. -/
def DiskCylinder.extensionHomotopy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] (f : C(Disk (E := E), X))
    (G : C((unitInterval) × Sphere (E := E), X)) (h0 : ∀ u, G (0, u) = f (boundaryToDisk u)) :
    f.Homotopy (extensionEndpoint f G h0)
    where
  toContinuousMap := DiskCylinder.extend f G h0
  map_zero_left := extend_bottom f G h0
  map_one_left _ := rfl

/-! ### The disk cone extension -/

/-- The radial parametrization of the disk by the cone on the sphere. -/
def DiskCone.radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C((unitInterval) × DiskCylinder.Sphere (E := E), DiskCylinder.Disk (E := E))
    where
  toFun
    p :=
    ⟨p.1.val • p.2.val,
      mem_closedBall_zero_iff.mpr
        (by
          rw [norm_smul, Real.norm_of_nonneg p.1.property.1,
            mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
          exact p.1.property.2)⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd)).subtype_mk
      _

/-- The radial point's norm is the cone parameter. -/
theorem DiskCone.radial_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : (unitInterval) × DiskCylinder.Sphere (E := E)) : ‖(radial p : E)‖ = p.1.val := by
  change ‖p.1.val • p.2.val‖ = p.1.val
  rw [norm_smul, Real.norm_of_nonneg p.1.property.1, mem_sphere_zero_iff_norm.mp p.2.property,
    mul_one]

/-- At parameter one the radial point is the sphere point. -/
@[simp]
theorem DiskCone.radial_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : DiskCylinder.Sphere (E := E)) :
    radial (1, s) = DiskCylinder.boundaryToDisk s :=
  Subtype.ext (one_smul ℝ s.val)

/-- At parameter zero the radial point is the center. -/
@[simp]
theorem DiskCone.radial_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : DiskCylinder.Sphere (E := E)) :
    radial (0, s) = (⟨0, by simp⟩ : DiskCylinder.Disk (E := E)) :=
  Subtype.ext (zero_smul ℝ s.val)

/-- The radial parametrization is surjective. -/
theorem DiskCone.radial_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s0 : DiskCylinder.Sphere (E := E)) : Function.Surjective (radial (E := E)) := by
  intro z
  by_cases hz : z.val = 0
  · exact ⟨(0, s0), (radial_zero s0).trans (Subtype.ext hz.symm)⟩
  · let t : (unitInterval) := ⟨‖z.val‖, norm_nonneg _, mem_closedBall_zero_iff.mp z.property⟩
    let s : DiskCylinder.Sphere (E := E) :=
      ⟨NormedSpace.normalize z.val, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hz)⟩
    exact ⟨(t, s), Subtype.ext (NormedSpace.norm_smul_normalize z.val)⟩

/-- Radial points agree exactly by equal parameters or zero. -/
theorem DiskCone.radial_eq_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : (unitInterval) × DiskCylinder.Sphere (E := E)) :
    radial p = radial q ↔ p = q ∨ p.1 = 0 ∧ q.1 = 0 := by
  constructor
  · intro h
    have ht : p.1 = q.1 :=
      Subtype.ext
        ((radial_norm p).symm.trans
          ((congrArg (fun z : DiskCylinder.Disk (E := E) => ‖(z : E)‖) h).trans
            (radial_norm q)))
    by_cases hp : p.1 = 0
    · exact Or.inr ⟨hp, ht.symm.trans hp⟩
    · left
      apply Prod.ext ht
      apply Subtype.ext
      have hn : p.1.val ≠ 0 := fun he => hp (Subtype.ext he)
      have hv : p.1.val • p.2.val = q.1.val • q.2.val := congrArg Subtype.val h
      rw [← ht] at hv
      exact (smul_right_inj hn).mp hv
  · rintro (rfl | ⟨hp, hq⟩)
    · rfl
    · change radial (p.1, p.2) = radial (q.1, q.2)
      rw [hp, hq, radial_zero, radial_zero]

/-- The radial map is a quotient map. -/
theorem DiskCone.radial_isQuotientMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s0 : DiskCylinder.Sphere (E := E)) :
    Topology.IsQuotientMap (radial (E := E)) :=
  .of_surjective_continuous (radial_surjective s0) radial.continuous

/-- A cone map constant on radial fibers descends to the disk. -/
theorem DiskCone.constant_on_radial_fibres {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : Type*} [TopologicalSpace X]
    (G : C((unitInterval) × DiskCylinder.Sphere (E := E), X)) (x : X)
    (hG : ∀ s, G (0, s) = x) (p q : (unitInterval) × DiskCylinder.Sphere (E := E))
    (h : radial p = radial q) : G p = G q := by
  rcases (radial_eq_iff p q).mp h with rfl | ⟨hp, hq⟩
  · rfl
  · change G (p.1, p.2) = G (q.1, q.2)
    rw [hp, hq, hG, hG]

/-- A cone map constant at the center extends to the disk. -/
def DiskCone.extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (s0 : DiskCylinder.Sphere (E := E))
    (G : C((unitInterval) × DiskCylinder.Sphere (E := E), X)) (x : X)
    (hG : ∀ s, G (0, s) = x) : C(DiskCylinder.Disk (E := E), X) :=
  (radial_isQuotientMap s0).lift G (constant_on_radial_fibres G x hG)

/-- The cone extension computes through the radial map. -/
theorem DiskCone.extension_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (s0 : DiskCylinder.Sphere (E := E))
    (G : C((unitInterval) × DiskCylinder.Sphere (E := E), X)) (x : X)
    (hG : ∀ s, G (0, s) = x) (t : (unitInterval)) (s : DiskCylinder.Sphere (E := E)) :
    extension s0 G x hG (radial (t, s)) = G (t, s) :=
  ContinuousMap.congr_fun
    ((radial_isQuotientMap s0).lift_comp G (constant_on_radial_fibres G x hG)) (t, s)

/-- The cone extension restricts to the boundary map. -/
theorem DiskCone.extension_boundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (s0 : DiskCylinder.Sphere (E := E))
    (G : C((unitInterval) × DiskCylinder.Sphere (E := E), X)) (x : X)
    (hG : ∀ s, G (0, s) = x) (s : DiskCylinder.Sphere (E := E)) :
    extension s0 G x hG (DiskCylinder.boundaryToDisk s) = G (1, s) := by
  rw [← radial_one, extension_radial]

/-- The cone extension at the center. -/
theorem DiskCone.extension_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
    (s0 : DiskCylinder.Sphere (E := E))
    (G : C((unitInterval) × DiskCylinder.Sphere (E := E), X)) (x : X)
    (hG : ∀ s, G (0, s) = x) : extension s0 G x hG ⟨0, by simp⟩ = x := by
  rw [← radial_zero s0, extension_radial, hG]

/-! ### Spheres under linear equivalences -/

/-- A unit sphere vector is nonzero. -/
theorem UnitSphereEquiv.vector_ne_zero {E : Type*} [NormedAddCommGroup E]
    (u : DiskCylinder.Sphere (E := E)) : u.val ≠ 0 := by
  intro h
  have hn := mem_sphere_zero_iff_norm.mp u.property
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

/-- A linear equivalence sends sphere vectors to nonzero vectors. -/
theorem UnitSphereEquiv.image_ne_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F)
    (u : DiskCylinder.Sphere (E := E)) : L u.val ≠ 0 := by
  intro h
  exact vector_ne_zero u (L.injective (h.trans (L.map_zero).symm))

/-- A linear equivalence normalized to a sphere map. -/
def UnitSphereEquiv.map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) :
    C(DiskCylinder.Sphere (E := E), DiskCylinder.Sphere (E := F))
    where
  toFun
    u :=
    ⟨NormedSpace.normalize (L u.val),
      mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (image_ne_zero L u))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      (((L.continuous.comp continuous_subtype_val).norm.inv₀
            (fun u => norm_ne_zero_iff.mpr (image_ne_zero L u))).smul
        (L.continuous.comp continuous_subtype_val))

/-- The normalized maps of `L` and `L⁻¹` are inverse. -/
theorem UnitSphereEquiv.map_inverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F)
    (u : DiskCylinder.Sphere (E := E)) :
    UnitSphereEquiv.map L.symm (UnitSphereEquiv.map L u) = u := by
  apply Subtype.ext
  change NormedSpace.normalize (L.symm (‖L u.val‖⁻¹ • L u.val)) = u.val
  rw [map_smul, L.symm_apply_apply,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr (norm_pos_iff.mpr (image_ne_zero L u)))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp u.property)

/-- A linear equivalence induces a sphere homeomorphism. -/
def UnitSphereEquiv.homeomorph {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) :
    DiskCylinder.Sphere (E := E) ≃ₜ DiskCylinder.Sphere (E := F)
    where
  toFun := UnitSphereEquiv.map L
  invFun := UnitSphereEquiv.map L.symm
  left_inv := map_inverse L
  right_inv := map_inverse L.symm
  continuous_toFun := (UnitSphereEquiv.map L).continuous
  continuous_invFun := (UnitSphereEquiv.map L.symm).continuous
