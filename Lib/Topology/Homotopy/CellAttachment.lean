/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/


import Lib.Geometry.Manifold.Morse.Handle
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Collar
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Analysis.Calculus.MorseLemma
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.Topology.Homotopy.HandleRetraction
import Lib.AlgebraicTopology.SingularHomology.SphereHomology

/-!
# Cell attachment: a handle deformation-retracts to its core

Attaching a handle is attaching a cell up to homotopy: `EmbeddedCellAttachment.*`,
`HandleCoreAttachment.*` (the core map and its boundary behaviour), `HandleCore*`
deformations, `DiskAnnulus`, `OuterDisk`, `ClosedHandleCore`, `RadialCoreShrink` — with the
cell-attachment Mayer–Vietoris cover (Hatcher, Prop 0.16's consequence and §2.3's matrix).

## Main definitions and results

* `HandleCoreAttachment.core` : the core-cell retraction.
* `EmbeddedCellAttachment.*` : the embedded cell attachment.
* `DiskAnnulus.*` : the disc-annulus decomposition.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Prop 0.16 and §2.3

## Tags

cell attachment, handle, deformation retract
-/

open Set Function Filter Manifold Topology

open scoped ContinuousMap

noncomputable section

/-! ### Radial shrinking of the disk -/

/-- The radial map shrinking a vector's norm by `a`. -/
def RadialCoreShrink.shrink {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (y : E) : E :=
  (Max.max (‖y‖ - Max.max a 0) 0 / ‖y‖) • y

/-- The shrink fixes the origin. -/
@[simp]
theorem RadialCoreShrink.shrink_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) : shrink a (0 : E) = 0 := by simp [shrink]

/-- The shrink reduces the norm by `a` clamped at zero. -/
theorem RadialCoreShrink.norm_shrink {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (y : E) : ‖shrink a y‖ = Max.max (‖y‖ - Max.max a 0) 0 := by
  by_cases hy : y = 0
  · subst y
    rw [shrink_zero, norm_zero]
    exact (max_eq_right (by linarith [le_max_right a 0])).symm
  rw [shrink, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (le_max_right _ _) (norm_nonneg y)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy)]

/-- The shrink never increases the norm. -/
theorem RadialCoreShrink.norm_shrink_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (y : E) : ‖shrink a y‖ ≤ ‖y‖ := by
  rw [norm_shrink]
  exact max_le (sub_le_self _ (le_max_right a 0)) (norm_nonneg y)

/-- Shrinking by zero is the identity. -/
@[simp]
theorem RadialCoreShrink.shrink_zero_parameter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (y : E) : shrink 0 y = y := by
  by_cases hy : y = 0
  · subst y
    exact shrink_zero 0
  rw [shrink, max_self, sub_zero, max_eq_left (norm_nonneg y), div_self (norm_ne_zero_iff.mpr hy),
    one_smul]

/-- Vectors inside radius `a` shrink to the origin. -/
theorem RadialCoreShrink.shrink_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} {y : E} (hy : ‖y‖ ≤ a) : shrink a y = 0 := by
  rw [shrink, max_eq_right (sub_nonpos.mpr (hy.trans (le_max_left a 0))), zero_div, zero_smul]

/-- The shrink is continuous in parameter and vector. -/
theorem RadialCoreShrink.continuous_shrink {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Continuous (fun z : ℝ × E => shrink z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a, y⟩
  by_cases hy : y = 0
  · subst y
    change Filter.Tendsto (fun z : ℝ × E => shrink z.1 z.2) (𝓝 (a, 0)) (𝓝 (shrink a 0))
    rw [shrink_zero]
    apply squeeze_zero_norm (fun z => norm_shrink_le z.1 z.2)
    simpa only [ContinuousAt, norm_zero] using
      (continuous_snd.norm.continuousAt : ContinuousAt (fun z : ℝ × E => ‖z.2‖) (a, 0))
  exact
    (((continuous_snd.norm.sub (continuous_fst.max continuous_const)).max
              continuous_const).continuousAt.div
          continuous_snd.norm.continuousAt (norm_ne_zero_iff.mpr hy)).smul
      continuous_snd.continuousAt

/-! ### The handle core collapse -/

/-- The normalizing factor of the handle core collapse. -/
def HandleCoreDeformation.denominator {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :
    ℝ :=
  Max.max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)

/-- The collapse denominator is positive. -/
theorem HandleCoreDeformation.denominator_pos {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :
    0 < denominator z := by
  have hy : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
  have h := le_max_right ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
  dsimp [denominator]
  linarith

/-- The collapse denominator is continuous. -/
theorem HandleCoreDeformation.continuous_denominator {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] : Continuous (denominator (N := N) (P := P)) :=
  (continuous_subtype_val.comp continuous_fst).norm.max
    (continuous_const.sub ((continuous_subtype_val.comp continuous_snd).norm.div_const 2))

/-- The negative component of the collapse. -/
def HandleCoreDeformation.negative {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :
    MorseHandle.UnitDisk N :=
  ⟨(denominator z)⁻¹ • (z.1 : N),
    by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (denominator_pos z))]
    calc
      _ ≤ (denominator z)⁻¹ * denominator z :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (inv_pos.mpr (denominator_pos z)).le
      _ = 1 := inv_mul_cancel₀ (denominator_pos z).ne'⟩

/-- The positive component of the collapse. -/
def HandleCoreDeformation.positive {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :
    MorseHandle.UnitDisk P :=
  ⟨RadialCoreShrink.shrink (2 * (1 - ‖(z.1 : N)‖)) (z.2 : P),
    mem_closedBall_zero_iff.mpr
      ((RadialCoreShrink.norm_shrink_le _ _).trans
        (mem_closedBall_zero_iff.mp z.2.property))⟩

/-- The negative component is continuous. -/
theorem HandleCoreDeformation.continuous_negative {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] : Continuous (negative (N := N) (P := P)) :=
  ((continuous_denominator.inv₀ (fun z => (denominator_pos z).ne')).smul
        (continuous_subtype_val.comp continuous_fst)).subtype_mk
    _

/-- The positive component is continuous. -/
theorem HandleCoreDeformation.continuous_positive {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] : Continuous (positive (N := N) (P := P)) :=
  (RadialCoreShrink.continuous_shrink.comp
        ((continuous_const.mul
              (continuous_const.sub (continuous_subtype_val.comp continuous_fst).norm)).prodMk
          (continuous_subtype_val.comp continuous_snd))).subtype_mk
    _

/-- The core deformation: the radial collapse of the handle onto its core, the deformation retraction realizing "attaching a handle is attaching a cell up to homotopy" (Hatcher, Algebraic Topology, Prop 0.16 consequence). -/
def HandleCoreDeformation.collapse {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] :
    C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P,
      MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :=
  ⟨fun z => (negative z, positive z), continuous_negative.prodMk continuous_positive⟩

/-- The union of the boundary face and the core disk of the handle. -/
def HandleCoreDeformation.faceCore {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] : Set (MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :=
  {z | ‖(z.1 : N)‖ = 1 ∨ (z.2 : P) = 0}

/-- The collapse lands in the face-core union. -/
theorem HandleCoreDeformation.collapse_mem {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) : collapse z ∈ faceCore := by
  rcases le_total (1 - ‖(z.2 : P)‖ / 2) ‖(z.1 : N)‖ with h | h
  · left
    have hx : 0 < ‖(z.1 : N)‖ := by
      have hpos := denominator_pos z
      rwa [denominator, max_eq_left h] at hpos
    change ‖(denominator z)⁻¹ • (z.1 : N)‖ = 1
    rw [denominator, max_eq_left h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
      inv_mul_cancel₀ hx.ne']
  · right
    apply RadialCoreShrink.shrink_eq_zero
    linarith

/-- The collapse fixes the boundary face. -/
theorem HandleCoreDeformation.collapse_face {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) (hz : ‖(z.1 : N)‖ = 1) :
    collapse z = z := by
  have hd : denominator z = 1 := by
    rw [denominator, hz, max_eq_left]
    linarith [norm_nonneg (z.2 : P)]
  apply Prod.ext
  · apply Subtype.ext
    change (denominator z)⁻¹ • (z.1 : N) = (z.1 : N)
    rw [hd, inv_one, one_smul]
  · apply Subtype.ext
    change RadialCoreShrink.shrink (2 * (1 - ‖(z.1 : N)‖)) (z.2 : P) = (z.2 : P)
    rw [hz, sub_self, MulZeroClass.mul_zero, RadialCoreShrink.shrink_zero_parameter]

/-- The collapse fixes the core disk. -/
theorem HandleCoreDeformation.collapse_core {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) (hz : (z.2 : P) = 0) :
    collapse z = z := by
  have hd : denominator z = 1 := by
    rw [denominator, hz, norm_zero, zero_div, sub_zero]
    exact max_eq_right (mem_closedBall_zero_iff.mp z.1.property)
  apply Prod.ext
  · apply Subtype.ext
    change (denominator z)⁻¹ • (z.1 : N) = (z.1 : N)
    rw [hd, inv_one, one_smul]
  · apply Subtype.ext
    change RadialCoreShrink.shrink (2 * (1 - ‖(z.1 : N)‖)) (z.2 : P) = (z.2 : P)
    rw [hz, RadialCoreShrink.shrink_zero]

/-- The collapse fixes the face-core union. -/
theorem HandleCoreDeformation.collapse_fixed {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) (hz : z ∈ faceCore) :
    collapse z = z :=
  hz.elim (collapse_face z) (collapse_core z)

/-- The convex blend between two disk points. -/
def HandleCoreDeformation.diskBlend {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : (unitInterval)) (x y : MorseHandle.UnitDisk V) : MorseHandle.UnitDisk V :=
  ⟨(1 - (t : ℝ)) • (x : V) + (t : ℝ) • (y : V),
    (convex_closedBall (0 : V) 1) x.property y.property (sub_nonneg.mpr t.property.2) t.property.1
      (sub_add_cancel 1 (t : ℝ))⟩

/-- The disk blend is continuous. -/
theorem HandleCoreDeformation.continuous_diskBlend {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] :
    Continuous
      (fun q : (unitInterval) × (MorseHandle.UnitDisk V × MorseHandle.UnitDisk V) =>
        diskBlend q.1 q.2.1 q.2.2) :=
  (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
            (continuous_subtype_val.comp continuous_snd.fst)).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd.snd))).subtype_mk
    _

/-- At time zero the blend is the first point. -/
@[simp]
theorem HandleCoreDeformation.diskBlend_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x y : MorseHandle.UnitDisk V) : diskBlend 0 x y = x := by
  apply Subtype.ext
  simp [diskBlend]

/-- At time one the blend is the second point. -/
@[simp]
theorem HandleCoreDeformation.diskBlend_one {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x y : MorseHandle.UnitDisk V) : diskBlend 1 x y = y := by
  apply Subtype.ext
  simp [diskBlend]

/-- Blending a point with itself is constant. -/
@[simp]
theorem HandleCoreDeformation.diskBlend_self {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (t : (unitInterval)) (x : MorseHandle.UnitDisk V) :
    diskBlend t x x = x := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • (x : V) + (t : ℝ) • (x : V) = (x : V)
  rw [← add_smul, sub_add_cancel, one_smul]

/-- The deformation retracting the handle onto its face-core union. -/
def HandleCoreDeformation.deformation {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (ContinuousMap.id (MorseHandle.UnitDisk N × MorseHandle.UnitDisk P)).HomotopyRel
      collapse faceCore
    where
  toFun q := (diskBlend q.1 q.2.1 (collapse q.2).1, diskBlend q.1 q.2.2 (collapse q.2).2)
  continuous_toFun :=
    (continuous_diskBlend.comp
          (continuous_fst.prodMk
            (continuous_snd.fst.prodMk (collapse.continuous.comp continuous_snd).fst))).prodMk
      (continuous_diskBlend.comp
        (continuous_fst.prodMk
          (continuous_snd.snd.prodMk (collapse.continuous.comp continuous_snd).snd)))
  map_zero_left z := by simp
  map_one_left z := by simp
  prop' t z
    hz := by
    change (diskBlend t z.1 (collapse z).1, diskBlend t z.2 (collapse z).2) = z
    rw [collapse_fixed z hz]
    simp

/-! ### Gluing on a closed cover -/

/-- A map glued from two closed embeddings covering the target. -/
def ClosedCover.mapOfClosedPieces {R P X Y : Type*} [TopologicalSpace R]
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y] (r : R → X) (p : P → X)
    (hr : Topology.IsClosedEmbedding r) (hp : Topology.IsClosedEmbedding p)
    (hcover : Set.range r ∪ Set.range p = Set.univ) (f : C(R, Y)) (g : C(P, Y))
    (hagree : ∀ a b, r a = p b → f a = g b) : C(X, Y) := by
  let a := hr.isEmbedding.toHomeomorph
  let b := hp.isEmbedding.toHomeomorph
  refine ⟨glue hcover (fun x => f (a.symm x)) (fun x => g (b.symm x)), ?_⟩
  apply
    continuous_glue hcover hr.isClosed_range hp.isClosed_range _ _
      (f.continuous.comp a.symm.continuous) (g.continuous.comp b.symm.continuous)
  intro x y hxy
  apply hagree
  exact
    (congrArg Subtype.val (a.apply_symm_apply x)).trans
      (hxy.trans (congrArg Subtype.val (b.apply_symm_apply y)).symm)

/-- The glued map agrees with the left piece. -/
theorem ClosedCover.mapOfClosedPieces_left {R P X Y : Type*} [TopologicalSpace R]
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y] (r : R → X) (p : P → X)
    (hr : Topology.IsClosedEmbedding r) (hp : Topology.IsClosedEmbedding p)
    (hcover : Set.range r ∪ Set.range p = Set.univ) (f : C(R, Y)) (g : C(P, Y))
    (hagree : ∀ a b, r a = p b → f a = g b) (x : R) :
    mapOfClosedPieces r p hr hp hcover f g hagree (r x) = f x := by
  let a := hr.isEmbedding.toHomeomorph
  let b := hp.isEmbedding.toHomeomorph
  change glue hcover (fun z => f (a.symm z)) (fun z => g (b.symm z)) (r x) = f x
  exact
    (glue_left hcover _ _ ⟨r x, Set.mem_range_self x⟩).trans (congrArg f (a.symm_apply_apply x))

/-- The glued map agrees with the right piece. -/
theorem ClosedCover.mapOfClosedPieces_right {R P X Y : Type*} [TopologicalSpace R]
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y] (r : R → X) (p : P → X)
    (hr : Topology.IsClosedEmbedding r) (hp : Topology.IsClosedEmbedding p)
    (hcover : Set.range r ∪ Set.range p = Set.univ) (f : C(R, Y)) (g : C(P, Y))
    (hagree : ∀ a b, r a = p b → f a = g b) (x : P) :
    mapOfClosedPieces r p hr hp hcover f g hagree (p x) = g x := by
  let a := hr.isEmbedding.toHomeomorph
  let b := hp.isEmbedding.toHomeomorph
  have hagree' :
    ∀ u : Set.range r, ∀ v : Set.range p, (u : X) = v → f (a.symm u) = g (b.symm v) := by
    intro u v huv
    apply hagree
    exact
      (congrArg Subtype.val (a.apply_symm_apply u)).trans
        (huv.trans (congrArg Subtype.val (b.apply_symm_apply v)).symm)
  change glue hcover (fun z => f (a.symm z)) (fun z => g (b.symm z)) (p x) = g x
  exact
    (glue_right hcover _ _ hagree' ⟨p x, Set.mem_range_self x⟩).trans
      (congrArg g (b.symm_apply_apply x))

/-- The core map of the attached handle: the restriction of the characteristic map to the core disk, with its boundary behaviour on the attaching region. -/
def HandleCoreAttachment.core {N P X : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    [TopologicalSpace X] (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) :
    C(MorseHandle.UnitDisk N, X) :=
  ⟨fun x => h (x, ⟨0, by simp⟩), h.continuous.comp (continuous_id.prodMk continuous_const)⟩

/-! ### Retraction of a handle attachment -/

/-- The union of the old space and the handle core inside `X`. -/
def HandleCoreAttachment.coreSpace {N P R X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) : Set X :=
  Set.range r ∪ Set.range (core h)

/-- The handle collapse lands in the core space. -/
theorem HandleCoreAttachment.collapse_lands {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1)
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :
    h (HandleCoreDeformation.collapse z) ∈ coreSpace r h := by
  rcases HandleCoreDeformation.collapse_mem z with hz | hz
  · exact Or.inl ((hface (HandleCoreDeformation.collapse z)).mpr hz)
  · right
    refine ⟨(HandleCoreDeformation.collapse z).1, ?_⟩
    apply congrArg h
    exact Prod.ext rfl (Subtype.ext hz.symm)

/-- The map sending an old point to the core space. -/
def HandleCoreAttachment.oldToCore {N P R X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) : C(R, coreSpace r h) :=
  ⟨fun a => ⟨r a, Or.inl (Set.mem_range_self a)⟩, hr.continuous.subtype_mk _⟩

/-- The retraction of the whole handle onto its core, built from the old-space and core maps agreeing on the overlap (Hatcher, Algebraic Topology, proof of Prop 0.16). -/
def HandleCoreAttachment.handleToCore {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) :
    C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, coreSpace r h) :=
  ⟨fun z => ⟨h (HandleCoreDeformation.collapse z), collapse_lands r h hface z⟩,
    (h.continuous.comp HandleCoreDeformation.collapse.continuous).subtype_mk _⟩

/-- The old and handle retractions agree on the attachment overlap. -/
theorem HandleCoreAttachment.coreMaps_agree {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) (a : R)
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) (haz : r a = h z) :
    oldToCore r h hr a = handleToCore r h hface z := by
  have hz : ‖(z.1 : N)‖ = 1 := (hface z).mp ⟨a, haz⟩
  apply Subtype.ext
  change r a = h (HandleCoreDeformation.collapse z)
  rw [HandleCoreDeformation.collapse_face z hz]
  exact haz

/-- The deformation retraction `r : M -> M` with image the core: fixed on the core, identity on the old space, and handle-collapsing in between. -/
def HandleCoreAttachment.retraction {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) : C(X, coreSpace r h) :=
  ClosedCover.mapOfClosedPieces r h hr hh hcover (oldToCore r h hr) (handleToCore r h hface)
    (coreMaps_agree r h hr hface)

/-- The retraction computes the identity on old points. -/
theorem HandleCoreAttachment.retraction_old {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) (a : R) :
    (retraction r h hr hh hcover hface (r a) : X) = r a :=
  congrArg Subtype.val
    (ClosedCover.mapOfClosedPieces_left r h hr hh hcover (oldToCore r h hr)
      (handleToCore r h hface) (coreMaps_agree r h hr hface) a)

/-- The retraction computes the collapse on handle points. -/
theorem HandleCoreAttachment.retraction_handle {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1)
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :
    (retraction r h hr hh hcover hface (h z) : X) = h (HandleCoreDeformation.collapse z) :=
  congrArg Subtype.val
    (ClosedCover.mapOfClosedPieces_right r h hr hh hcover (oldToCore r h hr)
      (handleToCore r h hface) (coreMaps_agree r h hr hface) z)

/-- The retraction fixes the core space. -/
theorem HandleCoreAttachment.retraction_fixed {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) (x : X) (hx : x ∈ coreSpace r h) :
    (retraction r h hr hh hcover hface x : X) = x := by
  rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · exact retraction_old r h hr hh hcover hface a
  · change (retraction r h hr hh hcover hface (h (z, ⟨0, by simp⟩)) : X) = h (z, ⟨0, by simp⟩)
    rw [retraction_handle, HandleCoreDeformation.collapse_core _ rfl]

/-- The two piece-maps cover the cylinder over the union. -/
theorem HandleCoreAttachment.time_cover {N P R X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hcover : Set.range r ∪ Set.range h = Set.univ) :
    Set.range (Prod.map (id : (unitInterval) → (unitInterval)) r) ∪
        Set.range (Prod.map (id : (unitInterval) → (unitInterval)) h) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨t, x⟩
  have hx : x ∈ Set.range r ∪ Set.range h := by rw [hcover]; trivial
  rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inl ⟨(t, a), rfl⟩
  · exact Or.inr ⟨(t, z), rfl⟩

/-- The stationary motion on the old part. -/
def HandleCoreAttachment.oldMotion {R X : Type*} [TopologicalSpace R] [TopologicalSpace X]
    (r : R → X) (hr : Topology.IsClosedEmbedding r) : C((unitInterval) × R, X) :=
  ⟨fun q => r q.2, hr.continuous.comp continuous_snd⟩

/-- The collapse motion on the handle part. -/
def HandleCoreAttachment.handleMotion {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace X]
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) :
    C((unitInterval) × (MorseHandle.UnitDisk N × MorseHandle.UnitDisk P), X) :=
  h.comp HandleCoreDeformation.deformation.toHomotopy.toContinuousMap

/-- The two motions agree on the overlap. -/
theorem HandleCoreAttachment.motions_agree {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1)
    (a : (unitInterval) × R)
    (z : (unitInterval) × (MorseHandle.UnitDisk N × MorseHandle.UnitDisk P))
    (haz : Prod.map id r a = Prod.map id h z) : oldMotion r hr a = handleMotion h z := by
  have ha : r a.2 = h z.2 := congrArg Prod.snd haz
  have hz : z.2 ∈ HandleCoreDeformation.faceCore := Or.inl ((hface z.2).mp ⟨a.2, ha⟩)
  change r a.2 = h (HandleCoreDeformation.deformation (z.1, z.2))
  rw [HandleCoreDeformation.deformation.eq_fst z.1 hz]
  exact ha

/-- The glued deformation of the union onto the core space. -/
def HandleCoreAttachment.motion {N P R X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R] [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) : C((unitInterval) × X, X) :=
  ClosedCover.mapOfClosedPieces (Prod.map id r) (Prod.map id h)
    (Topology.IsClosedEmbedding.id.prodMap hr) (Topology.IsClosedEmbedding.id.prodMap hh)
    (time_cover r h hcover) (oldMotion r hr) (handleMotion h) (motions_agree r h hr hface)

/-- The motion is stationary on the old part. -/
theorem HandleCoreAttachment.motion_old {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) (t : (unitInterval)) (a : R) :
    motion r h hr hh hcover hface (t, r a) = r a :=
  ClosedCover.mapOfClosedPieces_left (Prod.map id r) (Prod.map id h)
    (Topology.IsClosedEmbedding.id.prodMap hr) (Topology.IsClosedEmbedding.id.prodMap hh)
    (time_cover r h hcover) (oldMotion r hr) (handleMotion h) (motions_agree r h hr hface) (t, a)

/-- The motion computes the collapse on the handle part. -/
theorem HandleCoreAttachment.motion_handle {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) (t : (unitInterval))
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :
    motion r h hr hh hcover hface (t, h z) = h (HandleCoreDeformation.deformation (t, z)) :=
  ClosedCover.mapOfClosedPieces_right (Prod.map id r) (Prod.map id h)
    (Topology.IsClosedEmbedding.id.prodMap hr) (Topology.IsClosedEmbedding.id.prodMap hh)
    (time_cover r h hcover) (oldMotion r hr) (handleMotion h) (motions_agree r h hr hface) (t, z)

/-- The inclusion of the core space into the union. -/
def HandleCoreAttachment.coreInclusion {N P R X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) :
    C(coreSpace r h, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The deformation retraction of the attachment onto its core. -/
def HandleCoreAttachment.deformation {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) :
    (ContinuousMap.id X).HomotopyRel
      ((coreInclusion r h).comp (retraction r h hr hh hcover hface)) (coreSpace r h)
    where
  toFun := motion r h hr hh hcover hface
  continuous_toFun := (motion r h hr hh hcover hface).continuous
  map_zero_left
    x := by
    have hx : x ∈ Set.range r ∪ Set.range h := by rw [hcover]; trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · exact motion_old r h hr hh hcover hface 0 a
    · rw [motion_handle]
      exact congrArg h (HandleCoreDeformation.deformation.toHomotopy.map_zero_left z)
  map_one_left
    x := by
    change motion r h hr hh hcover hface (1, x) = (retraction r h hr hh hcover hface x : X)
    have hx : x ∈ Set.range r ∪ Set.range h := by rw [hcover]; trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · rw [motion_old, retraction_old]
    · rw [motion_handle, retraction_handle]
      exact congrArg h (HandleCoreDeformation.deformation.toHomotopy.map_one_left z)
  prop' t x
    hx := by
    change motion r h hr hh hcover hface (t, x) = x
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · exact motion_old r h hr hh hcover hface t a
    · change motion r h hr hh hcover hface (t, h (z, ⟨0, by simp⟩)) = h (z, ⟨0, by simp⟩)
      rw [motion_handle]
      exact congrArg h (HandleCoreDeformation.deformation.eq_fst t (Or.inr rfl))

/-- The core space is homotopy equivalent to the attachment union. -/
def HandleCoreAttachment.homotopyEquiv {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) : coreSpace r h ≃ₕ X
    where
  toFun := coreInclusion r h
  invFun := retraction r h hr hh hcover hface
  left_inv := by
    have heq :
      (retraction r h hr hh hcover hface).comp (coreInclusion r h) =
        ContinuousMap.id (coreSpace r h) := by
      apply ContinuousMap.ext
      intro x
      exact Subtype.ext (retraction_fixed r h hr hh hcover hface x.val x.property)
    rw [heq]
  right_inv := ⟨(deformation r h hr hh hcover hface).toHomotopy.symm⟩

/-! ### The closed two-piece cover -/

/-- The inclusion of the old set into the union. -/
def ClosedHandleCore.oldInclusion {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) :
    C(A, ↥(A ∪ Set.range h)) :=
  ⟨Set.inclusion (fun _ hx => Or.inl hx), continuous_inclusion _⟩

/-- The handle map into the union. -/
def ClosedHandleCore.handleInclusion {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) :
    C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, ↥(A ∪ Set.range h)) :=
  ⟨fun z => ⟨h z, Or.inr (Set.mem_range_self z)⟩, h.continuous.subtype_mk _⟩

/-- The old piece is closed in the union. -/
theorem ClosedHandleCore.old_closed {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) (hA : IsClosed A) :
    Topology.IsClosedEmbedding (oldInclusion A h) :=
  ClosedCover.isClosedEmbedding_codRestrict hA.isClosedEmbedding_subtypeVal
    (fun x => Or.inl x.property)

/-- The handle piece is closed in the union. -/
theorem ClosedHandleCore.handle_closed {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (hh : Topology.IsClosedEmbedding h) : Topology.IsClosedEmbedding (handleInclusion A h) :=
  ClosedCover.isClosedEmbedding_codRestrict hh (fun z => Or.inr (Set.mem_range_self z))

/-- The old and handle pieces cover the union. -/
theorem ClosedHandleCore.pieces_cover {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) :
    Set.range (oldInclusion A h) ∪ Set.range (handleInclusion A h) = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨x, hx | ⟨z, rfl⟩⟩
  · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inr ⟨z, rfl⟩

/-- A handle point lies in the old piece exactly on the boundary face. -/
theorem ClosedHandleCore.handle_mem_old_iff {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (z : MorseHandle.UnitDisk N × MorseHandle.UnitDisk P) :
    handleInclusion A h z ∈ Set.range (oldInclusion A h) ↔ h z ∈ A := by
  constructor
  · rintro ⟨a, ha⟩
    have heq : (a : X) = h z := congrArg Subtype.val ha
    exact heq ▸ a.property
  · intro hz
    exact ⟨⟨h z, hz⟩, rfl⟩

/-- The core space sits inside the union. -/
theorem ClosedHandleCore.core_subset {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) :
    A ∪ Set.range (HandleCoreAttachment.core h) ⊆ A ∪ Set.range h := by
  rintro x (hx | ⟨z, rfl⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨(z, ⟨0, by simp⟩), rfl⟩

/-- Membership in the core space characterized on the two pieces. -/
theorem ClosedHandleCore.coreSpace_iff {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X))
    (x : ↥(A ∪ Set.range h)) :
    x ∈ HandleCoreAttachment.coreSpace (oldInclusion A h) (handleInclusion A h) ↔
      x.val ∈ A ∪ Set.range (HandleCoreAttachment.core h) := by
  constructor
  · rintro (⟨a, ha⟩ | ⟨z, hz⟩)
    · left
      have heq : (a : X) = x.val := congrArg Subtype.val ha
      exact heq ▸ a.property
    · right
      exact ⟨z, congrArg Subtype.val hz⟩
  · rintro (hx | ⟨z, hz⟩)
    · exact Or.inl ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · exact Or.inr ⟨z, Subtype.ext hz⟩

/-- The union is homeomorphic to the glued core space. -/
def ClosedHandleCore.coreUnionHomeomorph {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) :
    ↥(A ∪ Set.range (HandleCoreAttachment.core h)) ≃ₜ
      HandleCoreAttachment.coreSpace (oldInclusion A h) (handleInclusion A h)
    where
  toFun x := ⟨⟨x.val, core_subset A h x.property⟩, (coreSpace_iff A h _).mpr x.property⟩
  invFun x := ⟨x.val.val, (coreSpace_iff A h x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The union is homotopy equivalent to the old set. -/
def ClosedHandleCore.unionHomotopyEquiv {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(MorseHandle.UnitDisk N × MorseHandle.UnitDisk P, X)) [NormedSpace ℝ N]
    [NormedSpace ℝ P] (hA : IsClosed A) (hh : Topology.IsClosedEmbedding h)
    (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) :
    ↥(A ∪ Set.range (HandleCoreAttachment.core h)) ≃ₕ ↥(A ∪ Set.range h) :=
  (coreUnionHomeomorph A h).toHomotopyEquiv.trans
    (HandleCoreAttachment.homotopyEquiv (oldInclusion A h) (handleInclusion A h)
      (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
      (fun z => (handle_mem_old_iff A h z).trans (hface z)))

/-! ### Embedded cell attachments -/

/-- An embedded cell attachment: the old closed set, the cell map, and the face condition. -/
structure EmbeddedCellAttachment (N X : Type*) [NormedAddCommGroup N]
    [TopologicalSpace X] where
  old : Set X
  old_closed : IsClosed old
  cell : C(MorseHandle.UnitDisk N, X)
  cell_closed : Topology.IsClosedEmbedding cell
  cover : old ∪ Set.range cell = Set.univ
  boundary : ∀ z, cell z ∈ old ↔ ‖(z : N)‖ = 1

/-- The attachment data assembled from a closed union with a cell. -/
def EmbeddedCellAttachment.ofUnion {N X : Type*} [NormedAddCommGroup N] [TopologicalSpace X]
    (A : Set X) (e : C(MorseHandle.UnitDisk N, X)) (hA : IsClosed A)
    (he : Topology.IsClosedEmbedding e) (hface : ∀ z, e z ∈ A ↔ ‖(z : N)‖ = 1) :
    EmbeddedCellAttachment N ↥(A ∪ Set.range e)
    where
  old := {x | x.val ∈ A}
  old_closed := hA.preimage continuous_subtype_val
  cell := ⟨fun z => ⟨e z, Or.inr (Set.mem_range_self z)⟩, e.continuous.subtype_mk _⟩
  cell_closed :=
    ClosedCover.isClosedEmbedding_codRestrict he (fun z => Or.inr (Set.mem_range_self z))
  cover := by
    apply Set.eq_univ_of_forall
    rintro ⟨x, hx | ⟨z, rfl⟩⟩
    · exact Or.inl hx
    · exact Or.inr ⟨z, rfl⟩
  boundary := hface

/-- The old set union the outer half of the cell. -/
def EmbeddedCellAttachment.oldNeighborhood {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) : Set X :=
  (D.cell '' {z : MorseHandle.UnitDisk N | ‖(z : N)‖ ≤ 1 / 2})ᶜ

/-- The open inner part of the cell. -/
def EmbeddedCellAttachment.diskPatch {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) : Set X :=
  D.oldᶜ

/-- The old neighbourhood is open. -/
theorem EmbeddedCellAttachment.isOpen_oldNeighborhood {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) : IsOpen D.oldNeighborhood :=
  (D.cell_closed.isClosedMap _
      (isClosed_le continuous_subtype_val.norm continuous_const)).isOpen_compl

/-- The disk patch is open. -/
theorem EmbeddedCellAttachment.isOpen_diskPatch {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) : IsOpen D.diskPatch :=
  D.old_closed.isOpen_compl

/-- A cell point lies in the old neighbourhood in the outer half. -/
theorem EmbeddedCellAttachment.cell_mem_oldNeighborhood_iff {N X : Type*}
    [NormedAddCommGroup N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (z : MorseHandle.UnitDisk N) : D.cell z ∈ D.oldNeighborhood ↔ 1 / 2 < ‖(z : N)‖ := by
  constructor
  · intro hz
    by_contra! hnorm
    exact hz ⟨z, hnorm, rfl⟩
  · rintro hnorm ⟨w, hw, heq⟩
    have hwz : w = z := D.cell_closed.injective heq
    subst w
    exact (not_le_of_gt hnorm) hw

/-- A cell point lies in the disk patch in the open interior. -/
theorem EmbeddedCellAttachment.cell_mem_diskPatch_iff {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (z : MorseHandle.UnitDisk N) : D.cell z ∈ D.diskPatch ↔ ‖(z : N)‖ < 1 := by
  change D.cell z ∉ D.old ↔ ‖(z : N)‖ < 1
  rw [D.boundary]
  have hz : ‖(z : N)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
  constructor
  · intro h
    exact lt_of_le_of_ne hz h
  · exact ne_of_lt

/-- The old set sits inside its neighbourhood. -/
theorem EmbeddedCellAttachment.old_subset_neighborhood {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) : D.old ⊆ D.oldNeighborhood := by
  rintro x hx ⟨z, hz, rfl⟩
  have heq := (D.boundary z).mp hx
  change ‖(z : N)‖ ≤ 1 / 2 at hz
  linarith

/-- The old neighbourhood and disk patch cover the union. -/
theorem EmbeddedCellAttachment.open_cover {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    D.oldNeighborhood ∪ D.diskPatch = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ D.old
  · exact Or.inl (D.old_subset_neighborhood hx)
  · exact Or.inr hx

/-- The disk patch lies in the cell image. -/
theorem EmbeddedCellAttachment.diskPatch_subset_range {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    D.diskPatch ⊆ Set.range D.cell := by
  intro x hx
  have hcover : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  exact hcover.resolve_left hx

/-- The overlap lies in the cell image. -/
theorem EmbeddedCellAttachment.overlap_subset_range {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    D.oldNeighborhood ∩ D.diskPatch ⊆ Set.range D.cell :=
  Set.inter_subset_right.trans D.diskPatch_subset_range

/-- The disk patch is homeomorphic to the open unit disk. -/
def EmbeddedCellAttachment.diskHomeomorph {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    { z : MorseHandle.UnitDisk N // ‖(z : N)‖ < 1 } ≃ₜ D.diskPatch :=
  (Homeomorph.setCongr
        (by
          ext z
          exact (D.cell_mem_diskPatch_iff z).symm)).trans
    (D.cell_closed.isEmbedding.homeomorphOfSubsetRange D.diskPatch_subset_range)

/-- The overlap is homeomorphic to the annulus `1/2 < ‖z‖ < 1`. -/
def EmbeddedCellAttachment.overlapHomeomorph {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    { z : MorseHandle.UnitDisk N // 1 / 2 < ‖(z : N)‖ ∧ ‖(z : N)‖ < 1 } ≃ₜ
      ↥(D.oldNeighborhood ∩ D.diskPatch) :=
  (Homeomorph.setCongr
        (by
          ext z
          exact
            (and_congr (D.cell_mem_oldNeighborhood_iff z)
                (D.cell_mem_diskPatch_iff z)).symm)).trans
    (D.cell_closed.isEmbedding.homeomorphOfSubsetRange D.overlap_subset_range)

/-! ### The outer annulus -/

/-- The closed annulus `1/2 ≤ ‖z‖ ≤ 1`. -/
abbrev OuterDisk.Space (E : Type*) [NormedAddCommGroup E] :=
  { z : MorseHandle.UnitDisk E // 1 / 2 < ‖(z : E)‖ }

/-- Outer-disk points are nonzero. -/
theorem OuterDisk.norm_pos {E : Type*} [NormedAddCommGroup E] (z : Space E) :
    0 < ‖(z.val : E)‖ := by linarith [z.property]

/-- The unit sphere viewed in the unit disk. -/
def OuterDisk.sphereDisk {E : Type*} [NormedAddCommGroup E] :
    C(Metric.sphere (0 : E) 1, MorseHandle.UnitDisk E) :=
  ⟨Set.inclusion Metric.sphere_subset_closedBall, continuous_inclusion _⟩

/-- The sphere points lie in the outer annulus. -/
theorem OuterDisk.sphereDisk_mem {E : Type*} [NormedAddCommGroup E]
    (u : Metric.sphere (0 : E) 1) : 1 / 2 < ‖(sphereDisk u : E)‖ := by
  change 1 / 2 < ‖(u : E)‖
  rw [mem_sphere_zero_iff_norm.mp u.property]
  norm_num

/-- The sphere included into the outer annulus. -/
def OuterDisk.fromSphere {E : Type*} [NormedAddCommGroup E] :
    C(Metric.sphere (0 : E) 1, Space E) :=
  ⟨fun u => ⟨sphereDisk u, sphereDisk_mem u⟩, sphereDisk.continuous.subtype_mk _⟩

/-- The radial projection of the outer annulus onto the sphere. -/
def OuterDisk.toSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(Space E, Metric.sphere (0 : E) 1) :=
  ⟨fun z => RadialExtension.direction (z.val : E) (norm_ne_zero_iff.mp (norm_pos z).ne'),
    (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
              (fun z => (norm_pos z).ne')).smul
          (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
      _⟩

/-- Radial projection followed by inclusion fixes the boundary. -/
theorem OuterDisk.fromSphere_toSphere_boundary {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (z : Space E) (hz : ‖(z.val : E)‖ = 1) : fromSphere (toSphere z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  change ‖(z.val : E)‖⁻¹ • (z.val : E) = (z.val : E)
  rw [hz, inv_one, one_smul]

/-- The radial blend deforming an annulus point toward the sphere. -/
def OuterDisk.blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : (unitInterval) × Space E) : E :=
  ((1 - (q.1 : ℝ)) + (q.1 : ℝ) / ‖(q.2.val : E)‖) • (q.2.val : E)

/-- The annulus blend is continuous. -/
theorem OuterDisk.continuous_blendVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Continuous (blendVector (E := E)) := by
  have ht : Continuous (fun q : (unitInterval) × Space E => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous (fun q : (unitInterval) × Space E => (q.2.val : E)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_const.sub ht).add (ht.div hz.norm (fun q => (norm_pos q.2).ne'))).smul hz

/-- The blend norm interpolates to the unit sphere. -/
theorem OuterDisk.norm_blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : (unitInterval)) (z : Space E) :
    ‖blendVector (t, z)‖ = (1 - (t : ℝ)) * ‖(z.val : E)‖ + (t : ℝ) := by
  have hscale : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) / ‖(z.val : E)‖ :=
    add_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg t.property.1 (norm_pos z).le)
  rw [blendVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale, add_mul,
    div_mul_cancel₀ _ (norm_pos z).ne']

/-- The blend stays in the outer annulus. -/
theorem OuterDisk.norm_blendVector_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : (unitInterval)) (z : Space E) :
    1 / 2 < ‖blendVector (t, z)‖ ∧ ‖blendVector (t, z)‖ ≤ 1 := by
  rw [norm_blendVector]
  have hz : ‖(z.val : E)‖ ∈ Set.Ioc (1 / 2 : ℝ) 1 :=
    ⟨z.property, mem_closedBall_zero_iff.mp z.val.property⟩
  have h :=
    (convex_Ioc (𝕜 := ℝ) (1 / 2 : ℝ) 1) hz (by norm_num : (1 : ℝ) ∈ Ioc (1 / 2) 1)
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
  simpa only [Set.mem_Ioc, smul_eq_mul, mul_one] using h

/-- The deformation of the outer annulus onto its boundary sphere. -/
def OuterDisk.blend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : (unitInterval) × Space E) : Space E :=
  ⟨⟨blendVector q, mem_closedBall_zero_iff.mpr (norm_blendVector_mem q.1 q.2).2⟩,
    (norm_blendVector_mem q.1 q.2).1⟩

/-- The annulus deformation is continuous. -/
theorem OuterDisk.continuous_blend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (blend (E := E)) :=
  (continuous_blendVector.subtype_mk _).subtype_mk _

/-- The deformation retraction of the outer annulus onto the sphere. -/
def OuterDisk.deformation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (ContinuousMap.id (Space E)).HomotopyRel (fromSphere.comp toSphere) {z | ‖(z.val : E)‖ = 1}
    where
  toFun := blend
  continuous_toFun := continuous_blend
  map_zero_left
    z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector]
  map_one_left
    z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector, fromSphere, sphereDisk, toSphere, RadialExtension.direction]
  prop' t z
    hz := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (t : ℝ)) + (t : ℝ) / ‖(z.val : E)‖) • (z.val : E) = (z.val : E)
    rw [hz, div_one, sub_add_cancel, one_smul]

/-- The inclusion of the old set into its neighbourhood. -/
def EmbeddedCellAttachment.oldInclusion {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) : C(D.old, D.oldNeighborhood) :=
  ⟨Set.inclusion D.old_subset_neighborhood, continuous_inclusion _⟩

/-- The old neighbourhood's cell part parametrized by the outer annulus. -/
def EmbeddedCellAttachment.outerParameterHomeomorph {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    OuterDisk.Space N ≃ₜ (D.cell ⁻¹' D.oldNeighborhood) :=
  Homeomorph.setCongr (by ext z; exact (D.cell_mem_oldNeighborhood_iff z).symm)

/-- The outer annulus mapped into the old neighbourhood. -/
def EmbeddedCellAttachment.outerInclusion {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    C(OuterDisk.Space N, D.oldNeighborhood) :=
  ⟨fun z => ⟨D.cell z.val, (D.cell_mem_oldNeighborhood_iff z.val).mpr z.property⟩,
    (D.cell.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The old inclusion is a closed embedding. -/
theorem EmbeddedCellAttachment.oldInclusion_closed {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    Topology.IsClosedEmbedding D.oldInclusion :=
  ClosedCover.isClosedEmbedding_codRestrict D.old_closed.isClosedEmbedding_subtypeVal
    (fun x => D.old_subset_neighborhood x.property)

/-- The outer inclusion is a closed embedding. -/
theorem EmbeddedCellAttachment.outerInclusion_closed {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    Topology.IsClosedEmbedding D.outerInclusion :=
  (D.oldNeighborhood.restrictPreimage_isClosedEmbedding D.cell_closed).comp
    D.outerParameterHomeomorph.isClosedEmbedding

/-- The old and outer pieces cover the neighbourhood. -/
theorem EmbeddedCellAttachment.oldNeighborhood_cover {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    Set.range D.oldInclusion ∪ Set.range D.outerInclusion = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨x, hx⟩
  have hcover : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  rcases hcover with hA | ⟨z, rfl⟩
  · exact Or.inl ⟨⟨x, hA⟩, rfl⟩
  · exact Or.inr ⟨⟨z, (D.cell_mem_oldNeighborhood_iff z).mp hx⟩, rfl⟩

/-- The attaching sphere lands in the old set. -/
theorem EmbeddedCellAttachment.sphere_attaches {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) (u : Metric.sphere (0 : N) 1) :
    D.cell (OuterDisk.sphereDisk u) ∈ D.old :=
  (D.boundary _).mpr (mem_sphere_zero_iff_norm.mp u.property)

/-- The attaching map of the cell's boundary sphere. -/
def EmbeddedCellAttachment.attachingSphere {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    C(Metric.sphere (0 : N) 1, D.old) :=
  ⟨fun u => ⟨D.cell (OuterDisk.sphereDisk u), D.sphere_attaches u⟩,
    (D.cell.continuous.comp OuterDisk.sphereDisk.continuous).subtype_mk _⟩

/-- The old and outer retractions agree on the overlap. -/
theorem EmbeddedCellAttachment.retractionMaps_agree {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) [NormedSpace ℝ N] (a : D.old)
    (z : OuterDisk.Space N) (haz : D.oldInclusion a = D.outerInclusion z) :
    a = D.attachingSphere (OuterDisk.toSphere z) := by
  have heq : (a : X) = D.cell z.val := congrArg Subtype.val haz
  have hnorm : ‖(z.val : N)‖ = 1 := (D.boundary z.val).mp (heq ▸ a.property)
  have hs : OuterDisk.sphereDisk (OuterDisk.toSphere z) = z.val :=
    congrArg Subtype.val (OuterDisk.fromSphere_toSphere_boundary z hnorm)
  apply Subtype.ext
  change (a : X) = D.cell (OuterDisk.sphereDisk (OuterDisk.toSphere z))
  rw [hs]
  exact heq

/-- The retraction of the old neighbourhood onto the old set. -/
def EmbeddedCellAttachment.oldRetraction {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) [NormedSpace ℝ N] :
    C(D.oldNeighborhood, D.old) :=
  ClosedCover.mapOfClosedPieces D.oldInclusion D.outerInclusion D.oldInclusion_closed
    D.outerInclusion_closed D.oldNeighborhood_cover (ContinuousMap.id D.old)
    (D.attachingSphere.comp OuterDisk.toSphere) D.retractionMaps_agree

/-- The retraction fixes the old set. -/
theorem EmbeddedCellAttachment.oldRetraction_old {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) [NormedSpace ℝ N] (a : D.old) :
    D.oldRetraction (D.oldInclusion a) = a :=
  ClosedCover.mapOfClosedPieces_left D.oldInclusion D.outerInclusion D.oldInclusion_closed
    D.outerInclusion_closed D.oldNeighborhood_cover (ContinuousMap.id D.old)
    (D.attachingSphere.comp OuterDisk.toSphere) D.retractionMaps_agree a

/-- The retraction maps outer points to the attaching sphere. -/
theorem EmbeddedCellAttachment.oldRetraction_outer {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) [NormedSpace ℝ N]
    (z : OuterDisk.Space N) :
    D.oldRetraction (D.outerInclusion z) = D.attachingSphere (OuterDisk.toSphere z) :=
  ClosedCover.mapOfClosedPieces_right D.oldInclusion D.outerInclusion D.oldInclusion_closed
    D.outerInclusion_closed D.oldNeighborhood_cover (ContinuousMap.id D.old)
    (D.attachingSphere.comp OuterDisk.toSphere) D.retractionMaps_agree z

/-- The two pieces cover the cylinder over the neighbourhood. -/
theorem EmbeddedCellAttachment.neighborhood_time_cover {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    Set.range (Prod.map (id : (unitInterval) → (unitInterval)) D.oldInclusion) ∪
        Set.range (Prod.map (id : (unitInterval) → (unitInterval)) D.outerInclusion) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨t, x⟩
  have hx : x ∈ Set.range D.oldInclusion ∪ Set.range D.outerInclusion := by
    rw [D.oldNeighborhood_cover]
    trivial
  rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inl ⟨(t, a), rfl⟩
  · exact Or.inr ⟨(t, z), rfl⟩

/-- The stationary motion on the old part. -/
def EmbeddedCellAttachment.stationaryOld {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    C((unitInterval) × D.old, D.oldNeighborhood) :=
  D.oldInclusion.comp ContinuousMap.snd

/-- The annulus deformation on the outer part. -/
def EmbeddedCellAttachment.movingOuter {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    C((unitInterval) × OuterDisk.Space N, D.oldNeighborhood) :=
  D.outerInclusion.comp OuterDisk.deformation.toHomotopy.toContinuousMap

/-- The two motions agree on the overlap. -/
theorem EmbeddedCellAttachment.neighborhoodMotions_agree {N X : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) (a : (unitInterval) × D.old)
    (z : (unitInterval) × OuterDisk.Space N)
    (haz : Prod.map id D.oldInclusion a = Prod.map id D.outerInclusion z) :
    D.stationaryOld a = D.movingOuter z := by
  have ha : D.oldInclusion a.2 = D.outerInclusion z.2 := congrArg Prod.snd haz
  have heq : (a.2 : X) = D.cell z.2.val := congrArg Subtype.val ha
  have hn : ‖(z.2.val : N)‖ = 1 := (D.boundary z.2.val).mp (heq ▸ a.2.property)
  change D.oldInclusion a.2 = D.outerInclusion (OuterDisk.deformation (z.1, z.2))
  rw [OuterDisk.deformation.eq_fst z.1 hn]
  exact ha

/-- The glued deformation of the old neighbourhood. -/
def EmbeddedCellAttachment.neighborhoodMotion {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    C((unitInterval) × D.oldNeighborhood, D.oldNeighborhood) :=
  ClosedCover.mapOfClosedPieces (Prod.map id D.oldInclusion) (Prod.map id D.outerInclusion)
    (Topology.IsClosedEmbedding.id.prodMap D.oldInclusion_closed)
    (Topology.IsClosedEmbedding.id.prodMap D.outerInclusion_closed) D.neighborhood_time_cover
    D.stationaryOld D.movingOuter D.neighborhoodMotions_agree

/-- The motion is stationary on the old part. -/
theorem EmbeddedCellAttachment.neighborhoodMotion_old {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (t : (unitInterval)) (a : D.old) :
    D.neighborhoodMotion (t, D.oldInclusion a) = D.oldInclusion a :=
  ClosedCover.mapOfClosedPieces_left (Prod.map id D.oldInclusion)
    (Prod.map id D.outerInclusion) (Topology.IsClosedEmbedding.id.prodMap D.oldInclusion_closed)
    (Topology.IsClosedEmbedding.id.prodMap D.outerInclusion_closed) D.neighborhood_time_cover
    D.stationaryOld D.movingOuter D.neighborhoodMotions_agree (t, a)

/-- The motion computes the annulus deformation. -/
theorem EmbeddedCellAttachment.neighborhoodMotion_outer {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (t : (unitInterval)) (z : OuterDisk.Space N) :
    D.neighborhoodMotion (t, D.outerInclusion z) =
      D.outerInclusion (OuterDisk.deformation (t, z)) :=
  ClosedCover.mapOfClosedPieces_right (Prod.map id D.oldInclusion)
    (Prod.map id D.outerInclusion) (Topology.IsClosedEmbedding.id.prodMap D.oldInclusion_closed)
    (Topology.IsClosedEmbedding.id.prodMap D.outerInclusion_closed) D.neighborhood_time_cover
    D.stationaryOld D.movingOuter D.neighborhoodMotions_agree (t, z)

/-- The deformation retraction of the neighbourhood onto the old set. -/
def EmbeddedCellAttachment.oldDeformation {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    (ContinuousMap.id D.oldNeighborhood).HomotopyRel (D.oldInclusion.comp D.oldRetraction)
      (Set.range D.oldInclusion)
    where
  toFun := D.neighborhoodMotion
  continuous_toFun := D.neighborhoodMotion.continuous
  map_zero_left
    x := by
    have hx : x ∈ Set.range D.oldInclusion ∪ Set.range D.outerInclusion := by
      rw [D.oldNeighborhood_cover]
      trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · exact D.neighborhoodMotion_old 0 a
    · rw [D.neighborhoodMotion_outer]
      exact congrArg D.outerInclusion (OuterDisk.deformation.toHomotopy.map_zero_left z)
  map_one_left
    x := by
    change D.neighborhoodMotion (1, x) = D.oldInclusion (D.oldRetraction x)
    have hx : x ∈ Set.range D.oldInclusion ∪ Set.range D.outerInclusion := by
      rw [D.oldNeighborhood_cover]
      trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · rw [D.neighborhoodMotion_old, D.oldRetraction_old]
    · rw [D.neighborhoodMotion_outer, D.oldRetraction_outer]
      exact congrArg D.outerInclusion (OuterDisk.deformation.toHomotopy.map_one_left z)
  prop' t x
    hx := by
    obtain ⟨a, rfl⟩ := hx
    exact D.neighborhoodMotion_old t a

/-- The old set is homotopy equivalent to its neighbourhood. -/
def EmbeddedCellAttachment.oldHomotopyEquiv {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    D.old ≃ₕ D.oldNeighborhood where
  toFun := D.oldInclusion
  invFun := D.oldRetraction
  left_inv := by
    have heq : D.oldRetraction.comp D.oldInclusion = ContinuousMap.id D.old :=
      ContinuousMap.ext D.oldRetraction_old
    rw [heq]
  right_inv := ⟨D.oldDeformation.toHomotopy.symm⟩

/-! ### The disk annulus -/

/-- The open unit disk of `E`. -/
abbrev DiskAnnulus.OpenDisk (E : Type*) [NormedAddCommGroup E] :=
  { z : MorseHandle.UnitDisk E // ‖(z : E)‖ < 1 }

/-- The annulus `1/2 < ‖z‖ < 1` of `E`. -/
abbrev DiskAnnulus.Annulus (E : Type*) [NormedAddCommGroup E] :=
  { z : MorseHandle.UnitDisk E // 1 / 2 < ‖(z : E)‖ ∧ ‖(z : E)‖ < 1 }

/-- Annulus points are nonzero. -/
theorem DiskAnnulus.norm_pos {E : Type*} [NormedAddCommGroup E] (z : Annulus E) :
    0 < ‖(z.val : E)‖ := by linarith [z.property.1]

/-- The open unit disk is homeomorphic to the metric ball. -/
def DiskAnnulus.openDiskHomeomorph {E : Type*} [NormedAddCommGroup E] :
    OpenDisk E ≃ₜ Metric.ball (0 : E) 1
    where
  toFun z := ⟨z.val.val, mem_ball_zero_iff.mpr z.property⟩
  invFun
    z :=
    ⟨⟨z.val, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp z.property).le⟩,
      mem_ball_zero_iff.mp z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The open unit disk is contractible. -/
theorem DiskAnnulus.openDisk_contractible {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : ContractibleSpace (OpenDisk E) := by
  let : ContractibleSpace (Metric.ball (0 : E) 1) :=
    (convex_ball (0 : E) 1).contractibleSpace ⟨0, by simp⟩
  exact openDiskHomeomorph.contractibleSpace

/-- The radial projection of the annulus onto the sphere. -/
def DiskAnnulus.toSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(Annulus E, Metric.sphere (0 : E) 1) :=
  ⟨fun z => RadialExtension.direction (z.val : E) (norm_ne_zero_iff.mp (norm_pos z).ne'),
    (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
              (fun z => (norm_pos z).ne')).smul
          (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
      _⟩

/-- Scaling a unit vector by `3/4` has norm `3/4`. -/
theorem DiskAnnulus.norm_middle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Metric.sphere (0 : E) 1) : ‖(3 / 4 : ℝ) • (u : E)‖ = 3 / 4 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

/-- The radius-`3/4` sphere point inside the unit disk. -/
def DiskAnnulus.middleDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Metric.sphere (0 : E) 1) : MorseHandle.UnitDisk E :=
  ⟨(3 / 4 : ℝ) • (u : E), by
    rw [mem_closedBall_zero_iff, norm_middle]
    norm_num⟩

/-- The middle sphere point lies in the annulus. -/
theorem DiskAnnulus.middleDisk_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Metric.sphere (0 : E) 1) : 1 / 2 < ‖(middleDisk u : E)‖ ∧ ‖(middleDisk u : E)‖ < 1 := by
  change 1 / 2 < ‖(3 / 4 : ℝ) • (u : E)‖ ∧ ‖(3 / 4 : ℝ) • (u : E)‖ < 1
  rw [norm_middle]
  norm_num

/-- The middle sphere included into the annulus. -/
def DiskAnnulus.fromSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(Metric.sphere (0 : E) 1, Annulus E) :=
  ⟨fun u => ⟨middleDisk u, middleDisk_mem u⟩,
    ((continuous_const.smul continuous_subtype_val).subtype_mk _).subtype_mk _⟩

/-- Radial projection of the middle sphere is the identity. -/
theorem DiskAnnulus.toSphere_fromSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Metric.sphere (0 : E) 1) : toSphere (fromSphere u) = u := by
  apply Subtype.ext
  change ‖(3 / 4 : ℝ) • (u : E)‖⁻¹ • ((3 / 4 : ℝ) • (u : E)) = (u : E)
  rw [norm_middle, inv_smul_smul₀ (by norm_num : (3 / 4 : ℝ) ≠ 0)]

/-- The radial blend deforming an annulus point toward the middle sphere. -/
def DiskAnnulus.blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : (unitInterval) × Annulus E) : E :=
  ((1 - (q.1 : ℝ)) + (q.1 : ℝ) * ((3 / 4 : ℝ) / ‖(q.2.val : E)‖)) • (q.2.val : E)

/-- The annulus blend is continuous. -/
theorem DiskAnnulus.continuous_blendVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Continuous (blendVector (E := E)) := by
  have ht : Continuous (fun q : (unitInterval) × Annulus E => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous (fun q : (unitInterval) × Annulus E => (q.2.val : E)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact
    ((continuous_const.sub ht).add
          (ht.mul (continuous_const.div hz.norm (fun q => (norm_pos q.2).ne')))).smul
      hz

/-- The blend norm interpolates to `3/4`. -/
theorem DiskAnnulus.norm_blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : (unitInterval)) (z : Annulus E) :
    ‖blendVector (t, z)‖ = (1 - (t : ℝ)) * ‖(z.val : E)‖ + (t : ℝ) * (3 / 4) := by
  have hscale : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * ((3 / 4 : ℝ) / ‖(z.val : E)‖) :=
    add_nonneg (sub_nonneg.mpr t.property.2)
      (mul_nonneg t.property.1 (div_nonneg (by norm_num) (norm_pos z).le))
  rw [blendVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale, add_mul, mul_assoc,
    div_mul_cancel₀ _ (norm_pos z).ne']

/-- The blend stays in the annulus. -/
theorem DiskAnnulus.norm_blendVector_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (t : (unitInterval)) (z : Annulus E) :
    1 / 2 < ‖blendVector (t, z)‖ ∧ ‖blendVector (t, z)‖ < 1 := by
  rw [norm_blendVector]
  have h :=
    (convex_Ioo (𝕜 := ℝ) (1 / 2 : ℝ) 1) z.property (by norm_num : (3 / 4 : ℝ) ∈ Ioo (1 / 2) 1)
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
  exact h

/-- The deformation of the annulus toward the middle sphere. -/
def DiskAnnulus.blend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : (unitInterval) × Annulus E) : Annulus E :=
  ⟨⟨blendVector q, mem_closedBall_zero_iff.mpr (norm_blendVector_mem q.1 q.2).2.le⟩,
    norm_blendVector_mem q.1 q.2⟩

/-- The annulus deformation is continuous. -/
theorem DiskAnnulus.continuous_blend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (blend (E := E)) :=
  (continuous_blendVector.subtype_mk _).subtype_mk _

/-- The deformation retraction of the annulus onto the middle sphere. -/
def DiskAnnulus.deformation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (ContinuousMap.id (Annulus E)).Homotopy (fromSphere.comp toSphere)
    where
  toFun := blend
  continuous_toFun := continuous_blend
  map_zero_left
    z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector]
  map_one_left
    z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector, fromSphere, middleDisk, toSphere, RadialExtension.direction,
      div_eq_mul_inv, smul_smul]

/-- The annulus is homotopy equivalent to the sphere. -/
def DiskAnnulus.sphereHomotopyEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Metric.sphere (0 : E) 1 ≃ₕ Annulus E
    where
  toFun := fromSphere
  invFun := toSphere
  left_inv := by
    have heq : toSphere.comp fromSphere = ContinuousMap.id (Metric.sphere (0 : E) 1) :=
      ContinuousMap.ext toSphere_fromSphere
    rw [heq]
  right_inv := ⟨deformation.symm⟩

/-- The disk patch is contractible. -/
theorem EmbeddedCellAttachment.diskPatch_contractible {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    ContractibleSpace D.diskPatch := by
  let : ContractibleSpace (DiskAnnulus.OpenDisk N) :=
    DiskAnnulus.openDisk_contractible
  exact D.diskHomeomorph.symm.contractibleSpace

/-- The overlap is homotopy equivalent to the sphere. -/
def EmbeddedCellAttachment.overlapSphereEquiv {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    Metric.sphere (0 : N) 1 ≃ₕ ↥(D.oldNeighborhood ∩ D.diskPatch) :=
  DiskAnnulus.sphereHomotopyEquiv.trans D.overlapHomeomorph.toHomotopyEquiv

/-- The map from the overlap to the old set through the retraction. -/
def EmbeddedCellAttachment.overlapOldMap {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X) :
    C(↥(D.oldNeighborhood ∩ D.diskPatch), D.old) :=
  D.oldRetraction.comp (ContinuousMap.inclusion Set.inter_subset_left)

/-- The overlap map computes the attaching sphere. -/
theorem EmbeddedCellAttachment.overlapOldMap_sphere {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : EmbeddedCellAttachment N X)
    (u : Metric.sphere (0 : N) 1) :
    D.overlapOldMap (D.overlapSphereEquiv u) = D.attachingSphere u := by
  let z : OuterDisk.Space N :=
    ⟨(DiskAnnulus.fromSphere u).val, (DiskAnnulus.fromSphere u).property.1⟩
  change D.oldRetraction (D.outerInclusion z) = D.attachingSphere u
  rw [D.oldRetraction_outer]
  apply congrArg D.attachingSphere
  exact DiskAnnulus.toSphere_fromSphere u

/-- The overlap map composed with the sphere equivalence is the attaching map. -/
theorem EmbeddedCellAttachment.overlapOldMap_comp_sphere {N X : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : EmbeddedCellAttachment N X) :
    D.overlapOldMap.comp D.overlapSphereEquiv.toFun = D.attachingSphere :=
  ContinuousMap.ext D.overlapOldMap_sphere
