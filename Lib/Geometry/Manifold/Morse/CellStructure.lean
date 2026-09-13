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
import Lib.Topology.Homotopy.CellAttachment
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Topology.Homotopy.CylinderHEP
import Lib.Analysis.Calculus.MorseLemma
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.Geometry.Manifold.ChartedSpace.Transport

/-!
# The finite cell structure of a compact smooth manifold

Every compact smooth manifold admits a Morse function and therefore has the homotopy type
of a finite cell complex with one cell per critical point (Milnor, Morse Theory, Thm 3.5):
`MorseCells.*`, `Attachment.*`, `CoreAttachment.*`,
`AttachmentMaps.*`, `Handle.*`, `FiniteCells.*`.

## Main definitions and results

* `FiniteCells.Built` : the inductive description of the built-up cell complex.
* `MorseCells.built_of_compact_smooth_manifold` : the theorem (in `Hopf/`, see
  obstruction note in Lib/reports/A.md).
* `FiniteCells.RelativeDiskLifting` : the relative lifting datum.

## References

* [John Milnor, *Morse Theory*][milnor63], Theorem 3.5

## Tags

finite cell complex, Morse cells, homotopy type
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Union and cylinder quotients -/

/-- The union of a space and an attachment along a map. -/
abbrev Attachment.Union {K M : Type*} [TopologicalSpace K] [TopologicalSpace M] (A : Set M)
    (h : C(K, M)) :=
  ↥(A ∪ Set.range h)

/-- The sum quotient realizing the union. -/
def Attachment.sumQuotient {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (h : C(K, M)) : C(A ⊕ K, Attachment.Union A h) :=
  ⟨ClosedAttachment.sumMap A h, ClosedAttachment.continuous_sumMap A h⟩

/-- The sum quotient map is surjective. -/
theorem Attachment.sumQuotient_surjective {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (h : C(K, M)) : Function.Surjective (sumQuotient A h) := by
  rintro ⟨x, hx | ⟨k, rfl⟩⟩
  · exact ⟨.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨.inr k, rfl⟩

/-- The cylinder quotient of the attaching map. -/
def Attachment.cylinderQuotient {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (h : C(K, M)) :
    C((unitInterval) × (A ⊕ K), (unitInterval) × Attachment.Union A h) :=
  (ContinuousMap.id (unitInterval)).prodMap (sumQuotient A h)

/-- The cylinder quotient map is surjective. -/
theorem Attachment.cylinderQuotient_surjective {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (h : C(K, M)) : Function.Surjective (cylinderQuotient A h) :=
  by
  rintro ⟨t, x⟩
  obtain ⟨z, rfl⟩ := sumQuotient_surjective A h x
  exact ⟨(t, z), rfl⟩

/-- The cylinder quotient is a quotient map. -/
theorem Attachment.cylinderQuotient_isQuotientMap {K M : Type*} [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (h : C(K, M)) :
    Topology.IsQuotientMap (cylinderQuotient A h) :=
  .of_surjective_continuous (cylinderQuotient_surjective A h) (cylinderQuotient A h).continuous

/-! ### The union family -/

/-- A family defined on the sum by cases. -/
def Attachment.familyOnSum {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) {r : C(K, K)}
    (H : (ContinuousMap.id K).HomotopyRel r B) :
    C((unitInterval) × (A ⊕ K), Attachment.Union A h)
    where
  toFun
    p :=
    match p.2 with
    | .inl a => ⟨a.val, Or.inl a.property⟩
    | .inr k => ⟨h (H (p.1, k)), Or.inr ⟨H (p.1, k), rfl⟩⟩
  continuous_toFun := by
    have ha :
      Continuous
        (fun p : (unitInterval) × A =>
          (⟨p.2.val, Or.inl p.2.property⟩ : Attachment.Union A h)) :=
      (continuous_subtype_val.comp continuous_snd).subtype_mk _
    have hk :
      Continuous
        (fun p : (unitInterval) × K =>
          (⟨h (H p), Or.inr ⟨H p, rfl⟩⟩ : Attachment.Union A h)) :=
      (h.continuous.comp H.continuous).subtype_mk _
    convert
      (ha.sumElim hk).comp
        (Homeomorph.prodSumDistrib : (unitInterval) × (A ⊕ K) ≃ₜ _).continuous using
      1
    funext p
    rcases p with ⟨t, a | k⟩ <;> rfl

/-- The sum family is constant on quotient fibres. -/
theorem Attachment.familyOnSum_constant_on_fibres {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (B : Set K) (h : C(K, M)) {r : C(K, K)}
    (H : (ContinuousMap.id K).HomotopyRel r B) (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) (p q : (unitInterval) × (A ⊕ K))
    (heq : cylinderQuotient A h p = cylinderQuotient A h q) :
    familyOnSum A B h H p = familyOnSum A B h H q := by
  rcases p with ⟨t, a⟩
  rcases q with ⟨s, b⟩
  have ht : t = s := congrArg Prod.fst heq
  subst s
  have hab : sumQuotient A h a = sumQuotient A h b := congrArg Prod.snd heq
  have hv := congrArg Subtype.val hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact Subtype.ext hv
    | inr k =>
      change a.val = h k at hv
      have hk : k ∈ B := (hface k).mp (hv ▸ a.property)
      apply Subtype.ext
      change a.val = h (H (t, k))
      rw [H.eq_fst t hk]
      exact hv
  | inr k =>
    cases b with
    | inl b =>
      change h k = b.val at hv
      have hk : k ∈ B := (hface k).mp (hv.symm ▸ b.property)
      apply Subtype.ext
      change h (H (t, k)) = b.val
      rw [H.eq_fst t hk]
      exact hv
    | inr l =>
      have hkl : k = l := hinj hv
      subst l
      rfl

/-- The family descending to the union. -/
def Attachment.unionFamily {K M : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (B : Set K) (h : C(K, M))
    {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B) (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) :
    C((unitInterval) × Attachment.Union A h, Attachment.Union A h) :=
  (cylinderQuotient_isQuotientMap A h).lift (familyOnSum A B h H)
    (familyOnSum_constant_on_fibres A B h H hinj hface)

/-- The union family computes the sum family. -/
@[simp]
theorem Attachment.unionFamily_apply {K M : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (B : Set K) (h : C(K, M))
    {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B) (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) (t : (unitInterval)) (z : A ⊕ K) :
    unionFamily A B h H hinj hface (t, sumQuotient A h z) = familyOnSum A B h H (t, z) :=
  ContinuousMap.congr_fun
    ((cylinderQuotient_isQuotientMap A h).lift_comp (familyOnSum A B h H)
      (familyOnSum_constant_on_fibres A B h H hinj hface))
    (t, z)

/-- The union family is fixed on the lower part. -/
theorem Attachment.unionFamily_fixed_lower {K M : Type*} [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (B : Set K)
    (h : C(K, M)) {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B)
    (hinj : Function.Injective h) (hface : ∀ k, h k ∈ A ↔ k ∈ B) (t : (unitInterval)) (a : A) :
    unionFamily A B h H hinj hface (t, ⟨a.val, Or.inl a.property⟩) = ⟨a.val, Or.inl a.property⟩ :=
  unionFamily_apply A B h H hinj hface t (.inl a)

/-- The union family on the handle. -/
theorem Attachment.unionFamily_on_handle {K M : Type*} [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (B : Set K)
    (h : C(K, M)) {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B)
    (hinj : Function.Injective h) (hface : ∀ k, h k ∈ A ↔ k ∈ B) (t : (unitInterval)) (k : K) :
    (unionFamily A B h H hinj hface (t, ⟨h k, Or.inr ⟨k, rfl⟩⟩)).val = h (H (t, k)) :=
  congrArg Subtype.val (unionFamily_apply A B h H hinj hface t (.inr k))

/-- The union family at parameter zero. -/
theorem Attachment.unionFamily_zero {K M : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (B : Set K) (h : C(K, M))
    {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B) (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) (x : Attachment.Union A h) :
    unionFamily A B h H hinj hface (0, x) = x := by
  obtain ⟨z, rfl⟩ := sumQuotient_surjective A h x
  rw [unionFamily_apply]
  cases z with
  | inl a => rfl
  | inr k =>
    apply Subtype.ext
    exact congrArg h (H.apply_zero k)

/-! ### Handle interpolation and deformation -/

/-- The interpolation between a point and its handle projection. -/
def Handle.interpolate {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (t : (unitInterval)) (z : Space (N := N) (P := P)) :
    Space (N := N) (P := P) :=
  (⟨(1 - (t : ℝ)) • (z.1 : N) + (t : ℝ) • ((retraction z).1 : N),
      (convex_closedBall (0 : N) 1 : Convex ℝ _) z.1.property (retraction z).1.property
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩,
    ⟨(1 - (t : ℝ)) • (z.2 : P) + (t : ℝ) • ((retraction z).2 : P),
      (convex_closedBall (0 : P) 1 : Convex ℝ _) z.2.property (retraction z).2.property
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩)

/-- The handle interpolation is continuous. -/
theorem Handle.continuous_interpolate {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] :
    Continuous (fun tz : (unitInterval) × Space (N := N) (P := P) => interpolate tz.1 tz.2) := by
  have ht : Continuous (fun tz : (unitInterval) × Space (N := N) (P := P) => (tz.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun tz : (unitInterval) × Space (N := N) (P := P) => (tz.2.1 : N)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hv : Continuous (fun tz : (unitInterval) × Space (N := N) (P := P) => (tz.2.2 : P)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hr : Continuous (fun tz : (unitInterval) × Space (N := N) (P := P) => retraction tz.2) :=
    retraction.continuous.comp continuous_snd
  exact
    (((continuous_const.sub ht).smul hu).add
            (ht.smul (continuous_subtype_val.comp (continuous_fst.comp hr)))).subtype_mk
        _ |>.prodMk
      ((((continuous_const.sub ht).smul hv).add
            (ht.smul (continuous_subtype_val.comp (continuous_snd.comp hr)))).subtype_mk
        _)

/-- The interpolation at zero is the point. -/
@[simp]
theorem Handle.interpolate_zero {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Space (N := N) (P := P)) :
    interpolate 0 z = z := by apply Prod.ext <;> apply Subtype.ext <;> simp [interpolate]

/-- The interpolation at one is the handle projection. -/
@[simp]
theorem Handle.interpolate_one {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Space (N := N) (P := P)) :
    interpolate 1 z = retraction z := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [interpolate]

/-- The interpolation fixes the lower part. -/
theorem Handle.interpolate_fixed {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (t : (unitInterval)) (z : Space (N := N) (P := P))
    (hz : z ∈ faceCore) : interpolate t z = z := by
  have hr := retraction_eq_self z hz
  apply Prod.ext <;> apply Subtype.ext <;> simp [interpolate, hr, ← add_smul]

/-- The deformation retract of the union onto the handle core. -/
def Handle.deformation {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (ContinuousMap.id (Space (N := N) (P := P))).HomotopyRel retraction faceCore
    where
  toFun tz := interpolate tz.1 tz.2
  continuous_toFun := continuous_interpolate
  map_zero_left := interpolate_zero
  map_one_left := interpolate_one
  prop' := interpolate_fixed

/-! ### The core attachment -/

/-- The core of an attachment: the union with the core disk. -/
abbrev CoreAttachment.Core {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P] :
    Set (Handle.Space (N := N) (P := P)) :=
  {z | (z.2 : P) = 0}

/-- A face of the core attachment. -/
abbrev CoreAttachment.Face {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P] :
    Set (Handle.Space (N := N) (P := P)) :=
  {z | ‖(z.1 : N)‖ = 1}

/-- The face deformation of the core attachment. -/
def CoreAttachment.faceDeformation {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (ContinuousMap.id (Handle.Space (N := N) (P := P))).HomotopyRel
      Handle.retraction Face
    where
  __ := Handle.deformation.toHomotopy
  prop' t z hz := Handle.interpolate_fixed t z (Or.inl hz)

/-- The union of all core faces. -/
abbrev CoreAttachment.CoreUnion {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] (A : Set M)
    (h : C(Handle.Space (N := N) (P := P), M)) :=
  ↥(A ∪ h '' Core)

/-- The deformation family of the core attachment. -/
def CoreAttachment.family {N P M : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N] [FiniteDimensional ℝ P]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) :
    C((unitInterval) × Attachment.Union A h, Attachment.Union A h) :=
  Attachment.unionFamily A Face h faceDeformation hinj hface

/-- The core family at parameter zero. -/
theorem CoreAttachment.family_zero {N P M : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N] [FiniteDimensional ℝ P]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) (x : Attachment.Union A h) :
    family A h hinj hface (0, x) = x :=
  Attachment.unionFamily_zero A Face h faceDeformation hinj hface x

/-- The core family is fixed on the lower part. -/
theorem CoreAttachment.family_fixed_lower {N P M : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) (t : (unitInterval)) (a : A) :
    family A h hinj hface (t, ⟨a.val, Or.inl a.property⟩) = ⟨a.val, Or.inl a.property⟩ :=
  Attachment.unionFamily_fixed_lower A Face h faceDeformation hinj hface t a

/-- The core family on the handle. -/
theorem CoreAttachment.family_on_handle {N P M : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) (t : (unitInterval))
    (z : Handle.Space (N := N) (P := P)) :
    (family A h hinj hface (t, ⟨h z, Or.inr ⟨z, rfl⟩⟩)).val = h (Handle.interpolate t z) :=
  Attachment.unionFamily_on_handle A Face h faceDeformation hinj hface t z

/-- The core family at time one lands in the core union. -/
theorem CoreAttachment.family_one_mem_coreUnion {N P M : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) (x : Attachment.Union A h) :
    (family A h hinj hface (1, x)).val ∈ A ∪ h '' Core := by
  rcases x with ⟨x, hx | ⟨z, rfl⟩⟩
  · have he := family_fixed_lower A h hinj hface 1 ⟨x, hx⟩
    exact Or.inl (congrArg Subtype.val he ▸ hx)
  · rw [family_on_handle, Handle.interpolate_one]
    rcases Handle.retraction_mem_faceCore z with hz | hz
    · exact Or.inl ((hface (Handle.retraction z)).mpr hz)
    · exact Or.inr ⟨Handle.retraction z, hz, rfl⟩

/-- The inclusion of the core union into the attachment. -/
def CoreAttachment.inclusion {N P M : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    [TopologicalSpace M] (A : Set M) (h : C(Handle.Space (N := N) (P := P), M)) :
    C(CoreUnion A h, Attachment.Union A h) :=
  ⟨fun x =>
    ⟨x.val,
      x.property.elim Or.inl (fun hx => Or.inr (by obtain ⟨z, _, hz⟩ := hx; exact ⟨z, hz⟩))⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The retraction of the attachment onto the core union. -/
def CoreAttachment.reduce {N P M : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N] [FiniteDimensional ℝ P]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) : C(Attachment.Union A h, CoreUnion A h) :=
  ⟨fun x => ⟨(family A h hinj hface (1, x)).val, family_one_mem_coreUnion A h hinj hface x⟩,
    ((continuous_subtype_val.comp (family A h hinj hface).continuous).comp
          (continuous_const.prodMk continuous_id)).subtype_mk
      _⟩

/-- The core family fixes the core union. -/
theorem CoreAttachment.family_fixed_coreUnion {N P M : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) (t : (unitInterval)) (x : CoreUnion A h) :
    family A h hinj hface (t, CoreAttachment.inclusion A h x) =
      CoreAttachment.inclusion A h x := by
  rcases x with ⟨x, hx | ⟨z, hz, rfl⟩⟩
  · exact family_fixed_lower A h hinj hface t ⟨x, hx⟩
  · apply Subtype.ext
    change (family A h hinj hface (t, ⟨h z, Or.inr ⟨z, rfl⟩⟩)).val = h z
    rw [family_on_handle, Handle.interpolate_fixed t z (Or.inr hz)]

/-- The core union is a deformation retract of the attachment. -/
def CoreAttachment.coreUnionHomotopyEquiv {N P M : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) : CoreUnion A h ≃ₕ Attachment.Union A h
    where
  toFun := CoreAttachment.inclusion A h
  invFun := reduce A h hinj hface
  left_inv := by
    have he :
      (reduce A h hinj hface).comp (CoreAttachment.inclusion A h) =
        ContinuousMap.id (CoreUnion A h) := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      change (family A h hinj hface (1, CoreAttachment.inclusion A h x)).val = x.val
      exact congrArg Subtype.val (family_fixed_coreUnion A h hinj hface 1 x)
    rw [he]
  right_inv := by
    let H :
      (ContinuousMap.id (Attachment.Union A h)).Homotopy
        ((CoreAttachment.inclusion A h).comp (reduce A h hinj hface)) :=
      { toContinuousMap := family A h hinj hface
        map_zero_left := family_zero A h hinj hface
        map_one_left := fun _ => rfl }
    exact ⟨H.symm⟩

/-! ### Core cells -/

/-- The core cell's dimension is the handle index. -/
theorem MorseCells.core_dimension_le {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.NegativeCoordinates ≤ Module.finrank ℝ E := by
  classical
  change Module.finrank ℝ (EuclideanSpace ℝ (MorseHandle.Negative c.weights)) ≤ _
  rw [finrank_euclideanSpace]
  exact (Fintype.card_subtype_le (fun i => c.weights i = -1)).trans_eq (Fintype.card_fin _)

/-- The characteristic map of a core cell. -/
def MorseCells.coreCellMap {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(MorseHandle.UnitDisk c.NegativeCoordinates, M) :=
  (c.attachingHandleMap ρ hρ hblock).comp
    ⟨fun u => (u, ⟨0, by simp⟩), continuous_id.prodMk continuous_const⟩

/-- The core cell map is injective on the interior. -/
theorem MorseCells.coreCellMap_injective {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Function.Injective (coreCellMap c ρ hρ hblock) := by
  intro u v h
  exact congrArg Prod.fst (c.attachingHandleMap_injective ρ hρ hblock h)

/-- A core cell image point lies in the lower part exactly on the boundary. -/
theorem MorseCells.coreCellMap_lower_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (u : MorseHandle.UnitDisk c.NegativeCoordinates) :
    f (coreCellMap c ρ hρ hblock u) ≤ f p - ρ ^ 2 ↔ ‖(u : c.NegativeCoordinates)‖ = 1 :=
  c.attachingHandleMap_lower_iff ρ hρ hblock (u, ⟨0, by simp⟩)

/-- The image of the core cell map. -/
theorem MorseCells.image_core {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    (c.attachingHandleMap ρ hρ hblock) '' CoreAttachment.Core =
      Set.range (coreCellMap c ρ hρ hblock) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.1, ?_⟩
    apply congrArg (c.attachingHandleMap ρ hρ hblock)
    exact Prod.ext rfl (Subtype.ext hz.symm)
  · rintro ⟨u, rfl⟩
    exact ⟨(u, ⟨0, by simp⟩), rfl, rfl⟩

/-- The handle attachment is homotopy equivalent to the cell attachment. -/
def MorseCells.cellHandleHomotopyEquiv {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    [T2Space M] [CompactSpace M] (hf : Continuous f) :
    ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
        {u : MorseHandle.UnitDisk c.NegativeCoordinates | ‖(u : c.NegativeCoordinates)‖ = 1}
        (coreCellMap c ρ hρ hblock) ≃ₕ
      ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
        {z | ‖(z.1 : c.NegativeCoordinates)‖ = 1} (c.attachingHandleMap ρ hρ hblock) := by
  let A := {x : M | f x ≤ f p - ρ ^ 2}
  have hA : IsCompact A := (isClosed_le hf continuous_const).isCompact
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let cell :=
    ClosedAttachment.unionHomeomorph A _ (coreCellMap c ρ hρ hblock) hA
      (coreCellMap_injective c ρ hρ hblock) (coreCellMap_lower_iff c ρ hρ hblock)
  let core :=
    CoreAttachment.coreUnionHomotopyEquiv A (c.attachingHandleMap ρ hρ hblock)
      (c.attachingHandleMap_injective ρ hρ hblock) (c.attachingHandleMap_lower_iff ρ hρ hblock)
  let mark := Homeomorph.setCongr (congrArg (fun S : Set M => A ∪ S) (image_core c ρ hρ hblock))
  exact
    cell.toHomotopyEquiv.trans
      (mark.symm.toHomotopyEquiv.trans
        (core.trans (c.attachingHandleUnionHomeomorph hf ρ hρ hblock).symm.toHomotopyEquiv))

/-! ### Finite cell attachment -/

/-- A finite cell complex built by successive attachments. -/
inductive FiniteCells.Built (d : ℕ) : (X : Type) → [TopologicalSpace X] → Prop
  | empty (X : Type) [TopologicalSpace X] [IsEmpty X] : Built d X
  |
  equiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (h : Built d X) :
    Built d Y
  |
  attach {V M : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace M] (A : Set M) (h : C(MorseHandle.UnitDisk V, M))
    (hboundary : ∀ u : MorseHandle.UnitDisk V, ‖(u : V)‖ = 1 → h u ∈ A)
    (hdim : Module.finrank ℝ V ≤ d) (hA : Built d A) :
    Built d (ClosedAttachment.Space A {u : MorseHandle.UnitDisk V | ‖(u : V)‖ = 1} h)

/-! ### Attaching maps -/

/-- The inclusion of the old complex into the attachment. -/
def AttachmentMaps.oldInclusion {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) : C(A, ClosedAttachment.Space A B h) :=
  ⟨fun a => Quot.mk _ (.inl a), continuous_quot_mk.comp continuous_inl⟩

/-- The inclusion of the cell into the attachment. -/
def AttachmentMaps.cellInclusion {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) : C(K, ClosedAttachment.Space A B h) :=
  ⟨fun k => Quot.mk _ (.inr k), continuous_quot_mk.comp continuous_inr⟩

/-- The attaching map agrees on the boundary. -/
theorem AttachmentMaps.boundary_eq {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) (a : A) (k : K) (hk : k ∈ B) (ha : a.val = h k) :
    oldInclusion A B h a = cellInclusion A B h k :=
  Quot.sound ⟨hk, ha⟩

/-- The sum map respects the quotient relation. -/
theorem AttachmentMaps.sum_respects {K M X : Type*} [TopologicalSpace K]
    [TopologicalSpace M] [TopologicalSpace X] (A : Set M) (B : Set K) (h : C(K, M)) (f : C(A, X))
    (g : C(K, X)) (hc : ∀ a k, k ∈ B → a.val = h k → f a = g k) (a b : A ⊕ K)
    (hab : ClosedAttachment.Rel A B h a b) : Sum.elim f g a = Sum.elim f g b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact hab.elim
    | inr k => exact hc a k hab.1 hab.2
  | inr k => cases b <;> exact hab.elim

/-- The glued attachment of a cell. -/
def AttachmentMaps.glue {K M X : Type*} [TopologicalSpace K] [TopologicalSpace M]
    [TopologicalSpace X] (A : Set M) (B : Set K) (h : C(K, M)) (f : C(A, X)) (g : C(K, X))
    (hc : ∀ a k, k ∈ B → a.val = h k → f a = g k) : C(ClosedAttachment.Space A B h, X)
    where
  toFun := Quot.lift (Sum.elim f g) (sum_respects A B h f g hc)
  continuous_toFun := continuous_quot_lift _ (continuous_sum_dom.mpr ⟨f.continuous, g.continuous⟩)

/-- The family on the old part. -/
def AttachmentMaps.familyOld {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
    (A : Set M) (F : C((unitInterval) × A, X)) (t : (unitInterval)) : C(A, X) :=
  F.comp ⟨fun a => (t, a), continuous_const.prodMk continuous_id⟩

/-- The family on the cell. -/
def AttachmentMaps.familyCell {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
    (G : C((unitInterval) × K, X)) (t : (unitInterval)) : C(K, X) :=
  G.comp ⟨fun k => (t, k), continuous_const.prodMk continuous_id⟩

/-- The glued deformation family. -/
def AttachmentMaps.glueFamily {K M X : Type*} [TopologicalSpace K] [TopologicalSpace M]
    [TopologicalSpace X] (A : Set M) (B : Set K) (h : C(K, M)) (F : C((unitInterval) × A, X))
    (G : C((unitInterval) × K, X)) (hFG : ∀ t a k, k ∈ B → a.val = h k → F (t, a) = G (t, k)) :
    C((unitInterval) × ClosedAttachment.Space A B h, X)
    where
  toFun p := glue A B h (familyOld A F p.1) (familyCell G p.1) (hFG p.1) p.2
  continuous_toFun := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    have hc :
      Continuous (fun p : ((unitInterval) × A) ⊕ ((unitInterval) × K) => Sum.elim F G p) :=
      continuous_sum_dom.mpr ⟨F.continuous, G.continuous⟩
    convert hc.comp (Homeomorph.prodSumDistrib : (unitInterval) × (A ⊕ K) ≃ₜ _).continuous using 1
    funext p
    rcases p with ⟨t, a | k⟩ <;> rfl

/-! ### Relative disk lifting -/

/-- A relative disk lifting through a cell attachment. -/
def FiniteCells.RelativeDiskLifting {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X, Y)) (d : ℕ) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Module.finrank ℝ V ≤ d →
      ∀ (a : C(DiskCylinder.Sphere (E := V), X))
        (u : C(DiskCylinder.Disk (E := V), Y))
        (H : C((unitInterval) × DiskCylinder.Sphere (E := V), Y)),
        (∀ s, H (0, s) = F (a s)) →
          (∀ s, H (1, s) = u (DiskCylinder.boundaryToDisk s)) →
            ∃ (v : C(DiskCylinder.Disk (E := V), X)) (G :
              C((unitInterval) × DiskCylinder.Disk (E := V), Y)),
              (∀ s, v (DiskCylinder.boundaryToDisk s) = a s) ∧
                (∀ z, G (0, z) = F (v z)) ∧
                  (∀ z, G (1, z) = u z) ∧
                    ∀ t s, G (t, DiskCylinder.boundaryToDisk s) = H (t, s)

/-- Maps into the target lift through the attachment. -/
def FiniteCells.MapsLift {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X, Y)) (Z : Type) [TopologicalSpace Z] : Prop :=
  ∀ u : C(Z, Y), ∃ v : C(Z, X), (F.comp v).Homotopic u

/-- The empty attachment lifts trivially. -/
theorem FiniteCells.mapsLift_empty {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X, Y)) (Z : Type) [TopologicalSpace Z] [IsEmpty Z] : MapsLift F Z := by
  intro u
  let v : C(Z, X) := ⟨isEmptyElim, continuous_iff_continuousAt.mpr (fun z => isEmptyElim z)⟩
  refine ⟨v, ?_⟩
  have he : F.comp v = u := ContinuousMap.ext (fun z => isEmptyElim z)
  rw [he]

/-- Lifting is preserved by equivalence. -/
theorem FiniteCells.mapsLift_equiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X, Y)) {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W] (e : Z ≃ₕ W)
    (h : MapsLift F Z) : MapsLift F W := by
  intro u
  obtain ⟨v, hv⟩ := h (u.comp e.toFun)
  refine ⟨v.comp e.invFun, ?_⟩
  have h₁ := hv.comp (ContinuousMap.Homotopic.refl e.invFun)
  have h₂ := (ContinuousMap.Homotopic.refl u).comp e.right_inv
  simpa only [ContinuousMap.comp_assoc, ContinuousMap.comp_id] using h₁.trans h₂

/-- Lifting extends across one attachment. -/
theorem FiniteCells.mapsLift_attach {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X, Y)) {d : ℕ} (hF : RelativeDiskLifting F d) {V M : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace M] (A : Set M)
    (h : C(MorseHandle.UnitDisk V, M))
    (hb : ∀ z : MorseHandle.UnitDisk V, ‖(z : V)‖ = 1 → h z ∈ A)
    (hd : Module.finrank ℝ V ≤ d) (hA : MapsLift F A) :
    MapsLift F
      (ClosedAttachment.Space A {z : MorseHandle.UnitDisk V | ‖(z : V)‖ = 1} h) := by
  intro u
  let B : Set (MorseHandle.UnitDisk V) := {z | ‖(z : V)‖ = 1}
  let iA := AttachmentMaps.oldInclusion A B h
  let iD := AttachmentMaps.cellInclusion A B h
  obtain ⟨vA, ⟨HA⟩⟩ := hA (u.comp iA)
  let b : C(DiskCylinder.Sphere (E := V), A) :=
    ⟨fun s =>
      ⟨h (DiskCylinder.boundaryToDisk s),
        hb (DiskCylinder.boundaryToDisk s) (mem_sphere_zero_iff_norm.mp s.property)⟩,
      (h.continuous.comp DiskCylinder.boundaryToDisk.continuous).subtype_mk _⟩
  let H : C((unitInterval) × DiskCylinder.Sphere (E := V), Y) :=
    HA.toContinuousMap.comp ((ContinuousMap.id (unitInterval)).prodMap b)
  have h0 : ∀ s, H (0, s) = F ((vA.comp b) s) := fun s => HA.map_zero_left (b s)
  have h1 : ∀ s, H (1, s) = (u.comp iD) (DiskCylinder.boundaryToDisk s) := by
    intro s
    change HA (1, b s) = u (iD (DiskCylinder.boundaryToDisk s))
    exact
      (HA.map_one_left (b s)).trans
        (congrArg u
          (AttachmentMaps.boundary_eq A B h (b s) (DiskCylinder.boundaryToDisk s)
            (mem_sphere_zero_iff_norm.mp s.property) rfl))
  obtain ⟨vD, GD, hvD, hGD0, hGD1, hGDside⟩ := hF V hd (vA.comp b) (u.comp iD) H h0 h1
  have hcompat : ∀ a z, z ∈ B → a.val = h z → vA a = vD z := by
    intro a z hz ha
    let s : DiskCylinder.Sphere (E := V) := ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
    have hab : a = b s := Subtype.ext ha
    exact (congrArg vA hab).trans (hvD s).symm
  let v := AttachmentMaps.glue A B h vA vD hcompat
  have hhom : ∀ t a z, z ∈ B → a.val = h z → HA (t, a) = GD (t, z) := by
    intro t a z hz ha
    let s : DiskCylinder.Sphere (E := V) := ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
    have hab : a = b s := Subtype.ext ha
    exact (congrArg (fun a => HA (t, a)) hab).trans (hGDside t s).symm
  refine
    ⟨v, ⟨{
          toContinuousMap := AttachmentMaps.glueFamily A B h HA.toContinuousMap GD hhom
          map_zero_left := ?_
          map_one_left := ?_ }⟩⟩
  · intro z
    induction z using Quot.inductionOn with
    | _ z =>
      cases z with
      | inl a => exact HA.map_zero_left a
      | inr z => exact hGD0 z
  · intro z
    induction z using Quot.inductionOn with
    | _ z =>
      cases z with
      | inl a => exact HA.map_one_left a
      | inr z => exact hGD1 z

/-- A built cell complex lifts maps. -/
theorem FiniteCells.mapsLift_of_built {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (F : C(X, Y)) {d : ℕ} (hF : RelativeDiskLifting F d) {Z : Type}
    [TopologicalSpace Z] (hZ : Built d Z) : MapsLift F Z := by
  induction hZ with
  | empty Z => exact mapsLift_empty F Z
  | equiv e _ ih => exact mapsLift_equiv F e ih
  | attach A h hb hd _ ih => exact mapsLift_attach F hF A h hb hd ih

/-! ### Morse cells -/

/-- A Morse cell attachment below a level exists. -/
theorem MorseCells.exists_morse_cell_attachment_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f) {p : M}
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hunique : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x = f p → x = p) {R : ℝ}
    (hR : 0 < R) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ),
      ρ < R ∧
        ∃ c : ManifoldMorse.SignedMorseChart (E := E) f p,
          ∃ hblock :
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
              c.splitChart.target,
            (∀ x ∈ ManifoldMorse.criticalPoints E f,
                f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) ∧
              Module.finrank ℝ c.NegativeCoordinates ≤ Module.finrank ℝ E ∧
                Nonempty
                  (ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
                      {u : MorseHandle.UnitDisk c.NegativeCoordinates |
                        ‖(u : c.NegativeCoordinates)‖ = 1}
                      (coreCellMap c ρ hρ hblock) ≃ₕ
                    { x : M // f x ≤ f p + ρ ^ 2 }) := by
  obtain ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, _, _, _⟩ :=
    FlowConstruction.exists_adaptedDescentFlow hf hm
  obtain ⟨c, heq⟩ := hcharts p hp
  obtain ⟨r, hr, W, hW, _, heqW, hblockr⟩ := c.exists_fieldCompatibleBlock V heq
  obtain ⟨ρ, hρ, hρmin, hband⟩ :=
    ManifoldMorse.exists_isolating_radius (ManifoldMorse.finite_criticalPoints hf hm)
      p hunique (lt_min hr hR)
  have hρr : ρ < r := hρmin.trans_le (min_le_left r R)
  have hρR : ρ < R := hρmin.trans_le (min_le_right r R)
  have hblockW :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
    intro z hz
    apply hblockr
    have hrad : 2 * ρ ≤ 2 * r := by linarith
    exact
      ⟨Metric.closedBall_subset_closedBall hrad hz.1,
        Metric.closedBall_subset_closedBall hrad hz.2⟩
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hagreement :
    ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    have hxW : c.attachingHandleMap ρ hρ hblock z ∈ W :=
      (hblockW (MorseHandle.modelMap_mem_product hρ z)).2
    filter_upwards [hW.mem_nhds hxW] with y hy
    exact heqW y hy
  obtain ⟨e, _⟩ :=
    c.exists_attachingUnionHomotopyEquiv hf hV hzero hdesc F hcurve ρ hρ hblock hagreement hband
  refine ⟨ρ, hρ, hρR, c, hblock, hband, core_dimension_le c, ?_⟩
  exact
    ⟨(cellHandleHomotopyEquiv c ρ hρ hblock hf.continuous).trans
        ((c.attachingHandleUnionHomeomorph hf.continuous ρ hρ hblock).toHomotopyEquiv.trans e)⟩

/-- A Morse cell: a chart block around a critical point. -/
structure MorseCells.Cell {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : ManifoldMorse.SignedMorseChart (E := E) f p
  block :
    Metric.closedBall (0 : chart.NegativeCoordinates) (2 * radius) ×ˢ
        Metric.closedBall (0 : chart.PositiveCoordinates) (2 * radius) ⊆
      chart.splitChart.target
  isolated :
    ∀ x ∈ ManifoldMorse.criticalPoints E f,
      f x ∈ Set.Icc (f p - radius ^ 2) (f p + radius ^ 2) → x = p
  dimension_le : Module.finrank ℝ chart.NegativeCoordinates ≤ Module.finrank ℝ E
  comparison :
    ClosedAttachment.Space {x : M | f x ≤ f p - radius ^ 2}
        {u : MorseHandle.UnitDisk chart.NegativeCoordinates |
          ‖(u : chart.NegativeCoordinates)‖ = 1}
        (coreCellMap chart radius radius_pos block) ≃ₕ
      { x : M // f x ≤ f p + radius ^ 2 }

/-- The height band of a Morse cell. -/
def MorseCells.Cell.band {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : MorseCells.Cell (E := E) f p) : Set ℝ :=
  Set.Icc (f p - c.radius ^ 2) (f p + c.radius ^ 2)

/-- A Morse cell below a level exists. -/
theorem MorseCells.exists_cell_lt {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) {p : M}
    (hp : p ∈ ManifoldMorse.criticalPoints E f)
    (hunique : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x = f p → x = p) {R : ℝ}
    (hR : 0 < R) : ∃ c : Cell (E := E) f p, c.radius < R := by
  obtain ⟨ρ, hρ, hlt, c, hb, hi, hd, ⟨e⟩⟩ := exists_morse_cell_attachment_lt hf hm hp hunique hR
  exact ⟨⟨ρ, hρ, c, hb, hi, hd, e⟩, hlt⟩

/-- Disjoint Morse cells at distinct critical points exist. -/
theorem MorseCells.exists_disjoint_cells {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (ManifoldMorse.criticalPoints E f)) :
    ∃ c : (p : ManifoldMorse.criticalPoints E f) → Cell (E := E) f p.val,
      ∀ p q, p ≠ q → Disjoint (c p).band (c q).band := by
  have hR (p : ManifoldMorse.criticalPoints E f) :
    ∃ R > (0 : ℝ),
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc (f p - R ^ 2) (f p + R ^ 2) → x = p := by
    obtain ⟨R, hR, _, hi⟩ :=
      ManifoldMorse.exists_isolating_radius
        (ManifoldMorse.finite_criticalPoints hf hm) p.val
        (fun x hx heq => hinj hx p.property heq) zero_lt_one
    exact ⟨R, hR, hi⟩
  choose R hR hiso using hR
  have hc (p : ManifoldMorse.criticalPoints E f) :
    ∃ c : Cell (E := E) f p.val, c.radius < R p / 2 :=
    exists_cell_lt hf hm p.property (fun x hx heq => hinj hx p.property heq) (half_pos (hR p))
  choose c hc using hc
  refine ⟨c, ?_⟩
  have hordered (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    Disjoint (c p).band (c q).band := by
    have hne : (p : M) ≠ q := fun he => (ne_of_lt hpq) (congrArg f he)
    have hp : (R p) ^ 2 < f q - f p := by
      by_contra h
      have he :=
        hiso p q q.property
          (show f q ∈ Set.Icc (f p - (R p) ^ 2) (f p + (R p) ^ 2) from
            ⟨by nlinarith [sq_nonneg (R p)], by linarith⟩)
      exact hne he.symm
    have hq : (R q) ^ 2 < f q - f p := by
      by_contra h
      have he :=
        hiso q p p.property
          (show f p ∈ Set.Icc (f q - (R q) ^ 2) (f q + (R q) ^ 2) from
            ⟨by linarith, by nlinarith [sq_nonneg (R q)]⟩)
      exact hne he
    have hsp : (c p).radius ^ 2 < (R p / 2) ^ 2 :=
      (sq_lt_sq₀ (c p).radius_pos.le (half_pos (hR p)).le).mpr (hc p)
    have hsq : (c q).radius ^ 2 < (R q / 2) ^ 2 :=
      (sq_lt_sq₀ (c q).radius_pos.le (half_pos (hR q)).le).mpr (hc q)
    apply Set.disjoint_left.mpr
    intro t htp htq
    change f p - (c p).radius ^ 2 ≤ t ∧ t ≤ f p + (c p).radius ^ 2 at htp
    change f q - (c q).radius ^ 2 ≤ t ∧ t ≤ f q + (c q).radius ^ 2 at htq
    nlinarith [htp.2, htq.1]
  intro p q hpq
  rcases lt_trichotomy (f p) (f q) with h | h | h
  · exact hordered p q h
  · exact (hpq (Subtype.ext (hinj p.property q.property h))).elim
  · exact (hordered q p h).symm

/-- Disjoint cells order by height. -/
theorem MorseCells.upper_lt_lower_of_disjoint {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p q : M}
    (c : Cell (E := E) f p) (d : Cell (E := E) f q) (h : Disjoint c.band d.band)
    (hpq : f p < f q) : f p + c.radius ^ 2 < f q - d.radius ^ 2 := by
  by_contra hn
  have hle : f q - d.radius ^ 2 ≤ f p + c.radius ^ 2 := le_of_not_gt hn
  let t := Max.max (f p - c.radius ^ 2) (f q - d.radius ^ 2)
  have hc : t ∈ c.band := by
    exact ⟨le_max_left _ _, max_le (by nlinarith [sq_nonneg c.radius]) hle⟩
  have hd : t ∈ d.band := by
    refine ⟨le_max_right _ _, max_le ?_ ?_⟩
    · nlinarith [sq_nonneg c.radius, sq_nonneg d.radius]
    · nlinarith [sq_nonneg d.radius]
  exact Set.disjoint_left.mp h hc hd

/-- A sublevel with no critical points is empty. -/
theorem MorseCells.isEmpty_sublevel_of_no_critical {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (h : ∀ p ∈ ManifoldMorse.criticalPoints E f, ¬f p ≤ a) : IsEmpty { x : M // f x ≤ a } :=
  by
  refine ⟨fun x => ?_⟩
  obtain ⟨p, _, hmin⟩ :=
    isCompact_univ.exists_isMinOn ⟨x.val, Set.mem_univ _⟩ hf.continuous.continuousOn
  have hp : p ∈ ManifoldMorse.criticalPoints E f :=
    ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun y => hmin (Set.mem_univ y)))
  exact h p hp ((hmin (Set.mem_univ x.val)).trans x.property)
end Mathoverflow1973
