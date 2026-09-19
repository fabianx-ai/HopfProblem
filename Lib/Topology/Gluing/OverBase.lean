/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Topology.Gluing
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Topology.Sets.OpenCover

/-!
# Gluing spaces over a covered base

Generic topological gluing data over an open cover, together with the star-cover specialization.
This is a move-only extraction from `Hopf/LCP/GlobalAssembly.lean` at
`fdab17008ae39b1387b3e13be073e7168f700667`; historical declaration names are retained so
existing consumers remain definitionally identical.
-/

@[expose] public section

open Set Function Topology
open scoped CategoryTheory Topology

noncomputable section

universe u

namespace Mathoverflow1973

structure ThreefoldGluing.Data (B : Type u) [TopologicalSpace B] where
  J : Type u
  patch : J → TopologicalSpace.Opens B
  cover : TopologicalSpace.IsOpenCover patch
  piece : J → TopCat.{u}
  toBase : ∀ i, C(piece i, B)
  toBase_mem : ∀ i x, toBase i x ∈ patch i
  transition : ∀ i j, OpenPartialHomeomorph (piece i) (piece j)
  source_eq : ∀ i j, (transition i j).source = toBase i ⁻¹' (patch j : Set B)
  self_eq : ∀ i, transition i i = OpenPartialHomeomorph.refl (piece i)
  symm_eq : ∀ i j, (transition i j).symm = transition j i
  preserves_base : ∀ i j x, x ∈ (transition i j).source → toBase j (transition i j x) = toBase i x
  cocycle :
    ∀ i j k x,
      x ∈ (transition i j).source →
        transition i j x ∈ (transition j k).source →
          transition j k (transition i j x) = transition i k x

theorem ThreefoldGluing.Data.transition_map_source {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i j : D.J) {x : D.piece i}
    (hx : x ∈ (D.transition i j).source) : D.transition i j x ∈ (D.transition j i).source := by
  rw [← D.symm_eq i j]
  exact (D.transition i j).map_source hx

theorem ThreefoldGluing.Data.transition_inter {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i j k : D.J) {x : D.piece i}
    (hx : x ∈ (D.transition i j).source) (hk : x ∈ (D.transition i k).source) :
    D.transition i j x ∈ (D.transition j k).source := by
  rw [D.source_eq] at hk ⊢
  change D.toBase j (D.transition i j x) ∈ D.patch k
  rw [D.preserves_base i j x hx]
  exact hk

abbrev ThreefoldGluing.Data.gluingCore {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) : TopCat.GlueData.MkCore
    where
  J := D.J
  U := D.piece
  V i j := ⟨(D.transition i j).source, (D.transition i j).open_source⟩
  t i
    j :=
    TopCat.ofHom
      { toFun := fun x => ⟨D.transition i j x, D.transition_map_source i j x.property⟩
        continuous_toFun := (D.transition i j).continuousOn.domRestrict.subtype_mk _ }
  V_id i := by apply TopologicalSpace.Opens.ext; simp [D.self_eq]
  t_id
    i := by
    funext x
    exact
      Subtype.ext
        (congrArg (fun e : OpenPartialHomeomorph (D.piece i) (D.piece i) => e x.val)
          (D.self_eq i))
  t_inter := by
    intro i j k x hx
    exact D.transition_inter i j k x.property hx
  cocycle i j k x hx := D.cocycle i j k x x.property (D.transition_inter i j k x.property hx)

abbrev ThreefoldGluing.Data.gluing {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) : TopCat.GlueData :=
  TopCat.GlueData.mk' D.gluingCore

abbrev ThreefoldGluing.Data.Space {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) :=
  D.gluing.toGlueData.glued

def ThreefoldGluing.Data.inclusion {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    (i : D.J) : D.piece i → D.Space :=
  D.gluing.toGlueData.ι i

theorem ThreefoldGluing.Data.inclusion_openEmbedding {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) : Topology.IsOpenEmbedding (D.inclusion i) :=
  D.gluing.ι_isOpenEmbedding i

theorem ThreefoldGluing.Data.inclusion_jointly_surjective {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (x : D.Space) : ∃ i z, D.inclusion i z = x :=
  D.gluing.ι_jointly_surjective x

theorem ThreefoldGluing.Data.inclusion_eq_iff {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i j : D.J) (x : D.piece i) (y : D.piece j) :
    D.inclusion i x = D.inclusion j y ↔ x ∈ (D.transition i j).source ∧ D.transition i j x = y := by
  refine (D.gluing.ι_eq_iff_rel i j x y).trans ?_
  constructor
  · rintro ⟨⟨z, hz⟩, hzx, hzy⟩
    change z = x at hzx
    change D.transition i j z = y at hzy
    subst z
    exact ⟨hz, hzy⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨⟨x, hx⟩, rfl, hxy⟩

def ThreefoldGluing.Data.representative {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (x : D.Space) : Σ i, D.piece i :=
  ⟨(D.inclusion_jointly_surjective x).choose,
    (D.inclusion_jointly_surjective x).choose_spec.choose⟩

theorem ThreefoldGluing.Data.inclusion_representative {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (x : D.Space) :
    D.inclusion (D.representative x).1 (D.representative x).2 = x :=
  (D.inclusion_jointly_surjective x).choose_spec.choose_spec
def ThreefoldGluing.Data.parametrization {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] (i : D.J) :
    OpenPartialHomeomorph (D.piece i) D.Space :=
  (D.inclusion_openEmbedding i).toOpenPartialHomeomorph (D.inclusion i)

@[simp]
theorem ThreefoldGluing.Data.parametrization_target {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] (i : D.J) :
    (D.parametrization i).target = Set.range (D.inclusion i) := by simp [parametrization]

theorem ThreefoldGluing.Data.parametrization_transition {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] (i j : D.J) {x : D.piece i}
    (hx : D.inclusion i x ∈ Set.range (D.inclusion j)) :
    x ∈ (D.transition i j).source ∧
      (D.parametrization j).symm (D.inclusion i x) = D.transition i j x := by
  obtain ⟨y, hy⟩ := hx
  have he := (D.inclusion_eq_iff i j x y).mp hy.symm
  refine ⟨he.1, ?_⟩
  rw [← hy]
  exact ((D.inclusion_openEmbedding j).toOpenPartialHomeomorph_left_inv).trans he.2.symm

/-! Projection and patch coordinates over the base: the representative, continuity, range,
and inclusion-homeomorphism argument of `CENTER_GENERIC_PATCH_HOMEOMORPH_TEXTBOOK.md`,
reviewed sections GP1–GP7. These require no separation or nonempty-piece hypotheses. -/

def ThreefoldGluing.Data.projection {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    (x : D.Space) : B :=
  D.toBase (D.representative x).1 (D.representative x).2

@[simp]
theorem ThreefoldGluing.Data.projection_inclusion {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) (x : D.piece i) :
    D.projection (D.inclusion i x) = D.toBase i x := by
  let r := D.representative (D.inclusion i x)
  have h := (D.inclusion_eq_iff r.1 i r.2 x).mp (D.inclusion_representative _)
  change D.toBase r.1 r.2 = D.toBase i x
  rw [← h.2]
  exact (D.preserves_base r.1 i r.2 h.1).symm

theorem ThreefoldGluing.Data.projection_continuous {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) : Continuous D.projection := by
  rw [continuous_def]
  intro U hU
  rw [D.gluing.isOpen_iff]
  change ∀ i : D.J, IsOpen (D.inclusion i ⁻¹' (D.projection ⁻¹' U))
  intro i
  convert hU.preimage (D.toBase i).continuous using 1
  ext x
  change D.projection (D.inclusion i x) ∈ U ↔ D.toBase i x ∈ U
  rw [D.projection_inclusion]

theorem ThreefoldGluing.Data.inclusion_range {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) :
    Set.range (D.inclusion i) = D.projection ⁻¹' (D.patch i : Set B) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change D.projection (D.inclusion i z) ∈ D.patch i
    rw [D.projection_inclusion]
    exact D.toBase_mem i z
  · intro hx
    obtain ⟨j, z, rfl⟩ := D.inclusion_jointly_surjective x
    have hz : z ∈ (D.transition j i).source := by
      rw [D.source_eq]
      simpa only [Set.mem_preimage, projection_inclusion] using hx
    exact ⟨D.transition j i z, ((D.inclusion_eq_iff j i z _).mpr ⟨hz, rfl⟩).symm⟩

def ThreefoldGluing.Data.localProjection {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) : C(D.piece i, D.patch i)
    where
  toFun x := ⟨D.toBase i x, D.toBase_mem i x⟩
  continuous_toFun := (D.toBase i).continuous.subtype_mk _

def ThreefoldGluing.Data.patchHomeomorph {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) :
    D.piece i ≃ₜ (D.projection ⁻¹' (D.patch i : Set B)) :=
  (D.inclusion_openEmbedding i).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (D.inclusion_range i))

theorem ThreefoldGluing.Data.patchHomeomorph_projection {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) (x : D.piece i) :
    (D.patch i : Set B).restrictPreimage D.projection (D.patchHomeomorph i x) =
      D.localProjection i x := by
  apply Subtype.ext
  exact D.projection_inclusion i x

structure SpecialPeriods.Threefold.Star.Input (B : Type u) [TopologicalSpace B] (I : Type u) where
  patch : Option I → TopologicalSpace.Opens B
  cover : TopologicalSpace.IsOpenCover patch
  disjoint :
    Pairwise
      (fun i j : I => Disjoint (patch (Option.some i) : Set B) (patch (Option.some j) : Set B))
  piece : Option I → TopCat.{u}
  toBase : ∀ i, C(piece i, B)
  toBase_mem : ∀ i x, toBase i x ∈ patch i
  overlap : ∀ i, OpenPartialHomeomorph (piece (Option.some i)) (piece Option.none)
  source_eq : ∀ i, (overlap i).source = toBase (Option.some i) ⁻¹' (patch Option.none : Set B)
  target_eq : ∀ i, (overlap i).target = toBase Option.none ⁻¹' (patch (Option.some i) : Set B)
  preserves_base :
    ∀ i x, x ∈ (overlap i).source → toBase Option.none (overlap i x) = toBase (Option.some i) x

def SpecialPeriods.Threefold.Star.Input.transition {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I) :
    ∀ i j : Option I, OpenPartialHomeomorph (D.piece i) (D.piece j)
  | none, Option.none => OpenPartialHomeomorph.refl _
  | none, Option.some j => (D.overlap j).symm
  | some i, Option.none => D.overlap i
  | some i, Option.some j => by
    classical
      exact
      if h : i = j then by
        subst j
        exact OpenPartialHomeomorph.refl _
      else (D.overlap i).trans (D.overlap j).symm

@[simp]
theorem SpecialPeriods.Threefold.Star.Input.transition_none_none {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) :
    D.transition Option.none Option.none = OpenPartialHomeomorph.refl (D.piece Option.none) :=
  rfl

@[simp]
theorem SpecialPeriods.Threefold.Star.Input.transition_none_some {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i : I) :
    D.transition Option.none (Option.some i) = (D.overlap i).symm :=
  rfl

@[simp]
theorem SpecialPeriods.Threefold.Star.Input.transition_some_none {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i : I) :
    D.transition (Option.some i) Option.none = D.overlap i :=
  rfl

@[simp]
theorem SpecialPeriods.Threefold.Star.Input.transition_some_self {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i : I) :
    D.transition (Option.some i) (Option.some i) =
      OpenPartialHomeomorph.refl (D.piece (Option.some i)) := by simp [transition]

theorem SpecialPeriods.Threefold.Star.Input.transition_some_some_of_ne {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) {i j : I} (h : i ≠ j) :
    D.transition (Option.some i) (Option.some j) = (D.overlap i).trans (D.overlap j).symm := by
  simp [transition, h]

@[simp]
theorem SpecialPeriods.Threefold.Star.Input.transition_self {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I) (i : Option I) :
    D.transition i i = OpenPartialHomeomorph.refl (D.piece i) := by cases i <;> simp

theorem SpecialPeriods.Threefold.Star.Input.transition_symm {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I) (i j : Option I) :
    (D.transition i j).symm = D.transition j i := by
  cases i with
  | none => cases j <;> simp
  | some i =>
    cases j with
    | none => simp
    | some j =>
      by_cases h : i = j
      · subst j
        simp
      · rw [D.transition_some_some_of_ne h, D.transition_some_some_of_ne (Ne.symm h)]
        simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.symm_symm]

theorem SpecialPeriods.Threefold.Star.Input.overlap_symm_preserves_base {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i : I)
    (x : D.piece Option.none) (hx : x ∈ (D.overlap i).target) :
    D.toBase (Option.some i) ((D.overlap i).symm x) = D.toBase Option.none x := by
  have h := D.preserves_base i ((D.overlap i).symm x) ((D.overlap i).map_target hx)
  rw [(D.overlap i).right_inv hx] at h
  exact h.symm

@[simp]
theorem SpecialPeriods.Threefold.Star.Input.toBase_preimage_own {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i : Option I) :
    D.toBase i ⁻¹' (D.patch i : Set B) = Set.univ :=
  Set.eq_univ_of_forall (D.toBase_mem i)

theorem SpecialPeriods.Threefold.Star.Input.filling_preimage_eq_empty {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) {i j : I} (h : i ≠ j) :
    D.toBase (Option.some i) ⁻¹' (D.patch (Option.some j) : Set B) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact Set.disjoint_left.mp (D.disjoint h) (D.toBase_mem (Option.some i) x) hx

theorem SpecialPeriods.Threefold.Star.Input.transition_some_some_source_eq_empty {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) {i j : I} (h : i ≠ j) :
    (D.transition (Option.some i) (Option.some j)).source = ∅ := by
  rw [D.transition_some_some_of_ne h, OpenPartialHomeomorph.trans_source]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hy⟩
  have hb : D.toBase Option.none (D.overlap i x) ∈ D.patch (Option.some j) := by
    simpa only [OpenPartialHomeomorph.symm_source, D.target_eq j, Set.mem_preimage,
      SetLike.mem_coe] using hy
  rw [D.preserves_base i x hx] at hb
  exact Set.disjoint_left.mp (D.disjoint h) (D.toBase_mem (Option.some i) x) hb

theorem SpecialPeriods.Threefold.Star.Input.transition_source_eq {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i j : Option I) :
    (D.transition i j).source = D.toBase i ⁻¹' (D.patch j : Set B) := by
  cases i with
  | none =>
    cases j with
    | none => simp
    | some j => simpa using D.target_eq j
  | some i =>
    cases j with
    | none => exact D.source_eq i
    | some j =>
      by_cases h : i = j
      · subst j
        simp
      · rw [D.transition_some_some_source_eq_empty h, D.filling_preimage_eq_empty h]

theorem SpecialPeriods.Threefold.Star.Input.transition_preserves_base {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i j : Option I)
    (x : D.piece i) (hx : x ∈ (D.transition i j).source) :
    D.toBase j (D.transition i j x) = D.toBase i x := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact D.overlap_symm_preserves_base j x hx
  | some i =>
    cases j with
    | none => exact D.preserves_base i x hx
    | some j =>
      by_cases h : i = j
      · subst j
        simp
      · rw [D.transition_some_some_source_eq_empty h] at hx
        exact hx.elim

theorem SpecialPeriods.Threefold.Star.Input.eq_or_eq_or_eq_of_common_base {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) (i j k : Option I) {b : B}
    (hi : b ∈ D.patch i) (hj : b ∈ D.patch j) (hk : b ∈ D.patch k) : i = j ∨ j = k ∨ i = k := by
  have he : ∀ a c : I, b ∈ D.patch (Option.some a) → b ∈ D.patch (Option.some c) → a = c := by
    intro a c ha hc
    by_contra h
    exact Set.disjoint_left.mp (D.disjoint h) ha hc
  cases i with
  | none =>
    cases j with
    | none => exact Or.inl rfl
    | some j =>
      cases k with
      | none => exact Or.inr (Or.inr rfl)
      | some k => exact Or.inr (Or.inl (congrArg Option.some (he j k hj hk)))
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact Or.inr (Or.inl rfl)
      | some k => exact Or.inr (Or.inr (congrArg Option.some (he i k hi hk)))
    | some j => exact Or.inl (congrArg Option.some (he i j hi hj))

theorem SpecialPeriods.Threefold.Star.Input.transition_cocycle {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I) (i j k : Option I) (x : D.piece i)
    (hx : x ∈ (D.transition i j).source) (hy : D.transition i j x ∈ (D.transition j k).source) :
    D.transition j k (D.transition i j x) = D.transition i k x := by
  have hj : D.toBase i x ∈ D.patch j := by
    simpa only [D.transition_source_eq i j, Set.mem_preimage, SetLike.mem_coe] using hx
  have hk : D.toBase i x ∈ D.patch k := by
    have h : D.toBase j (D.transition i j x) ∈ D.patch k := by
      simpa only [D.transition_source_eq j k, Set.mem_preimage, SetLike.mem_coe] using hy
    rwa [D.transition_preserves_base i j x hx] at h
  rcases D.eq_or_eq_or_eq_of_common_base i j k (D.toBase_mem i x) hj hk with hij | hjk | hik
  · subst j
    simp
  · subst k
    simp
  · subst k
    rw [← D.transition_symm i j, D.transition_self]
    exact (D.transition i j).left_inv hx

abbrev SpecialPeriods.Threefold.Star.Input.toData {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I) : ThreefoldGluing.Data B
    where
  J := Option I
  patch := D.patch
  cover := D.cover
  piece := D.piece
  toBase := D.toBase
  toBase_mem := D.toBase_mem
  transition := D.transition
  source_eq := D.transition_source_eq
  self_eq := D.transition_self
  symm_eq := D.transition_symm
  preserves_base := D.transition_preserves_base
  cocycle := D.transition_cocycle

end Mathoverflow1973
