/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle

/-!
# Smooth transport of the ranges of a family of projections

Let `P : E → F →L[ℝ] F` be a smooth family of idempotents near a compact set `K`. A
`DiskFraming.SmoothRangeTransportOn K P Q` is a smooth family of operators, invertible on `K`,
intertwining `P` and `Q` there; it carries `range (P x)` onto `range (Q x)`. The relation is
reflexive, symmetric and transitive, nearby projections are related through
`projectionIntertwiner`, and a continuity argument along a connected parameter space relates the
two ends of a homotopy of projection families. For `K` star-convex about `0` the radial homotopy
`P (t • x)` relates `P` to the constant family `P 0`, which gives a smooth frame
`A x : range (P 0) → F` with `range (A x) = range (P x)`: a vector bundle over a star-convex
compact set, presented as the range of a projection family, is trivial (cf. Hirsch,
*Differential Topology*, Ch. 4, §1–2: bundles over contractible bases).

## Main definitions and results

* `DiskFraming.SmoothRangeTransportOn` with `refl`, `symm`, `trans`, `map_range`,
  `ofProjections`.
* `isOpen_forall_compact` : `{x | ∀ y, R x y}` is open when `R` is open and `Y` is compact.
* `DiskFraming.nonempty_smoothRangeTransportOn_of_homotopy` : transport along a homotopy.
* `DiskFraming.exists_smooth_frame_near_starConvex`,
  `DiskFraming.exists_smooth_frame_on_neighborhood_closedBall` : smooth frames of the range
  bundle near a star-convex compact set, resp. near the closed unit ball.

## Tags

projection, vector bundle, frame, star-convex
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

@[expose] public noncomputable section

/-! ### Smooth range transport -/

/-- Two disks admit a smooth transport of ranges on a set. -/
structure DiskFraming.SmoothRangeTransportOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set E)
    (P Q : E → F →L[ℝ] F) where
  toFun : E → F →L[ℝ] F
  neighborhood : Set E
  open_neighborhood : IsOpen neighborhood
  contains : K ⊆ neighborhood
  smooth : ContDiffOn ℝ ∞ toFun neighborhood
  invertible : ∀ x ∈ K, (toFun x).IsInvertible
  intertwines : ∀ x ∈ K, Q x * toFun x = toFun x * P x

/-- Range transport is reflexive. -/
def DiskFraming.SmoothRangeTransportOn.refl {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set E) (P : E → F →L[ℝ] F) :
    DiskFraming.SmoothRangeTransportOn K P P
    where
  toFun _ := 1
  neighborhood := Set.univ
  open_neighborhood := isOpen_univ
  contains := Set.subset_univ _
  smooth := contDiffOn_const
  invertible _ _ := ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  intertwines _ _ := by rw [mul_one, one_mul]

/-- Range transport is transitive. -/
def DiskFraming.SmoothRangeTransportOn.trans {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q R : E → F →L[ℝ] F}
    (a : DiskFraming.SmoothRangeTransportOn K P Q)
    (b : DiskFraming.SmoothRangeTransportOn K Q R) :
    DiskFraming.SmoothRangeTransportOn K P R
    where
  toFun x := b.toFun x * a.toFun x
  neighborhood := a.neighborhood ∩ b.neighborhood
  open_neighborhood := a.open_neighborhood.inter b.open_neighborhood
  contains := fun _ hx => ⟨a.contains hx, b.contains hx⟩
  smooth := (b.smooth.mono Set.inter_subset_right).clm_comp (a.smooth.mono Set.inter_subset_left)
  invertible x hx := (b.invertible x hx).comp (a.invertible x hx)
  intertwines x
    hx := by
    calc
      R x * (b.toFun x * a.toFun x) = (R x * b.toFun x) * a.toFun x := (mul_assoc _ _ _).symm
      _ = (b.toFun x * Q x) * a.toFun x := by rw [b.intertwines x hx]
      _ = b.toFun x * (Q x * a.toFun x) := (mul_assoc _ _ _)
      _ = b.toFun x * (a.toFun x * P x) := by rw [a.intertwines x hx]
      _ = (b.toFun x * a.toFun x) * P x := (mul_assoc _ _ _).symm

/-- Range transport is symmetric. -/
def DiskFraming.SmoothRangeTransportOn.symm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q : E → F →L[ℝ] F}
    [CompleteSpace F] (a : DiskFraming.SmoothRangeTransportOn K P Q) :
    DiskFraming.SmoothRangeTransportOn K Q P
    where
  toFun x := (a.toFun x).inverse
  neighborhood := a.neighborhood ∩ {x | (a.toFun x).IsInvertible}
  open_neighborhood :=
    a.smooth.continuousOn.isOpen_inter_preimage a.open_neighborhood ContinuousLinearEquiv.isOpen
  contains := fun x hx => ⟨a.contains hx, a.invertible x hx⟩
  smooth := by
    intro x hx
    exact
      (hx.2.contDiffAt_map_inverse.comp x
          (a.smooth.contDiffAt (a.open_neighborhood.mem_nhds hx.1))).contDiffWithinAt
  invertible x hx := (a.invertible x hx).inverse
  intertwines x
    hx := by
    apply ContinuousLinearMap.ext
    intro v
    change P x ((a.toFun x).inverse v) = (a.toFun x).inverse (Q x v)
    apply (a.invertible x hx).injective
    rw [(a.invertible x hx).self_apply_inverse]
    have h := congrArg (fun L : F →L[ℝ] F => L ((a.toFun x).inverse v)) (a.intertwines x hx)
    change Q x (a.toFun x ((a.toFun x).inverse v)) = a.toFun x (P x ((a.toFun x).inverse v)) at h
    rw [(a.invertible x hx).self_apply_inverse] at h
    exact h.symm

/-- Range transport maps the range. -/
theorem DiskFraming.SmoothRangeTransportOn.map_range {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q : E → F →L[ℝ] F}
    (a : DiskFraming.SmoothRangeTransportOn K P Q) (x : E) (hx : x ∈ K) :
    Submodule.map (a.toFun x).toLinearMap (P x).range = (Q x).range := by
  rw [← LinearMap.range_comp]
  have hlin :
    (a.toFun x).toLinearMap.comp (P x).toLinearMap =
      (Q x).toLinearMap.comp (a.toFun x).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (a.intertwines x hx).symm
  rw [hlin]
  exact
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (a.invertible x hx).surjective)

/-- Projections give a range transport. -/
def DiskFraming.SmoothRangeTransportOn.ofProjections {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q : E → F →L[ℝ] F}
    (hP : ∀ x ∈ K, IsIdempotentElem (P x)) (hQ : ∀ x ∈ K, IsIdempotentElem (Q x)) {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U) (hKV : K ⊆ V) (hsP : ContDiffOn ℝ ∞ P U)
    (hsQ : ContDiffOn ℝ ∞ Q V)
    (hinv : ∀ x ∈ K, (projectionIntertwiner (P x) (Q x)).IsInvertible) :
    DiskFraming.SmoothRangeTransportOn K P Q
    where
  toFun x := projectionIntertwiner (P x) (Q x)
  neighborhood := U ∩ V
  open_neighborhood := hU.inter hV
  contains := fun _ hx => ⟨hKU hx, hKV hx⟩
  smooth :=
    ((hsQ.mono Set.inter_subset_right).clm_comp (hsP.mono Set.inter_subset_left)).add
      ((contDiffOn_const.sub (hsQ.mono Set.inter_subset_right)).clm_comp
        (contDiffOn_const.sub (hsP.mono Set.inter_subset_left)))
  invertible := hinv
  intertwines x hx := projectionIntertwiner_intertwines (P x) (Q x) (hP x hx) (hQ x hx)

/-- An open property on a compact set holds on a neighborhood. -/
theorem isOpen_forall_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] {R : X → Y → Prop} (ho : IsOpen {p : X × Y | R p.1 p.2}) :
    IsOpen {x | ∀ y, R x y} := by
  have hclosed := isClosedMap_fst_of_compactSpace _ ho.isClosed_compl
  have heq : {x | ∀ y, R x y} = (Prod.fst '' {p : X × Y | ¬R p.1 p.2})ᶜ := by
    ext x
    constructor
    · rintro h ⟨⟨x', y⟩, hn, he⟩
      change x' = x at he
      subst x'
      exact hn (h y)
    · intro h y
      by_contra hn
      exact h ⟨(x, y), hn, rfl⟩
  rw [heq]
  exact hclosed.isOpen_compl

/-- The domain where a homotopy transports the range. -/
def homotopyTransportDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*} {T : Type*} (P : T → M → F →L[ℝ] F) (s : T) : Set T :=
  {t | ∀ x, (projectionIntertwiner (P s x) (P t x)).IsInvertible}

/-- Membership in the homotopy transport domain. -/
theorem mem_homotopyTransportDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*} {T : Type*} (P : T → M → F →L[ℝ] F) (hP : ∀ t x, IsIdempotentElem (P t x))
    (s : T) : s ∈ homotopyTransportDomain P s := by
  intro x
  rw [projectionIntertwiner_self _ (hP s x)]
  exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩

/-- The homotopy transport domain is open. -/
theorem isOpen_continuousHomotopyTransportDomain {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {M T : Type*} [TopologicalSpace M] [CompactSpace M]
    [TopologicalSpace T] (P : T → M → F →L[ℝ] F) (hc : Continuous (fun p : T × M ↦ P p.1 p.2))
    (s : T) : IsOpen (homotopyTransportDomain P s) := by
  have hp : Continuous (fun p : T × M ↦ P s p.2) :=
    hc.comp (continuous_const.prodMk continuous_snd)
  have hr : Continuous (fun p : T × M ↦ projectionIntertwiner (P s p.2) (P p.1 p.2)) :=
    (hc.clm_comp hp).add ((continuous_const.sub hc).clm_comp (continuous_const.sub hp))
  have hi : IsOpen {A : F →L[ℝ] F | A.IsInvertible} := ContinuousLinearEquiv.isOpen
  exact isOpen_forall_compact (hi.preimage hr)

/-- The transport-on class is open. -/
theorem DiskFraming.isOpen_transportOnClass {E F T : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace T] {K : Set E} (hK : IsCompact K) (P : T → E → F →L[ℝ] F)
    (hP : ∀ t x, x ∈ K → IsIdempotentElem (P t x))
    (hc : Continuous (fun q : T × K => P q.1 q.2.1))
    (hs : ∀ t, ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (P t) U) (s : T) :
    IsOpen {t | Nonempty (SmoothRangeTransportOn K (P s) (P t))} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R (t : T) (x : K) := P t x.1
  have hR (t : T) (x : K) : IsIdempotentElem (R t x) := hP t x.1 x.property
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨a⟩
  have hdom := isOpen_continuousHomotopyTransportDomain R hc t
  have ht := mem_homotopyTransportDomain R hR t
  apply Filter.mem_of_superset (hdom.mem_nhds ht)
  intro u hu
  obtain ⟨Ut, hUt, hKt, hst⟩ := hs t
  obtain ⟨Uu, hUu, hKu, hsu⟩ := hs u
  exact
    ⟨a.trans
        (SmoothRangeTransportOn.ofProjections (hP t) (hP u) hUt hUu hKt hKu hst hsu
          (fun x hx => hu ⟨x, hx⟩))⟩

/-- The complement of the transport class is open. -/
theorem DiskFraming.isOpen_compl_transportOnClass {E F T : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace T] {K : Set E} (hK : IsCompact K) (P : T → E → F →L[ℝ] F)
    (hP : ∀ t x, x ∈ K → IsIdempotentElem (P t x))
    (hc : Continuous (fun q : T × K => P q.1 q.2.1))
    (hs : ∀ t, ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (P t) U) (s : T) :
    IsOpen {t | ¬Nonempty (SmoothRangeTransportOn K (P s) (P t))} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R (t : T) (x : K) := P t x.1
  have hR (t : T) (x : K) : IsIdempotentElem (R t x) := hP t x.1 x.property
  rw [isOpen_iff_mem_nhds]
  intro t ht
  have hdom := isOpen_continuousHomotopyTransportDomain R hc t
  have htmem := mem_homotopyTransportDomain R hR t
  apply Filter.mem_of_superset (hdom.mem_nhds htmem)
  rintro u hu ⟨a⟩
  obtain ⟨Ut, hUt, hKt, hst⟩ := hs t
  obtain ⟨Uu, hUu, hKu, hsu⟩ := hs u
  exact
    ht
      ⟨a.trans
          (SmoothRangeTransportOn.ofProjections (hP t) (hP u) hUt hUu hKt hKu hst hsu
              (fun x hx => hu ⟨x, hx⟩)).symm⟩

/-- A homotopy gives a smooth range transport. -/
theorem DiskFraming.nonempty_smoothRangeTransportOn_of_homotopy {E F T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [TopologicalSpace T] {K : Set E} (hK : IsCompact K) (P : T → E → F →L[ℝ] F)
    (hP : ∀ t x, x ∈ K → IsIdempotentElem (P t x))
    (hc : Continuous (fun q : T × K => P q.1 q.2.1))
    (hs : ∀ t, ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (P t) U) [PreconnectedSpace T]
    (s t : T) : Nonempty (SmoothRangeTransportOn K (P s) (P t)) := by
  let C : Set T := {u | Nonempty (SmoothRangeTransportOn K (P s) (P u))}
  have hclosed : IsClosed C := by
    simpa only [C, Set.compl_ofPred, Classical.not_not] using
      (isOpen_compl_transportOnClass hK P hP hc hs s).isClosed_compl
  have hclopen : IsClopen C := ⟨hclosed, isOpen_transportOnClass hK P hP hc hs s⟩
  have hall : C = Set.univ := hclopen.eq_univ ⟨s, ⟨SmoothRangeTransportOn.refl K (P s)⟩⟩
  have ht : t ∈ C := by rw [hall]; exact Set.mem_univ t
  exact ht

/-- A range transport exists on a star-convex set. -/
theorem DiskFraming.nonempty_transportOn_starConvex {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {K U : Set E}
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (P : E → F →L[ℝ] F) (hP : ∀ x ∈ K, IsIdempotentElem (P x)) (hs : ContDiffOn ℝ ∞ P U) :
    Nonempty (SmoothRangeTransportOn K (fun _ => P 0) P) := by
  let Q (t : unitInterval) (x : E) := P ((t : ℝ) • x)
  have hQ : ∀ t x, x ∈ K → IsIdempotentElem (Q t x) := fun t x hx =>
    hP _ (hstar.smul_mem hx t.property.1 t.property.2)
  have hmul : Continuous (fun q : unitInterval × K => (q.1 : ℝ) • (q.2 : E)) :=
    (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun q : unitInterval × K => Q q.1 q.2.1) :=
    hs.continuousOn.comp_continuous hmul
      (fun q => hKU (hstar.smul_mem q.2.property q.1.property.1 q.1.property.2))
  have hslice : ∀ t, ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ContDiffOn ℝ ∞ (Q t) V := by
    intro t
    let V : Set E := (fun x : E => (t : ℝ) • x) ⁻¹' U
    have hV : IsOpen V := hU.preimage (continuous_const.smul continuous_id)
    have hKV : K ⊆ V := fun x hx => hKU (hstar.smul_mem hx t.property.1 t.property.2)
    exact ⟨V, hV, hKV, hs.comp (contDiff_const.smul contDiff_id).contDiffOn (fun _ hx => hx)⟩
  have hstart : Q 0 = fun _ => P 0 := by
    funext x
    change P ((0 : ℝ) • x) = P 0
    rw [zero_smul]
  have hend : Q 1 = P := by
    funext x
    change P ((1 : ℝ) • x) = P x
    rw [one_smul]
  simpa only [hstart, hend] using
    nonempty_smoothRangeTransportOn_of_homotopy hK Q hQ hc hslice 0 1

/-- A smooth frame exists near a star-convex set. -/
theorem DiskFraming.exists_smooth_frame_near_starConvex {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {K U : Set E}
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (P : E → F →L[ℝ] F) (hP : ∀ x ∈ K, IsIdempotentElem (P x)) (hs : ContDiffOn ℝ ∞ P U) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ A : E → (P 0).range →L[ℝ] F,
            ContDiffOn ℝ ∞ A V ∧ ∀ x ∈ K, Function.Injective (A x) ∧ (A x).range = (P x).range := by
  obtain ⟨a⟩ := nonempty_transportOn_starConvex hK hstar hU hKU P hP hs
  let A (x : E) : (P 0).range →L[ℝ] F := (a.toFun x).comp (P 0).range.subtypeL
  refine
    ⟨a.neighborhood, a.open_neighborhood, a.contains, A, a.smooth.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨(a.invertible x hx).injective.comp Subtype.val_injective, ?_⟩
  change ((a.toFun x).toLinearMap.comp (P 0).range.subtype).range = (P x).range
  rw [LinearMap.range_comp, Submodule.range_subtype]
  exact a.map_range x hx

/-- A smooth frame exists on a neighborhood of a closed ball. -/
theorem DiskFraming.exists_smooth_frame_on_neighborhood_closedBall {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {U : Set E} (hU : IsOpen U)
    (hballU : Metric.closedBall (0 : E) 1 ⊆ U) (P : E → F →L[ℝ] F)
    (hP : ∀ x ∈ U, IsIdempotentElem (P x)) (hs : ContDiffOn ℝ ∞ P U) :
    ∃ V : Set E,
      IsOpen V ∧
        Metric.closedBall (0 : E) 1 ⊆ V ∧
          V ⊆ U ∧
            ∃ A : E → (P 0).range →L[ℝ] F,
              ContDiffOn ℝ ∞ A V ∧
                ∀ x ∈ V, Function.Injective (A x) ∧ (A x).range = (P x).range := by
  obtain ⟨δ, hδ, hthick⟩ :=
    (ProperSpace.isCompact_closedBall (0 : E) 1).exists_cthickening_subset_open hU hballU
  have hbU : Metric.closedBall (0 : E) (δ + 1) ⊆ U := by
    simpa only [cthickening_closedBall hδ.le zero_le_one] using hthick
  have hr : 1 < δ + 1 := by linarith
  obtain ⟨W, hW, hbW, A, hA, hArange⟩ :=
    exists_smooth_frame_near_starConvex (ProperSpace.isCompact_closedBall (0 : E) (δ + 1))
      ((convex_closedBall (0 : E) (δ + 1)).starConvex (Metric.mem_closedBall_self (by linarith)))
      hU hbU P (fun x hx => hP x (hbU hx)) hs
  refine
    ⟨W ∩ Metric.ball 0 (δ + 1), hW.inter Metric.isOpen_ball, ?_, ?_, A,
      hA.mono Set.inter_subset_left, ?_⟩
  · intro x hx
    exact
      ⟨hbW (Metric.closedBall_subset_closedBall hr.le hx), Metric.closedBall_subset_ball hr hx⟩
  · exact fun _ hx => hbU (Metric.ball_subset_closedBall hx.2)
  · exact fun x hx => hArange x (Metric.ball_subset_closedBall hx.2)
