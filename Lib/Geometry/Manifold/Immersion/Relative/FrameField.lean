/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Transversality.Basic

/-!
# Frame fields, sheared blocks and axis coordinates

Linear algebra and calculus for modifying a tubular chart along its zero section.
`FrameField.complementQuotient G C` is the projection `F →L[ℝ] Z` determined by an invertible
coproduct `G ⊕ C : D × Z → F` (it kills `range G` and is the identity on `C`), and
`FrameField.correctedComplement G C L K` adjusts a complement `L` to have prescribed projection `K`;
both depend smoothly on parameters (`FrameField.contDiffOn_complementQuotient`,
`FrameField.contDiffOn_correctedComplement`). The block `FrameField.shearedBlock A T : X × Z → X × F`,
`(x, z) ↦ (x + A z, T z)`, is bijective when `T` is, and a smooth field of such blocks integrates to
the nonlinear shear `FrameField.shearedMap A T`, a partial diffeomorphism near the zero section
(`FrameField.exists_sheared_frame_chart`), which turns a tubular chart into another one with the same
zero section, prescribed transition germs and prescribed derivative along the zero section
(`FrameField.exists_sheared_tubular_chart`).

`AxisCoordinates` decomposes an endomorphism of `ℝ × V` fixing the axis vector `(1, 0)` into its
shear `AxisCoordinates.tangentShear` and its transverse part `AxisCoordinates.transverseBlock`
(`AxisCoordinates.axis_block_eq`), and describes the transition between two charts agreeing along
the axis (`AxisCoordinates.exists_native_axis_transition_data`).
`AxisCoordinates.exists_flat_local_correction` and `AxisCoordinates.exists_axis_germ_correction`
modify a smooth map near points so as to have prescribed germs there while keeping its values and
derivatives along a set. `TransverseCoordinates.surjective_normal_comp` and
`TransverseCoordinates.bijective_normal_comp`: the normal component of a transverse complement is
onto, and bijective when the dimensions agree.

## References

* cf. Hirsch, *Differential Topology*, Ch. 4 (vector bundles and tubular neighbourhoods).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- If `Q` is surjective, `A ⊕ C` is surjective and `Q ∘ A = 0`, then `Q ∘ C` is surjective: the
normal component of a transverse complement is onto. -/
theorem TransverseCoordinates.surjective_normal_comp {D Z E B : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Q : E →L[ℝ] B) (A : D →L[ℝ] E) (C : Z →L[ℝ] E) (hQ : Function.Surjective Q)
    (hAC : Function.Surjective (A.coprod C)) (hQA : Q.comp A = 0) :
    Function.Surjective (Q.comp C) := by
  intro w
  obtain ⟨z, hz⟩ := hQ w
  obtain ⟨⟨u, v⟩, huv⟩ := hAC z
  have hAu : Q (A u) = 0 := congrArg (fun T : D →L[ℝ] B => T u) hQA
  refine ⟨v, ?_⟩
  change Q (C v) = w
  have hsum : Q (A u + C v) = w := (congrArg Q huv).trans hz
  simpa only [map_add, hAu, zero_add] using hsum

/-- Under the same hypotheses, `Q ∘ C` is bijective as soon as the dimensions of source and target
agree. -/
theorem TransverseCoordinates.bijective_normal_comp {D Z E B : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ Z]
    [FiniteDimensional ℝ B] (Q : E →L[ℝ] B) (A : D →L[ℝ] E) (C : Z →L[ℝ] E)
    (hQ : Function.Surjective Q) (hAC : Function.Surjective (A.coprod C)) (hQA : Q.comp A = 0)
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) : Function.Bijective (Q.comp C) := by
  have hs := surjective_normal_comp Q A C hQ hAC hQA
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hs, hs⟩

/-- The projection `F →L[ℝ] Z` onto the complement `Z` determined by an invertible `G ⊕ C`. -/
def FrameField.complementQuotient {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : D →L[ℝ] F) (C : Z →L[ℝ] F) : F →L[ℝ] Z :=
  (ContinuousLinearMap.snd ℝ D Z).comp (G.coprod C).inverse

/-- The projection kills the image of `G`. -/
theorem FrameField.complementQuotient_left {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) (u : D) :
    complementQuotient G C (G u) = 0 := by
  have hi := h.inverse_apply_self (u, 0)
  change (G.coprod C).inverse (G u + C 0) = (u, 0) at hi
  rw [map_zero, add_zero] at hi
  exact congrArg Prod.snd hi

/-- The projection restricts to the identity on the complement `C`. -/
theorem FrameField.complementQuotient_right {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) (v : Z) :
    complementQuotient G C (C v) = v := by
  have hi := h.inverse_apply_self (0, v)
  change (G.coprod C).inverse (G 0 + C v) = (0, v) at hi
  rw [map_zero, zero_add] at hi
  exact congrArg Prod.snd hi

/-- The kernel of the projection is exactly the image of `G`. -/
theorem FrameField.ker_complementQuotient {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) :
    (complementQuotient G C).ker = G.range := by
  ext w
  constructor
  · intro hw
    let p := (G.coprod C).inverse w
    have hp : p.2 = 0 := hw
    have hi := h.self_apply_inverse w
    change G p.1 + C p.2 = w at hi
    rw [hp, map_zero, add_zero] at hi
    exact ⟨p.1, hi⟩
  · rintro ⟨u, rfl⟩
    exact complementQuotient_left G C h u

/-- `G ⊕ H` is bijective as soon as the projection of `H` to the complement is. -/
theorem FrameField.bijective_coprod_of_quotient {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C H : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible)
    (hH : Function.Bijective ((complementQuotient G C).comp H)) :
    Function.Bijective (G.coprod H) := by
  have hG : Function.Injective G := by
    intro u v huv
    have hpair : (G.coprod C) (u, 0) = (G.coprod C) (v, 0) := by
      change G u + C 0 = G v + C 0
      rw [huv]
    exact congrArg Prod.fst (h.injective hpair)
  constructor
  · intro p q hpq
    have hq := congrArg (complementQuotient G C) hpq
    change complementQuotient G C (G p.1 + H p.2) = complementQuotient G C (G q.1 + H q.2) at hq
    rw [map_add, map_add, complementQuotient_left G C h, complementQuotient_left G C h, zero_add,
      zero_add] at hq
    have hp₂ : p.2 = q.2 := hH.1 hq
    have hp₁ : p.1 = q.1 := by
      change G p.1 + H p.2 = G q.1 + H q.2 at hpq
      rw [hp₂] at hpq
      exact hG (add_right_cancel hpq)
    exact Prod.ext hp₁ hp₂
  · intro w
    obtain ⟨v, hv⟩ := hH.2 (complementQuotient G C w)
    have hmem : w - H v ∈ G.range := by
      rw [← ker_complementQuotient G C h]
      change complementQuotient G C (w - H v) = 0
      rw [map_sub]
      change complementQuotient G C w - ((complementQuotient G C).comp H) v = 0
      rw [hv, sub_self]
    obtain ⟨u, hu⟩ := hmem
    refine ⟨(u, v), ?_⟩
    change G u + H v = w
    change G u = w - H v at hu
    rw [hu, sub_add_cancel]

/-- The complement `C ∘ K + (L - C ∘ (complementQuotient G C) ∘ L)`, which has prescribed projection
`K` and agrees with `L` along the image of `G`. -/
def FrameField.correctedComplement {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z) : Z →L[ℝ] F :=
  L + C.comp (K - (complementQuotient G C).comp L)

/-- The corrected complement has projection exactly `K`. -/
theorem FrameField.quotient_correctedComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z)
    (h : (G.coprod C).IsInvertible) :
    (complementQuotient G C).comp (correctedComplement G C L K) = K := by
  apply ContinuousLinearMap.ext
  intro v
  change complementQuotient G C (L v + C ((K - (complementQuotient G C).comp L) v)) = K v
  rw [map_add, complementQuotient_right G C h]
  change complementQuotient G C (L v) + (K v - complementQuotient G C (L v)) = K v
  rw [← add_sub_assoc, add_sub_cancel_left]

/-- Correcting `L` by its own projection returns `L`. -/
theorem FrameField.correctedComplement_self {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) :
    correctedComplement G C L ((complementQuotient G C).comp L) = L := by
  simp only [correctedComplement, sub_self, ContinuousLinearMap.comp_zero, add_zero]

/-- `G ⊕ correctedComplement G C L K` is bijective when `K` is. -/
theorem FrameField.bijective_coprod_correctedComplement {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z)
    (h : (G.coprod C).IsInvertible) (hK : Function.Bijective K) :
    Function.Bijective (G.coprod (correctedComplement G C L K)) := by
  apply bijective_coprod_of_quotient G C _ h
  rw [quotient_correctedComplement G C L K h]
  exact hK

/-- A smooth family of coproducts is smooth. -/
theorem FrameField.contDiffOn_coprod {X D Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] {G : X → (D →L[ℝ] F)}
    {C : X → (Z →L[ℝ] F)} {U : Set X} (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (fun x => (G x).coprod (C x)) U :=
  (hG.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ D Z))).add
    (hC.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ D Z)))

/-- A smooth family of projections onto complements is smooth where the coproduct is invertible. -/
theorem FrameField.contDiffOn_complementQuotient {X D Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {G : X → (D →L[ℝ] F)} {C : X → (Z →L[ℝ] F)} {U : Set X}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hi : ∀ x ∈ U, ((G x).coprod (C x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => complementQuotient (G x) (C x)) U := by
  have hT := contDiffOn_coprod hG hC
  have hInv : ContDiffOn ℝ ∞ (fun x => ((G x).coprod (C x)).inverse) U := by
    intro x hx
    exact
      ((hi x hx).contDiffAt_map_inverse.comp x (hT.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  exact contDiffOn_const.clm_comp hInv

/-- A smooth family of corrected complements is smooth. -/
theorem FrameField.contDiffOn_correctedComplement {X D Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {G : X → (D →L[ℝ] F)} {C L : X → (Z →L[ℝ] F)} {K : X → (Z →L[ℝ] Z)}
    {U : Set X} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hL : ContDiffOn ℝ ∞ L U) (hK : ContDiffOn ℝ ∞ K U)
    (hi : ∀ x ∈ U, ((G x).coprod (C x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => correctedComplement (G x) (C x) (L x) (K x)) U :=
  hL.add (hC.clm_comp (hK.sub ((contDiffOn_complementQuotient hU hG hC hi).clm_comp hL)))

/-- The block map `(x, z) ↦ (x + A z, T z)` of `X × Z → X × F`: a shear along `X` followed by `T` on
the transverse factor. -/
def FrameField.shearedBlock {X Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) : (X × Z) →L[ℝ] (X × F) :=
  (ContinuousLinearMap.inl ℝ X F).coprod (A.prod T)

/-- The formula for the sheared block. -/
theorem FrameField.shearedBlock_apply {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (p : X × Z) :
    shearedBlock A T p = (p.1 + A p.2, T p.2) := by
  simp [shearedBlock, ContinuousLinearMap.coprod_apply]

/-- The sheared block fixes the horizontal subspace `X × {0}` pointwise. -/
theorem FrameField.shearedBlock_horizontal {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (x : X) :
    shearedBlock A T (x, 0) = (x, 0) := by simp only [shearedBlock_apply, map_zero, add_zero]

/-- The sheared block is bijective as soon as its transverse part `T` is. -/
theorem FrameField.bijective_shearedBlock {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (hi : Function.Bijective T) :
    Function.Bijective (shearedBlock A T) := by
  constructor
  · intro p q hpq
    have hz : p.2 = q.2 := hi.1 (by simpa only [shearedBlock_apply] using congrArg Prod.snd hpq)
    have hx : p.1 + A p.2 = q.1 + A q.2 := by
      simpa only [shearedBlock_apply] using congrArg Prod.fst hpq
    rw [hz] at hx
    exact Prod.ext (add_right_cancel hx) hz
  · intro q
    obtain ⟨z, hz⟩ := hi.2 q.2
    refine ⟨(q.1 - A z, z), ?_⟩
    rw [shearedBlock_apply]
    simp only [sub_add_cancel, hz]

/-- The nonlinear shear `(x, z) ↦ (x + A x z, T x z)` given by a field of sheared blocks. -/
def FrameField.shearedMap {X Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : X → (Z →L[ℝ] X)) (T : X → (Z →L[ℝ] F)) (p : X × Z) : X × F :=
  (p.1 + A p.1 p.2, T p.1 p.2)

/-- The sheared map fixes the zero section pointwise. -/
theorem FrameField.shearedMap_zero {X Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : X → (Z →L[ℝ] X)) (T : X → (Z →L[ℝ] F)) (x : X) : shearedMap A T (x, 0) = (x, 0) := by
  simp only [shearedMap, map_zero, add_zero]

/-- The sheared map is smooth over the domain of the fields. -/
theorem FrameField.contDiffOn_shearedMap {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {A : X → (Z →L[ℝ] X)} {T : X → (Z →L[ℝ] F)} {U : Set X}
    (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U) :
    ContDiffOn ℝ ∞ (shearedMap A T) (Prod.fst ⁻¹' U) :=
  (contDiffOn_fst.add ((hA.comp contDiffOn_fst (fun _ hp => hp)).clm_apply contDiffOn_snd)).prodMk
    ((hT.comp contDiffOn_fst (fun _ hp => hp)).clm_apply contDiffOn_snd)

/-- Along the zero section the derivative of the sheared map is the corresponding sheared block. -/
theorem FrameField.hasFDerivAt_shearedMap_zero {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {A : X → (Z →L[ℝ] X)} {T : X → (Z →L[ℝ] F)} {x : X}
    (hA : DifferentiableAt ℝ A x) (hT : DifferentiableAt ℝ T x) :
    HasFDerivAt (shearedMap A T) (shearedBlock (A x) (T x)) (x, 0) := by
  have hAa :
    HasFDerivAt (fun p : X × Z => A p.1) ((fderiv ℝ A x).comp (ContinuousLinearMap.fst ℝ X Z))
      (x, 0) :=
    hA.hasFDerivAt.comp (x, 0) hasFDerivAt_fst
  have hTt :
    HasFDerivAt (fun p : X × Z => T p.1) ((fderiv ℝ T x).comp (ContinuousLinearMap.fst ℝ X Z))
      (x, 0) :=
    hT.hasFDerivAt.comp (x, 0) hasFDerivAt_fst
  have hs : HasFDerivAt (fun p : X × Z => p.2) (ContinuousLinearMap.snd ℝ X Z) (x, 0) :=
    hasFDerivAt_snd
  have hf : HasFDerivAt (fun p : X × Z => p.1) (ContinuousLinearMap.fst ℝ X Z) (x, 0) :=
    hasFDerivAt_fst
  have hd := (hf.add (hAa.clm_apply hs)).prodMk (hTt.clm_apply hs)
  convert hd using 1 <;>
    first
    | rfl
    | (apply ContinuousLinearMap.ext; intro p; simp [shearedBlock_apply])

/-- The sheared block is invertible when its transverse part is. -/
theorem FrameField.isInvertible_shearedBlock {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] (A : Z →L[ℝ] X)
    (T : Z →L[ℝ] F) (hi : T.IsInvertible) : (shearedBlock A T).IsInvertible := by
  let e :=
    (LinearEquiv.ofBijective (shearedBlock A T).toLinearMap
        (bijective_shearedBlock A T hi.bijective)).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

/-- A field of invertible sheared blocks over a compact set integrates to a partial diffeomorphism
of `X × Z` onto `X × F` given by the sheared map. -/
theorem FrameField.exists_sheared_frame_chart {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] {A : X → (Z →L[ℝ] X)}
    {T : X → (Z →L[ℝ] F)} {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U) (hi : ∀ x ∈ K, (T x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, X × F) (X × Z) (X × F) ∞,
      K ×ˢ {(0 : Z)} ⊆ Φ.source ∧
        Φ.source ⊆ Prod.fst ⁻¹' U ∧ (Φ : X × Z → X × F) = shearedMap A T := by
  have hzeroInj : Set.InjOn (shearedMap A T) (K ×ˢ {(0 : Z)}) := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩ ⟨y, w⟩ ⟨hy, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [shearedMap_zero, shearedMap_zero] at heq
    exact Prod.ext (congrArg (fun q : X × F => q.1) heq) rfl
  have hlocal :
    ∀ p ∈ K ×ˢ {(0 : Z)}, IsLocalDiffeomorphAt 𝓘(ℝ, X × Z) 𝓘(ℝ, X × F) ∞ (shearedMap A T) p := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply
      isLocalDiffeomorphAt_of_contMDiffOn (D := X × Z) (E := X × F) (M := X × F)
        (hU.preimage continuous_fst) (show (x, (0 : Z)) ∈ Prod.fst ⁻¹' U from hKU hx)
        (contDiffOn_shearedMap hA hT).contMDiffOn
    rw [mfderiv_eq_fderiv,
      (hasFDerivAt_shearedMap_zero
          ((hA.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
          ((hT.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))).fderiv]
    exact isInvertible_shearedBlock (A x) (T x) (hi x hx)
  exact
    exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton) hzeroInj hlocal
      (hU.preimage continuous_fst) (fun _ hp => hKU hp.1)

/-- The shear component `V →L[ℝ] ℝ` of an endomorphism of `ℝ × V` fixing the axis vector
`(1, 0)`. -/
def AxisCoordinates.tangentShear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) : V →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ V).comp (L.comp (ContinuousLinearMap.inr ℝ ℝ V))

/-- The transverse component `V →L[ℝ] V` of such an endomorphism. -/
def AxisCoordinates.transverseBlock {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) : V →L[ℝ] V :=
  (ContinuousLinearMap.snd ℝ ℝ V).comp (L.comp (ContinuousLinearMap.inr ℝ ℝ V))

/-- The shear component depends smoothly on the endomorphism. -/
theorem AxisCoordinates.contDiff_tangentShear {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] : ContDiff ℝ ∞ (tangentShear (V := V)) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

/-- The transverse component depends smoothly on the endomorphism. -/
theorem AxisCoordinates.contDiff_transverseBlock {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] : ContDiff ℝ ∞ (transverseBlock (V := V)) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

/-- An endomorphism fixing the axis vector acts by `(s, z) ↦ (s + tangentShear z, transverseBlock
z)`. -/
theorem AxisCoordinates.axis_block_apply {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0)) (s : ℝ) (z : V) :
    L (s, z) = (s + tangentShear L z, transverseBlock L z) := by
  have hp : (s, z) = s • (1, (0 : V)) + (0, z) := by simp
  rw [hp, map_add, map_smul, hL]
  apply Prod.ext <;> simp [tangentShear, transverseBlock]

/-- Hence such an endomorphism is the sheared block of its two components. -/
theorem AxisCoordinates.axis_block_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0)) :
    L = FrameField.shearedBlock (tangentShear L) (transverseBlock L) := by
  apply ContinuousLinearMap.ext
  intro p
  rw [FrameField.shearedBlock_apply]
  exact axis_block_apply L hL p.1 p.2

/-- The transverse component of a bijective endomorphism fixing the axis is bijective. -/
theorem AxisCoordinates.bijective_transverseBlock {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0))
    (hi : Function.Bijective L) : Function.Bijective (transverseBlock L) := by
  constructor
  · intro z w hzw
    have he : L (-tangentShear L z, z) = L (-tangentShear L w, w) := by
      rw [axis_block_apply L hL, axis_block_apply L hL]
      simp only [neg_add_cancel, hzw]
    exact congrArg (fun p : ℝ × V => p.2) (hi.1 he)
  · intro w
    obtain ⟨⟨s, z⟩, hz⟩ := hi.2 (0, w)
    rw [axis_block_apply L hL] at hz
    exact ⟨z, congrArg (fun p : ℝ × V => p.2) hz⟩

/-- The transverse component of an invertible endomorphism fixing the axis is invertible. -/
theorem AxisCoordinates.isInvertible_transverseBlock {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0))
    (hi : L.IsInvertible) : (transverseBlock L).IsInvertible := by
  let e :=
    (LinearEquiv.ofBijective (transverseBlock L).toLinearMap
        (bijective_transverseBlock L hL hi.bijective)).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

/-- A map that restricts to the identity along the axis has derivative fixing the axis vector `(1,
0)`. -/
theorem AxisCoordinates.derivative_fixes_axis {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : (ℝ × V) → (ℝ × V)} {s : ℝ} (hF : ContDiffAt ℝ ∞ F (s, 0))
    (heq : (fun r : ℝ => F (r, 0)) =ᶠ[𝓝 s] (fun r => (r, (0 : V)))) :
    fderiv ℝ F (s, 0) (1, 0) = (1, 0) := by
  have ha : HasDerivAt (fun r : ℝ => (r, (0 : V))) (1, 0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s 0)
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s ha
  exact hd.deriv.symm.trans (heq.deriv_eq.trans ha.deriv)

/-- Transition data between two charts agreeing along the axis: on a neighbourhood of the parameter,
the transition fixes the axis, its derivative is the sheared block of its two components, these
depend smoothly on the parameter, and the transverse component is invertible. -/
theorem AxisCoordinates.exists_native_axis_transition_data {V E M : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) {s₀ : ℝ}
    (hΦ : (s₀, (0 : V)) ∈ Φ.source) (hΨ : (s₀, (0 : V)) ∈ Ψ.source)
    (haxis : (fun s : ℝ => Φ (s, 0)) =ᶠ[𝓝 s₀] (fun s => Ψ (s, 0))) :
    ∃ U : Set ℝ,
      IsOpen U ∧
        s₀ ∈ U ∧
          (∀ s ∈ U, (s, (0 : V)) ∈ (Φ.trans Ψ.symm).source) ∧
            (∀ s ∈ U, Ψ.symm (Φ (s, 0)) = (s, 0)) ∧
              ContDiffOn ℝ ∞ (fun s => tangentShear (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) U ∧
                ContDiffOn ℝ ∞ (fun s => transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) U ∧
                  (∀ s ∈ U, (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))).IsInvertible) ∧
                    ∀ s ∈ U,
                      fderiv ℝ (Ψ.symm ∘ Φ) (s, 0) =
                        FrameField.shearedBlock
                          (tangentShear (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0)))
                          (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) := by
  let R := Φ.trans Ψ.symm
  have hR0 : (s₀, (0 : V)) ∈ R.source := by
    refine ⟨hΦ, ?_⟩
    change Φ (s₀, 0) ∈ Ψ.target
    rw [haxis.eq_of_nhds]
    exact Ψ.map_source' hΨ
  have hRsource : ∀ᶠ s in 𝓝 s₀, (s, (0 : V)) ∈ R.source :=
    (continuous_id.prodMk continuous_const).continuousAt (R.open_source.mem_nhds hR0)
  have hΨsource : ∀ᶠ s in 𝓝 s₀, (s, (0 : V)) ∈ Ψ.source :=
    (continuous_id.prodMk continuous_const).continuousAt (Ψ.open_source.mem_nhds hΨ)
  have hRaxis : ∀ᶠ s in 𝓝 s₀, R (s, (0 : V)) = (s, 0) := by
    filter_upwards [haxis, hΨsource] with s hs hsΨ
    change Ψ.symm (Φ (s, 0)) = (s, 0)
    rw [hs]
    exact Ψ.left_inv' hsΨ
  obtain ⟨U, hUN, hU, hs₀⟩ := mem_nhds_iff.mp (hRsource.and hRaxis)
  have hdf : ContDiffOn ℝ ∞ (fun s : ℝ => fderiv ℝ R (s, (0 : V))) U :=
    (R.contMDiffOn_toFun.contDiffOn.fderiv_of_isOpen R.open_source (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun s hs => (hUN hs).1)
  have hfix (s : ℝ) (hs : s ∈ U) : fderiv ℝ R (s, (0 : V)) (1, 0) = (1, 0) := by
    apply
      derivative_fixes_axis
        (R.contMDiffOn_toFun.contDiffOn.contDiffAt (R.open_source.mem_nhds (hUN hs).1))
    filter_upwards [hU.mem_nhds hs] with r hr
    exact (hUN hr).2
  refine
    ⟨U, hU, hs₀, fun s hs => (hUN hs).1, fun s hs => (hUN hs).2,
      (contDiff_tangentShear (V := V)).contDiffOn.comp hdf (fun _ _ => Set.mem_univ _),
      (contDiff_transverseBlock (V := V)).contDiffOn.comp hdf (fun _ _ => Set.mem_univ _), ?_, ?_⟩
  · intro s hs
    have hl : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ R (s, 0) :=
      PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ R (hUN hs).1
    have hi : (fderiv ℝ R (s, 0)).IsInvertible := by
      refine ⟨hl.mfderivToContinuousLinearEquiv (by simp), ?_⟩
      have he := hl.mfderivToContinuousLinearEquiv_coe (by simp)
      rw [mfderiv_eq_fderiv] at he
      exact he
    exact isInvertible_transverseBlock _ (hfix s hs) hi
  · intro s hs
    exact axis_block_eq _ (hfix s hs)


/-- A smooth map can be modified near a point so as to have a prescribed germ there while keeping
its values and first derivatives on a set `K` and its germ outside an open set `U`. -/
theorem AxisCoordinates.exists_flat_local_correction {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H R : E → F} {K U : Set E} {x : E} (hH : ContDiff ℝ ∞ H) (hR : ContDiffOn ℝ ∞ R U)
    (hU : IsOpen U) (hx : x ∈ U) (hvalue : ∀ y ∈ K ∩ U, R y = H y)
    (hderiv : ∀ y ∈ K ∩ U, fderiv ℝ R y = fderiv ℝ H y) :
    ∃ G : E → F,
      ContDiff ℝ ∞ G ∧
        (G =ᶠ[𝓝 x] R) ∧
          (∀ y ∉ U, G =ᶠ[𝓝 y] H) ∧ Set.EqOn G H K ∧ Set.EqOn (fderiv ℝ G) (fderiv ℝ H) K := by
  obtain ⟨β, hβ, -, hsupp, hone, -⟩ :=
    exists_compact_smooth_cutoff (isCompact_singleton : IsCompact ({ x } : Set E)) hU
      (Set.singleton_subset_iff.mpr hx)
  let G : E → F := fun y => H y + β y • (R y - H y)
  have hoff (y : E) (hy : y ∉ tsupport β) : G =ᶠ[𝓝 y] H := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp only [G, hz, Pi.zero_apply, zero_smul, add_zero]
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport β
    · exact
        hH.contDiffAt.add
          (hβ.contDiffAt.smul ((hR.contDiffAt (hU.mem_nhds (hsupp hy))).sub hH.contDiffAt))
    · exact hH.contDiffAt.congr_of_eventuallyEq (hoff y hy)
  have hGeq (y : E) (hy : y ∈ K) : G y = H y := by
    by_cases hb : y ∈ tsupport β
    · simp only [G, hvalue y ⟨hy, hsupp hb⟩, sub_self, smul_zero, add_zero]
    · exact (hoff y hb).eq_of_nhds
  refine ⟨G, hG, ?_, fun y hy => hoff y (fun h => hy (hsupp h)), hGeq, ?_⟩
  · have hone' : ∀ᶠ y in 𝓝 x, β y = 1 := by simpa only [nhdsSet_singleton] using hone
    filter_upwards [hone'] with y hy
    simp only [G, hy, one_smul]
    abel
  · intro y hy
    by_cases hb : y ∈ tsupport β
    · have hr := (hR.contDiffAt (hU.mem_nhds (hsupp hb))).differentiableAt (by simp)
      have hh := hH.differentiable (by simp) y
      have hd : HasFDerivAt (fun z => R z - H z) (0 : E →L[ℝ] F) y := by
        simpa only [hderiv y ⟨hy, hsupp hb⟩, sub_self, Pi.sub_def] using
          hr.hasFDerivAt.sub hh.hasFDerivAt
      have hc : HasFDerivAt (fun z => β z • (R z - H z)) (0 : E →L[ℝ] F) y := by
        simpa only [hvalue y ⟨hy, hsupp hb⟩, sub_self, smul_zero,
          ContinuousLinearMap.smulRight_zero, add_zero, Pi.smul_def'] using
          (hβ.differentiable (by simp) y).hasFDerivAt.smul hd
      simpa only [add_zero, Pi.add_def, G] using (hh.hasFDerivAt.add hc).fderiv
    · exact (hoff y hb).fderiv_eq

/-- Two prescribed germs at `(p, 0)` and `(q, 0)`, agreeing with `H` in value and derivative along
the axis, are realised by a single smooth map agreeing with `H` in value and derivative along
the whole axis. -/
theorem AxisCoordinates.exists_axis_germ_correction {V F : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H R₀ R₁ : (ℝ × V) → F} {U₀ U₁ : Set (ℝ × V)} {p q : ℝ} (hpq : p < q) (hH : ContDiff ℝ ∞ H)
    (hR₀ : ContDiffOn ℝ ∞ R₀ U₀) (hR₁ : ContDiffOn ℝ ∞ R₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0 : (p, (0 : V)) ∈ U₀) (h1 : (q, (0 : V)) ∈ U₁)
    (hv₀ : (fun s : ℝ => R₀ (s, 0)) =ᶠ[𝓝 p] (fun s => H (s, 0)))
    (hv₁ : (fun s : ℝ => R₁ (s, 0)) =ᶠ[𝓝 q] (fun s => H (s, 0)))
    (hd₀ : (fun s : ℝ => fderiv ℝ R₀ (s, 0)) =ᶠ[𝓝 p] (fun s => fderiv ℝ H (s, 0)))
    (hd₁ : (fun s : ℝ => fderiv ℝ R₁ (s, 0)) =ᶠ[𝓝 q] (fun s => fderiv ℝ H (s, 0))) :
    ∃ G : (ℝ × V) → F,
      ContDiff ℝ ∞ G ∧
        (∀ s : ℝ, G (s, 0) = H (s, 0)) ∧
          (∀ s : ℝ, fderiv ℝ G (s, 0) = fderiv ℝ H (s, 0)) ∧
            (G =ᶠ[𝓝 (p, (0 : V))] R₀) ∧ (G =ᶠ[𝓝 (q, (0 : V))] R₁) := by
  obtain ⟨I₀, hI₀sub, hI₀, h0I⟩ := mem_nhds_iff.mp (hv₀.and hd₀)
  obtain ⟨I₁, hI₁sub, hI₁, h1I⟩ := mem_nhds_iff.mp (hv₁.and hd₁)
  let W₀ := U₀ ∩ Prod.fst ⁻¹' (I₀ ∩ Set.Iio ((p + q) / 2))
  let W₁ := U₁ ∩ Prod.fst ⁻¹' (I₁ ∩ Set.Ioi ((p + q) / 2))
  have hW₀ : IsOpen W₀ := hU₀.inter ((hI₀.inter isOpen_Iio).preimage continuous_fst)
  have hW₁ : IsOpen W₁ := hU₁.inter ((hI₁.inter isOpen_Ioi).preimage continuous_fst)
  have h0W : (p, (0 : V)) ∈ W₀ := ⟨h0, h0I, by change p < (p + q) / 2; linarith⟩
  have h1W : (q, (0 : V)) ∈ W₁ := ⟨h1, h1I, by change (p + q) / 2 < q; linarith⟩
  let K : Set (ℝ × V) := Set.univ ×ˢ {0}
  have hv0 (y : ℝ × V) (hy : y ∈ K ∩ W₀) : R₀ y = H y := by
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₀sub hy.2.2.1).1
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  have hd0 (y : ℝ × V) (hy : y ∈ K ∩ W₀) : fderiv ℝ R₀ y = fderiv ℝ H y := by
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₀sub hy.2.2.1).2
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  obtain ⟨G₀, hG₀, hg₀, -, hvG₀, hdG₀⟩ :=
    exists_flat_local_correction hH (hR₀.mono Set.inter_subset_left) hW₀ h0W hv0 hd0
  have hv1 (y : ℝ × V) (hy : y ∈ K ∩ W₁) : R₁ y = G₀ y := by
    rw [hvG₀ hy.1]
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₁sub hy.2.2.1).1
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  have hd1 (y : ℝ × V) (hy : y ∈ K ∩ W₁) : fderiv ℝ R₁ y = fderiv ℝ G₀ y := by
    rw [hdG₀ hy.1]
    have hz : y.2 = 0 := hy.1.2
    have hh := (hI₁sub hy.2.2.1).2
    exact (show (y.1, (0 : V)) = y from Prod.ext rfl hz.symm) ▸ hh
  obtain ⟨G, hG, hg₁, hoff, hvG, hdG⟩ :=
    exists_flat_local_correction hG₀ (hR₁.mono Set.inter_subset_left) hW₁ h1W hv1 hd1
  have h0not : (p, (0 : V)) ∉ W₁ := by
    intro hh
    have hbad : (p + q) / 2 < p := hh.2.2
    linarith
  refine ⟨G, hG, ?_, ?_, (hoff _ h0not).trans hg₀, hg₁⟩
  · intro s
    have hs : (s, (0 : V)) ∈ K := ⟨Set.mem_univ s, rfl⟩
    exact (hvG hs).trans (hvG₀ hs)
  · intro s
    have hs : (s, (0 : V)) ∈ K := ⟨Set.mem_univ s, rfl⟩
    exact (hdG hs).trans (hdG₀ hs)

/-- Shearing a tubular chart: a field of invertible sheared blocks over a compact set turns a
tubular chart `Ψ` into a tubular chart `Φ` with the same zero section, prescribed transition
germs and prescribed derivative along the zero section. -/
theorem FrameField.exists_sheared_tubular_chart {X Z F E M : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Ψ : PartialDiffeomorph 𝓘(ℝ, X × F) 𝓘(ℝ, E) (X × F) M ∞) {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hzero : K ×ˢ {(0 : F)} ⊆ Ψ.source) {A : X → (Z →L[ℝ] X)}
    {T : X → (Z →L[ℝ] F)} (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U)
    (hi : ∀ x ∈ K, (T x).IsInvertible) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, E) (X × Z) M ∞,
          K ×ˢ Metric.closedBall (0 : Z) ε ⊆ Φ.source ∧
            (∀ p, Φ p = Ψ (shearedMap A T p)) ∧
              Φ.target ⊆ Ψ.target ∧
                (∀ x ∈ K, (Ψ.symm ∘ Φ) =ᶠ[𝓝 (x, (0 : Z))] shearedMap A T) ∧
                  ∀ x ∈ K, HasFDerivAt (Ψ.symm ∘ Φ) (shearedBlock (A x) (T x)) (x, 0) := by
  obtain ⟨χ, hzeroχ, -, hχ⟩ := exists_sheared_frame_chart hK hU hKU hA hT hi
  let Φ := χ.trans Ψ
  have hzeroΦ : K ×ˢ {(0 : Z)} ⊆ Φ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hzeroχ ⟨hx, rfl⟩, ?_⟩
    change χ (x, 0) ∈ Ψ.source
    rw [hχ, shearedMap_zero]
    exact hzero ⟨hx, rfl⟩
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset hK Φ.open_source hzeroΦ
  have hgerm : ∀ x ∈ K, (Ψ.symm ∘ Φ) =ᶠ[𝓝 (x, (0 : Z))] shearedMap A T := by
    intro x hx
    filter_upwards [Φ.open_source.mem_nhds (hzeroΦ ⟨hx, rfl⟩)] with p hp
    change Ψ.symm (Ψ (χ p)) = shearedMap A T p
    have hpΨ : χ p ∈ Ψ.source := hp.2
    exact (Ψ.left_inv' hpΨ).trans (congrFun hχ p)
  refine ⟨ε, hε, Φ, hprod, ?_, fun _ hy => hy.1, hgerm, ?_⟩
  · intro p
    change Ψ (χ p) = Ψ (shearedMap A T p)
    rw [hχ]
  · intro x hx
    apply (hgerm x hx).hasFDerivAt_iff.mpr
    exact
      hasFDerivAt_shearedMap_zero
        ((hA.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
        ((hT.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))


/-- In finite dimension a bijective coproduct is invertible as a continuous linear map. -/
theorem FrameField.isInvertible_coprod_of_bijective {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] (G : D →L[ℝ] F)
    (C : Z →L[ℝ] F) (h : Function.Bijective (G.coprod C)) : (G.coprod C).IsInvertible := by
  let e := (LinearEquiv.ofBijective (G.coprod C).toLinearMap h).toContinuousLinearEquiv
  exact ⟨e, rfl⟩
