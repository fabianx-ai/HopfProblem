/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Immersion.Relative.AffinePerturbation
import Lib.Geometry.Manifold.Whitney.FrameField.BlockDeterminant

/-!
# Intersection coordinates of two sheets

Two sheet frames `P : ℝ × A →L Plane × F` and `Q : ℝ × B →L Plane × F`, together with a splitting
`j : A × B ≃L F` of the normal space, give the joint block
`IntersectionCoordinates.jointBlock j P Q`, an endomorphism of `Plane × (A × B)` whose determinant
is the intersection sign of the two sheets. When the first columns of `P` and `Q` lie in the plane
directions, this determinant factors as the planar determinant of the two tangent vectors times the
determinant of the two normal blocks (`IntersectionCoordinates.det_jointBlock`); it also equals the
determinant of `P ⊞ Q` in regrouped coordinates
(`IntersectionCoordinates.det_jointBlock_eq_tangentSum`).

The file also transports a complement `H` of a reference frame `W₀ ⊞ B₀` to a frame `W ⊞ B`
(`FrameField.transportComplement`), preserving invertibility and smoothness in parameters.

Cf. Milnor, *Lectures on the h-cobordism theorem*, §6 (the intersection number of two transverse
sheets as a determinant sign).

## Tags

intersection sign, frame, determinant
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- The endomorphism of `Plane × (A × B)` built from two sheet frames `P` and `Q`: the plane
coordinates record the two tangent directions and the remaining coordinates the two normal
blocks, read through the splitting `j`. -/
def IntersectionCoordinates.jointBlock {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F) (P : (ℝ × A) →L[ℝ] (PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (PlaneImmersion.Plane × F)) :
    (PlaneImmersion.Plane × (A × B)) →L[ℝ] (PlaneImmersion.Plane × (A × B)) :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ PlaneImmersion.Plane)
        j.symm).toContinuousLinearMap.comp
    ((P.coprod Q).comp
      (ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B).symm.toContinuousLinearMap)

/-- Value of the joint block: the plane component is the first component of the sum of the two
frames, and the remaining component is that sum read through `j⁻¹`. -/
theorem IntersectionCoordinates.jointBlock_apply {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F) (P : (ℝ × A) →L[ℝ] (PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (PlaneImmersion.Plane × F))
    (p : PlaneImmersion.Plane × (A × B)) :
    jointBlock j P Q p =
      ((P (p.1.1, p.2.1) + Q (p.1.2, p.2.2)).1,
        j.symm ((P (p.1.1, p.2.1) + Q (p.1.2, p.2.2)).2)) :=
  rfl

/-- A continuous linear map is homogeneous along the first axis: `P (s, 0) = s • P (1, 0)`. -/
theorem IntersectionCoordinates.map_first_axis {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : (ℝ × A) →L[ℝ] (PlaneImmersion.Plane × F)) (s : ℝ) : P (s, 0) = s • P (1, 0) := by
  have hs : (s, (0 : A)) = s • ((1 : ℝ), 0) := by ext <;> simp
  rw [hs, map_smul]

/-- If the two frames have first columns `(u, 0)` and `(v, 0)` in the plane directions, the
determinant of their joint block factors as the planar determinant of `(u, v)` times the
determinant of the two normal blocks. -/
theorem IntersectionCoordinates.det_jointBlock {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] (j : (A × B) ≃L[ℝ] F)
    (P : (ℝ × A) →L[ℝ] (PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (PlaneImmersion.Plane × F)) {u v : PlaneImmersion.Plane}
    (hP : P (1, 0) = (u, 0)) (hQ : Q (1, 0) = (v, 0)) :
    (jointBlock j P Q).toLinearMap.det =
      (PlaneImmersion.linearMap (u, v)).toLinearMap.det *
        (j.symm.toContinuousLinearMap.comp
            (((ContinuousLinearMap.snd ℝ PlaneImmersion.Plane F).comp
                  (P.comp (ContinuousLinearMap.inr ℝ ℝ A))).coprod
              ((ContinuousLinearMap.snd ℝ PlaneImmersion.Plane F).comp
                (Q.comp (ContinuousLinearMap.inr ℝ ℝ B))))).toLinearMap.det := by
  have hzero : ∀ w : PlaneImmersion.Plane, (jointBlock j P Q (w, 0)).2 = 0 := by
    intro w
    rw [jointBlock_apply]
    change j.symm ((P (w.1, 0) + Q (w.2, 0)).2) = 0
    rw [map_first_axis P w.1, map_first_axis Q w.2, hP, hQ]
    simp
  have hfirst :
    (ContinuousLinearMap.fst ℝ PlaneImmersion.Plane (A × B)).comp
        ((jointBlock j P Q).comp (ContinuousLinearMap.inl ℝ PlaneImmersion.Plane (A × B))) =
      PlaneImmersion.linearMap (u, v) := by
    apply ContinuousLinearMap.ext
    intro w
    change (jointBlock j P Q (w, 0)).1 = w.1 • u + w.2 • v
    rw [jointBlock_apply]
    change (P (w.1, 0) + Q (w.2, 0)).1 = w.1 • u + w.2 • v
    rw [map_first_axis P w.1, map_first_axis Q w.2, hP, hQ]
    rfl
  have hsecond :
    (ContinuousLinearMap.snd ℝ PlaneImmersion.Plane (A × B)).comp
        ((jointBlock j P Q).comp (ContinuousLinearMap.inr ℝ PlaneImmersion.Plane (A × B))) =
      j.symm.toContinuousLinearMap.comp
        (((ContinuousLinearMap.snd ℝ PlaneImmersion.Plane F).comp
              (P.comp (ContinuousLinearMap.inr ℝ ℝ A))).coprod
          ((ContinuousLinearMap.snd ℝ PlaneImmersion.Plane F).comp
            (Q.comp (ContinuousLinearMap.inr ℝ ℝ B)))) := by
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [FrameField.det_of_zero_lower_left _ hzero, hfirst, hsecond]


/-- The coproduct of two maps is bijective irrespective of the order of the two blocks. -/
theorem FrameField.bijective_coprod_comm {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (H : Z →L[ℝ] F) (hi : Function.Bijective (H.coprod W)) :
    Function.Bijective (W.coprod H) := by
  have heq :
    W.coprod H = (H.coprod W).comp (ContinuousLinearEquiv.prodComm ℝ D Z).toContinuousLinearMap :=
    by
    apply ContinuousLinearMap.ext
    intro p
    change W p.1 + H p.2 = H p.2 + W p.1
    exact add_comm _ _
  rw [heq]
  exact hi.comp (ContinuousLinearEquiv.prodComm ℝ D Z).bijective

/-- The complement `H` of the reference frame `W₀ ⊞ B₀`, transported to the frame `W ⊞ B`. -/
def FrameField.transportComplement {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : D →L[ℝ] F) (B : Z →L[ℝ] F) (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F) : Z →L[ℝ] F :=
  (W.coprod B).comp ((W₀.coprod B₀).inverse.comp H)

/-- Transporting a complement along the identity frame does nothing. -/
theorem FrameField.transportComplement_self {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (B H : Z →L[ℝ] F) (h : (W.coprod B).IsInvertible) :
    transportComplement W B W B H = H := by
  apply ContinuousLinearMap.ext
  intro z
  exact h.self_apply_inverse (H z)

/-- The transported complement is characterised by `W ⊞ transport H = (W ⊞ B) ∘ (W₀ ⊞ B₀)⁻¹ ∘ (W₀ ⊞
H)`. -/
theorem FrameField.coprod_transportComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (B : Z →L[ℝ] F) (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F)
    (h₀ : (W₀.coprod B₀).IsInvertible) :
    W.coprod (transportComplement W B W₀ B₀ H) =
      ((W.coprod B).comp (W₀.coprod B₀).inverse).comp (W₀.coprod H) := by
  have hfirst (u : D) : (W₀.coprod B₀).inverse (W₀ u) = (u, 0) := by
    simpa only [ContinuousLinearMap.coprod_apply, map_zero, add_zero] using
      h₀.inverse_apply_self (u, 0)
  apply ContinuousLinearMap.ext
  intro p
  simp only [transportComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coprod_apply, map_add, hfirst, map_zero, add_zero]

/-- Transport preserves invertibility of a frame: if `W₀ ⊞ H` is bijective then so is `W ⊞ transport
H`. -/
theorem FrameField.bijective_transportComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : D →L[ℝ] F) (B : Z →L[ℝ] F) (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F)
    (h : (W.coprod B).IsInvertible) (h₀ : (W₀.coprod B₀).IsInvertible)
    (hH : Function.Bijective (W₀.coprod H)) :
    Function.Bijective (W.coprod (transportComplement W B W₀ B₀ H)) := by
  rw [coprod_transportComplement W B W₀ B₀ H h₀]
  exact (h.bijective.comp h₀.inverse.bijective).comp hH

/-- The transported complement depends smoothly on a parameter when all five data do and the
reference frame stays invertible. -/
theorem FrameField.contDiffOn_transportComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {W W₀ : X → (D →L[ℝ] F)} {B B₀ H : X → (Z →L[ℝ] F)} {U : Set X}
    (hU : IsOpen U) (hW : ContDiffOn ℝ ∞ W U) (hB : ContDiffOn ℝ ∞ B U)
    (hW₀ : ContDiffOn ℝ ∞ W₀ U) (hB₀ : ContDiffOn ℝ ∞ B₀ U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : ∀ x ∈ U, ((W₀ x).coprod (B₀ x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => transportComplement (W x) (B x) (W₀ x) (B₀ x) (H x)) U := by
  have hT₀ := contDiffOn_coprod hW₀ hB₀
  have hInv : ContDiffOn ℝ ∞ (fun x => ((W₀ x).coprod (B₀ x)).inverse) U := by
    intro x hx
    exact
      ((hi x hx).contDiffAt_map_inverse.comp x (hT₀.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  exact (contDiffOn_coprod hW hB).clm_comp (hInv.clm_comp hH)


/-- The regrouping `(ℝ × A) × (ℝ × B) ≃ Plane × F` splitting off the two tangent directions, built
from a splitting `j : A × B ≃ F`. -/
def IntersectionCoordinates.pairCoordinates {A B F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F) :
    ((ℝ × A) × (ℝ × B)) ≃L[ℝ] (PlaneImmersion.Plane × F) :=
  (ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B).trans
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ PlaneImmersion.Plane) j)

/-- The determinant of the joint block of two frames equals the determinant of their coproduct read
in the regrouped coordinates. -/
theorem IntersectionCoordinates.det_jointBlock_eq_tangentSum {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (A × B) ≃L[ℝ] F)
    (P : (ℝ × A) →L[ℝ] (PlaneImmersion.Plane × F))
    (Q : (ℝ × B) →L[ℝ] (PlaneImmersion.Plane × F)) :
    (jointBlock j P Q).det =
      ((pairCoordinates j).symm.toContinuousLinearMap.comp (P.coprod Q)).det := by
  let k := ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B
  let T := (pairCoordinates j).symm.toContinuousLinearMap.comp (P.coprod Q)
  have heq :
    (jointBlock j P Q).toLinearMap =
      k.toLinearEquiv.toLinearMap.comp (T.toLinearMap.comp k.symm.toLinearEquiv.toLinearMap) := by
    apply LinearMap.ext
    intro z
    rfl
  change (jointBlock j P Q).toLinearMap.det = T.toLinearMap.det
  rw [heq]
  exact LinearMap.det_conj T.toLinearMap k.toLinearEquiv

end
