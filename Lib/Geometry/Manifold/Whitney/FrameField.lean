/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.AnnularExtension

/-!
# Frame fields along tubular bigons

Frame fields along a tubular Whitney bigon: planar frames and the two components of `GL₂(ℝ)`,
intersection coordinates of two sheets, disk framings, the strip normal data of the two boundary
arcs, native sheet coordinates, and the invertibility of coproducts of frame maps.

The Whitney trick needs a field of frames over the Whitney disc restricting on the two boundary
arcs to the normal frames of the two sheets; such a field exists when the two intersection points
have opposite signs, which is the content of the frame-existence statements here
(`TubularBigon.exists_rankThree_adapted_frame_of_opposite_corner_signs`).

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6 (the Whitney trick and the
  framing of the Whitney disc).

## Tags

Morse theory, Whitney trick, handle cancellation
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- The lower boundary arc of the standard planar bigon: the segment `t ↦ (2 t - 1, 0)`, `t ∈ [0,
1]`. -/
def WhitneyPairModel.lowerBoundaryArc (t : ℝ) : ℝ × ℝ :=
  (2 * t - 1, 0)

/-- The upper boundary arc of the standard planar bigon of height `h`: the parabolic arc `t ↦ (2 t -
1, h (1 - (2 t - 1)^2))`, `t ∈ [0, 1]`. -/
def WhitneyPairModel.upperBoundaryArc (h t : ℝ) : ℝ × ℝ :=
  (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))

/-- The lower boundary arc has constant velocity `(2, 0)`. -/
theorem WhitneyPairModel.hasDerivAt_lowerBoundaryArc (t : ℝ) :
    HasDerivAt lowerBoundaryArc (2, 0) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  exact hs.prodMk (hasDerivAt_const t (0 : ℝ))

/-- The upper boundary arc has velocity `(2, -4 h (2 t - 1))` at time `t`. -/
theorem WhitneyPairModel.hasDerivAt_upperBoundaryArc (h t : ℝ) :
    HasDerivAt (upperBoundaryArc h) (2, -4 * h * (2 * t - 1)) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  have hy : HasDerivAt (fun s : ℝ => h * (1 - (2 * s - 1) ^ 2)) (-4 * h * (2 * t - 1)) t := by
    convert HasDerivAt.const_mul h ((hasDerivAt_const t (1 : ℝ)).sub (hs.pow 2)) using 1 <;>
      first
      | rfl
      | ring
  exact hs.prodMk hy

/-- The lower boundary arc stays inside the bigon on the parameter interval `[0, 1]`. -/
theorem TubularBigon.lowerBoundaryArc_mem_bigon {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    WhitneyPairModel.lowerBoundaryArc t ∈ WhitneyPairModel.bigon h := by
  have hf :
    WhitneyPairModel.lowerBoundaryArc t ∈ frontier (WhitneyPairModel.bigon h) :=
    (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
      ⟨t, ht, Or.inl rfl⟩
  exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1

/-- The upper boundary arc stays inside the bigon on the parameter interval `[0, 1]`. -/
theorem TubularBigon.upperBoundaryArc_mem_bigon {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    WhitneyPairModel.upperBoundaryArc h t ∈ WhitneyPairModel.bigon h := by
  have hf :
    WhitneyPairModel.upperBoundaryArc h t ∈ frontier (WhitneyPairModel.bigon h) :=
    (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
      ⟨t, ht, Or.inr rfl⟩
  exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1

/-- The zero section over a point of the lower boundary arc lies in the source of the tubular chart
of a tubular bigon. -/
theorem TubularBigon.lowerBoundaryArc_zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (WhitneyPairModel.lowerBoundaryArc t, 0) ∈ tube.chart.source :=
  tube.source_contains
    ⟨tube.lowerBoundaryArc_mem_bigon ht, Metric.mem_closedBall_self tube.radius_pos.le⟩

/-- The zero section over a point of the upper boundary arc lies in the source of the tubular chart
of a tubular bigon. -/
theorem TubularBigon.upperBoundaryArc_zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (WhitneyPairModel.upperBoundaryArc h t, 0) ∈ tube.chart.source :=
  tube.source_contains
    ⟨tube.upperBoundaryArc_mem_bigon ht, Metric.mem_closedBall_self tube.radius_pos.le⟩

/-- Along the lower sheet, the centre line of a strip chart lands in the target of the tubular chart
of the bigon. -/
theorem TubularBigon.lower_chart_center_mem_target {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.chart (StripCoordinates.center t) ∈ tube.chart.target := by
  have hg := (tube.lower_germ t ht).eq_of_nhds
  dsimp only [Function.comp_apply] at hg
  rw [WhitneyPairModel.lowerStripCoordinates_lower, d.center t] at hg
  have hp := tube.chart.map_source' (tube.lowerBoundaryArc_zero_mem_source ht)
  rw [tube.zero_section, WhitneyPairModel.lowerBoundaryArc, hg] at hp
  exact hp

/-- Along the upper sheet, the centre line of a strip chart lands in the target of the tubular chart
of the bigon. -/
theorem TubularBigon.upper_chart_center_mem_target {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.chart (StripCoordinates.center t) ∈ tube.chart.target := by
  have hg := (tube.upper_germ t ht).eq_of_nhds
  dsimp only [Function.comp_apply] at hg
  rw [WhitneyPairModel.upperStripCoordinates_upper, d.center t] at hg
  have hp := tube.chart.map_source' (tube.upperBoundaryArc_zero_mem_source ht)
  rw [tube.zero_section, WhitneyPairModel.upperBoundaryArc, hg] at hp
  exact hp

/-- Near each parameter `t ∈ [0, 1]`, the transition from the strip chart of the lower sheet to the
tubular chart of the bigon carries the centre line onto the lower boundary arc, with vanishing
normal component. -/
theorem TubularBigon.lower_sheetTransition_center_germ {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.sheetTransition tube.chart (s, 0)) =ᶠ[𝓝 t] fun s =>
      (WhitneyPairModel.lowerBoundaryArc s, 0) :=
  d.sheetTransition_center_germ tube.chart tube.zero_section
    (WhitneyPairModel.hasDerivAt_lowerBoundaryArc t).continuousAt
    (tube.lowerBoundaryArc_zero_mem_source ht)
    (WhitneyPairModel.lowerStripCoordinates_lower h) (tube.lower_germ t ht)

/-- Near each parameter `t ∈ [0, 1]`, the transition from the strip chart of the upper sheet to the
tubular chart of the bigon carries the centre line onto the upper boundary arc, with vanishing
normal component. -/
theorem TubularBigon.upper_sheetTransition_center_germ {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.sheetTransition tube.chart (s, 0)) =ᶠ[𝓝 t] fun s =>
      (WhitneyPairModel.upperBoundaryArc h s, 0) :=
  d.sheetTransition_center_germ tube.chart tube.zero_section
    (WhitneyPairModel.hasDerivAt_upperBoundaryArc h t).continuousAt
    (tube.upperBoundaryArc_zero_mem_source ht)
    (WhitneyPairModel.upperStripCoordinates_upper h) (tube.upper_germ t ht)

/-- The differential of the lower sheet transition sends the unit tangent of the centre line to the
velocity `((2, 0), 0)` of the lower boundary arc. -/
theorem TubularBigon.lower_sheetDifferential_arc {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.sheetDifferential tube.chart t (1, 0) = ((2, 0), 0) :=
  d.sheetDifferential_arc_of_germ tube.chart ht (tube.lower_chart_center_mem_target d ht)
    (WhitneyPairModel.hasDerivAt_lowerBoundaryArc t)
    (tube.lower_sheetTransition_center_germ d ht)

/-- The differential of the upper sheet transition sends the unit tangent of the centre line to the
velocity `((2, -4 h (2 t - 1)), 0)` of the upper boundary arc. -/
theorem TubularBigon.upper_sheetDifferential_arc {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.sheetDifferential tube.chart t (1, 0) = ((2, -4 * h * (2 * t - 1)), 0) :=
  d.sheetDifferential_arc_of_germ tube.chart ht (tube.upper_chart_center_mem_target d ht)
    (WhitneyPairModel.hasDerivAt_upperBoundaryArc h t)
    (tube.upper_sheetTransition_center_germ d ht)

/-- An endomorphism of `D × Z` preserving the first factor `D × {0}` is block triangular, so its
determinant is the product of the determinants of its two diagonal blocks. -/
theorem FrameField.det_of_zero_lower_left {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (T : (D × Z) →L[ℝ] (D × Z)) (hT : ∀ u : D, (T (u, 0)).2 = 0) :
    T.toLinearMap.det =
      ((ContinuousLinearMap.fst ℝ D Z).comp
            (T.comp (ContinuousLinearMap.inl ℝ D Z))).toLinearMap.det *
        ((ContinuousLinearMap.snd ℝ D Z).comp
            (T.comp (ContinuousLinearMap.inr ℝ D Z))).toLinearMap.det := by
  classical
  let bD := Module.finBasis ℝ D
  let bZ := Module.finBasis ℝ Z
  let A := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inl ℝ D Z))
  let B := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  let K := (ContinuousLinearMap.snd ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  have hmat :
    LinearMap.toMatrix (bD.prod bZ) (bD.prod bZ) T.toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix bD bD A.toLinearMap)
        (LinearMap.toMatrix bZ bD B.toLinearMap) 0 (LinearMap.toMatrix bZ bZ K.toLinearMap) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply, hT, A, B, K]
  rw [← LinearMap.det_toMatrix (bD.prod bZ), hmat, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

/-- An endomorphism of `D × Z` fixing the first factor `D × {0}` pointwise has the determinant of
its lower right block on `Z`. -/
theorem FrameField.det_of_fixed_first_factor {D Z : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (T : (D × Z) →L[ℝ] (D × Z)) (hT : ∀ u : D, T (u, 0) = (u, 0)) :
    T.toLinearMap.det =
      ((ContinuousLinearMap.snd ℝ D Z).comp
          (T.comp (ContinuousLinearMap.inr ℝ D Z))).toLinearMap.det := by
  classical
  let bD := Module.finBasis ℝ D
  let bZ := Module.finBasis ℝ Z
  let B := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  let K := (ContinuousLinearMap.snd ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  have hmat :
    LinearMap.toMatrix (bD.prod bZ) (bD.prod bZ) T.toLinearMap =
      Matrix.fromBlocks 1 (LinearMap.toMatrix bZ bD B.toLinearMap) 0
        (LinearMap.toMatrix bZ bZ K.toLinearMap) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, hT, B, K, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.det_toMatrix (bD.prod bZ), hmat, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    one_mul, LinearMap.det_toMatrix]

/-- Replacing the second block `C` of an invertible frame `G ⊞ C` by a map `L` multiplies the
determinant of the frame by the determinant of `L` read in the quotient complement of the range
of `G`. -/
theorem FrameField.det_frame_eq_det_split_mul_det_coefficient {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : (D × Z) ≃L[ℝ] F) (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).toLinearMap.det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).toLinearMap.det *
        ((complementQuotient G C).comp L).toLinearMap.det := by
  let T := G.coprod C
  let R := G.coprod L
  let A := T.inverse.comp R
  have hA : ∀ u : D, A (u, 0) = (u, 0) := by
    intro u
    change T.inverse (G u + L 0) = (u, 0)
    rw [map_zero, add_zero]
    have hi := h.inverse_apply_self (u, 0)
    change T.inverse (G u + C 0) = (u, 0) at hi
    simpa only [map_zero, add_zero] using hi
  have hblock :
    (ContinuousLinearMap.snd ℝ D Z).comp (A.comp (ContinuousLinearMap.inr ℝ D Z)) =
      (complementQuotient G C).comp L := by
    apply ContinuousLinearMap.ext
    intro v
    change (T.inverse (G 0 + L v)).2 = (T.inverse (L v)).2
    rw [map_zero, zero_add]
  have hdetA : A.toLinearMap.det = ((complementQuotient G C).comp L).toLinearMap.det := by
    rw [det_of_fixed_first_factor A hA, hblock]
  have hfactor :
    j.symm.toContinuousLinearMap.comp R = (j.symm.toContinuousLinearMap.comp T).comp A := by
    apply ContinuousLinearMap.ext
    intro v
    change j.symm (R v) = j.symm (T (T.inverse (R v)))
    rw [h.self_apply_inverse]
  change (j.symm.toContinuousLinearMap.comp R).toLinearMap.det = _
  rw [hfactor]
  have hmul :
    ((j.symm.toContinuousLinearMap.comp T).comp A).toLinearMap.det =
      (j.symm.toContinuousLinearMap.comp T).toLinearMap.det * A.toLinearMap.det :=
    map_mul LinearMap.det _ _
  rw [hmul, hdetA]

/-- The area form of two vectors of the plane: the determinant `u₁ v₂ - u₂ v₁`. -/
def PlanarFrame.area (u v : PlaneImmersion.Plane) : ℝ :=
  u.1 * v.2 - u.2 * v.1

/-- The squared Euclidean length of a plane vector. -/
def PlanarFrame.squareLength (u : PlaneImmersion.Plane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

/-- The quarter turn of the plane, `(u₁, u₂) ↦ (-u₂, u₁)`. -/
def PlanarFrame.quarterTurn (u : PlaneImmersion.Plane) : PlaneImmersion.Plane :=
  (-u.2, u.1)

/-- The coefficient of `v` along `u` in the orthogonal basis `(u, quarterTurn u)`. -/
def PlanarFrame.parallelCoeff (u v : PlaneImmersion.Plane) : ℝ :=
  (u.1 * v.1 + u.2 * v.2) / squareLength u

/-- The coefficient of `v` along `quarterTurn u` in the orthogonal basis `(u, quarterTurn u)`. -/
def PlanarFrame.transverseCoeff (u v : PlaneImmersion.Plane) : ℝ :=
  area u v / squareLength u

/-- The determinant of an endomorphism of the plane, as the area of its two columns. -/
def PlanarFrame.determinant
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) : ℝ :=
  area (L (1, 0)) (L (0, 1))

/-- A nonzero plane vector has positive squared length. -/
theorem PlanarFrame.squareLength_pos {u : PlaneImmersion.Plane} (hu : u ≠ 0) :
    0 < squareLength u := by
  have hsq₁ := sq_nonneg u.1
  have hsq₂ := sq_nonneg u.2
  by_contra h
  have hz : u.1 ^ 2 + u.2 ^ 2 ≤ 0 := le_of_not_gt h
  have hu₁ : u.1 = 0 := by nlinarith
  have hu₂ : u.2 = 0 := by nlinarith
  exact hu (Prod.ext hu₁ hu₂)

/-- For `u ≠ 0`, the basis `(u, quarterTurn u)` decomposes every plane vector: `v = parallelCoeff u
v • u + transverseCoeff u v • quarterTurn u`. -/
theorem PlanarFrame.decompose_second_column {u : PlaneImmersion.Plane} (hu : u ≠ 0)
    (v : PlaneImmersion.Plane) :
    parallelCoeff u v • u + transverseCoeff u v • quarterTurn u = v := by
  have hnorm := (squareLength_pos hu).ne'
  ext <;> dsimp [parallelCoeff, transverseCoeff, area, quarterTurn]
  · field_simp
    simp only [squareLength]
    ring
  · field_simp
    simp only [squareLength]
    ring

/-- The area of `u` with a vector written in the basis `(u, quarterTurn u)` reads off the transverse
coefficient: `area u (a • u + b • quarterTurn u) = b * squareLength u`. -/
theorem PlanarFrame.area_transverse (u : PlaneImmersion.Plane) (a b : ℝ) :
    area u (a • u + b • quarterTurn u) = b * squareLength u := by
  dsimp [area, quarterTurn, squareLength]
  ring

/-- The plane endomorphism with columns `(u, v)` sends the first basis vector to `u`. -/
theorem PlanarFrame.linearMap_first (u v : PlaneImmersion.Plane) :
    PlaneImmersion.linearMap (u, v) (1, 0) = u := by
  simp [PlaneImmersion.linearMap_apply]

/-- The plane endomorphism with columns `(u, v)` sends the second basis vector to `v`. -/
theorem PlanarFrame.linearMap_second (u v : PlaneImmersion.Plane) :
    PlaneImmersion.linearMap (u, v) (0, 1) = v := by
  simp [PlaneImmersion.linearMap_apply]

/-- An endomorphism of the plane is the endomorphism whose columns are its values on the two basis
vectors. -/
theorem PlanarFrame.linearMap_columns
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) :
    PlaneImmersion.linearMap (L (1, 0), L (0, 1)) = L := by
  apply ContinuousLinearMap.ext
  intro p
  have hp : p = p.1 • ((1 : ℝ), 0) + p.2 • (0, 1) := by ext <;> simp
  rw [PlaneImmersion.linearMap_apply, ← map_smul, ← map_smul, ← map_add, ← hp]

/-- The determinant of the plane endomorphism with columns `(u, v)` is the area of `u` and `v`. -/
theorem PlanarFrame.determinant_linearMap (u v : PlaneImmersion.Plane) :
    determinant (PlaneImmersion.linearMap (u, v)) = area u v := by
  rw [determinant, linearMap_first, linearMap_second]

/-- The planar determinant agrees with the determinant of the underlying linear map. -/
theorem PlanarFrame.determinant_eq_det
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) :
    determinant L = L.toLinearMap.det := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr, determinant, area, mul_comm]

/-- An endomorphism of the plane with nonzero determinant is bijective. -/
theorem PlanarFrame.bijective_of_determinant_ne_zero
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (hL : determinant L ≠ 0) :
    Function.Bijective L := by
  have hdet : L.toLinearMap.det ≠ 0 := by rwa [determinant_eq_det] at hL
  have hker : L.toLinearMap.ker = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hi : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

/-- The determinant is continuous on endomorphisms of the plane. -/
theorem PlanarFrame.continuous_determinant : Continuous determinant := by
  have h₁ :
    Continuous
      (fun L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane => L (1, 0)) :=
    continuous_id.clm_apply continuous_const
  have h₂ :
    Continuous
      (fun L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane => L (0, 1)) :=
    continuous_id.clm_apply continuous_const
  exact (h₁.fst.mul h₂.snd).sub (h₁.snd.mul h₂.fst)

/-- The quarter turn is continuous. -/
theorem PlanarFrame.continuous_quarterTurn : Continuous quarterTurn :=
  continuous_snd.neg.prodMk continuous_fst

/-- Assembling an endomorphism of the plane from its two columns is continuous. -/
theorem PlanarFrame.continuous_linearMap :
    Continuous
      (PlaneImmersion.linearMap :
        (PlaneImmersion.Plane × PlaneImmersion.Plane) →
          (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane)) := by
  exact
    ((ContinuousLinearMap.smulRightL ℝ PlaneImmersion.Plane PlaneImmersion.Plane
              (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.comp
          continuous_fst).add
      ((ContinuousLinearMap.smulRightL ℝ PlaneImmersion.Plane PlaneImmersion.Plane
            (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.comp
        continuous_snd)

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

/-- In an inner-product space, the coproduct of two injective maps is bijective as soon as the range
of the second is the orthogonal complement of the range of the first. -/
theorem FrameField.bijective_coprod_of_orthogonal_range {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : D →L[ℝ] F)
    (B : Z →L[ℝ] F) (hL : Function.Injective L) (hB : Function.Injective B)
    (hr : B.range = L.rangeᗮ) : Function.Bijective (L.coprod B) := by
  have hd : Disjoint L.range B.range := by
    rw [hr]
    exact L.range.orthogonal_disjoint
  constructor
  · change Function.Injective (L.toLinearMap.coprod B.toLinearMap)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
      LinearMap.ker_eq_bot.mpr hL, LinearMap.ker_eq_bot.mpr hB, Submodule.prod_bot]
  · change Function.Surjective (L.toLinearMap.coprod B.toLinearMap)
    rw [← LinearMap.range_eq_top, LinearMap.range_coprod, hr]
    exact L.range.isCompl_orthogonal.sup_eq_top

/-- A smooth family of injective maps `L x : D →L F` on a neighbourhood of a compact star-shaped set
`K` admits a smooth family of complements: a family `B` whose range is `(L x)ᗮ` on `K` and for
which `L x ⊞ B x` is bijective on a neighbourhood of `K`. -/
theorem FrameField.exists_smooth_complement_near_starConvex_on {E D F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {L : E → (D →L[ℝ] F)} {O : Set E} (hO : IsOpen O) (hL : ContDiffOn ℝ ∞ L O) {K : Set E}
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K) (h0 : (0 : E) ∈ K) (hKO : K ⊆ O)
    (hi : ∀ x ∈ K, Function.Injective (L x)) (n : ℕ)
    (hdim : Module.finrank ℝ D + n = Module.finrank ℝ F) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ B : E → (EuclideanSpace ℝ (Fin n) →L[ℝ] F),
            ContDiffOn ℝ ∞ B V ∧
              (∀ x ∈ K, (B x).range = (L x).rangeᗮ) ∧
                ∀ x ∈ V, Function.Bijective ((L x).coprod (B x)) := by
  let φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ D)) ≃L[ℝ] D :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let A (x : E) := (L x).comp φ.toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A O := hL.clm_comp contDiffOn_const
  have hAr (x : E) : (A x).range = (L x).range :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
  let U : Set E := O ∩ {x | Function.Injective (L x)}
  have hU : IsOpen U :=
    hL.continuousOn.isOpen_inter_preimage hO ContinuousLinearMap.isOpen_injective
  have hKU : K ⊆ U := fun x hx => ⟨hKO hx, hi x hx⟩
  let P (x : E) : F →L[ℝ] F := 1 - gramProjection (A x)
  have hP (x : E) (hx : x ∈ U) : P x = ((L x).rangeᗮ).starProjection := by
    dsimp only [P]
    rw [gramProjection_eq_starProjection _ (hx.2.comp φ.injective)]
    simp only [hAr]
    exact (Submodule.starProjection_orthogonal' (L x).range).symm
  have hsP : ContDiffOn ℝ ∞ P U := by
    intro x hx
    have hg : ContDiffAt ℝ ∞ (fun y => gramProjection (A y)) x :=
      (contMDiffAt_gramProjection (hA.contDiffAt (hO.mem_nhds hx.1)).contMDiffAt
          (hx.2.comp φ.injective)).contDiffAt
    exact (contDiffAt_const.sub hg).contDiffWithinAt
  have hidem : ∀ x ∈ K, IsIdempotentElem (P x) := by
    intro x hx
    rw [hP x (hKU hx)]
    exact ((L x).rangeᗮ).isIdempotentElem_starProjection
  obtain ⟨W, hW, hKW, B₀, hB₀, hB₀i⟩ :=
    DiskFraming.exists_smooth_frame_near_starConvex hK hstar hU hKU P hidem hsP
  have hr (x : E) (hx : x ∈ K) : (P x).range = (L x).rangeᗮ := by
    rw [hP x (hKU hx), Submodule.range_starProjection]
  have hcenter : Module.finrank ℝ (P 0).range = n := by
    have hrank : Module.finrank ℝ (L 0).range = Module.finrank ℝ D :=
      LinearMap.finrank_range_of_inj (hi 0 h0)
    have hs := (L 0).range.finrank_add_finrank_orthogonal
    rw [hrank] at hs
    rw [hr 0 h0]
    omega
  let ψ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (P 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  let B (x : E) := (B₀ x).comp ψ.toContinuousLinearMap
  have hB : ContDiffOn ℝ ∞ B (W ∩ O) := (hB₀.clm_comp contDiffOn_const).mono Set.inter_subset_left
  have hBr : ∀ x ∈ K, (B x).range = (L x).rangeᗮ := by
    intro x hx
    calc
      (B x).range = (B₀ x).range :=
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr ψ.surjective)
      _ = (P x).range := (hB₀i x hx).2
      _ = (L x).rangeᗮ := hr x hx
  have hBi : ∀ x ∈ K, Function.Injective (B x) := fun x hx => (hB₀i x hx).1.comp ψ.injective
  let T (x : E) := (L x).coprod (B x)
  have hT : ContDiffOn ℝ ∞ T (W ∩ O) := by
    have hs :=
      ((hL.mono Set.inter_subset_right).clm_comp
            (contDiffOn_const (c := ContinuousLinearMap.fst ℝ D (EuclideanSpace ℝ (Fin n))))).add
        (hB.clm_comp
          (contDiffOn_const (c := ContinuousLinearMap.snd ℝ D (EuclideanSpace ℝ (Fin n)))))
    exact hs
  have hTi : ∀ x ∈ K, Function.Bijective (T x) := fun x hx =>
    bijective_coprod_of_orthogonal_range (L x) (B x) (hi x hx) (hBi x hx) (hBr x hx)
  let V : Set E := (W ∩ O) ∩ {x | Function.Injective (T x)}
  have hV : IsOpen V :=
    hT.continuousOn.isOpen_inter_preimage (hW.inter hO) ContinuousLinearMap.isOpen_injective
  refine
    ⟨V, hV, fun x hx => ⟨⟨hKW hx, hKO hx⟩, (hTi x hx).1⟩, B, hB.mono Set.inter_subset_left, hBr,
      ?_⟩
  intro x hx
  have hdim' : Module.finrank ℝ (D × EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ F := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact hdim
  exact ⟨hx.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hx.2⟩

/-- Version of `FrameField.exists_smooth_complement_near_starConvex_on` for a family that is smooth
on the whole space. -/
theorem FrameField.exists_smooth_complement_near_starConvex {E D F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {L : E → (D →L[ℝ] F)} (hL : ContDiff ℝ ∞ L) {K : Set E} (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : E) K) (h0 : (0 : E) ∈ K) (hi : ∀ x ∈ K, Function.Injective (L x))
    (n : ℕ) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ F) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ B : E → (EuclideanSpace ℝ (Fin n) →L[ℝ] F),
            ContDiffOn ℝ ∞ B V ∧
              (∀ x ∈ K, (B x).range = (L x).rangeᗮ) ∧
                ∀ x ∈ V, Function.Bijective ((L x).coprod (B x)) :=
  exists_smooth_complement_near_starConvex_on isOpen_univ hL.contDiffOn hK hstar h0
    (Set.subset_univ K) hi n hdim

/-- Along the lower sheet of a tubular bigon, the normal frame of the strip chart is smooth on a
neighbourhood of `[0, 1]` and injective at every parameter of `[0, 1]`. -/
theorem TubularBigon.lower_sheetFrame {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : (ℝ × ℝ) → M} {n : ℕ} (tube : TubularBigon (E := E) S T a b k.map l h n)
    (d : StripNormalData A B (E := E) S k.map) :
    (∃ U : Set ℝ,
        IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (d.normalFrame tube.chart t) := by
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ WhitneyPairModel.bigon h := by
    intro t ht
    have hf : (2 * t - 1, 0) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inl rfl⟩
    exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1
  have hsource : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((2 * t - 1, 0), 0) ∈ tube.chart.source := fun t ht =>
    tube.source_contains ⟨hpoint t ht, Metric.mem_closedBall_self tube.radius_pos.le⟩
  constructor
  · apply d.exists_open_normalFrame_domain tube.chart
    intro t ht
    have hp := tube.chart.map_source' (hsource t ht)
    rw [tube.zero_section, tube.lower t ht] at hp
    rw [← d.center t, k.center t ht]
    exact hp
  · intro t ht
    have hkt : (t, (0 : ℝ)) ∈ k.domain :=
      k.contains_strip ⟨ht, ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩⟩
    have hcs :
      Function.Surjective
        (fderiv ℝ (WhitneyPairModel.lowerStripCoordinates h) (2 * t - 1, 0)) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (WhitneyPairModel.injective_fderiv_lowerStripCoordinates tube.height_pos.ne'
          (2 * t - 1))
    exact
      d.injective_normalFrame_of_strip_germ tube.chart ht
        (k.smooth.contMDiffAt (k.open_domain.mem_nhds hkt)) tube.zero_section (hsource t ht)
        (WhitneyPairModel.contDiff_lowerStripCoordinates tube.height_pos.ne').contDiffAt
        (WhitneyPairModel.lowerStripCoordinates_lower h t) hcs (tube.lower_germ t ht)

/-- Along the upper sheet of a tubular bigon, the normal frame of the strip chart is smooth on a
neighbourhood of `[0, 1]` and injective at every parameter of `[0, 1]`. -/
theorem TubularBigon.upper_sheetFrame {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} {l : CleanStripPatch (E := E) T S b k₀ k₁}
    {k : (ℝ × ℝ) → M} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l.map h n)
    (d : StripNormalData A B (E := E) T l.map) :
    (∃ U : Set ℝ,
        IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (d.normalFrame tube.chart t) := by
  have hpoint :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ WhitneyPairModel.bigon h := by
    intro t ht
    have hf :
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inr rfl⟩
    exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1
  have hsource :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ((2 * t - 1, h * (1 - (2 * t - 1) ^ 2)), 0) ∈ tube.chart.source :=
    fun t ht => tube.source_contains ⟨hpoint t ht, Metric.mem_closedBall_self tube.radius_pos.le⟩
  constructor
  · apply d.exists_open_normalFrame_domain tube.chart
    intro t ht
    have hp := tube.chart.map_source' (hsource t ht)
    rw [tube.zero_section, tube.upper t ht] at hp
    rw [← d.center t, l.center t ht]
    exact hp
  · intro t ht
    have hlt : (t, (0 : ℝ)) ∈ l.domain :=
      l.contains_strip ⟨ht, ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩⟩
    have hcs :
      Function.Surjective
        (fderiv ℝ (WhitneyPairModel.upperStripCoordinates h)
          (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (WhitneyPairModel.injective_fderiv_upperStripCoordinates tube.height_pos.ne'
          (2 * t - 1))
    exact
      d.injective_normalFrame_of_strip_germ tube.chart ht
        (l.smooth.contMDiffAt (l.open_domain.mem_nhds hlt)) tube.zero_section (hsource t ht)
        (WhitneyPairModel.contDiff_upperStripCoordinates tube.height_pos.ne').contDiffAt
        (WhitneyPairModel.upperStripCoordinates_upper h t) hcs (tube.upper_germ t ht)

/-- When the sheet directions and the chosen complement fill the normal fibre by dimension count,
the normal frame along the upper sheet extends to a smooth field of complements `C t`,
orthogonal to the frame on `[0, 1]`, with `normalFrame t ⊞ C t` bijective. -/
theorem TubularBigon.upper_sheetFrame_complement_of_finrank {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} [FiniteDimensional ℝ A]
    {l : CleanStripPatch (E := E) T S b k₀ k₁} {k : (ℝ × ℝ) → M} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k l.map h n)
    (d : StripNormalData A B (E := E) T l.map) (m : ℕ) (hdim : Module.finrank ℝ A + m = n) :
    ∃ V : Set ℝ,
      IsOpen V ∧
        Set.Icc (0 : ℝ) 1 ⊆ V ∧
          ContDiffOn ℝ ∞ (d.normalFrame tube.chart) V ∧
            ∃ C : ℝ → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)),
              ContDiffOn ℝ ∞ C V ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1, (C t).range = (d.normalFrame tube.chart t).rangeᗮ) ∧
                  ∀ t ∈ V, Function.Bijective ((d.normalFrame tube.chart t).coprod (C t)) := by
  obtain ⟨⟨U, hU, hIU, hs⟩, hi⟩ := tube.upper_sheetFrame d
  have hstar : StarConvex ℝ (0 : ℝ) (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  have hdim' : Module.finrank ℝ A + m = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨W, hW, hIW, C, hC, hr, hc⟩ :=
    FrameField.exists_smooth_complement_near_starConvex_on hU hs
      CompactIccSpace.isCompact_Icc hstar (by simp) hIU hi m hdim'
  exact
    ⟨W ∩ U, hW.inter hU, fun t ht => ⟨hIW ht, hIU ht⟩, hs.mono Set.inter_subset_right, C,
      hC.mono Set.inter_subset_left, hr, fun t ht => hc t ht.1⟩

/-- The punctured model of a normed space: the open set of nonzero vectors. -/
def DiskFraming.puncturedModel (B : Type*) [NormedAddCommGroup B] :
    TopologicalSpace.Opens B :=
  ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩

/-- A smooth curve defined near `t₀` and nonzero there is the germ at `t₀` of a globally defined
smooth curve avoiding the origin. -/
theorem DiskFraming.exists_smooth_punctured_curve_with_germ {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {a : ℝ → B} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ≠ 0) :
    ∃ f : C(ℝ, puncturedModel B),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ f ∧ (fun t => (f t : B)) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → puncturedModel B := fun t => if h : a t = 0 then ⟨a t₀, ha0⟩ else ⟨a t, h⟩
  let V := U ∩ a ⁻¹' ({0}ᶜ : Set B)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hs0 : a s ≠ 0 := hs.2
    simp only [Function.comp_apply, A, dif_neg hs0]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ A V := by
    intro t ht
    have haAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ a t :=
      (ha.contDiffAt (hU.mem_nhds ht.1)).contMDiffAt
    have hvalAt := haAt.congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff (puncturedModel B) A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨f, hf, hfgerm⟩ := exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨f, hf, ?_⟩
  filter_upwards [hfgerm, hval htV] with t ht htval
  exact (congrArg Subtype.val ht).trans htval

/-- In a real vector space of dimension at least two, two prescribed nonzero smooth germs at the
endpoints `0` and `1` are realised by a single smooth nowhere-zero curve. -/
theorem DiskFraming.exists_nonzero_smooth_curve_with_endpoint_germs {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] {a b : ℝ → B} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V) (ha0 : a 0 ≠ 0) (hb1 : b 1 ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) :
    ∃ v : ℝ → B, ContDiff ℝ ∞ v ∧ (∀ t, v t ≠ 0) ∧ (v =ᶠ[𝓝 (0 : ℝ)] a) ∧ (v =ᶠ[𝓝 (1 : ℝ)] b) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_punctured_curve_with_germ ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_smooth_punctured_curve_with_germ hb hV h1V hb1
  have hrank : 1 < Module.rank ℝ B := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ B by omega)
  let : PathConnectedSpace (puncturedModel B) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : B))
  let γ := PathConnectedSpace.somePath (a' 0) (b' 1)
  obtain ⟨f, hf, hfa, hfb⟩ := exists_smooth_curve_with_endpoint_germs a' b' ha' hb' γ
  let v : ℝ → B := fun t => (f t : B)
  have hv : ContDiff ℝ ∞ v :=
    ((contMDiff_subtype_val (I := 𝓘(ℝ, B)) (U := puncturedModel B)).comp hf).contDiff
  refine ⟨v, hv, fun t => (f t).property, ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num), heqa] with t ht hta
    change t < 1 / 8 at ht
    exact (congrArg Subtype.val (hfa ht.le)).trans hta
  · filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num), heqb] with t ht htb
    change 7 / 8 < t at ht
    exact (congrArg Subtype.val (hfb ht.le)).trans htb

/-- The open set of plane endomorphisms whose determinant has the sign `σ`. -/
def PlanarFrame.determinantComponent (σ : ℝ) :
    TopologicalSpace.Opens (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) :=
  ⟨{L | 0 < σ * determinant L},
    isOpen_lt continuous_const (continuous_const.mul continuous_determinant)⟩

/-- An endomorphism with a definite determinant sign has nonzero first column. -/
theorem PlanarFrame.first_column_ne_zero {σ : ℝ} (L : determinantComponent σ) :
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0) ≠ 0 := by
  intro hz
  have h := L.property
  change
    0 <
      σ *
        area ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
          ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1)) at h
  rw [hz] at h
  simp [area] at h

/-- For an endomorphism with determinant of sign `σ`, the transverse coefficient of the second
column relative to the first has that same sign. -/
theorem PlanarFrame.signed_transverseCoeff_pos {σ : ℝ} (L : determinantComponent σ) :
    0 <
      σ *
        transverseCoeff ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
          ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1)) := by
  rw [transverseCoeff, ← mul_div_assoc]
  exact div_pos L.property (squareLength_pos (first_column_ne_zero L))

/-- The set of plane endomorphisms of a fixed determinant sign is path-connected: `GL₂(ℝ)` has two
path components, distinguished by the sign of the determinant. -/
theorem PlanarFrame.nonempty_path_determinantComponent {σ : ℝ}
    (a b : determinantComponent σ) : Nonempty (Path a b) := by
  have hrank : 1 < Module.rank ℝ PlaneImmersion.Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
  let : PathConnectedSpace (DiskFraming.puncturedModel PlaneImmersion.Plane) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : PlaneImmersion.Plane))
  let a₁ : DiskFraming.puncturedModel PlaneImmersion.Plane :=
    ⟨(a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0),
      first_column_ne_zero a⟩
  let b₁ : DiskFraming.puncturedModel PlaneImmersion.Plane :=
    ⟨(b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0),
      first_column_ne_zero b⟩
  let γ := PathConnectedSpace.somePath a₁ b₁
  let v : unitInterval → PlaneImmersion.Plane := fun t => (γ t : PlaneImmersion.Plane)
  have hv : Continuous v := continuous_subtype_val.comp γ.continuous
  have hvne (t : unitInterval) : v t ≠ 0 := (γ t).property
  let α₀ :=
    parallelCoeff ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let α₁ :=
    parallelCoeff ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let β₀ :=
    transverseCoeff ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let β₁ :=
    transverseCoeff ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let α (t : unitInterval) : ℝ := (1 - (t : ℝ)) * α₀ + (t : ℝ) * α₁
  let β (t : unitInterval) : ℝ := (1 - (t : ℝ)) * β₀ + (t : ℝ) * β₁
  have hα : Continuous α :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hβ : Continuous β :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hβpos (t : unitInterval) : 0 < σ * β t := by
    have hpos : 0 < (1 - (t : ℝ)) * (σ * β₀) + (t : ℝ) * (σ * β₁) :=
      (convex_Ioi (0 : ℝ)) (signed_transverseCoeff_pos a) (signed_transverseCoeff_pos b)
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    have heq : σ * β t = (1 - (t : ℝ)) * (σ * β₀) + (t : ℝ) * (σ * β₁) := by
      dsimp only [β]
      ring
    rwa [heq]
  let F (t : unitInterval) : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane :=
    PlaneImmersion.linearMap (v t, α t • v t + β t • quarterTurn (v t))
  have hF : Continuous F :=
    continuous_linearMap.comp
      (hv.prodMk ((hα.smul hv).add (hβ.smul (continuous_quarterTurn.comp hv))))
  have hcomponent (t : unitInterval) : F t ∈ determinantComponent σ := by
    change
      0 <
        σ *
          determinant (PlaneImmersion.linearMap (v t, α t • v t + β t • quarterTurn (v t)))
    rw [determinant_linearMap, area_transverse, ← mul_assoc]
    exact mul_pos (hβpos t) (squareLength_pos (hvne t))
  have hv0 : v 0 = (a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0) :=
    congrArg Subtype.val γ.source
  have hv1 : v 1 = (b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0) :=
    congrArg Subtype.val γ.target
  have hF0 : F 0 = (a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) := by
    change PlaneImmersion.linearMap (v 0, α 0 • v 0 + β 0 • quarterTurn (v 0)) = _
    have hα0 : α 0 = α₀ := by simp [α]
    have hβ0 : β 0 = β₀ := by simp [β]
    rw [hv0, hα0, hβ0, decompose_second_column (first_column_ne_zero a)]
    exact linearMap_columns a
  have hF1 : F 1 = (b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) := by
    change PlaneImmersion.linearMap (v 1, α 1 • v 1 + β 1 • quarterTurn (v 1)) = _
    have hα1 : α 1 = α₁ := by simp [α]
    have hβ1 : β 1 = β₁ := by simp [β]
    rw [hv1, hα1, hβ1, decompose_second_column (first_column_ne_zero b)]
    exact linearMap_columns b
  exact
    ⟨{  toFun := fun t => ⟨F t, hcomponent t⟩
        continuous_toFun := hF.subtype_mk hcomponent
        source' := Subtype.ext hF0
        target' := Subtype.ext hF1 }⟩

/-- Two smooth germs of plane endomorphisms at the endpoints `0` and `1`, whose determinants have
the same sign, are joined by a smooth path of invertible endomorphisms of that determinant sign. -/
theorem PlanarFrame.exists_smooth_join_of_same_determinant_sign
    {a b : ℝ → (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hsign
    exact lt_irrefl _ hsign
  have ha0 : a 0 ∈ determinantComponent σ := by
    change 0 < (a 0).toLinearMap.det * determinant (a 0)
    rw [determinant_eq_det]
    exact mul_self_pos.mpr ha0ne
  have hb1 : b 1 ∈ determinantComponent σ := by
    change 0 < (a 0).toLinearMap.det * determinant (b 1)
    rw [determinant_eq_det]
    exact hsign
  obtain ⟨γ⟩ :=
    nonempty_path_determinantComponent (⟨a 0, ha0⟩ : determinantComponent σ)
      (⟨b 1, hb1⟩ : determinantComponent σ)
  obtain ⟨L, hL, hmem, hleft, hright⟩ :=
    exists_smooth_open_curve_with_endpoint_germs (determinantComponent σ) ha hb hU hV h0U
      h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := by
    have h := hmem t
    change 0 < (a 0).toLinearMap.det * determinant (L t) at h
    rwa [determinant_eq_det] at h
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  apply bijective_of_determinant_ne_zero (L t)
  intro hz
  rw [determinant_eq_det] at hz
  have h := hpositive t
  rw [hz, MulZeroClass.mul_zero] at h
  exact lt_irrefl _ h

/-- Version of the join of two germs of invertible endomorphisms of the same determinant sign for an
abstract real vector space of dimension two. -/
theorem FrameField.exists_smooth_invertible_join_of_finrank_two {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (hdim : Module.finrank ℝ D = 2) {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  have hdim' : Module.finrank ℝ PlaneImmersion.Plane = Module.finrank ℝ D := by
    simp [PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self, hdim]
  let e : PlaneImmersion.Plane ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq hdim'
  let a' (t : ℝ) := e.symm.toContinuousLinearMap.comp ((a t).comp e.toContinuousLinearMap)
  let b' (t : ℝ) := e.symm.toContinuousLinearMap.comp ((b t).comp e.toContinuousLinearMap)
  have ha' : ContDiffOn ℝ ∞ a' U := contDiffOn_const.clm_comp (ha.clm_comp contDiffOn_const)
  have hb' : ContDiffOn ℝ ∞ b' V := contDiffOn_const.clm_comp (hb.clm_comp contDiffOn_const)
  have hadet (t : ℝ) : (a' t).toLinearMap.det = (a t).toLinearMap.det :=
    LinearMap.det_conj (a t).toLinearMap e.symm.toLinearEquiv
  have hbdet (t : ℝ) : (b' t).toLinearMap.det = (b t).toLinearMap.det :=
    LinearMap.det_conj (b t).toLinearMap e.symm.toLinearEquiv
  have hsign' : 0 < (a' 0).toLinearMap.det * (b' 1).toLinearMap.det := by
    rw [hadet, hbdet]
    exact hsign
  obtain ⟨L', hL', hi', hdet', hleft, hright⟩ :=
    PlanarFrame.exists_smooth_join_of_same_determinant_sign ha' hb' hU hV h0U h1V hsign'
  let L (t : ℝ) := e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap)
  have hL : ContDiff ℝ ∞ L := contDiff_const.clm_comp (hL'.clm_comp contDiff_const)
  have hi (t : ℝ) : Function.Bijective (L t) := e.bijective.comp ((hi' t).comp e.symm.bijective)
  have hdet (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := by
    have heq : (L t).toLinearMap.det = (L' t).toLinearMap.det :=
      LinearMap.det_conj (L' t).toLinearMap e.toLinearEquiv
    rw [heq, ← hadet 0]
    exact hdet' t
  refine ⟨L, hL, hi, hdet, ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    change e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap) = a t
    rw [ht]
    apply ContinuousLinearMap.ext
    intro v
    change e (e.symm (a t (e (e.symm v)))) = a t v
    simp only [e.apply_symm_apply]
  · filter_upwards [hright] with t ht
    change e.toContinuousLinearMap.comp ((L' t).comp e.symm.toContinuousLinearMap) = b t
    rw [ht]
    apply ContinuousLinearMap.ext
    intro v
    change e (e.symm (b t (e (e.symm v)))) = b t v
    simp only [e.apply_symm_apply]

/-- A map defined and smooth on an open set is the germ along any closed subset of that open set of
a globally smooth map. -/
theorem FrameField.exists_global_field_with_closed_germ {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {L : PlaneImmersion.Plane → F} {U C : Set PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) :
    ∃ L₀ : PlaneImmersion.Plane → F, ContDiff ℝ ∞ L₀ ∧ L₀ =ᶠ[𝓝ˢ C] L := by
  have hdisj : Disjoint Uᶜ C := Set.disjoint_left.mpr (fun _ hxU hxC => hxU (hCU hxC))
  obtain ⟨β, hβ0, hβ1, _⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, PlaneImmersion.Plane)
      hU.isClosed_compl hC hdisj (n := ⊤)
  let L₀ : PlaneImmersion.Plane → F := fun x => β x • L x
  have hβ : ContDiff ℝ ∞ (β : PlaneImmersion.Plane → ℝ) := β.contMDiff.contDiff
  have hL₀ : ContDiff ℝ ∞ L₀ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hβ.contDiffAt.smul (hL.contDiffAt (hU.mem_nhds hx))
    · apply
        (contDiffAt_const :
            ContDiffAt ℝ ∞ (fun _ : PlaneImmersion.Plane => (0 : F))
              x).congr_of_eventuallyEq
      have hβx : ∀ᶠ y in 𝓝 x, β y = 0 := hβ0.filter_mono (nhds_le_nhdsSet hx)
      filter_upwards [hβx] with y hy
      change β y • L y = 0
      rw [hy, zero_smul]
  refine ⟨L₀, hL₀, ?_⟩
  filter_upwards [hβ1] with x hx
  change β x • L x = L x
  rw [hx, one_smul]

/-- A smooth field with values in a space of dimension larger than that of the source can be
perturbed relative to a closed set, on which it is nowhere zero, to a field that is nowhere zero
on a prescribed compact set (general position for a section of a bundle of rank exceeding the
base dimension). -/
theorem FrameField.exists_nonzero_field_rel_closed {P F : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {v : P → F} (hv : ContDiff ℝ ∞ v)
    (hdim : Module.finrank ℝ P < Module.finrank ℝ F) {K C : Set P} (hK : IsCompact K)
    (hC : IsClosed C) (hne : ∀ x ∈ K ∩ C, v x ≠ 0) :
    ∃ v' : P → F, ContDiff ℝ ∞ v' ∧ v' =ᶠ[𝓝ˢ C] v ∧ ∀ x ∈ K, v' x ≠ 0 := by
  let B : Set P := K ∩ v ⁻¹' {0}
  have hB : IsCompact B := hK.inter_right (isClosed_singleton.preimage hv.continuous)
  have hdisj : Disjoint C B := Set.disjoint_left.mpr (fun x hxC hxB => hne x ⟨hxB.1, hxC⟩ hxB.2)
  obtain ⟨β, hβ0, hβ1, -⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, P) hC hB.isClosed hdisj (n := ⊤)
  have hfixed : ∀ x ∈ K, β x = 0 → v x ≠ 0 := by
    intro x hx hβx hvx
    have heq : β x = 1 := hβ1.self_of_nhdsSet x ⟨hx, hvx⟩
    exact zero_ne_one (hβx.symm.trans heq)
  let Z := EuclideanSpace ℝ (Fin 0)
  let g : Z → F := fun _ => 0
  have hg : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, F) ∞ g := contMDiff_const
  have hdim' : Module.finrank ℝ P + Module.finrank ℝ Z < Module.finrank ℝ F := by
    simpa only [Z, finrank_euclideanSpace_fin, add_zero] using hdim
  obtain ⟨a, -, ha⟩ :=
    exists_small_localized_image_avoidance hv.contMDiff hg β.contMDiff hdim'
      (show (0 : ℝ) < 1 by norm_num)
  refine ⟨fun x => v x + β x • a, hv.add (β.contMDiff.contDiff.smul contDiff_const), ?_, ?_⟩
  · filter_upwards [hβ0] with x hx
    rw [hx, zero_smul, add_zero]
  · intro x hx
    by_cases hβx : β x = 0
    · simpa only [hβx, zero_smul, add_zero] using hfixed x hx hβx
    · exact ha x hβx (0 : Z)

/-- A locally defined nowhere-zero field on the plane, given near a closed set, extends to a
globally smooth field, unchanged near the closed set, that is nowhere zero on a prescribed
compact set, provided the target has dimension at least three. -/
theorem FrameField.exists_nonzero_extension_of_local_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {v : PlaneImmersion.Plane → F} {U C K : Set PlaneImmersion.Plane} (hU : IsOpen U)
    (hv : ContDiffOn ℝ ∞ v U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hne : ∀ x ∈ K ∩ C, v x ≠ 0) (hdim : 3 ≤ Module.finrank ℝ F) :
    ∃ v' : PlaneImmersion.Plane → F, ContDiff ℝ ∞ v' ∧ v' =ᶠ[𝓝ˢ C] v ∧ ∀ x ∈ K, v' x ≠ 0 := by
  obtain ⟨v₀, hv₀, heq⟩ := exists_global_field_with_closed_germ hU hv hC hCU
  have hne₀ : ∀ x ∈ K ∩ C, v₀ x ≠ 0 := by
    intro x hx
    rw [heq.self_of_nhdsSet hx.2]
    exact hne x hx
  have hdim' : Module.finrank ℝ PlaneImmersion.Plane < Module.finrank ℝ F := by
    change Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ F
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨v', hv', hgerm, hne'⟩ := exists_nonzero_field_rel_closed hv₀ hdim' hK hC hne₀
  exact ⟨v', hv', hgerm.trans heq, hne'⟩

/-- A linear map out of a line is injective exactly when it is nonzero. -/
theorem FrameField.injective_iff_ne_zero_of_finrank_one {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hA : Module.finrank ℝ A = 1) (L : A →L[ℝ] F) : Function.Injective L ↔ L ≠ 0 := by
  constructor
  · intro hi hzero
    let : Nontrivial A := Module.nontrivial_of_finrank_pos (by rw [hA]; norm_num)
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    apply hi
    rw [hzero]
    rfl
  · intro hne
    have hr : L.range ≠ ⊥ := by
      intro hbot
      have hz : L.toLinearMap = 0 := LinearMap.range_eq_bot.mp hbot
      apply hne
      ext x
      exact congrArg (fun f : A →ₗ[ℝ] F => f x) hz
    have hrank := L.toLinearMap.finrank_range_add_finrank_ker
    have hpos : 1 ≤ Module.finrank ℝ L.range := Submodule.one_le_finrank_iff.mpr hr
    have hk : Module.finrank ℝ L.ker = 0 := by
      rw [hA] at hrank
      omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The space of linear maps out of a line has the dimension of the target. -/
theorem FrameField.finrank_one_column {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hA : Module.finrank ℝ A = 1) : Module.finrank ℝ (A →L[ℝ] F) = Module.finrank ℝ F := by
  rw [← (LinearMap.toContinuousLinearMap : (A →ₗ[ℝ] F) ≃ₗ[ℝ] (A →L[ℝ] F)).finrank_eq,
    Module.finrank_linearMap, hA, one_mul]

/-- Version of the nowhere-zero extension for one-column frames: a locally defined family of
injective maps out of a line extends to a global smooth family, unchanged near the closed set,
injective on a prescribed compact set. -/
theorem FrameField.exists_one_column_extension_of_local_field {A F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (hA : Module.finrank ℝ A = 1)
    {L : PlaneImmersion.Plane → (A →L[ℝ] F)} {U C K : Set PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hi : ∀ x ∈ K ∩ C, Function.Injective (L x)) (hdim : 3 ≤ Module.finrank ℝ F) :
    ∃ L' : PlaneImmersion.Plane → (A →L[ℝ] F),
      ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧ ∀ x ∈ K, Function.Injective (L' x) := by
  have hne : ∀ x ∈ K ∩ C, L x ≠ 0 := fun x hx =>
    (injective_iff_ne_zero_of_finrank_one hA (L x)).mp (hi x hx)
  have hdim' : 3 ≤ Module.finrank ℝ (A →L[ℝ] F) := by rwa [finrank_one_column hA]
  obtain ⟨L', hL', heq, hne'⟩ := exists_nonzero_extension_of_local_field hU hL hC hCU hK hne hdim'
  exact
    ⟨L', hL', heq, fun x hx => (injective_iff_ne_zero_of_finrank_one hA (L' x)).mpr (hne' x hx)⟩

/-- In a three-dimensional target, a one-column frame given near a closed set extends to a global
smooth frame, unchanged near that closed set, which on a neighbourhood of a compact star-shaped
set is completed by a smooth two-column field spanning its orthogonal complement. -/
theorem FrameField.exists_completed_one_column_frame {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hA : Module.finrank ℝ A = 1)
    {L : PlaneImmersion.Plane → (A →L[ℝ] F)} {U C K : Set PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : PlaneImmersion.Plane) K)
    (h0 : (0 : PlaneImmersion.Plane) ∈ K) (hi : ∀ x ∈ K ∩ C, Function.Injective (L x))
    (hdim : Module.finrank ℝ F = 3) :
    ∃ L' : PlaneImmersion.Plane → (A →L[ℝ] F),
      ContDiff ℝ ∞ L' ∧
        L' =ᶠ[𝓝ˢ C] L ∧
          ∃ V : Set PlaneImmersion.Plane,
            IsOpen V ∧
              K ⊆ V ∧
                ∃ B : PlaneImmersion.Plane → (EuclideanSpace ℝ (Fin 2) →L[ℝ] F),
                  ContDiffOn ℝ ∞ B V ∧
                    (∀ x ∈ K, (B x).range = (L' x).rangeᗮ) ∧
                      ∀ x ∈ V, Function.Bijective ((L' x).coprod (B x)) := by
  obtain ⟨L', hL', heq, hi'⟩ :=
    exists_one_column_extension_of_local_field hA hU hL hC hCU hK hi hdim.ge
  have hcodim : Module.finrank ℝ A + 2 = Module.finrank ℝ F := by rw [hA, hdim]
  obtain ⟨V, hV, hKV, B, hB, hr, hb⟩ :=
    exists_smooth_complement_near_starConvex hL' hK hstar h0 hi' 2 hcodim
  exact ⟨L', hL', heq, V, hV, hKV, B, hB, hr, hb⟩

/-- On a line, every endomorphism is multiplication by its determinant. -/
theorem FrameField.eq_det_smul_id_of_finrank_one {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (hdim : Module.finrank ℝ D = 1) (A : D →L[ℝ] D) :
    A.toLinearMap = A.toLinearMap.det • LinearMap.id := by
  obtain ⟨a, ha, -⟩ := A.toLinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
  have hdet : A.toLinearMap.det = a := by
    rw [ha, LinearMap.det_smul, hdim, pow_one, LinearMap.det_id, mul_one]
  rw [hdet]
  exact ha

/-- On a line, the determinant is linear: `det (a • A + b • B) = a det A + b det B`. -/
theorem FrameField.det_smul_add_of_finrank_one {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (hdim : Module.finrank ℝ D = 1) (A B : D →L[ℝ] D) (a b : ℝ) :
    (a • A + b • B).toLinearMap.det = a * A.toLinearMap.det + b * B.toLinearMap.det := by
  have hlin :
    (a • A + b • B).toLinearMap =
      (a * A.toLinearMap.det + b * B.toLinearMap.det) • LinearMap.id := by
    calc
      _ = a • (A.toLinearMap.det • LinearMap.id) + b • (B.toLinearMap.det • LinearMap.id) :=
        congrArg₂ (fun L K : D →ₗ[ℝ] D => a • L + b • K) (eq_det_smul_id_of_finrank_one hdim A)
          (eq_det_smul_id_of_finrank_one hdim B)
      _ = _ := by rw [smul_smul, smul_smul, ← add_smul]
  rw [hlin, LinearMap.det_smul, hdim, pow_one, LinearMap.det_id, mul_one]

/-- Version of the join of two germs of invertible endomorphisms of the same determinant sign for a
space of dimension one. -/
theorem FrameField.exists_smooth_invertible_join_of_finrank_one {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (hdim : Module.finrank ℝ D = 1) {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  let S : TopologicalSpace.Opens (D →L[ℝ] D) :=
    ⟨{L | 0 < σ * L.toLinearMap.det},
      isOpen_lt continuous_const (continuous_const.mul ContinuousLinearMap.continuous_det)⟩
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hsign
    exact lt_irrefl _ hsign
  have hpos : 0 < σ * (a 0).toLinearMap.det := mul_self_pos.mpr ha0ne
  have ha0 : a 0 ∈ S := hpos
  have hb1 : b 1 ∈ S := hsign
  let γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S) :=
    { toFun := fun t =>
        ⟨(1 - (t : ℝ)) • a 0 + (t : ℝ) • b 1,
          by
          change 0 < σ * ((1 - (t : ℝ)) • a 0 + (t : ℝ) • b 1).toLinearMap.det
          rw [det_smul_add_of_finrank_one hdim]
          have heq :
            σ * ((1 - (t : ℝ)) * (a 0).toLinearMap.det + (t : ℝ) * (b 1).toLinearMap.det) =
              (1 - (t : ℝ)) * (σ * (a 0).toLinearMap.det) +
                (t : ℝ) * (σ * (b 1).toLinearMap.det) := by ring
          rw [heq]
          by_cases ht : (t : ℝ) = 0
          · simpa only [ht, sub_zero, one_mul, MulZeroClass.zero_mul, add_zero] using hpos
          · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
            exact
              add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr t.property.2) hpos.le)
                (mul_pos htpos hsign)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        fun_prop
      source' := by
        apply Subtype.ext
        simp
      target' := by
        apply Subtype.ext
        simp }
  obtain ⟨L, hL, hmem, hleft, hright⟩ :=
    exists_smooth_open_curve_with_endpoint_germs S ha hb hU hV h0U h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := hmem t
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  have hdet : (L t).toLinearMap.det ≠ 0 := by
    intro hz
    have hp := hpositive t
    rw [hz, MulZeroClass.mul_zero] at hp
    exact lt_irrefl _ hp
  have hker : (L t).toLinearMap.ker = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hi : Function.Injective (L t) := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

/-- A continuous nowhere-zero real function on `[0, 1]` has endpoint values of the same sign, so
their product is positive. -/
theorem FrameField.mul_endpoints_pos_of_continuous_nonzero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) :
    0 < f 0 * f 1 := by
  by_contra h
  rcases mul_nonpos_iff.mp (le_of_not_gt h) with h | h
  · obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hf ⟨h.2, h.1⟩
    exact hne t ht hft
  · obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf h
    exact hne t ht hft

/-- A continuous path of invertible endomorphisms on `[0, 1]` has endpoint determinants of the same
sign. -/
theorem FrameField.det_mul_endpoints_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {T : ℝ → (E →L[ℝ] E)}
    (hT : ContinuousOn T (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective (T t)) :
    0 < (T 0).toLinearMap.det * (T 1).toLinearMap.det := by
  apply
    mul_endpoints_pos_of_continuous_nonzero
      (ContinuousLinearMap.continuous_det.comp_continuousOn hT)
  intro t ht hz
  have hker : (T t).toLinearMap.ker ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz
  exact hker (LinearMap.ker_eq_bot.mpr (hi t ht).1)

/-- For a path of frames `G ⊞ C` that stays invertible, the two endpoint determinants of `G ⊞ L`
have the same sign exactly when the two endpoint determinants of `L` read in the quotient
complement of `G` do. -/
theorem FrameField.same_sign_frames_iff_coefficients {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (D × Z) ≃L[ℝ] F)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} (hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1))
    (hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible) :
    (0 <
        (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) ↔
      (0 <
        ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) := by
  let T (t : ℝ) := j.symm.toContinuousLinearMap.comp ((G t).coprod (C t))
  have hs : ContDiffOn ℝ ∞ T (Set.Icc (0 : ℝ) 1) :=
    contDiffOn_const.clm_comp (contDiffOn_coprod hG hC)
  have hT : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective (T t) := fun t ht =>
    j.symm.bijective.comp (hi t ht).bijective
  have hpositive := det_mul_endpoints_pos hs.continuousOn hT
  have h0 := det_frame_eq_det_split_mul_det_coefficient j (G 0) (C 0) (L 0) (hi 0 (by simp))
  have h1 := det_frame_eq_det_split_mul_det_coefficient j (G 1) (C 1) (L 1) (hi 1 (by simp))
  rw [h0, h1]
  have heq :
    ((T 0).toLinearMap.det * ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det) *
        ((T 1).toLinearMap.det * ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) =
      ((T 0).toLinearMap.det * (T 1).toLinearMap.det) *
        (((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) := by ring
  change (0 < ((T 0).toLinearMap.det * _) * ((T 1).toLinearMap.det * _)) ↔ _
  rw [heq]
  exact mul_pos_iff_of_pos_left hpositive

/-- If the complement directions have dimension one or two, a path `L` whose endpoint coefficients
in the quotient complement have determinants of the same sign can be replaced, keeping its germs
at `0` and `1`, by a path `H` for which `G ⊞ H` is invertible throughout. -/
theorem FrameField.exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two
    {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hdim : Module.finrank ℝ Z = 1 ∨ Module.finrank ℝ Z = 2)
    {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ} (hU : IsOpen U) (h0U : (0 : ℝ) ∈ U)
    (h1U : (1 : ℝ) ∈ U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hL : ContDiffOn ℝ ∞ L U) (hi : ∀ t ∈ U, Function.Bijective ((G t).coprod (C t)))
    (hsign :
      0 <
        ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F),
      ContDiffOn ℝ ∞ H U ∧
        (∀ t ∈ U, Function.Bijective ((G t).coprod (H t))) ∧
          (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) := by
  have hinv : ∀ t ∈ U, ((G t).coprod (C t)).IsInvertible := fun t ht =>
    isInvertible_coprod_of_bijective (G t) (C t) (hi t ht)
  let K (t : ℝ) := (complementQuotient (G t) (C t)).comp (L t)
  have hK : ContDiffOn ℝ ∞ K U := (contDiffOn_complementQuotient hU hG hC hinv).clm_comp hL
  have hjoin :=
    hdim.elim
      (fun hd => exists_smooth_invertible_join_of_finrank_one hd hK hK hU hU h0U h1U hsign)
      (fun hd => exists_smooth_invertible_join_of_finrank_two hd hK hK hU hU h0U h1U hsign)
  obtain ⟨K', hK', hiK', _, hleft, hright⟩ := hjoin
  let H (t : ℝ) := correctedComplement (G t) (C t) (L t) (K' t)
  have hH : ContDiffOn ℝ ∞ H U := contDiffOn_correctedComplement hU hG hC hL hK'.contDiffOn hinv
  refine
    ⟨H, hH, fun t ht =>
      bijective_coprod_correctedComplement (G t) (C t) (L t) (K' t) (hinv t ht) (hiK' t), ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    change correctedComplement (G t) (C t) (L t) (K' t) = L t
    rw [ht]
    exact correctedComplement_self (G t) (C t) (L t)
  · filter_upwards [hright] with t ht
    change correctedComplement (G t) (C t) (L t) (K' t) = L t
    rw [ht]
    exact correctedComplement_self (G t) (C t) (L t)

/-- Frame-determinant form of the previous statement: the hypothesis is the sign of the product of
the two endpoint determinants of `G ⊞ L` read through the splitting `j`. -/
theorem FrameField.exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
    {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hdim : Module.finrank ℝ Z = 1 ∨ Module.finrank ℝ Z = 2)
    (j : (D × Z) ≃L[ℝ] F) {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)} {U : Set ℝ}
    (hU : IsOpen U) (hIU : Set.Icc (0 : ℝ) 1 ⊆ U) (hG : ContDiffOn ℝ ∞ G U)
    (hC : ContDiffOn ℝ ∞ C U) (hL : ContDiffOn ℝ ∞ L U)
    (hi : ∀ t ∈ U, Function.Bijective ((G t).coprod (C t)))
    (hsign :
      0 <
        (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) :
    ∃ H : ℝ → (Z →L[ℝ] F),
      ContDiffOn ℝ ∞ H U ∧
        (∀ t ∈ U, Function.Bijective ((G t).coprod (H t))) ∧
          (H =ᶠ[𝓝 (0 : ℝ)] L) ∧ (H =ᶠ[𝓝 (1 : ℝ)] L) := by
  have hinv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible := fun t ht =>
    isInvertible_coprod_of_bijective _ _ (hi t (hIU ht))
  have hcoeff := (same_sign_frames_iff_coefficients j (hG.mono hIU) (hC.mono hIU) hinv).mp hsign
  exact
    exists_smooth_complement_with_endpoint_germs_of_finrank_one_or_two hdim hU (hIU (by simp))
      (hIU (by simp)) hG hC hL hi hcoeff

/-- Two smooth fields along the two boundary arcs of the bigon, agreeing near the two corners, are
the restrictions of one smooth field defined on a neighbourhood of the boundary of the bigon. -/
theorem WhitneyPairModel.exists_smooth_bigon_boundary_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ} (hh : 0 < h) {L H : ℝ → F} {D : Set ℝ}
    (hD : IsOpen D) (hID : Set.Icc (0 : ℝ) 1 ⊆ D) (hL : ContDiffOn ℝ ∞ L D)
    (hH : ContDiffOn ℝ ∞ H D) (h0 : H =ᶠ[𝓝 (0 : ℝ)] L) (h1 : H =ᶠ[𝓝 (1 : ℝ)] L) :
    ∃ U V : Set (ℝ × ℝ),
      IsOpen U ∧
        IsOpen V ∧
          frontier (bigon h) ⊆ U ∪ V ∧
            Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U ∧
              Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V ∧
                ∃ W : (ℝ × ℝ) → F,
                  ContDiffOn ℝ ∞ W (U ∪ V) ∧
                    Set.EqOn W (L ∘ arcTime) U ∧ Set.EqOn W (H ∘ arcTime) V := by
  let P := arcTime ⁻¹' D
  have hP : IsOpen P := hD.preimage contDiff_arcTime.continuous
  have hLP : ContDiffOn ℝ ∞ (L ∘ arcTime) P :=
    hL.comp contDiff_arcTime.contDiffOn (fun _ hp => hp)
  have hHP : ContDiffOn ℝ ∞ (H ∘ arcTime) P :=
    hH.comp contDiff_arcTime.contDiffOn (fun _ hp => hp)
  have htime0 : Filter.Tendsto arcTime (𝓝 ((-1 : ℝ), (0 : ℝ))) (𝓝 (0 : ℝ)) := by
    simpa [ContinuousAt, arcTime] using
      (contDiff_arcTime.continuous.continuousAt (x := ((-1 : ℝ), (0 : ℝ))))
  have htime1 : Filter.Tendsto arcTime (𝓝 ((1 : ℝ), (0 : ℝ))) (𝓝 (1 : ℝ)) := by
    simpa [ContinuousAt, arcTime] using
      (contDiff_arcTime.continuous.continuousAt (x := ((1 : ℝ), (0 : ℝ))))
  have hg0 : (L ∘ arcTime) =ᶠ[𝓝 ((-1 : ℝ), (0 : ℝ))] (H ∘ arcTime) := h0.symm.comp_tendsto htime0
  have hg1 : (L ∘ arcTime) =ᶠ[𝓝 ((1 : ℝ), (0 : ℝ))] (H ∘ arcTime) := h1.symm.comp_tendsto htime1
  obtain ⟨O₀, hO₀sub, hO₀, hleft⟩ := mem_nhds_iff.mp hg0
  obtain ⟨O₁, hO₁sub, hO₁, hright⟩ := mem_nhds_iff.mp hg1
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  have hlowP : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) P := by
    intro t ht
    change arcTime (2 * t - 1, 0) ∈ D
    rw [htime]
    exact hID ht
  have huppP : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) P :=
    by
    intro t ht
    change arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ D
    rw [htime]
    exact hID ht
  obtain ⟨U, V, hU, hV, hUP, hVP, hover, hlowU, huppV, hfront⟩ :=
    exists_bigon_boundary_cover hh hP hP (hO₀.union hO₁) (Or.inl hleft) (Or.inr hright) hlowP
      huppP
  have hLH : Set.EqOn (L ∘ arcTime) (H ∘ arcTime) (U ∩ V) := by
    intro p hp
    rcases hover hp with hp0 | hp1
    · exact hO₀sub hp0
    · exact hO₁sub hp1
  obtain ⟨W, hW, hWL, hWH⟩ :=
    exists_smooth_open_gluing hU hV (hLP.mono hUP).contMDiffOn (hHP.mono hVP).contMDiffOn
      hLH
  exact ⟨U, V, hU, hV, hfront, hlowU, huppV, W, hW.contDiffOn, hWL, hWH⟩

/-- Version of the previous statement for fields of injective linear maps: the resulting field on a
neighbourhood of the boundary of the bigon has the prescribed germs along the two arcs and is
injective at every boundary point. -/
theorem WhitneyPairModel.exists_injective_bigon_boundary_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {h : ℝ} (hh : 0 < h) {L H : ℝ → (A →L[ℝ] F)} {D : Set ℝ} (hD : IsOpen D)
    (hID : Set.Icc (0 : ℝ) 1 ⊆ D) (hL : ContDiffOn ℝ ∞ L D) (hH : ContDiffOn ℝ ∞ H D)
    (h0 : H =ᶠ[𝓝 (0 : ℝ)] L) (h1 : H =ᶠ[𝓝 (1 : ℝ)] L)
    (hiL : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (L t))
    (hiH : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (H t)) :
    ∃ O : Set (ℝ × ℝ),
      IsOpen O ∧
        frontier (bigon h) ⊆ O ∧
          ∃ W : (ℝ × ℝ) → (A →L[ℝ] F),
            ContDiffOn ℝ ∞ W O ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, W =ᶠ[𝓝 (2 * t - 1, 0)] (L ∘ arcTime)) ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                    W =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))] (H ∘ arcTime)) ∧
                  ∀ p ∈ frontier (bigon h), Function.Injective (W p) := by
  obtain ⟨U, V, hU, hV, hfront, hlow, hupp, W, hW, hWL, hWH⟩ :=
    exists_smooth_bigon_boundary_field hh hD hID hL hH h0 h1
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  refine ⟨U ∪ V, hU.union hV, hfront, W, hW, ?_, ?_, ?_⟩
  · intro t ht
    exact Filter.mem_of_superset (hU.mem_nhds (hlow ht)) (fun _ hp => hWL hp)
  · intro t ht
    exact Filter.mem_of_superset (hV.mem_nhds (hupp ht)) (fun _ hp => hWH hp)
  · intro p hp
    obtain ⟨t, ht, rfl | rfl⟩ := (mem_frontier_bigon_iff_exists_time hh p).mp hp
    · rw [hWL (hlow ht)]
      dsimp only [Function.comp_apply]
      rw [htime]
      exact hiL t ht
    · rw [hWH (hupp ht)]
      dsimp only [Function.comp_apply]
      rw [htime]
      exact hiH t ht

/-- A fixed linear identification `ℝ² × ℝ¹ ≃ ℝ³` of the split rank-three normal space with
`EuclideanSpace ℝ (Fin 3)`. -/
def FrameField.rankThreePairCoordinates :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearEquiv.ofFinrankEq
    (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin])

/-- The determinant of a pair of frames `A : ℝ² →L ℝ³` and `B : ℝ¹ →L ℝ³`, read through the
identification `ℝ² × ℝ¹ ≃ ℝ³`. -/
def FrameField.rankThreePairDet
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (B : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (rankThreePairCoordinates.symm.toContinuousLinearMap.comp (A.coprod B)).toLinearMap.det

/-- In the rank-three situation, if the two corner frame determinants have the same sign, the normal
frame along the lower sheet can be replaced by a smooth complement `H` of the upper normal frame
on a neighbourhood of `[0, 1]`, with the same germs at both corners. -/
theorem TubularBigon.exists_rankThree_boundary_complement_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ U : Set ℝ,
      IsOpen U ∧
        Set.Icc (0 : ℝ) 1 ⊆ U ∧
          ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U ∧
            ∃ H : ℝ → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
              ContDiffOn ℝ ∞ H U ∧
                (∀ t ∈ U, Function.Bijective ((e.normalFrame tube.chart t).coprod (H t))) ∧
                  (H =ᶠ[𝓝 (0 : ℝ)] d.normalFrame tube.chart) ∧
                    (H =ᶠ[𝓝 (1 : ℝ)] d.normalFrame tube.chart) := by
  obtain ⟨⟨V, hV, hIV, hL⟩, -⟩ := tube.lower_sheetFrame d
  obtain ⟨W, hW, hIW, hR, C, hC, -, hRC⟩ :=
    tube.upper_sheetFrame_complement_of_finrank e 1 (by simp only [finrank_euclideanSpace_fin])
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  have hIU : Set.Icc (0 : ℝ) 1 ⊆ U := fun _ ht => ⟨hIV ht, hIW ht⟩
  have hLU := hL.mono (show U ⊆ V from Set.inter_subset_left)
  have hRU := hR.mono (show U ⊆ W from Set.inter_subset_right)
  have hCU := hC.mono (show U ⊆ W from Set.inter_subset_right)
  have hsplit : ∀ t ∈ U, Function.Bijective ((e.normalFrame tube.chart t).coprod (C t)) :=
    fun t ht => hRC t ht.2
  obtain ⟨H, hH, hiH, hleft, hright⟩ :=
    FrameField.exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
      (Or.inl finrank_euclideanSpace_fin) FrameField.rankThreePairCoordinates hU hIU hRU hCU
      hLU hsplit hsign
  exact ⟨U, hU, hIU, hLU, H, hH, hiH, hleft, hright⟩

/-- The complement of the previous statement, transported to a field on a neighbourhood of the
boundary of the bigon: it has the germ of the lower normal frame along the lower arc, completes
the upper normal frame along the upper arc, and is injective on the boundary. -/
theorem TubularBigon.exists_rankThree_planar_boundary_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ O : Set (ℝ × ℝ),
      IsOpen O ∧
        frontier (WhitneyPairModel.bigon h) ⊆ O ∧
          ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
            ContDiffOn ℝ ∞ W O ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                  W =ᶠ[𝓝 (2 * t - 1, 0)]
                    (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                    Function.Bijective
                      ((e.normalFrame tube.chart t).coprod
                        (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
                  ∀ p ∈ frontier (WhitneyPairModel.bigon h), Function.Injective (W p) := by
  obtain ⟨D, hD, hID, hL, H, hH, hcomp, h0, h1⟩ :=
    tube.exists_rankThree_boundary_complement_of_normal_sign d e hsign
  have hHi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (H t) := by
    intro t ht u v huv
    have heq :
      ((e.normalFrame tube.chart t).coprod (H t)) (0, u) =
        ((e.normalFrame tube.chart t).coprod (H t)) (0, v) := by
      simpa only [ContinuousLinearMap.coprod_apply, map_zero, zero_add] using huv
    exact congrArg Prod.snd ((hcomp t (hID ht)).1 heq)
  obtain ⟨O, hO, hfront, W, hW, hlo, hhi, hinj⟩ :=
    WhitneyPairModel.exists_injective_bigon_boundary_field tube.height_pos hD hID hL hH h0
      h1 (tube.lower_sheetFrame d).2 hHi
  refine ⟨O, hO, hfront, W, hW, hlo, ?_, hinj⟩
  intro t ht
  rw [(hhi t ht).eq_of_nhds]
  have htime : WhitneyPairModel.arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = t := by
    dsimp [WhitneyPairModel.arcTime]
    ring
  change
    Function.Bijective
      ((e.normalFrame tube.chart t).coprod
        (H (WhitneyPairModel.arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)))))
  rw [htime]
  exact hcomp t (hID ht)

/-- The boundary field of the previous statement extends to a globally smooth field on the plane
which, on a neighbourhood of the bigon, is completed by a smooth two-column field spanning its
orthogonal complement. -/
theorem TubularBigon.exists_rankThree_planar_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
              Function.Bijective
                ((e.normalFrame tube.chart t).coprod
                  (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
            ∃ V : Set (ℝ × ℝ),
              IsOpen V ∧
                WhitneyPairModel.bigon h ⊆ V ∧
                  ∃ B : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                    ContDiffOn ℝ ∞ B V ∧
                      (∀ p ∈ WhitneyPairModel.bigon h, (B p).range = (W p).rangeᗮ) ∧
                        ∀ p ∈ V, Function.Bijective ((W p).coprod (B p)) := by
  obtain ⟨O, hO, hfront, W₀, hW₀, hlo, hhi, hinj⟩ :=
    tube.exists_rankThree_planar_boundary_frame_of_normal_sign d e hsign
  obtain ⟨W, hW, heq, V, hV, hKV, B, hB, hr, hb⟩ :=
    FrameField.exists_completed_one_column_frame finrank_euclideanSpace_fin hO hW₀
      isClosed_frontier hfront (WhitneyPairModel.isCompact_bigon tube.height_pos)
      (WhitneyPairModel.starConvex_bigon tube.height_pos.le)
      (WhitneyPairModel.zero_mem_bigon tube.height_pos.le) (fun p hp => hinj p hp.2)
      finrank_euclideanSpace_fin
  refine ⟨W, hW, ?_, ?_, V, hV, hKV, B, hB, hr, hb⟩
  · intro t ht
    have hp : (2 * t - 1, 0) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inl rfl⟩
    exact (heq.filter_mono (nhds_le_nhdsSet hp)).trans (hlo t ht)
  · intro t ht
    have hp :
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inr rfl⟩
    rw [heq.self_of_nhdsSet hp]
    exact hhi t ht

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

/-- In the rank-three situation with corner frame determinants of the same sign, there is a globally
smooth field `W` with the germs of the lower normal frame along the lower arc, completed on a
neighbourhood of the bigon by a smooth field `C` that restricts to the upper normal frame along
the upper arc. -/
theorem TubularBigon.exists_rankThree_adapted_frame_of_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign :
      0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
          ∃ O : Set (ℝ × ℝ),
            IsOpen O ∧
              WhitneyPairModel.bigon h ⊆ O ∧
                ∃ C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                  ContDiffOn ℝ ∞ C O ∧
                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                        C (WhitneyPairModel.upperBoundaryArc h t) =
                          e.normalFrame tube.chart t) ∧
                      ∀ p ∈ O, Function.Bijective ((W p).coprod (C p)) := by
  obtain ⟨W, hW, hlo, hhi, V, hV, hKV, B, hB, -, hb⟩ :=
    tube.exists_rankThree_planar_frame_of_normal_sign d e hsign
  obtain ⟨⟨D, hD, hID, hG⟩, -⟩ := tube.upper_sheetFrame e
  let r : (ℝ × ℝ) → (ℝ × ℝ) :=
    WhitneyPairModel.upperBoundaryArc h ∘ WhitneyPairModel.arcTime
  have hq : ContDiff ℝ ∞ (WhitneyPairModel.upperBoundaryArc h) := by
    unfold WhitneyPairModel.upperBoundaryArc; fun_prop
  have hr : ContDiff ℝ ∞ r := hq.comp WhitneyPairModel.contDiff_arcTime
  have htime (t y : ℝ) : WhitneyPairModel.arcTime (2 * t - 1, y) = t := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have htq (t : ℝ) :
    WhitneyPairModel.arcTime (WhitneyPairModel.upperBoundaryArc h t) = t := htime t _
  have hrq (t : ℝ) :
    r (WhitneyPairModel.upperBoundaryArc h t) =
      WhitneyPairModel.upperBoundaryArc h t := by
    dsimp only [r, Function.comp_apply]
    rw [htq]
  have htimeK :
    Set.MapsTo WhitneyPairModel.arcTime (WhitneyPairModel.bigon h)
      (Set.Icc (0 : ℝ) 1) := by
    intro p hp
    have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have hrK : Set.MapsTo r (WhitneyPairModel.bigon h) (WhitneyPairModel.bigon h) :=
    fun _ hp => tube.upperBoundaryArc_mem_bigon (htimeK hp)
  let O₀ := V ∩ (r ⁻¹' V ∩ WhitneyPairModel.arcTime ⁻¹' D)
  have hO₀ : IsOpen O₀ :=
    hV.inter
      ((hV.preimage hr.continuous).inter
        (hD.preimage WhitneyPairModel.contDiff_arcTime.continuous))
  have hKO₀ : WhitneyPairModel.bigon h ⊆ O₀ := fun p hp =>
    ⟨hKV hp, hKV (hrK hp), hID (htimeK hp)⟩
  let C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) := fun p =>
    FrameField.transportComplement (W p) (B p) (W (r p)) (B (r p))
      (e.normalFrame tube.chart (WhitneyPairModel.arcTime p))
  have hC : ContDiffOn ℝ ∞ C O₀ := by
    apply
      FrameField.contDiffOn_transportComplement hO₀ hW.contDiffOn
        (hB.mono Set.inter_subset_left) (hW.comp hr).contDiffOn
        (hB.comp hr.contDiffOn (fun _ hp => hp.2.1))
        (hG.comp WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.2))
    intro p hp
    exact FrameField.isInvertible_coprod_of_bijective (W (r p)) (B (r p)) (hb _ hp.2.1)
  have hcompK : ∀ p ∈ WhitneyPairModel.bigon h, Function.Bijective ((W p).coprod (C p)) := by
    intro p hp
    have ht := htimeK hp
    have hupper :
      Function.Bijective
        ((W (r p)).coprod (e.normalFrame tube.chart (WhitneyPairModel.arcTime p))) :=
      FrameField.bijective_coprod_comm _ _ (hhi (WhitneyPairModel.arcTime p) ht)
    exact
      FrameField.bijective_transportComplement (W p) (B p) (W (r p)) (B (r p)) _
        (FrameField.isInvertible_coprod_of_bijective _ _ (hb p (hKV hp)))
        (FrameField.isInvertible_coprod_of_bijective _ _ (hb _ (hKV (hrK hp)))) hupper
  have hTC : ContDiffOn ℝ ∞ (fun p => (W p).coprod (C p)) O₀ :=
    FrameField.contDiffOn_coprod hW.contDiffOn hC
  let O := O₀ ∩ {p | Function.Injective ((W p).coprod (C p))}
  have hO : IsOpen O :=
    hTC.continuousOn.isOpen_inter_preimage hO₀ ContinuousLinearMap.isOpen_injective
  have hKO : WhitneyPairModel.bigon h ⊆ O := fun p hp => ⟨hKO₀ hp, (hcompK p hp).1⟩
  refine ⟨W, hW, hlo, O, hO, hKO, C, hC.mono Set.inter_subset_left, ?_, ?_⟩
  · intro t ht
    dsimp only [C]
    rw [hrq, htq]
    exact
      FrameField.transportComplement_self _ _ _
        (FrameField.isInvertible_coprod_of_bijective _ _
          (hb _ (hKV (tube.upperBoundaryArc_mem_bigon ht))))
  · intro p hp
    have hdim :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact ⟨hp.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hp.2⟩

/-- The joint block of the two sheet differentials of a rank-three tubular bigon at the parameter
`t`, read in the coordinates `ℝ² × ℝ¹ ≃ ℝ³`. -/
def TubularBigon.rankThreeSheetPairJacobian {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (t : ℝ) :
    ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) →L[ℝ]
      ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) :=
  IntersectionCoordinates.jointBlock FrameField.rankThreePairCoordinates
    (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)

/-- The determinant of the joint block of the two sheet differentials: the intersection sign of the
two sheets at the parameter `t`. -/
def TubularBigon.rankThreeSheetPairDet {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (t : ℝ) : ℝ :=
  (tube.rankThreeSheetPairJacobian d e t).toLinearMap.det

/-- At the two corners of the bigon the strip charts of the two sheets have the same centre point.
At the two corners of the bigon the strip charts of the two sheets have the same centre point. -/
theorem TubularBigon.rankThree_corner_sheet_charts_coincide {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    {t : ℝ} (ht : t = 0 ∨ t = 1) :
    d.chart (StripCoordinates.center t) = e.chart (StripCoordinates.center t) := by
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
  have hheight : h * (1 - (2 * t - 1) ^ 2) = 0 := by rcases ht with rfl | rfl <;> ring
  have hd := (tube.lower_germ t htI).eq_of_nhds
  have he := (tube.upper_germ t htI).eq_of_nhds
  dsimp only [Function.comp_apply] at hd he
  rw [WhitneyPairModel.lowerStripCoordinates_lower, d.center t] at hd
  rw [WhitneyPairModel.upperStripCoordinates_upper, e.center t, hheight] at he
  exact hd.symm.trans he

/-- At each parameter, the sheet pair determinant is `8 h (2 t - 1)` times the determinant of the
pair of normal frames: the two differ by the velocity factor of the boundary arcs. -/
theorem TubularBigon.rankThreeSheetPairDet_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    tube.rankThreeSheetPairDet d e t =
      (8 * h * (2 * t - 1)) *
        FrameField.rankThreePairDet (e.normalFrame tube.chart t)
          (d.normalFrame tube.chart t) := by
  rw [rankThreeSheetPairDet, rankThreeSheetPairJacobian,
    IntersectionCoordinates.det_jointBlock FrameField.rankThreePairCoordinates
      (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)
      (tube.upper_sheetDifferential_arc e ht) (tube.lower_sheetDifferential_arc d ht),
    e.normal_sheetDifferential tube.chart ht (tube.upper_chart_center_mem_target e ht),
    d.normal_sheetDifferential tube.chart ht (tube.lower_chart_center_mem_target d ht)]
  have hplane :
    (PlaneImmersion.linearMap ((2, -4 * h * (2 * t - 1)), (2, 0))).toLinearMap.det =
      8 * h * (2 * t - 1) := by
    rw [← PlanarFrame.determinant_eq_det, PlanarFrame.determinant_linearMap]
    dsimp [PlanarFrame.area]
    ring
  rw [hplane]
  rfl

/-- The two corner sheet-pair determinants have opposite signs exactly when the two corner
normal-frame determinants have the same sign: the factor `8 h (2 t - 1)` changes sign between
the corners. -/
theorem TubularBigon.opposite_rankThree_corner_determinants_iff_normal_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l) :
    (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
      (0 <
        FrameField.rankThreePairDet (e.normalFrame tube.chart 0)
            (d.normalFrame tube.chart 0) *
          FrameField.rankThreePairDet (e.normalFrame tube.chart 1)
            (d.normalFrame tube.chart 1)) := by
  let n :=
    FrameField.rankThreePairDet (e.normalFrame tube.chart 0) (d.normalFrame tube.chart 0) *
      FrameField.rankThreePairDet (e.normalFrame tube.chart 1) (d.normalFrame tube.chart 1)
  have hprod :
    tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 = -((8 * h) ^ 2 * n) := by
    rw [tube.rankThreeSheetPairDet_eq d e (t := 0) (by simp),
      tube.rankThreeSheetPairDet_eq d e (t := 1) (by simp)]
    dsimp only [n]
    ring
  have hscale : 0 < (8 * h) ^ 2 := sq_pos_of_pos (mul_pos (by norm_num) tube.height_pos)
  change (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔ 0 < n
  rw [hprod]
  constructor
  · intro hn
    have hp : 0 < (8 * h) ^ 2 * n := by linarith
    exact (mul_pos_iff_of_pos_left hscale).mp hp
  · intro hn
    have hp : 0 < (8 * h) ^ 2 * n := mul_pos hscale hn
    linarith

/-- The adapted frame over the bigon exists as soon as the two corner intersection signs are
opposite, which is the Whitney condition on the two intersection points. -/
theorem TubularBigon.exists_rankThree_adapted_frame_of_opposite_corner_signs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
            W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ WhitneyPairModel.arcTime)) ∧
          ∃ O : Set (ℝ × ℝ),
            IsOpen O ∧
              WhitneyPairModel.bigon h ⊆ O ∧
                ∃ C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
                  ContDiffOn ℝ ∞ C O ∧
                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                        C (WhitneyPairModel.upperBoundaryArc h t) =
                          e.normalFrame tube.chart t) ∧
                      ∀ p ∈ O, Function.Bijective ((W p).coprod (C p)) :=
  tube.exists_rankThree_adapted_frame_of_normal_sign d e
    ((tube.opposite_rankThree_corner_determinants_iff_normal_sign d e).mp hsign)

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

/-- A map `Q` killing the range of `G` factors through the quotient complement of `G` in an
invertible frame `G ⊞ C`. -/
theorem FrameField.normalDetector_eq_comp_quotient {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (Q : F →L[ℝ] Z)
    (hi : (G.coprod C).IsInvertible) (hQG : Q.comp G = 0) :
    Q = (Q.comp C).comp (complementQuotient G C) := by
  apply ContinuousLinearMap.ext
  intro v
  let w := (G.coprod C).inverse v
  have hv : G w.1 + C w.2 = v := hi.self_apply_inverse v
  have hzero : Q (G w.1) = 0 := congrArg (fun L : D →L[ℝ] Z => L w.1) hQG
  change Q v = Q (C w.2)
  rw [← hv, map_add, hzero, zero_add]

/-- The determinant identity relating the two ways of measuring `L` against an invertible frame `G ⊞
C`: `det (G ⊞ L) * det (Q ∘ C) = det (G ⊞ C) * det (Q ∘ L)` for any `Q` killing `G`. -/
theorem FrameField.det_intersection_mul_normalComplement {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    (j : (D × Z) ≃L[ℝ] F) (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (Q : F →L[ℝ] Z)
    (hi : (G.coprod C).IsInvertible) (hQG : Q.comp G = 0) :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).det * (Q.comp C).det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).det * (Q.comp L).det := by
  have hnormal : Q.comp L = (Q.comp C).comp ((complementQuotient G C).comp L) := by
    have h := normalDetector_eq_comp_quotient G C Q hi hQG
    exact congrArg (fun R : F →L[ℝ] Z => R.comp L) h
  have hdet : (Q.comp L).det = (Q.comp C).det * ((complementQuotient G C).comp L).det := by
    rw [hnormal]
    exact LinearMap.det_comp _ _
  have hframe :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).det *
        ((complementQuotient G C).comp L).det :=
    det_frame_eq_det_split_mul_det_coefficient j G C L hi
  rw [hframe, hdet]
  ring

/-- Endpoint form of the previous identity: the two corner determinants of `G ⊞ L` have opposite
signs exactly when the two corner determinants of `Q ∘ L` do. -/
theorem FrameField.opposite_intersectionDet_iff_normalDet {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    (j : (D × Z) ≃L[ℝ] F) (G : ℝ → (D →L[ℝ] F)) (C L : ℝ → (Z →L[ℝ] F)) (Q : ℝ → (F →L[ℝ] Z))
    (hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1)) (hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1))
    (hQ : ContDiffOn ℝ ∞ Q (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible)
    (hQs : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Surjective (Q t))
    (hQG : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Q t).comp (G t) = 0) :
    ((j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
          (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det <
        0) ↔
      ((Q 0).comp (L 0)).det * ((Q 1).comp (L 1)).det < 0 := by
  let T (t : ℝ) := j.symm.toContinuousLinearMap.comp ((G t).coprod (C t))
  let K (t : ℝ) := (Q t).comp (C t)
  have hT : ContDiffOn ℝ ∞ T (Set.Icc (0 : ℝ) 1) :=
    contDiffOn_const.clm_comp (contDiffOn_coprod hG hC)
  have hK : ContDiffOn ℝ ∞ K (Set.Icc (0 : ℝ) 1) := hQ.clm_comp hC
  have hTpos :=
    det_mul_endpoints_pos hT.continuousOn (fun t ht => j.symm.bijective.comp (hi t ht).bijective)
  have hKpos :=
    det_mul_endpoints_pos hK.continuousOn
      (fun t ht =>
        TransverseCoordinates.bijective_normal_comp (Q t) (G t) (C t) (hQs t ht)
          (hi t ht).surjective (hQG t ht) rfl)
  have h₀ :=
    det_intersection_mul_normalComplement j (G 0) (C 0) (L 0) (Q 0) (hi 0 (by simp))
      (hQG 0 (by simp))
  have h₁ :=
    det_intersection_mul_normalComplement j (G 1) (C 1) (L 1) (Q 1) (hi 1 (by simp))
      (hQG 1 (by simp))
  let a :=
    (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
      (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det
  let b := ((Q 0).comp (L 0)).det * ((Q 1).comp (L 1)).det
  have heq : a * ((K 0).det * (K 1).det) = ((T 0).det * (T 1).det) * b := by
    dsimp [a, b, T, K]
    calc
      _ =
          ((j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
              ((Q 0).comp (C 0)).det) *
            ((j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det *
              ((Q 1).comp (C 1)).det) := by ring
      _ = _ := by rw [h₀, h₁]; ring
  change a < 0 ↔ b < 0
  constructor
  · intro ha
    have hn : ((T 0).det * (T 1).det) * b < 0 := heq ▸ mul_neg_of_neg_of_pos ha hKpos
    rcases mul_neg_iff.mp hn with ⟨_, hb⟩ | ⟨ht, _⟩
    · exact hb
    · exact (not_lt_of_gt hTpos ht).elim
  · intro hb
    have hn : a * ((K 0).det * (K 1).det) < 0 := heq.symm ▸ mul_neg_of_pos_of_neg hTpos hb
    rcases mul_neg_iff.mp hn with ⟨_, hk⟩ | ⟨ha, _⟩
    · exact (not_lt_of_gt hKpos hk).elim
    · exact ha

/-- The plane component of the sheet differential along the sheet directions: the base frame of the
sheet at the parameter `t`. -/
def StripNormalData.sheetBaseFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    A →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ (ℝ × ℝ) Z).comp
    ((d.sheetDifferential Ψ t).comp (ContinuousLinearMap.inr ℝ ℝ A))

/-- The sheet differential depends smoothly on the parameter where the centre line is in the source
of the strip chart and its image in the target of the tubular chart. -/
theorem StripNormalData.contDiffOn_sheetDifferential {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetDifferential Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have htransition : ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
    ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds ht.2)).comp
        (StripCoordinates.center t)
        (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1))).contDiffAt
  have hs : ContDiffAt ℝ ∞ (d.sheetTransition Ψ) (t, 0) :=
    htransition.comp (t, 0) (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffAt
  have hc : ContDiff ℝ ∞ (fun s : ℝ => (s, (0 : A))) := contDiff_id.prodMk contDiff_const
  exact ((hs.fderiv_right (by simp)).comp t hc.contDiffAt).contDiffWithinAt

/-- The sheet base frame depends smoothly on the parameter on the same set. -/
theorem StripNormalData.contDiffOn_sheetBaseFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetBaseFrame Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} :=
  contDiffOn_const.clm_comp ((d.contDiffOn_sheetDifferential Ψ).clm_comp contDiffOn_const)

/-- If the centre line lands in the target of the tubular chart over all of `[0, 1]`, the sheet base
frame is smooth on an open neighbourhood of `[0, 1]`. -/
theorem StripNormalData.exists_open_sheetBaseFrame_domain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.sheetBaseFrame Ψ) U := by
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hO : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  exact
    ⟨StripCoordinates.center ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target), hO.preimage hc,
      fun t ht => ⟨d.line ht, htarget t ht⟩, d.contDiffOn_sheetBaseFrame Ψ⟩

/-- In the tubular chart, the sheet differential splits along the sheet directions into its plane
part, the base frame, and its normal part, the normal frame. -/
theorem StripNormalData.sheetDifferential_transverse_eq {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (u : A) : d.sheetDifferential Ψ t (0, u) = (d.sheetBaseFrame Ψ t u, d.normalFrame Ψ t u) := by
  apply Prod.ext
  · rfl
  · exact congrArg (fun L : A →L[ℝ] Z => L u) (d.normal_sheetDifferential Ψ ht htarget)

/-- The derivative at the centre of the transition from the strip chart to the tubular chart. -/
def StripNormalData.tubularTransitionDerivative {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    StripCoordinates.Space A B →L[ℝ] ((ℝ × ℝ) × Z) :=
  fderiv ℝ (Ψ.symm ∘ d.chart) (StripCoordinates.center t)

/-- The block of that derivative on the complementary directions `B` of the strip chart: the
complement of the sheet in the tubular chart. -/
def StripNormalData.sheetComplement {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    B →L[ℝ] ((ℝ × ℝ) × Z) :=
  (d.tubularTransitionDerivative Ψ t).comp (ContinuousLinearMap.inr ℝ (ℝ × A) B)

/-- The transition derivative is smooth in the parameter where the centre line is in the source of
the strip chart and its image in the target of the tubular chart. -/
theorem StripNormalData.contDiffOn_tubularTransitionDerivative {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.tubularTransitionDerivative Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have htransition : ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
    ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds ht.2)).comp
        (StripCoordinates.center t)
        (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1))).contDiffAt
  have hc : ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  exact ((htransition.fderiv_right (by simp)).comp t hc.contDiffAt).contDiffWithinAt

/-- The sheet complement is smooth in the parameter on the same set. -/
theorem StripNormalData.contDiffOn_sheetComplement {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetComplement Ψ)
      {t |
        StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (StripCoordinates.center t) ∈ Ψ.target} :=
  (d.contDiffOn_tubularTransitionDerivative Ψ).clm_comp contDiffOn_const

/-- The transition derivative is bijective, being the derivative of a transition between two charts.
The transition derivative is bijective, being the derivative of a transition between two charts. -/
theorem StripNormalData.bijective_tubularTransitionDerivative {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    Function.Bijective (d.tubularTransitionDerivative Ψ t) := by
  unfold tubularTransitionDerivative
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp (StripCoordinates.center t) (Ψ.symm.mdifferentiableAt (by simp) htarget)
      (d.chart.mdifferentiableAt (by simp) (d.line ht))]
  exact
    (PartialChart.bijective_mfderiv Ψ.symm htarget).comp
      (PartialChart.bijective_mfderiv d.chart (d.line ht))

/-- The sheet differential and the sheet complement together make up the transition derivative:
`sheetDifferential ⊞ sheetComplement = tubularTransitionDerivative`. -/
theorem StripNormalData.sheet_coprod_complement_eq {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (d.sheetDifferential Ψ t).coprod (d.sheetComplement Ψ t) =
      d.tubularTransitionDerivative Ψ t := by
  rw [d.sheetDifferential_eq Ψ ht htarget]
  apply ContinuousLinearMap.ext
  intro z
  change
    d.tubularTransitionDerivative Ψ t (z.1, 0) + d.tubularTransitionDerivative Ψ t (0, z.2) =
      d.tubularTransitionDerivative Ψ t z
  rw [← map_add]
  simp

/-- Consequently the frame `sheetDifferential ⊞ sheetComplement` is invertible. -/
theorem StripNormalData.isInvertible_sheet_coprod_complement {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) [FiniteDimensional ℝ A]
    [FiniteDimensional ℝ B] {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ((d.sheetDifferential Ψ t).coprod (d.sheetComplement Ψ t)).IsInvertible := by
  apply FrameField.isInvertible_coprod_of_bijective
  rw [d.sheet_coprod_complement_eq Ψ ht htarget]
  exact d.bijective_tubularTransitionDerivative Ψ ht htarget

/-- The derivative in the tubular chart of an ambient map `q`, at the point of the centre line with
parameter `t`: the linear detector of the normal directions of `q`. -/
def StripNormalData.normalDetector {A B Z E M N : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) (t : ℝ) :
    ((ℝ × ℝ) × Z) →L[ℝ] N :=
  fderiv ℝ (q ∘ Ψ) (Ψ.symm (d.chart (StripCoordinates.center t)))

/-- An ambient map smooth at a centre point is smooth in the tubular chart near the corresponding
point. -/
theorem StripNormalData.contDiffAt_normalMap_in_tube {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    ContDiffAt ℝ ∞ (q ∘ Ψ) (Ψ.symm (d.chart (StripCoordinates.center t))) := by
  have hinv :
    Ψ (Ψ.symm (d.chart (StripCoordinates.center t))) =
      d.chart (StripCoordinates.center t) :=
    Ψ.right_inv' htarget
  have hq' :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (Ψ (Ψ.symm (d.chart (StripCoordinates.center t)))) :=
    hinv.symm ▸ hq
  exact
    (hq'.comp _
        (Ψ.contMDiffOn_toFun.contMDiffAt
          (Ψ.open_source.mem_nhds (Ψ.map_target' htarget)))).contDiffAt

/-- The normal detector is smooth on `[0, 1]` when the ambient map is smooth on an open set
containing the centre line. -/
theorem StripNormalData.contDiffOn_normalDetector {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {O : Set M}
    (hO : IsOpen O) (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q O)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hcenter : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ O) :
    ContDiffOn ℝ ∞ (d.normalDetector Ψ q) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  have hqΨ :=
    d.contDiffAt_normalMap_in_tube Ψ q (htarget t ht)
      (hq.contMDiffAt (hO.mem_nhds (hcenter t ht)))
  have hc : ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  have hx : ContDiffAt ℝ ∞ (fun s => Ψ.symm (d.chart (StripCoordinates.center s))) t :=
    (d.contDiffAt_tubularTransition Ψ ht (htarget t ht)).comp t hc.contDiffAt
  exact ((hqΨ.fderiv_right (by simp)).comp t hx).contDiffWithinAt

/-- The normal detector is the composite of the differential of the ambient map with the
differential of the tubular chart. -/
theorem StripNormalData.normalDetector_eq_native {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    d.normalDetector Ψ q t =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) q (d.chart (StripCoordinates.center t)) : E →L[ℝ] N).comp
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) Ψ
            (Ψ.symm (d.chart (StripCoordinates.center t))) :
          ((ℝ × ℝ) × Z) →L[ℝ] E) := by
  have hinv :
    Ψ (Ψ.symm (d.chart (StripCoordinates.center t))) =
      d.chart (StripCoordinates.center t) :=
    Ψ.right_inv' htarget
  have hq' :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) q
      (Ψ (Ψ.symm (d.chart (StripCoordinates.center t)))) :=
    hinv.symm ▸ hq.mdifferentiableAt (by simp)
  unfold normalDetector
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp _ hq' (Ψ.mdifferentiableAt (by simp) (Ψ.map_target' htarget)), hinv]

/-- The normal detector is surjective wherever the differential of the ambient map is. -/
theorem StripNormalData.surjective_normalDetector {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t)))
    (hqs :
      Function.Surjective
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) q (d.chart (StripCoordinates.center t)))) :
    Function.Surjective (d.normalDetector Ψ q t) := by
  rw [d.normalDetector_eq_native Ψ q htarget hq]
  exact hqs.comp (PartialChart.bijective_mfderiv Ψ (Ψ.map_target' htarget)).surjective

/-- If the ambient map vanishes on the sheet, its normal detector kills the sheet differential. -/
theorem StripNormalData.normalDetector_comp_sheet_eq_zero {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {O : Set M}
    (hO : IsOpen O) (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q O) (hzero : ∀ y ∈ S ∩ O, q y = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hcenter : d.chart (StripCoordinates.center t) ∈ O) :
    (d.normalDetector Ψ q t).comp (d.sheetDifferential Ψ t) = 0 := by
  let i := ContinuousLinearMap.inl ℝ (ℝ × A) B
  have hi : ContinuousAt i (t, 0) := i.continuous.continuousAt
  have hdc : ContinuousAt d.chart (i (t, 0)) :=
    d.chart.contMDiffOn_toFun.continuousOn.continuousAt (d.chart.open_source.mem_nhds (d.line ht))
  have hd : ContinuousAt (d.chart ∘ i) (t, 0) := ContinuousAt.comp (g := d.chart) (f := i) hdc hi
  have hnearS : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), i w ∈ d.chart.source :=
    hi.preimage_mem_nhds (d.chart.open_source.mem_nhds (d.line ht))
  have hnear : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), d.chart (i w) ∈ Ψ.target ∩ O :=
    hd.preimage_mem_nhds ((Ψ.open_target.inter hO).mem_nhds ⟨htarget, hcenter⟩)
  have hvanish : ((q ∘ Ψ) ∘ d.sheetTransition Ψ) =ᶠ[𝓝 (t, (0 : A))] (fun _ => 0) := by
    filter_upwards [hnearS, hnear] with w hw hwo
    change q (Ψ (Ψ.symm (d.chart (i w)))) = 0
    have hinv : Ψ (Ψ.symm (d.chart (i w))) = d.chart (i w) := Ψ.right_inv' hwo.1
    rw [hinv]
    exact hzero _ ⟨(d.sheet _ hw).mpr rfl, hwo.2⟩
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q htarget (hq.contMDiffAt (hO.mem_nhds hcenter))
  have hsheet := d.contDiffAt_sheetTransition Ψ ht htarget
  have hchain :=
    fderiv_comp (t, (0 : A)) (hqΨ.differentiableAt (by simp)) (hsheet.differentiableAt (by simp))
  have hder : fderiv ℝ ((q ∘ Ψ) ∘ d.sheetTransition Ψ) (t, (0 : A)) = 0 := by
    rw [hvanish.fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : N) (t, (0 : A))).fderiv
  exact hchain.symm.trans hder

/-- The normal detector composed with the sheet differential is the derivative of the ambient map
read in the strip chart of the sheet. -/
theorem StripNormalData.normalDetector_comp_sheet {A B Z E M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (q : M → N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    (d.normalDetector Ψ q t).comp (d.sheetDifferential Ψ t) =
      fderiv ℝ (fun w : ℝ × A => q (d.chart (w, 0))) (t, 0) := by
  let i := ContinuousLinearMap.inl ℝ (ℝ × A) B
  have hi : ContinuousAt i (t, 0) := i.continuous.continuousAt
  have hdc : ContinuousAt d.chart (i (t, 0)) :=
    d.chart.contMDiffOn_toFun.continuousOn.continuousAt (d.chart.open_source.mem_nhds (d.line ht))
  have hd : ContinuousAt (d.chart ∘ i) (t, 0) := ContinuousAt.comp (g := d.chart) (f := i) hdc hi
  have hnear : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), d.chart (i w) ∈ Ψ.target :=
    hd.preimage_mem_nhds (Ψ.open_target.mem_nhds htarget)
  have heq :
    ((q ∘ Ψ) ∘ d.sheetTransition Ψ) =ᶠ[𝓝 (t, (0 : A))] (fun w : ℝ × A => q (d.chart (w, 0))) := by
    filter_upwards [hnear] with w hw
    exact congrArg q (Ψ.right_inv' hw)
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q htarget hq
  have hsheet := d.contDiffAt_sheetTransition Ψ ht htarget
  have hchain :=
    fderiv_comp (t, (0 : A)) (hqΨ.differentiableAt (by simp)) (hsheet.differentiableAt (by simp))
  exact hchain.symm.trans heq.fderiv_eq

/-- In the rank-three situation, the two corner sheet-pair determinants have opposite signs exactly
when the two corner determinants of a defining map of the second sheet, read in the strip chart
of the first, do: the intersection signs can be computed from a local defining function. -/
theorem TubularBigon.opposite_rankThree_corners_iff_normal_sheet_determinants {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} (tube : TubularBigon (E := E) S T a b k l h 3)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)
    (q : M → (ℝ × EuclideanSpace ℝ (Fin 1))) {O : Set M} (hO : IsOpen O)
    (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q O)
    (hzero : ∀ y ∈ T ∩ O, q y = 0)
    (hcenter : ∀ t ∈ Set.Icc (0 : ℝ) 1, e.chart (StripCoordinates.center t) ∈ O)
    (hqs :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Function.Surjective
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) q
            (e.chart (StripCoordinates.center t)))) :
    (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
      (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (0, 0)).det *
          (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (1, 0)).det <
        0 := by
  let i : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let j := IntersectionCoordinates.pairCoordinates FrameField.rankThreePairCoordinates
  let G := e.sheetDifferential tube.chart
  let L := d.sheetDifferential tube.chart
  let C (t : ℝ) := (e.sheetComplement tube.chart t).comp i.toContinuousLinearMap
  let Q := e.normalDetector tube.chart q
  have htarget :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, e.chart (StripCoordinates.center t) ∈ tube.chart.target :=
    fun _ ht => tube.upper_chart_center_mem_target e ht
  have hG : ContDiffOn ℝ ∞ G (Set.Icc (0 : ℝ) 1) :=
    (e.contDiffOn_sheetDifferential tube.chart).mono (fun t ht => ⟨e.line ht, htarget t ht⟩)
  have hC : ContDiffOn ℝ ∞ C (Set.Icc (0 : ℝ) 1) :=
    ((e.contDiffOn_sheetComplement tube.chart).mono
          (fun t ht => ⟨e.line ht, htarget t ht⟩)).clm_comp
      contDiffOn_const
  have hQ : ContDiffOn ℝ ∞ Q (Set.Icc (0 : ℝ) 1) :=
    e.contDiffOn_normalDetector tube.chart q hO hq htarget hcenter
  have hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible := by
    intro t ht
    let p :=
      ContinuousLinearEquiv.prodCongr
        (ContinuousLinearEquiv.refl ℝ (ℝ × EuclideanSpace ℝ (Fin 2))) i
    have heq :
      (G t).coprod (C t) =
        ((e.sheetDifferential tube.chart t).coprod (e.sheetComplement tube.chart t)).comp
          p.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro z
      rfl
    apply FrameField.isInvertible_coprod_of_bijective
    rw [heq]
    exact
      (e.isInvertible_sheet_coprod_complement tube.chart ht (htarget t ht)).bijective.comp
        p.bijective
  have hQs : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Surjective (Q t) := fun t ht =>
    e.surjective_normalDetector tube.chart q (htarget t ht)
      (hq.contMDiffAt (hO.mem_nhds (hcenter t ht))) (hqs t ht)
  have hQG : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Q t).comp (G t) = 0 := fun t ht =>
    e.normalDetector_comp_sheet_eq_zero tube.chart q hO hq hzero ht (htarget t ht) (hcenter t ht)
  have hsign :=
    FrameField.opposite_intersectionDet_iff_normalDet j G C L Q hG hC hQ hi hQs hQG
  have hdet (t : ℝ) :
    tube.rankThreeSheetPairDet d e t =
      (j.symm.toContinuousLinearMap.comp ((G t).coprod (L t))).det :=
    IntersectionCoordinates.det_jointBlock_eq_tangentSum
      FrameField.rankThreePairCoordinates (G t) (L t)
  have hcoeff (t : ℝ) (ht : t = 0 ∨ t = 1) :
    (Q t).comp (L t) =
      fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (t, 0) := by
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
    have hpoint := tube.rankThree_corner_sheet_charts_coincide d e ht
    have hqD :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q
        (d.chart (StripCoordinates.center t)) :=
      hpoint.symm ▸ hq.contMDiffAt (hO.mem_nhds (hcenter t htI))
    have hQeq : Q t = d.normalDetector tube.chart q t := by
      change e.normalDetector tube.chart q t = d.normalDetector tube.chart q t
      unfold StripNormalData.normalDetector
      rw [hpoint]
    rw [hQeq]
    exact
      d.normalDetector_comp_sheet tube.chart q htI (tube.lower_chart_center_mem_target d htI) hqD
  rw [hdet 0, hdet 1]
  exact hsign.trans (by rw [hcoeff 0 (Or.inl rfl), hcoeff 1 (Or.inr rfl)])

/-- The normal coordinates of the belt sphere in the negative directions of a Morse chart, read
through a chosen splitting `j`. -/
def ManifoldMorse.MorseSurgeryData.beltSheetNormal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p)
    (j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates) :
    D.UpperLevel → (ℝ × EuclideanSpace ℝ (Fin 1)) :=
  j.symm ∘ D.beltNormal

attribute [local instance 100] Classical.propDecidable in
/-- For a rank-three tubular bigon between a sheet and a belt sphere of a Morse surgery, the two
corner intersection signs are opposite exactly when the two corner determinants of the belt
normal coordinates are. -/
theorem ManifoldMorse.MorseSurgeryData.opposite_belt_corners_iff_normal_sheet_determinants
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates) {S : Set D.UpperLevel}
    {a b : ℝ → D.UpperLevel} {k l : (ℝ × ℝ) → D.UpperLevel} {h : ℝ} :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∀
      (tube :
        TubularBigon (E := RegularLevel.Model E) S (Set.range D.surgery.beltSphere) a
          b k l h 3)
      (d :
        StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E :=
          RegularLevel.Model E) S k)
      (e :
        StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E :=
          RegularLevel.Model E) (Set.range D.surgery.beltSphere) l),
      (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
        (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => D.beltSheetNormal j (d.chart (w, 0)))
                (0, 0)).det *
            (fderiv ℝ
                (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => D.beltSheetNormal j (d.chart (w, 0)))
                (1, 0)).det <
          0 := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  intro tube d e
  have hq :
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞
      (D.beltSheetNormal j) D.beltNormalDomain :=
    j.symm.contDiff.contMDiff.comp_contMDiffOn (D.contMDiffOn_beltNormal hf)
  have hcenter (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    e.chart (StripCoordinates.center t) ∈ Set.range D.surgery.beltSphere :=
    (e.sheet _ (e.line ht)).mpr rfl
  have hcenterO (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    e.chart (StripCoordinates.center t) ∈ D.beltNormalDomain := by
    obtain ⟨v, hv⟩ := hcenter t ht
    exact hv ▸ D.belt_mem_normalDomain v
  apply
    tube.opposite_rankThree_corners_iff_normal_sheet_determinants d e (D.beltSheetNormal j)
      D.isOpen_beltNormalDomain hq
  · rintro y ⟨⟨v, rfl⟩, _⟩
    change j.symm (D.beltNormal (D.surgery.beltSphere v)) = 0
    rw [D.beltNormal_belt, map_zero]
  · exact hcenterO
  · intro t ht
    obtain ⟨v, hv⟩ := hcenter t ht
    rw [← hv]
    have hnormal :=
      (D.contMDiffOn_beltNormal hf).contMDiffAt
        (D.isOpen_beltNormalDomain.mem_nhds (D.belt_mem_normalDomain v))
    have hJ :
      mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) j.symm
          (D.beltNormal (D.surgery.beltSphere v)) =
        j.symm.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact j.symm.toContinuousLinearMap.fderiv
    have hjSmooth :
      ContMDiff 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ j.symm :=
      j.symm.contDiff.contMDiff
    rw [beltSheetNormal,
      mfderiv_comp _ (hjSmooth.mdifferentiableAt (by simp)) (hnormal.mdifferentiableAt (by simp)),
      hJ]
    exact j.symm.surjective.comp (D.surjective_beltNormal_derivative hf v)

/-- The sheet coordinate of a point: the first component of its image under the inverse of a chart
in which the sheet is the zero set of the second coordinate. -/
def NativeSheetCoordinates.projection {D B E M N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M) (x : N) : D :=
  (Φ.symm (F x)).1

/-- The sheet projection is smooth on the preimage of the chart target. -/
theorem NativeSheetCoordinates.contMDiffOn_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) : ContMDiffOn I 𝓘(ℝ, D) ∞ (projection Φ F) (F ⁻¹' Φ.target) := by
  have hcoord : ContMDiffOn I 𝓘(ℝ, D × B) ∞ (Φ.symm ∘ F) (F ⁻¹' Φ.target) :=
    Φ.contMDiffOn_invFun.comp hF.contMDiffOn (fun _ hx => hx)
  exact contDiff_fst.contMDiff.comp_contMDiffOn hcoord

/-- Where the chart is clean for the image of `F` (the image meets the chart exactly in the zero set
of the second coordinate), the differential of the sheet projection is injective wherever that
of `F` is. -/
theorem NativeSheetCoordinates.injective_mfderiv_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0) {x : N}
    (hx : F x ∈ Φ.target) (hiF : Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    Function.Injective (mfderiv I 𝓘(ℝ, D) (projection Φ F) x) := by
  let C : N → (D × B) := Φ.symm ∘ F
  let T : G →L[ℝ] (D × B) := mfderiv I 𝓘(ℝ, D × B) C x
  have hC : ContMDiffAt I 𝓘(ℝ, D × B) ∞ C x :=
    (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hx)).comp x hF.contMDiffAt
  have hTi : Function.Injective T := by
    change Function.Injective (mfderiv I 𝓘(ℝ, D × B) (Φ.symm ∘ F) x)
    rw [mfderiv_comp x (Φ.symm.mdifferentiableAt (by simp) hx) (hF.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv Φ.symm hx).injective.comp hiF
  have hfst :
    (mfderiv I 𝓘(ℝ, D) (projection Φ F) x : G →L[ℝ] D) = (ContinuousLinearMap.fst ℝ D B).comp T :=
    by
    have hp : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, D) ∞ (Prod.fst : D × B → D) := contDiff_fst.contMDiff
    have hd :
      mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, D) (Prod.fst : D × B → D) (C x) = ContinuousLinearMap.fst ℝ D B := by
      rw [mfderiv_eq_fderiv]
      exact (ContinuousLinearMap.fst ℝ D B).fderiv
    change mfderiv I 𝓘(ℝ, D) (Prod.fst ∘ C) x = _
    rw [mfderiv_comp x (hp.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp)), hd]
    rfl
  have hzero : (Prod.snd ∘ C) =ᶠ[𝓝 x] (fun _ => (0 : B)) := by
    filter_upwards [hF.continuous.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)] with
      y hy
    exact (hclean _ (Φ.map_target' hy)).mp ⟨y, (Φ.right_inv' hy).symm⟩
  have hsnd : (ContinuousLinearMap.snd ℝ D B).comp T = 0 := by
    have hp : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
    have hd :
      mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, B) (Prod.snd : D × B → B) (C x) = ContinuousLinearMap.snd ℝ D B := by
      rw [mfderiv_eq_fderiv]
      exact (ContinuousLinearMap.snd ℝ D B).fderiv
    have hz : (mfderiv I 𝓘(ℝ, B) (Prod.snd ∘ C) x : G →L[ℝ] B) = 0 := by
      rw [hzero.mfderiv_eq, mfderiv_const]
      rfl
    rw [mfderiv_comp x (hp.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp)),
      hd] at hz
    exact hz
  intro u v huv
  apply hTi
  apply Prod.ext
  · exact
      (congrArg (fun L : G →L[ℝ] D => L u) hfst).symm.trans
        (huv.trans (congrArg (fun L : G →L[ℝ] D => L v) hfst))
  · have hz (w : G) : (T w).2 = 0 := congrArg (fun L : G →L[ℝ] B => L w) hsnd
    rw [hz u, hz v]

/-- Under the same cleanness hypothesis, and when source and sheet directions have the same
dimension, the sheet projection is a local diffeomorphism on the preimage of the chart target. -/
theorem NativeSheetCoordinates.isLocalDiffeomorphOn_projection {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M) [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ G] [I.Boundaryless] [IsManifold I ∞ N] (hF : ContMDiff I 𝓘(ℝ, E) ∞ F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D)
    (hiF : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    IsLocalDiffeomorphOn I 𝓘(ℝ, D) ∞ (projection Φ F) (F ⁻¹' Φ.target) := by
  have hU : IsOpen (F ⁻¹' Φ.target) := Φ.open_target.preimage hF.continuous
  intro x
  let A : G →L[ℝ] D := mfderiv I 𝓘(ℝ, D) (projection Φ F) x.1
  have hi : Function.Injective A := injective_mfderiv_projection Φ F hF hclean x.2 (hiF x.1)
  have hb : Function.Bijective A :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩
  have hA : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  exact isLocalDiffeomorphAt_boundaryless hU x.2 (contMDiffOn_projection Φ F hF) hA

/-- A clean chart for an injective immersion `F` induces a chart of the source: a partial
diffeomorphism onto the slice `{u | (u, 0) ∈ Φ.source}` whose inverse is the sheet projection
and which is carried by `F` to `u ↦ Φ (u, 0)`. -/
theorem NativeSheetCoordinates.exists_induced_sheet_chart {D B E G H M N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {I : ModelWithCorners ℝ G H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I ∞ N] [Nonempty N]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)
    (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) (hinjF : Function.Injective F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ Set.range F ↔ z.2 = 0)
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D)
    (hiF : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, D) I D N ∞,
      c.source = {u | (u, (0 : B)) ∈ Φ.source} ∧
        c.target = F ⁻¹' Φ.target ∧
          (∀ u ∈ c.source, F (c u) = Φ (u, 0)) ∧ ∀ x, c.symm x = projection Φ F x := by
  let U := F ⁻¹' Φ.target
  have hU : IsOpen U := Φ.open_target.preimage hF.continuous
  have hzero (x : N) (hx : x ∈ U) : (Φ.symm (F x)).2 = 0 :=
    (hclean _ (Φ.map_target' hx)).mp ⟨x, (Φ.right_inv' hx).symm⟩
  have hinj : Set.InjOn (projection Φ F) U := by
    intro x hx y hy heq
    have hc : Φ.symm (F x) = Φ.symm (F y) := Prod.ext heq ((hzero x hx).trans (hzero y hy).symm)
    apply hinjF
    exact (Φ.right_inv' hx).symm.trans ((congrArg Φ hc).trans (Φ.right_inv' hy))
  let p :=
    partialDiffeomorphOfInjectiveLocal hU hinj
      (isLocalDiffeomorphOn_projection Φ F hF hclean hdim hiF)
  have htarget : p.target = {u | (u, (0 : B)) ∈ Φ.source} := by
    change projection Φ F '' U = _
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      have heq : (projection Φ F x, (0 : B)) = Φ.symm (F x) := Prod.ext rfl (hzero x hx).symm
      change (projection Φ F x, (0 : B)) ∈ Φ.source
      rw [heq]
      exact Φ.map_target' hx
    · intro hu
      obtain ⟨x, hx⟩ := (hclean (u, 0) hu).mpr rfl
      have hxU : x ∈ U := by
        change F x ∈ Φ.target
        rw [hx]
        exact Φ.map_source' hu
      refine ⟨x, hxU, ?_⟩
      change (Φ.symm (F x)).1 = u
      rw [hx]
      exact congrArg Prod.fst (Φ.left_inv' hu)
  refine ⟨p.symm, htarget, rfl, ?_, fun _ => rfl⟩
  intro u hu
  have hx : p.symm u ∈ U := p.map_target' hu
  have hp : projection Φ F (p.symm u) = u := p.right_inv' hu
  have heq : Φ.symm (F (p.symm u)) = (u, (0 : B)) := Prod.ext hp (hzero (p.symm u) hx)
  exact (Φ.right_inv' hx).symm.trans (congrArg Φ heq)

end
