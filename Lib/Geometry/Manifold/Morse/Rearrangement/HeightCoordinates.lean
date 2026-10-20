/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.LocalDiffeomorph
/-!
# Regular height coordinates

For a smooth `F : ℝ × V → ℝ` the *height map* `RegularHeightCoordinates.heightMap F`
sends `(t, z)` to `(F (t, z), z)`, keeping the transverse coordinate. Its derivative is
block triangular (`fderiv_heightMap`), so it is a local diffeomorphism wherever the time
derivative `fderiv F p (1, 0)` is nonzero (`heightMap_localDiffeomorph`). For the displaced
height `displacedHeight u (t, z) = t + u (t, z)` with `u` smooth, compactly supported and
`0 < 1 + ∂u/∂t`, the height map is injective (`heightMap_injective_of_positive`) and
surjective (`heightMap_surjective_of_compactSupport`), hence a diffeomorphism of `ℝ × V`
(`longitudinalDiffeomorph`).

This is the coordinate change by which a Morse function is modified along the gradient lines
of a band without creating critical points: the proof of the rearrangement theorem,
Milnor, *Lectures on the h-cobordism theorem*, §4 (Theorem 4.1).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Regular height coordinates -/

/-- The map `(t, z) ↦ (F(t, z), z)` keeping the transverse coordinate. -/
def RegularHeightCoordinates.heightMap {V : Type*} (F : ℝ × V → ℝ) (p : ℝ × V) : ℝ × V :=
  (F p, p.2)

/-- A linear map on `ℝ × V` splits into scalar and transverse parts. -/
theorem RegularHeightCoordinates.linear_decomposition {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℝ × V →L[ℝ] ℝ) (s : ℝ) (z : V) : L (s, z) = s * L (1, 0) + L (0, z) := by
  have he : (s, z) = s • (1, (0 : V)) + (0, z) := by simp
  rw [he, map_add, map_smul]
  rfl

/-- A height-preserving triangular map with nonzero axis component is bijective. -/
theorem RegularHeightCoordinates.triangular_bijective {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℝ × V →L[ℝ] ℝ) (hL : L (1, 0) ≠ 0) :
    Function.Bijective (L.prod (ContinuousLinearMap.snd ℝ ℝ V)) := by
  constructor
  · rintro ⟨s, z⟩ ⟨t, w⟩ h
    have hzw : z = w := congrArg Prod.snd h
    subst w
    have he : L (s, z) = L (t, z) := congrArg Prod.fst h
    rw [linear_decomposition L s z, linear_decomposition L t z] at he
    have hst : s = t := (mul_right_cancel₀ hL) (by linarith)
    exact Prod.ext hst rfl
  · rintro ⟨s, z⟩
    refine ⟨((s - L (0, z)) / L (1, 0), z), ?_⟩
    apply Prod.ext
    · change L ((s - L (0, z)) / L (1, 0), z) = s
      rw [linear_decomposition L, div_mul_cancel₀ _ hL]
      ring
    · rfl

/-- The triangular map as a continuous linear equivalence. -/
def RegularHeightCoordinates.triangularEquiv {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : ℝ × V →L[ℝ] ℝ) (hL : L (1, 0) ≠ 0) :
    (ℝ × V) ≃L[ℝ] (ℝ × V) :=
  (LinearEquiv.ofBijective (L.prod (ContinuousLinearMap.snd ℝ ℝ V)).toLinearMap
      (triangular_bijective L hL)).toContinuousLinearEquiv

/-- The height map is smooth when `F` is. -/
theorem RegularHeightCoordinates.contDiff_heightMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (heightMap F) :=
  hF.prodMk contDiff_snd

/-- The derivative of the height map in block form. -/
theorem RegularHeightCoordinates.fderiv_heightMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) (p : ℝ × V) :
    fderiv ℝ (heightMap F) p = (fderiv ℝ F p).prod (ContinuousLinearMap.snd ℝ ℝ V) :=
  (((hF.differentiable (by simp) p).hasFDerivAt).prodMk
      (ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt).fderiv

/-- The height map is a local diffeomorphism where its time derivative is nonzero. -/
theorem RegularHeightCoordinates.heightMap_localDiffeomorph {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {F : ℝ × V → ℝ}
    (hF : ContDiff ℝ ∞ F) {p : ℝ × V} (hreg : fderiv ℝ F p (1, 0) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ (heightMap F) p := by
  have hinv : (fderiv ℝ (heightMap F) p).IsInvertible := by
    refine ⟨triangularEquiv (fderiv ℝ F p) hreg, ?_⟩
    rw [fderiv_heightMap hF]
    rfl
  obtain ⟨Φ, hp, _, hΦ⟩ :=
    exists_partialDiffeomorph_of_contDiffOn isOpen_univ (Set.mem_univ p)
      (contDiff_heightMap hF).contDiffOn hinv
  exact IsLocalDiffeomorphAt.of_eqOn Φ hp (fun _ _ => congrFun hΦ.symm _)

/-- The height with a longitudinal displacement added. -/
def RegularHeightCoordinates.displacedHeight {V : Type*} (u : ℝ × V → ℝ) (p : ℝ × V) : ℝ :=
  p.1 + u p

/-- The displaced height is smooth. -/
theorem RegularHeightCoordinates.contDiff_displacedHeight {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (displacedHeight u) :=
  contDiff_fst.add hu

/-- The scalar time derivative of a height function. -/
theorem RegularHeightCoordinates.scalar_derivative {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) (s : ℝ) (z : V) :
    HasDerivAt (fun t : ℝ => F (t, z)) (fderiv ℝ F (s, z) (1, 0)) s :=
  ((hF.differentiable (by simp) (s, z)).hasFDerivAt).comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))

/-- Positive time derivative makes the height map injective. -/
theorem RegularHeightCoordinates.heightMap_injective_of_positive {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hpos : ∀ p, 0 < fderiv ℝ F p (1, 0)) : Function.Injective (heightMap F) := by
  have hmono (z : V) : StrictMono (fun s : ℝ => F (s, z)) :=
    strictMono_of_deriv_pos (fun s => by rw [(scalar_derivative hF s z).deriv]; exact hpos _)
  rintro ⟨s, z⟩ ⟨t, w⟩ he
  have hzw : z = w := congrArg Prod.snd he
  subst w
  have hst : s = t := (hmono z).injective (congrArg Prod.fst he)
  exact Prod.ext hst rfl

/-- Bounded slope makes the height map surjective. -/
theorem RegularHeightCoordinates.heightMap_surjective_of_bounded {V : Type*}
    [NormedAddCommGroup V] {u : ℝ × V → ℝ} (hu : Continuous u) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p, |u p| ≤ C) : Function.Surjective (heightMap (displacedHeight u)) := by
  rintro ⟨r, z⟩
  let a := r - (C + 1)
  let b := r + (C + 1)
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hs : Continuous (fun s : ℝ => displacedHeight u (s, z)) :=
    continuous_id.add (hu.comp (continuous_id.prodMk continuous_const))
  have hlo : displacedHeight u (a, z) ≤ r := by
    have h := (abs_le.mp (hbound (a, z))).2
    dsimp [displacedHeight, a] at *
    linarith
  have hhi : r ≤ displacedHeight u (b, z) := by
    have h := (abs_le.mp (hbound (b, z))).1
    dsimp [displacedHeight, b] at *
    linarith
  obtain ⟨s, _, he⟩ := intermediate_value_Icc hab hs.continuousOn ⟨hlo, hhi⟩
  exact ⟨(s, z), Prod.ext he rfl⟩

/-- Compactly supported displacement keeps the height map surjective. -/
theorem RegularHeightCoordinates.heightMap_surjective_of_compactSupport {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : Function.Surjective (heightMap (displacedHeight u)) := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hu.continuous).isBounded.exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg (u 0)).trans (hC _ ⟨0, rfl⟩)
  exact
    heightMap_surjective_of_bounded hu.continuous C hC0
      (fun p => by simpa only [Real.norm_eq_abs] using hC _ ⟨p, rfl⟩)

/-- The longitudinal displacement as a diffeomorphism of `ℝ × V`. -/
def RegularHeightCoordinates.longitudinalDiffeomorph {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {u : ℝ × V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hpos : ∀ p, 0 < fderiv ℝ (displacedHeight u) p (1, 0)) :
    (ℝ × V) ≃ₘ⟮𝓘(ℝ, ℝ × V), 𝓘(ℝ, ℝ × V)⟯ (ℝ × V) := by
  have hs := contDiff_displacedHeight hu
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ (heightMap (displacedHeight u)) :=
    fun p => heightMap_localDiffeomorph hs (hpos p).ne'
  exact
    hloc.diffeomorph'
      ⟨heightMap_injective_of_positive hs hpos, heightMap_surjective_of_compactSupport hu hc⟩
