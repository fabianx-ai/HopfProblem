/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.CellStructure
/-!
# Reeb's theorem from two Morse critical points

`ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points` gives
`Nonempty (M ≃ₜ Hemisphere.Sphere (Module.finrank ℝ E))` for a compact
finite-dimensional smooth manifold carrying a smooth Morse function whose
critical set is exactly `{p, q}`, with `f p < f q`.

## Outline of the proof

1. At a local minimum, the negative Morse coordinates vanish; the positive
   coordinates describe a small disk sublevel.
2. `FlowConstruction.nonempty_regularSublevelDisk` transports a disk sublevel
   across a band without critical points.
3. Applying the minimum construction to `f` and `-f` gives the two disk caps
   used by `twoDiskDecompositionOfSublevels`.
4. The disk-double quotient maps homeomorphically to the sphere
   (`DiskDouble.homeomorphSphere`, `TwoDiskDecomposition.homeomorphSphere`).
5. `homeomorphSphereOfSublevelDisks` finishes the two-critical-point theorem.

## Main definitions and results

* `SublevelDisk`: a disk presentation with control of the boundary level.
* `TwoDiskDecomposition`: two disk presentations covering a space.
* `ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points`: Reeb's theorem.

## References

* [milnor63] J. Milnor, *Morse Theory*, Theorem 4.1.

## Tags

morse-theory, reeb-theorem, sublevel-sets, spheres
-/

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Disk sublevels near a Morse minimum -/

attribute [local instance 100] Classical.propDecidable in
/-- At a local minimum, every vector in the negative Morse-coordinate space is zero. -/
theorem ManifoldMorse.SignedMorseChart.negative_eq_zero_of_localMin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p)
    (u : c.NegativeCoordinates) : u = 0 := by
  by_contra hu
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨U, hUmin, hU, hpU⟩ := _root_.mem_nhds_iff.mp hmin
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hU hpU
  let z : c.NegativeCoordinates := (r / ‖u‖) • u
  have hz : ‖z‖ = r := by
    rw [show z = (r / ‖u‖) • u from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hnorm), div_mul_cancel₀ _ hnorm.ne']
  have hpoint :=
    hblock
      (show (z, (0 : c.PositiveCoordinates)) ∈ Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r from
        ⟨mem_closedBall_zero_iff.mpr hz.le, by
          simpa only [mem_closedBall_zero_iff, norm_zero] using hr.le⟩)
  have hh := hUmin hpoint.2
  change f p ≤ f (c.splitChart.symm (z, (0 : c.PositiveCoordinates))) at hh
  rw [c.splitChart_inverse_equation hpoint.1, hz, norm_zero] at hh
  nlinarith [sq_pos_of_pos hr]

attribute [local instance 100] Classical.propDecidable in
/-- The negative Morse-coordinate space at a local minimum is a subsingleton. -/
theorem ManifoldMorse.SignedMorseChart.subsingleton_negative_of_localMin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    Subsingleton c.NegativeCoordinates :=
  ⟨fun u v =>
    (c.negative_eq_zero_of_localMin hmin u).trans (c.negative_eq_zero_of_localMin hmin v).symm⟩

attribute [local instance 100] Classical.propDecidable in
/-- Near a unique minimum on a compact Hausdorff space, a sufficiently small global sublevel is a disk in the positive Morse coordinates, with an explicit quadratic height formula. -/
theorem ManifoldMorse.SignedMorseChart.exists_minimum_disk_sublevel_with_height
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b) :
    ∃ ρ > (0 : ℝ),
      f p + ρ ^ 2 < b ∧
        ∃ e : MorseHandle.UnitDisk c.PositiveCoordinates ≃ₜ { x : M // f x ≤ f p + ρ ^ 2 },
          ∀ v, f (e v).1 = f p + ρ ^ 2 * ‖(v : c.PositiveCoordinates)‖ ^ 2 := by
  have hglobal : ∀ x, f p ≤ f x := by
    intro x
    by_contra! h
    have hxp := hunique x h.le
    rw [hxp] at h
    exact lt_irrefl _ h
  have hmin : IsLocalMin f p := Filter.Eventually.of_forall hglobal
  let : Subsingleton c.NegativeCoordinates := c.subsingleton_negative_of_localMin hmin
  obtain ⟨R, hR, hblockR⟩ := c.exists_closed_productBlock
  obtain ⟨ε, hε, hsublevel⟩ :=
    exists_small_sublevel_subset hf hunique c.splitChart.open_source c.splitChart_mem_source
  let δ := Min.min ε (b - f p)
  have hδ : 0 < δ := lt_min hε (sub_pos.mpr hb)
  let ρ := Min.min (R / 2) (Min.min 1 (δ / 2))
  have hρ : 0 < ρ := lt_min (half_pos hR) (lt_min zero_lt_one (half_pos hδ))
  have hρR : ρ ≤ R / 2 := min_le_left _ _
  have hρone : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < δ := by nlinarith
  have hsqε : ρ ^ 2 < ε := hρsq.trans_le (min_le_left _ _)
  have hsqb : ρ ^ 2 < b - f p := hρsq.trans_le (min_le_right _ _)
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target := by
    intro z hz
    have hr : 2 * ρ ≤ R := by linarith
    exact
      hblockR
        ⟨Metric.closedBall_subset_closedBall hr hz.1, Metric.closedBall_subset_closedBall hr hz.2⟩
  let z₀ : MorseHandle.UnitDisk c.NegativeCoordinates := ⟨0, by simp⟩
  let h : C(MorseHandle.UnitDisk c.PositiveCoordinates, { x : M // f x ≤ f p + ρ ^ 2 }) :=
    { toFun := fun v =>
        ⟨c.attachingHandleMap ρ hρ hblock (z₀, v), c.attachingHandleMap_upper ρ hρ hblock (z₀, v)⟩
      continuous_toFun :=
        ((c.attachingHandleMap ρ hρ hblock).continuous.comp
              (continuous_const.prodMk continuous_id)).subtype_mk
          _ }
  have hinj : Function.Injective h := by
    intro v w hvw
    have heq := c.attachingHandleMap_injective ρ hρ hblock (congrArg Subtype.val hvw)
    exact congrArg Prod.snd heq
  have hsurj : Function.Surjective h := by
    intro y
    have hyS : y.1 ∈ c.splitChart.source :=
      hsublevel
        (show f y.1 ≤ f p + ε from by
          have hy := y.2
          linarith)
    have heq := c.splitChart_equation hyS
    have hnegative : (c.splitChart y.1).1 = 0 := Subsingleton.elim _ _
    rw [hnegative, norm_zero] at heq
    have hypos : ‖(c.splitChart y.1).2‖ ≤ ρ := by
      have hy := y.2
      nlinarith [norm_nonneg (c.splitChart y.1).2]
    have hylower : f p - ρ ^ 2 ≤ f y.1 := by
      have hy := hglobal y.1
      linarith [sq_nonneg ρ]
    obtain ⟨⟨u, v⟩, huv⟩ :=
      (c.mem_range_attachingHandleMap_iff_inequalities ρ hρ hblock hyS).mpr ⟨hypos, hylower⟩
    have hu : u = z₀ := Subsingleton.elim _ _
    subst u
    exact ⟨v, Subtype.ext huv⟩
  refine ⟨ρ, hρ, by linarith, ?_⟩
  refine
    ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective h ⟨hinj, hsurj⟩) h.continuous, ?_⟩
  intro v
  change f (c.attachingHandleMap ρ hρ hblock (z₀, v)) = _
  rw [c.attachingHandleMap_quadratic]
  change
    f p +
        (-‖(ρ * Real.sqrt (1 + ‖(v : c.PositiveCoordinates)‖ ^ 2)) •
                  (0 : c.NegativeCoordinates)‖ ^
              2 +
          ‖ρ • (v : c.PositiveCoordinates)‖ ^ 2) =
      _
  simp only [smul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, zero_add,
    norm_smul, Real.norm_eq_abs, abs_of_pos hρ, mul_pow]

attribute [local instance 100] Classical.propDecidable in
/-- At a local minimum, the positive Morse-coordinate space has the same real dimension as the manifold model. -/
theorem ManifoldMorse.SignedMorseChart.finrank_positive_of_localMin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    Module.finrank ℝ c.PositiveCoordinates = Module.finrank ℝ E := by
  let : Unique c.NegativeCoordinates :=
    { default := 0, uniq := c.negative_eq_zero_of_localMin hmin }
  let e : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] c.PositiveCoordinates :=
    (MorseHandle.splitLinearEquiv c.weights).trans
      (LinearEquiv.uniqueProd (R := ℝ) (M := c.PositiveCoordinates) (M₂ := c.NegativeCoordinates))
  simpa using e.finrank_eq.symm

attribute [local instance 100] Classical.propDecidable in
/-- Identify the positive coordinates at a Morse minimum isometrically with the standard Euclidean space of the manifold dimension. -/
def ManifoldMorse.SignedMorseChart.minimumPositiveIsometry {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    c.PositiveCoordinates ≃ₗᵢ[ℝ] Hemisphere.Ambient (Module.finrank ℝ E) :=
  (stdOrthonormalBasis ℝ c.PositiveCoordinates).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (c.finrank_positive_of_localMin hmin)))

attribute [local instance 100] Classical.propDecidable in
/-- The positive-coordinate unit disk at a Morse minimum is homeomorphic to the standard closed unit ball. -/
def ManifoldMorse.SignedMorseChart.minimumDiskHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    MorseHandle.UnitDisk c.PositiveCoordinates ≃ₜ
      Hemisphere.Ball (Module.finrank ℝ E) :=
  (c.minimumPositiveIsometry hmin).toHomeomorph.subtype (p := fun x => x ∈ Metric.closedBall 0 1)
    (q := fun x => x ∈ Metric.closedBall 0 1)
    (fun x => by
      simp only [mem_closedBall_zero_iff, LinearIsometryEquiv.coe_toHomeomorph,
        LinearIsometryEquiv.norm_map])

attribute [local instance 100] Classical.propDecidable in
/-- The inverse identification of the minimum disk preserves the Euclidean norm. -/
theorem ManifoldMorse.SignedMorseChart.norm_minimumDiskHomeomorph_symm {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p)
    (v : Hemisphere.Ball (Module.finrank ℝ E)) :
    ‖((c.minimumDiskHomeomorph hmin).symm v : c.PositiveCoordinates)‖ =
      ‖(v : Hemisphere.Ambient (Module.finrank ℝ E))‖ := by
  change
    ‖(c.minimumPositiveIsometry hmin).symm (v : Hemisphere.Ambient (Module.finrank ℝ E))‖ =
      _
  exact (c.minimumPositiveIsometry hmin).symm.norm_map _

/-! ### Hemisphere coordinates -/

/-- The vector of all coordinates of a sphere point except its first coordinate. -/
def Hemisphere.tail {n : ℕ} (y : Sphere n) : Ambient n :=
  WithLp.toLp 2 (fun i => (y : Ambient (n + 1)) i.succ)

/-- The squared first coordinate plus the squared norm of the remaining coordinates of a unit-sphere point is one. -/
theorem Hemisphere.head_sq_add_tail_norm_sq {n : ℕ} (y : Sphere n) :
    (y : Ambient (n + 1)) 0 ^ 2 + ‖tail y‖ ^ 2 = 1 := by
  have hy : ‖(y : Ambient (n + 1))‖ ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm.mp y.property]
    exact one_pow 2
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at hy
  rw [EuclideanSpace.real_norm_sq_eq]
  exact hy

/-- The remaining coordinates of a unit-sphere point lie in the closed unit ball. -/
theorem Hemisphere.tail_mem_ball {n : ℕ} (y : Sphere n) :
    tail y ∈ Metric.closedBall (0 : Ambient n) 1 := by
  rw [mem_closedBall_zero_iff]
  have hy := head_sq_add_tail_norm_sq y
  nlinarith [sq_nonneg ((y : Ambient (n + 1)) 0), norm_nonneg (tail y)]

/-- Project a sphere point to the closed unit ball by dropping its first coordinate. -/
def Hemisphere.disk {n : ℕ} (y : Sphere n) : Ball n :=
  ⟨tail y, tail_mem_ball y⟩

/-- The missing hemisphere height of the projected disk point is the absolute value of the original first coordinate. -/
theorem Hemisphere.radius_disk {n : ℕ} (y : Sphere n) :
    radius (disk y) = |(y : Ambient (n + 1)) 0| := by
  have hy := head_sq_add_tail_norm_sq y
  have hs : 1 - ‖tail y‖ ^ 2 = (y : Ambient (n + 1)) 0 ^ 2 := by linarith
  change Real.sqrt (1 - ‖tail y‖ ^ 2) = _
  rw [hs, Real.sqrt_sq_eq_abs]

/-- A sphere point with nonnegative first coordinate is recovered by the positive-hemisphere parametrization of its disk projection. -/
theorem Hemisphere.point_disk_of_nonneg {n : ℕ} (y : Sphere n)
    (hy : 0 ≤ (y : Ambient (n + 1)) 0) : point Bool.true (disk y) = y := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radius_disk, abs_of_nonneg hy]
  · rfl

/-- A sphere point with nonpositive first coordinate is recovered by the negative-hemisphere parametrization of its disk projection. -/
theorem Hemisphere.point_disk_of_nonpos {n : ℕ} (y : Sphere n)
    (hy : (y : Ambient (n + 1)) 0 ≤ 0) : point Bool.false (disk y) = y := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radius_disk, abs_of_nonpos hy]
  · rfl

/-- The positive and negative hemisphere parametrizations jointly cover the sphere. -/
theorem Hemisphere.point_jointly_surjective {n : ℕ} (y : Sphere n) : ∃ b x, point b x = y :=
  by
  rcases le_total 0 ((y : Ambient (n + 1)) 0) with hy | hy
  · exact ⟨Bool.true, disk y, point_disk_of_nonneg y hy⟩
  · exact ⟨Bool.false, disk y, point_disk_of_nonpos y hy⟩

/-! ### The double of a disk -/

/-- Map the two copies of the closed disk to the negative and positive hemispheres. -/
def DiskDouble.hemisphereMap (n : ℕ) :
    Hemisphere.Ball n ⊕ Hemisphere.Ball n → Hemisphere.Sphere n :=
  Sum.elim (Hemisphere.point Bool.false) (Hemisphere.point Bool.true)

/-- The map from the disjoint union of the two disks to their hemispheres is continuous. -/
theorem DiskDouble.continuous_hemisphereMap (n : ℕ) : Continuous (hemisphereMap n) :=
  continuous_sum_dom.mpr
    ⟨Hemisphere.continuous_point Bool.false, Hemisphere.continuous_point Bool.true⟩

/-- The two hemisphere maps agree along the identity identification of their boundary spheres. -/
theorem DiskDouble.hemisphereMap_respects (n : ℕ)
    (x y : Hemisphere.Ball n ⊕ Hemisphere.Ball n)
    (h : DiskDouble.Rel (Homeomorph.refl (Boundary (Hemisphere.Ambient n))) x y) :
    hemisphereMap n x = hemisphereMap n y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact h.elim
    | inr y =>
      obtain ⟨z, rfl, rfl⟩ := h
      exact Hemisphere.point_boundary z
  | inr x => cases y <;> exact h.elim

/-- Descend the hemisphere maps to the disk double glued by the identity boundary map. -/
def DiskDouble.sphereMap (n : ℕ) :
    Space (Homeomorph.refl (Boundary (Hemisphere.Ambient n))) → Hemisphere.Sphere n :=
  Quot.lift (hemisphereMap n) (hemisphereMap_respects n)

/-- The descended map from the untwisted disk double to the sphere is continuous. -/
theorem DiskDouble.continuous_sphereMap (n : ℕ) : Continuous (sphereMap n) :=
  continuous_quot_lift (hemisphereMap_respects n) (continuous_hemisphereMap n)

/-- The descended hemisphere map identifies no points beyond those already glued in the disk double. -/
theorem DiskDouble.sphereMap_injective (n : ℕ) : Function.Injective (sphereMap n) := by
  intro a b
  induction a using Quot.inductionOn with
  | _ x =>
    induction b using Quot.inductionOn with
    | _ y =>
      intro h
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have hxy := Hemisphere.point_injective Bool.false h
          subst y
          rfl
        | inr y => exact Quot.sound ((Hemisphere.point_false_eq_true_iff x y).mp h)
      | inr x =>
        cases y with
        | inl y =>
          exact (Quot.sound ((Hemisphere.point_false_eq_true_iff y x).mp h.symm)).symm
        | inr y =>
          have hxy := Hemisphere.point_injective Bool.true h
          subst y
          rfl

/-- Every sphere point is represented by a point of the untwisted disk double. -/
theorem DiskDouble.sphereMap_surjective (n : ℕ) : Function.Surjective (sphereMap n) := by
  intro y
  obtain ⟨b, x, hx⟩ := Hemisphere.point_jointly_surjective y
  cases b
  · exact ⟨Quot.mk _ (.inl x), hx⟩
  · exact ⟨Quot.mk _ (.inr x), hx⟩

/-- The disk double glued by the identity on the boundary is homeomorphic to the sphere. -/
def DiskDouble.homeomorphSphere (n : ℕ) :
    Space (Homeomorph.refl (Boundary (Hemisphere.Ambient n))) ≃ₜ
      Hemisphere.Sphere n :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (sphereMap n) ⟨sphereMap_injective n, sphereMap_surjective n⟩)
    (continuous_sphereMap n)

/-- Gluing the two disks by any boundary homeomorphism produces a space homeomorphic to the sphere. -/
def DiskDouble.twistedHomeomorphSphere (n : ℕ)
    (e : Boundary (Hemisphere.Ambient n) ≃ₜ Boundary (Hemisphere.Ambient n)) :
    Space e ≃ₜ Hemisphere.Sphere n :=
  (homeomorphUntwisted e).trans (homeomorphSphere n)

/-! ### Spaces covered by two disks -/

/-- Two injective continuous disk parametrizations covering a space, with their overlap exactly specified by a boundary homeomorphism. -/
structure TwoDiskDecomposition (n : ℕ) (M : Type*) [TopologicalSpace M] where
  boundaryEquiv :
    DiskDouble.Boundary (Hemisphere.Ambient n) ≃ₜ DiskDouble.Boundary (Hemisphere.Ambient n)
  left : C(Hemisphere.Ball n, M)
  right : C(Hemisphere.Ball n, M)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  covers : ∀ p : M, (∃ x, left x = p) ∨ ∃ y, right y = p
  overlap :
    ∀ x y,
      left x = right y ↔
        ∃ z : DiskDouble.Boundary (Hemisphere.Ambient n),
          x = DiskDouble.boundary (Hemisphere.Ambient n) z ∧
            y = DiskDouble.boundary (Hemisphere.Ambient n) (boundaryEquiv z)

/-- Combine the two disk parametrizations into a map from their disjoint union. -/
def TwoDiskDecomposition.sumMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : TwoDiskDecomposition n M) :
    Hemisphere.Ball n ⊕ Hemisphere.Ball n → M :=
  Sum.elim d.left d.right

/-- The combined map from the two disks is continuous. -/
theorem TwoDiskDecomposition.continuous_sumMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : TwoDiskDecomposition n M) : Continuous d.sumMap :=
  continuous_sum_dom.mpr ⟨d.left.continuous, d.right.continuous⟩

/-- The combined disk map respects the boundary identification recorded by the decomposition. -/
theorem TwoDiskDecomposition.sumMap_respects {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : TwoDiskDecomposition n M) (x y : Hemisphere.Ball n ⊕ Hemisphere.Ball n)
    (h : DiskDouble.Rel d.boundaryEquiv x y) : d.sumMap x = d.sumMap y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact h.elim
    | inr y => exact (d.overlap x y).mpr h
  | inr x => cases y <;> exact h.elim

/-- The disk-double quotient maps to the space described by the two-disk decomposition. -/
def TwoDiskDecomposition.quotientMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : TwoDiskDecomposition n M) : DiskDouble.Space d.boundaryEquiv → M :=
  Quot.lift d.sumMap d.sumMap_respects

/-- The quotient map associated with a two-disk decomposition is continuous. -/
theorem TwoDiskDecomposition.continuous_quotientMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : TwoDiskDecomposition n M) : Continuous d.quotientMap :=
  continuous_quot_lift d.sumMap_respects d.continuous_sumMap

/-- The overlap condition makes the quotient map of a two-disk decomposition injective. -/
theorem TwoDiskDecomposition.quotientMap_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : TwoDiskDecomposition n M) : Function.Injective d.quotientMap := by
  intro a b
  induction a using Quot.inductionOn with
  | _ x =>
    induction b using Quot.inductionOn with
    | _ y =>
      intro h
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have hxy := d.left_injective h
          subst y
          rfl
        | inr y => exact Quot.sound ((d.overlap x y).mp h)
      | inr x =>
        cases y with
        | inl y => exact (Quot.sound ((d.overlap y x).mp h.symm)).symm
        | inr y =>
          have hxy := d.right_injective h
          subst y
          rfl

/-- The covering condition makes the quotient map of a two-disk decomposition surjective. -/
theorem TwoDiskDecomposition.quotientMap_surjective {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : TwoDiskDecomposition n M) : Function.Surjective d.quotientMap := by
  intro p
  rcases d.covers p with ⟨x, hx⟩ | ⟨y, hy⟩
  · exact ⟨Quot.mk _ (.inl x), hx⟩
  · exact ⟨Quot.mk _ (.inr y), hy⟩

/-- A two-disk decomposition of a Hausdorff space identifies that space homeomorphically with its disk double. -/
def TwoDiskDecomposition.quotientHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : TwoDiskDecomposition n M) [T2Space M] :
    DiskDouble.Space d.boundaryEquiv ≃ₜ M :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective d.quotientMap ⟨d.quotientMap_injective, d.quotientMap_surjective⟩)
    d.continuous_quotientMap

/-- A Hausdorff space with a two-disk decomposition is homeomorphic to the corresponding sphere. -/
def TwoDiskDecomposition.homeomorphSphere {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : TwoDiskDecomposition n M) [T2Space M] : M ≃ₜ Hemisphere.Sphere n :=
  d.quotientHomeomorph.symm.trans (DiskDouble.twistedHomeomorphSphere n d.boundaryEquiv)

/-! ### Boundary-controlled sublevel disks -/

/-- A disk presentation of a closed sublevel set whose boundary sphere corresponds exactly to the boundary level. -/
structure SublevelDisk (n : ℕ) {M : Type*} [TopologicalSpace M] (f : M → ℝ) (a : ℝ) where
  homeomorph : Hemisphere.Ball n ≃ₜ { x : M // f x ≤ a }
  boundary_iff : ∀ v, f (homeomorph v).1 = a ↔ ‖(v : Hemisphere.Ambient n)‖ = 1

/-- The continuous map from the model disk into the ambient space underlying a sublevel-disk presentation. -/
def SublevelDisk.map {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : SublevelDisk n f a) : C(Hemisphere.Ball n, M)
    where
  toFun v := (d.homeomorph v).1
  continuous_toFun := continuous_subtype_val.comp d.homeomorph.continuous

/-- The ambient map of a sublevel-disk presentation is injective. -/
theorem SublevelDisk.map_injective {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} (d : SublevelDisk n f a) : Function.Injective d.map := by
  intro v w h
  exact d.homeomorph.injective (Subtype.ext h)

/-- Restrict a sublevel-disk presentation to a continuous map from its boundary sphere to the boundary level set. -/
def SublevelDisk.boundaryMap {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : SublevelDisk n f a) :
    C(DiskDouble.Boundary (Hemisphere.Ambient n), { x : M // f x = a })
    where
  toFun
    z :=
    ⟨d.map (DiskDouble.boundary _ z),
      (d.boundary_iff _).mpr
        (by simpa only [DiskDouble.boundary, mem_sphere_zero_iff_norm] using z.2)⟩
  continuous_toFun :=
    (d.map.continuous.comp
          (continuous_subtype_val.subtype_mk
            (fun z => Metric.sphere_subset_closedBall z.2))).subtype_mk
      _

/-- The boundary map of a sublevel-disk presentation is injective. -/
theorem SublevelDisk.boundaryMap_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a : ℝ} (d : SublevelDisk n f a) : Function.Injective d.boundaryMap := by
  intro z w h
  have heq : d.map (DiskDouble.boundary _ z) = d.map (DiskDouble.boundary _ w) :=
    congrArg (fun y : { x : M // f x = a } => y.1) h
  have h' := d.map_injective heq
  apply Subtype.ext
  exact congrArg (fun v : Hemisphere.Ball n => (v : Hemisphere.Ambient n)) h'

/-- Every point of the boundary level is represented by the boundary sphere of the sublevel disk. -/
theorem SublevelDisk.boundaryMap_surjective {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a : ℝ} (d : SublevelDisk n f a) : Function.Surjective d.boundaryMap := by
  intro y
  let v := d.homeomorph.symm ⟨y.1, y.2.le⟩
  have hv : (d.homeomorph v).1 = y.1 :=
    congrArg Subtype.val (d.homeomorph.apply_symm_apply ⟨y.1, y.2.le⟩)
  have hnorm : ‖(v : Hemisphere.Ambient n)‖ = 1 :=
    (d.boundary_iff v).mp (by rw [hv]; exact y.2)
  let z : DiskDouble.Boundary (Hemisphere.Ambient n) :=
    ⟨v.1, mem_sphere_zero_iff_norm.mpr hnorm⟩
  refine ⟨z, Subtype.ext ?_⟩
  exact hv

/-- In a Hausdorff ambient space, the boundary sphere of a sublevel disk is homeomorphic to its boundary level set. -/
def SublevelDisk.boundaryHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} (d : SublevelDisk n f a) [T2Space M] :
    DiskDouble.Boundary (Hemisphere.Ambient n) ≃ₜ { x : M // f x = a } :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective d.boundaryMap ⟨d.boundaryMap_injective, d.boundaryMap_surjective⟩)
    d.boundaryMap.continuous

/-! ### Extending a minimum disk through regular bands -/

attribute [local instance 100] Classical.propDecidable in
/-- A unique Morse minimum on a compact Hausdorff space has a disk sublevel at some level below any prescribed higher bound. -/
theorem ManifoldMorse.SignedMorseChart.exists_minimumSublevelDisk {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b) :
    ∃ a ∈ Set.Ioo (f p) b, Nonempty (SublevelDisk (Module.finrank ℝ E) f a) := by
  have hglobal : ∀ x, f p ≤ f x := by
    intro x
    by_contra! h
    have hxp := hunique x h.le
    rw [hxp] at h
    exact lt_irrefl _ h
  have hmin : IsLocalMin f p := Filter.Eventually.of_forall hglobal
  obtain ⟨ρ, hρ, hab, e, he⟩ := exists_minimum_disk_sublevel_with_height c hf hunique hb
  let d := (c.minimumDiskHomeomorph hmin).symm.trans e
  have hd (v : Hemisphere.Ball (Module.finrank ℝ E)) :
    f (d v).1 = f p + ρ ^ 2 * ‖(v : Hemisphere.Ambient (Module.finrank ℝ E))‖ ^ 2 := by
    change f (e ((c.minimumDiskHomeomorph hmin).symm v)).1 = _
    rw [he, c.norm_minimumDiskHomeomorph_symm]
  refine ⟨f p + ρ ^ 2, ⟨by linarith [sq_pos_of_pos hρ], hab⟩, ⟨⟨d, ?_⟩⟩⟩
  intro v
  rw [hd]
  constructor
  · intro h
    have hs : ‖(v : Hemisphere.Ambient (Module.finrank ℝ E))‖ ^ 2 = 1 :=
      mul_left_cancel₀ (pow_ne_zero 2 hρ.ne') (by linarith)
    nlinarith [norm_nonneg (v : Hemisphere.Ambient (Module.finrank ℝ E))]
  · intro h
    rw [h, one_pow, mul_one]

/-- On a compact smooth manifold, a common regular band gives a homeomorphism between two sublevels that identifies their boundary levels. -/
theorem FlowConstruction.exists_regularSublevelHomeomorph_with_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c a b : ℝ} (hca : c < a) (hcb : c < b)
    (hband : ∀ x, f x ∈ Set.Icc c (Max.max a b) → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ e : { x : M // f x ≤ a } ≃ₜ { x : M // f x ≤ b }, ∀ x, f (e x).1 = b ↔ f x.1 = a := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  refine
    ⟨regularSublevelHomeomorphOfFlow F hF hf.continuous hca hcb (le_max_left a b)
        (le_max_right a b),
      ?_⟩
  exact
    regularSublevelHomeomorphOfFlow_level_iff F hF hf.continuous hca hcb (le_max_left a b)
      (le_max_right a b)

/-- Transport a disk presentation along a sublevel homeomorphism that matches the boundary levels. -/
def SublevelDisk.transport {M : Type*} [TopologicalSpace M] {n : ℕ} {f : M → ℝ} {a b : ℝ}
    (d : SublevelDisk n f a) (e : { x : M // f x ≤ a } ≃ₜ { x : M // f x ≤ b })
    (he : ∀ x, f (e x).1 = b ↔ f x.1 = a) : SublevelDisk n f b
    where
  homeomorph := d.homeomorph.trans e
  boundary_iff v := (he (d.homeomorph v)).trans (d.boundary_iff v)

/-- A disk presentation of one sublevel transports to another across the specified regular band on a compact smooth manifold. -/
theorem FlowConstruction.nonempty_regularSublevelDisk {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {n : ℕ} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c a b : ℝ} (hca : c < a) (hcb : c < b)
    (hband : ∀ x, f x ∈ Set.Icc c (Max.max a b) → x ∉ ManifoldMorse.criticalPoints E f)
    (d : SublevelDisk n f a) : Nonempty (SublevelDisk n f b) := by
  obtain ⟨e, he⟩ := exists_regularSublevelHomeomorph_with_level hf hca hcb hband
  exact ⟨d.transport e he⟩

/-- The sublevel above a unique Morse minimum remains a disk as long as no further critical point is encountered. -/
theorem ManifoldMorse.SignedMorseChart.nonempty_sublevelDisk_before_next_critical
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} {p : M} (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b)
    (hregular : ∀ x, f p < f x → f x ≤ b → x ∉ ManifoldMorse.criticalPoints E f) :
    Nonempty (SublevelDisk (Module.finrank ℝ E) f b) := by
  obtain ⟨a, ha, ⟨d⟩⟩ := c.exists_minimumSublevelDisk hf.continuous hunique hb
  obtain ⟨l, hpl, hla⟩ := exists_between ha.1
  apply FlowConstruction.nonempty_regularSublevelDisk hf hla (hla.trans ha.2) _ d
  intro x hx
  apply hregular x (hpl.trans_le hx.1)
  exact hx.2.trans (max_le ha.2.le le_rfl)

/-! ### Assembling the two-critical-point sphere -/

/-- Identify the level `-f = -a` with the level `f = a` by retaining the underlying point. -/
def negLevelHomeomorph {M : Type*} [TopologicalSpace M] (f : M → ℝ) (a : ℝ) :
    { x : M // -f x = -a } ≃ₜ { x : M // f x = a }
    where
  toFun x := ⟨x.1, neg_inj.mp x.2⟩
  invFun x := ⟨x.1, congrArg Neg.neg x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- Disk presentations of the lower and upper sublevels at a common level assemble into a two-disk decomposition of a Hausdorff space. -/
def twoDiskDecompositionOfSublevels {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ}
    {f : M → ℝ} {a : ℝ} (L : SublevelDisk n f a) (R : SublevelDisk n (fun x => -f x) (-a)) :
    TwoDiskDecomposition n M := by
  let B := L.boundaryHomeomorph
  let C := R.boundaryHomeomorph.trans (negLevelHomeomorph f a)
  let e := B.trans C.symm
  refine
    { boundaryEquiv := e
      left := L.map
      right := R.map
      left_injective := L.map_injective
      right_injective := R.map_injective
      covers := ?_
      overlap := ?_ }
  · intro y
    by_cases hy : f y ≤ a
    · left
      exact
        ⟨L.homeomorph.symm ⟨y, hy⟩, congrArg Subtype.val (L.homeomorph.apply_symm_apply ⟨y, hy⟩)⟩
    · right
      have hy' : -f y ≤ -a := neg_le_neg (le_of_not_ge hy)
      exact
        ⟨R.homeomorph.symm ⟨y, hy'⟩,
          congrArg Subtype.val (R.homeomorph.apply_symm_apply ⟨y, hy'⟩)⟩
  · intro x y
    constructor
    · intro h
      have hL : f (L.map x) ≤ a := (L.homeomorph x).2
      have hR : -f (R.map y) ≤ -a := (R.homeomorph y).2
      have hxlevel : f (L.map x) = a := by rw [← h] at hR; linarith
      have hylevel : -f (R.map y) = -a := by rw [← h, hxlevel]
      have hxnorm := (L.boundary_iff x).mp hxlevel
      have hynorm := (R.boundary_iff y).mp hylevel
      let z : DiskDouble.Boundary (Hemisphere.Ambient n) :=
        ⟨x.1, mem_sphere_zero_iff_norm.mpr hxnorm⟩
      let w : DiskDouble.Boundary (Hemisphere.Ambient n) :=
        ⟨y.1, mem_sphere_zero_iff_norm.mpr hynorm⟩
      have hbc : B z = C w := Subtype.ext h
      have hew : e z = w := by
        apply C.injective
        change C (C.symm (B z)) = C w
        rw [C.apply_symm_apply]
        exact hbc
      refine ⟨z, rfl, ?_⟩
      rw [hew]
      rfl
    · rintro ⟨z, rfl, rfl⟩
      have heq := congrArg Subtype.val (C.apply_symm_apply (B z))
      exact heq.symm

/-- Matching lower and upper disk sublevels identify a Hausdorff space with a sphere. -/
def homeomorphSphereOfSublevelDisks {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ}
    {f : M → ℝ} {a : ℝ} (L : SublevelDisk n f a) (R : SublevelDisk n (fun x => -f x) (-a)) :
    M ≃ₜ Hemisphere.Sphere n :=
  (twoDiskDecompositionOfSublevels L R).homeomorphSphere

/-- Reeb's theorem: a compact finite-dimensional smooth manifold with a Morse function having exactly two critical points of distinct values is homeomorphic to the sphere of its dimension. -/
theorem ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p q : M} (hpq : f p < f q)
    (hcrit : criticalPoints E f = { p, q }) :
    Nonempty (M ≃ₜ Hemisphere.Sphere (Module.finrank ℝ E)) := by
  have hcover : ∀ x ∈ criticalPoints E f, x = p ∨ x = q := by
    intro x hx
    rw [hcrit] at hx
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  have hp : p ∈ criticalPoints E f := by rw [hcrit]; simp
  have hq : q ∈ criticalPoints E f := by rw [hcrit]; simp
  obtain ⟨hmin, hmax⟩ := unique_extrema_of_two_critical_values hf hpq hcover
  obtain ⟨cp⟩ := nonempty_signedMorseChart hf hm p hp
  obtain ⟨cq⟩ := nonempty_signedMorseChart hf hm q hq
  let a := (f p + f q) / 2
  have hpa : f p < a := by dsimp [a]; linarith
  have haq : a < f q := by dsimp [a]; linarith
  have hregularL : ∀ x, f p < f x → f x ≤ a → x ∉ criticalPoints E f := by
    intro x hxlo hxhi hxcrit
    rcases hcover x hxcrit with h | h
    · rw [h] at hxlo
      exact lt_irrefl _ hxlo
    · rw [h] at hxhi
      exact not_le_of_gt haq hxhi
  obtain ⟨L⟩ := cp.nonempty_sublevelDisk_before_next_critical hf hmin hpa hregularL
  have hminNeg : ∀ x, -f x ≤ -f q → x = q := fun x hx => hmax x (neg_le_neg_iff.mp hx)
  have hregularR : ∀ x, -f q < -f x → -f x ≤ -a → x ∉ criticalPoints E (fun y => -f y) := by
    intro x hxlo hxhi hxcrit
    have hxcrit' : x ∈ criticalPoints E f := by
      rw [← criticalPoints_neg (E := E) f]
      exact hxcrit
    rcases hcover x hxcrit' with h | h
    · rw [h] at hxhi
      linarith
    · rw [h] at hxlo
      exact lt_irrefl _ hxlo
  obtain ⟨R⟩ :=
    cq.neg.nonempty_sublevelDisk_before_next_critical hf.neg hminNeg (neg_lt_neg haq) hregularR
  exact ⟨homeomorphSphereOfSublevelDisks L R⟩

