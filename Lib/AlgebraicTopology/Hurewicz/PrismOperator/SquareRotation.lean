/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
/-!
# Rotating a based square by a quarter turn

The quarter-turn rotation `quarterTurn : I² → I²`, `u ↦ (u 1, 1 - u 0)`, is isotopic to the
identity through boundary-preserving maps: centering the square, blending the identity linearly
with the rotation by `90°` and renormalizing radially (`quarterTurnHomotopyMap`) gives a
homotopy that preserves the boundary of the square.  Hence for every based square
`p : GenLoop (Fin 2) X x`, the rotated square `rotatedSquareLoop p = p ∘ quarterTurn`
represents the same element of `π_2` (`rotatedSquareLoop_class`).  This is the elementary fact
that a rotation of `S²` fixing the basepoint acts trivially on `π_2` (cf. Hatcher, §4.1).

## Main definitions

* `Hurewicz.DegreeTwo.SimplyConnected.quarterTurn`, `quarterTurnHomotopyMap`.
* `Hurewicz.DegreeTwo.SimplyConnected.rotatedSquareLoop`, `rotatedSquareLoop_homotopy`,
  `rotatedSquareLoop_class`.
-/

open Set Function Topology

noncomputable section

/-! ### The quarter-turn rotation of the square -/

/-- The quarter-turn rotation of the square `I × I` about its center. -/
def Hurewicz.DegreeTwo.SimplyConnected.quarterTurn : C(Fin 2 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u 1, (unitInterval.symm) (u 0)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

/-- `quarterTurn u = ![u 1, 1 - u 0]`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.quarterTurn_apply (u : Fin 2 → (unitInterval)) :
    quarterTurn u = ![u 1, (unitInterval.symm) (u 0)] :=
  rfl

/-- `quarterTurn` preserves the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.quarterTurn_boundary (u : Fin 2 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 2)) : quarterTurn u ∈ Cube.boundary (Fin 2) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact ⟨1, Or.inr (by simp [hi])⟩
    · exact ⟨0, Or.inl (by simpa using hi)⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact ⟨1, Or.inl (by simp [hi])⟩
    · exact ⟨0, Or.inr (by simpa using hi)⟩

/-- The based square loop `p ∘ quarterTurn`. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotatedSquareLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp quarterTurn, fun u hu => p.property _ (quarterTurn_boundary u hu)⟩

/-- The rotation vector field on the square used for the rotation homotopy. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationVector (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, -v.1)

/-- The norm of the rotation vector. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationVector_norm (v : ℝ × ℝ) :
    ‖rotationVector v‖ = ‖v‖ := by simp [rotationVector, Prod.norm_def, max_comm]

/-- The affine blend `((1 - t) * v.1 + t * v.2, (1 - t) * v.2 - t * v.1)` interpolating `v` toward `rotationVector v`. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationBlend (t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - t) * v.1 + t * v.2, (1 - t) * v.2 - t * v.1)

/-- At `t = 0` the rotation blend is the identity. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationBlend_zero (v : ℝ × ℝ) : rotationBlend 0 v = v := by
  ext <;> simp [rotationBlend]

/-- At `t = 1` the rotation blend reaches `rotationVector v`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationBlend_one (v : ℝ × ℝ) :
    rotationBlend 1 v = rotationVector v := by ext <;> simp [rotationBlend, rotationVector]

/-- For every `t`, `rotationBlend t 0 = 0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationBlend_zero_vector (t : ℝ) :
    rotationBlend t 0 = 0 := by ext <;> simp [rotationBlend]

/-- The rotation blend is nonzero off the center. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationBlend_ne_zero (t : ℝ) {v : ℝ × ℝ} (hv : v ≠ 0) :
    rotationBlend t v ≠ 0 := by
  intro h
  have h₁ : (1 - t) * v.1 + t * v.2 = 0 := congrArg Prod.fst h
  have h₂ : (1 - t) * v.2 - t * v.1 = 0 := congrArg Prod.snd h
  have hd : (1 - t) ^ 2 + t ^ 2 ≠ 0 := by
    have hp : 0 < (1 - t) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
    exact ne_of_gt hp
  have ha : ((1 - t) ^ 2 + t ^ 2) * v.1 = 0 := by linear_combination (1 - t) * h₁ - t * h₂
  have hb : ((1 - t) ^ 2 + t ^ 2) * v.2 = 0 := by linear_combination t * h₁ + (1 - t) * h₂
  apply hv
  exact Prod.ext (mul_eq_zero.mp ha |>.resolve_left hd) (mul_eq_zero.mp hb |>.resolve_left hd)

/-- The rotation blend is continuous. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationBlend_continuous :
    Continuous (fun z : ℝ × (ℝ × ℝ) => rotationBlend z.1 z.2) := by
  unfold rotationBlend
  fun_prop

/-- The centered square coordinates `(2 * u 0 - 1, 2 * u 1 - 1)`. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationCentered (u : Fin 2 → (unitInterval)) : ℝ × ℝ :=
  (2 * (u 0 : ℝ) - 1, 2 * (u 1 : ℝ) - 1)

/-- The centering map is continuous. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationCentered_continuous :
    Continuous rotationCentered := by
  unfold rotationCentered
  fun_prop

/-- The centered coordinates have norm at most `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationCentered_norm_le (u : Fin 2 → (unitInterval)) :
    ‖rotationCentered u‖ ≤ 1 := by
  rw [norm_prod_le_iff]
  constructor <;> rw [Real.norm_eq_abs, abs_le]
  · constructor <;> dsimp [rotationCentered] <;> linarith [(u 0).property.1, (u 0).property.2]
  · constructor <;> dsimp [rotationCentered] <;> linarith [(u 1).property.1, (u 1).property.2]

/-- On the square boundary, the centered coordinates have norm `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationCentered_norm_boundary (u : Fin 2 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 2)) : ‖rotationCentered u‖ = 1 := by
  apply le_antisymm (rotationCentered_norm_le u)
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      have hc : ‖(rotationCentered u).1‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_fst_le (rotationCentered u)
    · change u 1 = 0 at hi
      have hc : ‖(rotationCentered u).2‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_snd_le (rotationCentered u)
  · fin_cases i
    · change u 0 = 1 at hi
      have hc : ‖(rotationCentered u).1‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_fst_le (rotationCentered u)
    · change u 1 = 1 at hi
      have hc : ‖(rotationCentered u).2‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_snd_le (rotationCentered u)

/-- The normalizing denominator for radial projection to the boundary. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationDenominator (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ℝ :=
  1 - ‖rotationCentered u‖ + ‖rotationBlend t (rotationCentered u)‖

/-- The rotation denominator is positive. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationDenominator_pos (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : 0 < rotationDenominator t u := by
  by_cases hv : rotationCentered u = 0
  · simp [rotationDenominator, hv]
  · have hnorm : 0 < ‖rotationBlend t (rotationCentered u)‖ :=
      norm_pos_iff.mpr (rotationBlend_ne_zero t hv)
    have hle := rotationCentered_norm_le u
    unfold rotationDenominator
    linarith

/-- The rotation denominator is continuous. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationDenominator_continuous :
    Continuous
      (fun z : (unitInterval) × (Fin 2 → (unitInterval)) => rotationDenominator z.1 z.2) := by
  unfold rotationDenominator
  apply Continuous.add
  · exact continuous_const.sub (rotationCentered_continuous.comp continuous_snd).norm
  · apply Continuous.norm
    exact
      rotationBlend_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (rotationCentered_continuous.comp continuous_snd))

/-- The radial normalization of centered square coordinates to the boundary. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ℝ × ℝ :=
  (rotationDenominator t u)⁻¹ • rotationBlend t (rotationCentered u)

/-- The radial normalization is continuous. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized_continuous :
    Continuous
      (fun z : (unitInterval) × (Fin 2 → (unitInterval)) => rotationNormalized z.1 z.2) := by
  unfold rotationNormalized
  apply
    Continuous.smul (f := fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
      (rotationDenominator z.1 z.2)⁻¹) (g := fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
      rotationBlend z.1 (rotationCentered z.2))
  · exact
      rotationDenominator_continuous.inv₀ (fun z => ne_of_gt (rotationDenominator_pos z.1 z.2))
  · exact
      rotationBlend_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (rotationCentered_continuous.comp continuous_snd))

/-- The normalized coordinates stay within the boundary norm. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized_norm_le (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ‖rotationNormalized t u‖ ≤ 1 := by
  have hd := rotationDenominator_pos t u
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [inv_mul_le_iff₀ hd, mul_one]
  unfold rotationDenominator
  linarith [rotationCentered_norm_le u]

/-- On the boundary the normalization is the identity. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized_norm_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    ‖rotationNormalized t u‖ = 1 := by
  have hd := rotationDenominator_pos t u
  have he : rotationDenominator t u = ‖rotationBlend t (rotationCentered u)‖ := by
    simp [rotationDenominator, rotationCentered_norm_boundary u hu]
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [← he, inv_mul_cancel₀ (ne_of_gt hd)]

/-- At `t = 0` the normalization is the identity. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized_zero (u : Fin 2 → (unitInterval)) :
    rotationNormalized 0 u = rotationCentered u := by
  simp [rotationNormalized, rotationDenominator]

/-- At `t = 1` the normalization reaches the quarter-turned boundary point. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized_one (u : Fin 2 → (unitInterval)) :
    rotationNormalized 1 u = rotationVector (rotationCentered u) := by
  simp [rotationNormalized, rotationDenominator]

/-- The uncentering map (adding the center back). -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationUncenter (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) :
    Fin 2 → (unitInterval) :=
  ![⟨(v.1 + 1) / 2,
      by
      have h := abs_le.mp (show |v.1| ≤ 1 from (norm_fst_le v).trans hv)
      constructor <;> linarith⟩,
    ⟨(v.2 + 1) / 2,
      by
      have h := abs_le.mp (show |v.2| ≤ 1 from (norm_snd_le v).trans hv)
      constructor <;> linarith⟩]

/-- `rotationUncenter` respects equality. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationUncenter_congr {v w : ℝ × ℝ} {hv : ‖v‖ ≤ 1}
    {hw : ‖w‖ ≤ 1} (h : v = w) : rotationUncenter v hv = rotationUncenter w hw := by
  subst w
  rfl

/-- `rotationUncenter` of centered coordinates recovers the point. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationUncenter_centered (u : Fin 2 → (unitInterval)) :
    rotationUncenter (rotationCentered u) (rotationCentered_norm_le u) = u := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> dsimp [rotationUncenter, rotationCentered] <;> ring

/-- `rotationUncenter` applied to the rotated vector. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationUncenter_vector (u : Fin 2 → (unitInterval)) :
    rotationUncenter (rotationVector (rotationCentered u))
        (by simpa using rotationCentered_norm_le u) =
      quarterTurn u := by
  rw [quarterTurn_apply]
  funext i
  fin_cases i <;> apply Subtype.ext <;>
      dsimp [rotationUncenter, rotationVector, rotationCentered, unitInterval.symm] <;>
    ring

/-- `rotationUncenter` preserves the boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationUncenter_boundary (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1)
    (he : ‖v‖ = 1) : rotationUncenter v hv ∈ Cube.boundary (Fin 2) := by
  have hm : 1 ≤ Max.max |v.1| |v.2| := by simpa [Prod.norm_def, Real.norm_eq_abs] using he.ge
  rcases le_max_iff.mp hm with ha | hb
  · have hn : |v.1| = 1 := le_antisymm ((norm_fst_le v).trans hv) ha
    by_cases hp : 0 ≤ v.1
    · have h : v.1 = 1 := by simpa [abs_of_nonneg hp] using hn
      refine ⟨0, Or.inr ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
    · have h : v.1 = -1 := by
        rw [abs_of_neg (lt_of_not_ge hp)] at hn
        linarith
      refine ⟨0, Or.inl ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
  · have hn : |v.2| = 1 := le_antisymm ((norm_snd_le v).trans hv) hb
    by_cases hp : 0 ≤ v.2
    · have h : v.2 = 1 := by simpa [abs_of_nonneg hp] using hn
      refine ⟨1, Or.inr ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
    · have h : v.2 = -1 := by
        rw [abs_of_neg (lt_of_not_ge hp)] at hn
        linarith
      refine ⟨1, Or.inl ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith

/-- The homotopy map rotating the square by a quarter turn. -/
def Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap :
    C((unitInterval) × (Fin 2 → (unitInterval)), Fin 2 → (unitInterval))
    where
  toFun z := rotationUncenter (rotationNormalized z.1 z.2) (rotationNormalized_norm_le z.1 z.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · apply Continuous.subtype_mk
      change
        Continuous
          (fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
            ((rotationNormalized z.1 z.2).1 + 1) / 2)
      exact (rotationNormalized_continuous.fst.add continuous_const).div_const 2
    · apply Continuous.subtype_mk
      change
        Continuous
          (fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
            ((rotationNormalized z.1 z.2).2 + 1) / 2)
      exact (rotationNormalized_continuous.snd.add continuous_const).div_const 2

/-- At time `0` the quarter-turn homotopy is the identity. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap_zero (u : Fin 2 → (unitInterval)) :
    quarterTurnHomotopyMap (0, u) = u := by
  exact
    (rotationUncenter_congr (hv := rotationNormalized_norm_le 0 u)
          (rotationNormalized_zero u)).trans
      (rotationUncenter_centered u)

/-- At time `1` the quarter-turn homotopy is the quarter turn. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap_one (u : Fin 2 → (unitInterval)) :
    quarterTurnHomotopyMap (1, u) = quarterTurn u := by
  exact
    (rotationUncenter_congr (hv := rotationNormalized_norm_le 1 u)
          (rotationNormalized_one u)).trans
      (rotationUncenter_vector u)

/-- The quarter-turn homotopy preserves the boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    quarterTurnHomotopyMap (t, u) ∈ Cube.boundary (Fin 2) :=
  rotationUncenter_boundary (rotationNormalized t u) (rotationNormalized_norm_le t u)
    (rotationNormalized_norm_boundary t u hu)

/-- The homotopy from a based square to its quarter-turned rotation. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotatedSquareLoop_homotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel (rotatedSquareLoop p).val (Cube.boundary (Fin 2))
    where
  toFun z := p (quarterTurnHomotopyMap z)
  continuous_toFun := p.val.continuous.comp quarterTurnHomotopyMap.continuous
  map_zero_left u := congrArg p (quarterTurnHomotopyMap_zero u)
  map_one_left u := congrArg p (quarterTurnHomotopyMap_one u)
  prop' t u
    hu := (p.property _ (quarterTurnHomotopyMap_boundary t u hu)).trans (p.property u hu).symm

/-- The rotated square loop has the same `π_2`-class: `⟦rotatedSquareLoop p⟧ = ⟦p⟧`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotatedSquareLoop_class {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) : (⟦rotatedSquareLoop p⟧ : π_ 2 X x) = ⟦p⟧ := by
  have h : (⟦p⟧ : π_ 2 X x) = ⟦rotatedSquareLoop p⟧ :=
    Quotient.sound
      (show GenLoop.Homotopic p (rotatedSquareLoop p) from ⟨rotatedSquareLoop_homotopy p⟩)
  exact h.symm
