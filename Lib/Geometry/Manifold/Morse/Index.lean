/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SublevelSets
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Flow.Compact
public import Lib.Geometry.Manifold.Flow.HeightTranslating
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
/-!
# The index of a nondegenerate critical point

  The index of a nondegenerate critical point: the number of negative eigenvalues
  of the Hessian. Local coordinates bring the function to the quadratic model
  `f = f(p) - x_1^2 - ... - x_i^2 + x_{i+1}^2 + ... ` (Milnor, Morse Theory,
  Lemma 2.2; the index is a local homotopy invariant).
-/



open Set Function Filter Manifold Topology

open scoped ContinuousMap

@[expose] public noncomputable section

/-! ### Stretching heights along a flow -/

/-- The piecewise-linear stretch of `ℝ` fixing `c` and scaling above it. -/
def FlowConstruction.stretchHeight (c k r : ℝ) : ℝ :=
  r + (k - 1) * Max.max 0 (r - c)

/-- Below `c` the stretch is the identity. -/
theorem FlowConstruction.stretchHeight_of_le {c k r : ℝ} (hr : r ≤ c) :
    stretchHeight c k r = r := by
  simp only [stretchHeight, max_eq_left (sub_nonpos.mpr hr), MulZeroClass.mul_zero, add_zero]

/-- Above `c` the stretch scales by `k`. -/
theorem FlowConstruction.stretchHeight_of_ge {c k r : ℝ} (hr : c ≤ r) :
    stretchHeight c k r = c + k * (r - c) := by
  rw [stretchHeight, max_eq_right (sub_nonneg.mpr hr)]
  ring

/-- Stretching by `k` then `k⁻¹` is the identity. -/
theorem FlowConstruction.stretchHeight_inverse {c k : ℝ} (hk : 0 < k) (r : ℝ) :
    stretchHeight c k⁻¹ (stretchHeight c k r) = r := by
  by_cases hr : r ≤ c
  · rw [stretchHeight_of_le hr, stretchHeight_of_le hr]
  · have hcr : c < r := lt_of_not_ge hr
    have hs : c ≤ stretchHeight c k r := by
      rw [stretchHeight_of_ge hcr.le]
      exact le_add_of_nonneg_right (mul_nonneg hk.le (sub_nonneg.mpr hcr.le))
    rw [stretchHeight_of_ge hs, stretchHeight_of_ge hcr.le]
    field_simp
    ring

/-- The height stretch is continuous. -/
theorem FlowConstruction.continuous_stretchHeight (c k : ℝ) :
    Continuous (stretchHeight c k) :=
  continuous_id.add
    (continuous_const.mul (continuous_const.max (continuous_id.sub continuous_const)))

/-- The height stretch is a homeomorphism for positive `k`. -/
def FlowConstruction.stretchHeightHomeomorph (c k : ℝ) (hk : 0 < k) : ℝ ≃ₜ ℝ
    where
  toFun := stretchHeight c k
  invFun := stretchHeight c k⁻¹
  left_inv := stretchHeight_inverse hk
  right_inv r := by simpa only [inv_inv] using stretchHeight_inverse (c := c) (inv_pos.mpr hk) r
  continuous_toFun := continuous_stretchHeight c k
  continuous_invFun := continuous_stretchHeight c k⁻¹

/-- The stretch sending level `a` to level `b`. -/
theorem FlowConstruction.stretchHeight_endpoint {c a b : ℝ} (hca : c < a) :
    stretchHeight c ((b - c) / (a - c)) a = b := by
  rw [stretchHeight_of_ge hca.le, div_mul_cancel₀ _ (sub_ne_zero.mpr hca.ne')]
  ring

/-- The stretch hits `b` exactly at `a`. -/
theorem FlowConstruction.stretchHeight_endpoint_iff {c a b r : ℝ} (hca : c < a)
    (hcb : c < b) : stretchHeight c ((b - c) / (a - c)) r = b ↔ r = a := by
  have hk : 0 < (b - c) / (a - c) := div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)
  constructor
  · intro h
    exact
      (stretchHeightHomeomorph c ((b - c) / (a - c)) hk).injective
        (h.trans (stretchHeight_endpoint hca).symm)
  · rintro rfl
    exact stretchHeight_endpoint hca

/-- Points at or below `a` stretch to at most `b`. -/
theorem FlowConstruction.stretchHeight_le_target {c a b r : ℝ} (hca : c < a) (hcb : c < b)
    (hr : r ≤ a) : stretchHeight c ((b - c) / (a - c)) r ≤ b := by
  by_cases hrc : r ≤ c
  · rw [stretchHeight_of_le hrc]
    exact hrc.trans hcb.le
  · have hcr : c ≤ r := le_of_not_ge hrc
    have hk : 0 ≤ (b - c) / (a - c) := (div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)).le
    rw [stretchHeight_of_ge hcr]
    calc
      _ ≤ c + ((b - c) / (a - c)) * (a - c) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right hr c) hk)
      _ = b := by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hca.ne')]; ring

/-- The flow rescaled by the height stretch. -/
def FlowConstruction.stretchFlow {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (f : X → ℝ)
    (c k : ℝ) (x : X) : X :=
  F (stretchHeight c k (f x) - f x) x

/-- The stretched flow is continuous. -/
theorem FlowConstruction.continuous_stretchFlow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (hf : Continuous f) (c k : ℝ) : Continuous (stretchFlow F f c k) :=
  F.continuous (((continuous_stretchHeight c k).comp hf).sub hf) continuous_id

/-- The stretched flow realizes the height stretch on `f`-levels. -/
theorem FlowConstruction.stretchFlow_height {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {f : X → ℝ} {c d a b : ℝ}
    (hF : ∀ x t, f x ∈ Set.Icc c d → f x + t ∈ Set.Icc c d → f (F t x) = f x + t) (hca : c < a)
    (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d) {x : X} (hx : f x ≤ a) :
    f (stretchFlow F f c ((b - c) / (a - c)) x) = stretchHeight c ((b - c) / (a - c)) (f x) := by
  by_cases hxc : f x ≤ c
  · simp only [stretchFlow, stretchHeight_of_le hxc, sub_self, F.map_zero_apply]
  · have hcx : c ≤ f x := le_of_not_ge hxc
    have hk : 0 < (b - c) / (a - c) := div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)
    have hslo : c ≤ stretchHeight c ((b - c) / (a - c)) (f x) := by
      rw [stretchHeight_of_ge hcx]
      exact le_add_of_nonneg_right (mul_nonneg hk.le (sub_nonneg.mpr hcx))
    have hshi := stretchHeight_le_target hca hcb hx
    have hsum :
      f x + (stretchHeight c ((b - c) / (a - c)) (f x) - f x) =
        stretchHeight c ((b - c) / (a - c)) (f x) := by ring
    have hh :=
      hF x (stretchHeight c ((b - c) / (a - c)) (f x) - f x) ⟨hcx, hx.trans ha⟩
        (by rw [hsum]; exact ⟨hslo, hshi.trans hb⟩)
    exact hh.trans hsum

/-- The stretched flow maps level `a` below level `b`. -/
theorem FlowConstruction.stretchFlow_le_target {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {c d a b : ℝ}
    (hF : ∀ x t, f x ∈ Set.Icc c d → f x + t ∈ Set.Icc c d → f (F t x) = f x + t) (hca : c < a)
    (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d) {x : X} (hx : f x ≤ a) :
    f (stretchFlow F f c ((b - c) / (a - c)) x) ≤ b := by
  rw [stretchFlow_height F hF hca hcb ha hb hx]
  exact stretchHeight_le_target hca hcb hx

/-- The stretched flows at inverse factors compose to the identity. -/
theorem FlowConstruction.stretchFlow_inverse {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {f : X → ℝ} {c d a b : ℝ}
    (hF : ∀ x t, f x ∈ Set.Icc c d → f x + t ∈ Set.Icc c d → f (F t x) = f x + t) (hca : c < a)
    (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d) {x : X} (hx : f x ≤ a) :
    stretchFlow F f c ((a - c) / (b - c)) (stretchFlow F f c ((b - c) / (a - c)) x) = x := by
  have hh := stretchFlow_height F hF hca hcb ha hb hx
  have hk : 0 < (b - c) / (a - c) := div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)
  have hi : (a - c) / (b - c) = ((b - c) / (a - c))⁻¹ := (inv_div _ _).symm
  change
    F
        (stretchHeight c ((a - c) / (b - c)) (f (stretchFlow F f c ((b - c) / (a - c)) x)) -
          f (stretchFlow F f c ((b - c) / (a - c)) x))
        (F (stretchHeight c ((b - c) / (a - c)) (f x) - f x) x) =
      x
  rw [hh, hi, stretchHeight_inverse hk, ← F.map_add]
  rw [show
      f x - stretchHeight c ((b - c) / (a - c)) (f x) +
          (stretchHeight c ((b - c) / (a - c)) (f x) - f x) =
        0
      by ring,
    F.map_zero_apply]

/-! ### Flow moves between regular sublevels -/

/-- Flow stretching gives a homeomorphism between regular sublevels. -/
def FlowConstruction.regularSublevelHomeomorphOfFlow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {c d a b : ℝ}
    (hF : ∀ x t, f x ∈ Set.Icc c d → f x + t ∈ Set.Icc c d → f (F t x) = f x + t)
    (hf : Continuous f) (hca : c < a) (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d) :
    { x : X // f x ≤ a } ≃ₜ { x : X // f x ≤ b }
    where
  toFun
    x := ⟨stretchFlow F f c ((b - c) / (a - c)) x.1, stretchFlow_le_target F hF hca hcb ha hb x.2⟩
  invFun
    x := ⟨stretchFlow F f c ((a - c) / (b - c)) x.1, stretchFlow_le_target F hF hcb hca hb ha x.2⟩
  left_inv x := Subtype.ext (stretchFlow_inverse F hF hca hcb ha hb x.2)
  right_inv x := Subtype.ext (stretchFlow_inverse F hF hcb hca hb ha x.2)
  continuous_toFun :=
    ((continuous_stretchFlow F f hf c _).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_stretchFlow F f hf c _).comp continuous_subtype_val).subtype_mk _

/-- The sublevel homeomorphism reaches level `b` exactly at level `a`. -/
theorem FlowConstruction.regularSublevelHomeomorphOfFlow_level_iff {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f : X → ℝ} {c d a b : ℝ}
    (hF : ∀ x t, f x ∈ Set.Icc c d → f x + t ∈ Set.Icc c d → f (F t x) = f x + t)
    (hf : Continuous f) (hca : c < a) (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d)
    (x : { x : X // f x ≤ a }) :
    f ((regularSublevelHomeomorphOfFlow F hF hf hca hcb ha hb) x).1 = b ↔ f x.1 = a := by
  change f (stretchFlow F f c ((b - c) / (a - c)) x.1) = b ↔ _
  rw [stretchFlow_height F hF hca hcb ha hb x.2]
  exact stretchHeight_endpoint_iff hca hcb

/-! ### Negating the Morse function -/

/-- Negating `f` does not change its critical points. -/
theorem ManifoldMorse.criticalPoints_neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) :
    criticalPoints E (fun x => -f x) = criticalPoints E f := by
  ext x
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (-f) x = 0 ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
  rw [mfderiv_neg]
  exact neg_eq_zero

/-- The signed Morse chart of `-f` obtained by flipping the positive part. -/
def ManifoldMorse.SignedMorseChart.neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) :
    ManifoldMorse.SignedMorseChart (E := E) (fun x => -f x) p
    where
  weights i := -c.weights i
  signs
    i := by
    rcases c.signs i with h | h
    · exact Or.inr (by rw [h]; ring)
    · exact Or.inl (by rw [h])
  chart := c.chart
  mem_source := c.mem_source
  center := c.center
  equation y
    hy := by
    rw [c.equation y hy]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_add]
  inverse_equation y
    hy := by
    rw [c.inverse_equation y hy]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_add]

/-! ### The sublevel deformation retraction -/

/-- The inclusion of a smaller sublevel into a larger one. -/
def FlowConstruction.sublevelInclusion {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a b : ℝ} (hab : a ≤ b) : C({ x : M // f x ≤ a }, { x : M // f x ≤ b })
    where
  toFun x := ⟨x.1, x.2.trans hab⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The flow deformation interpolates the height down to `a`. -/
theorem FlowConstruction.sublevel_deformation_height {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t) {x : M}
    (hx : f x ≤ b) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    f (F (u * Min.min 0 (a - f x)) x) = f x + u * Min.min 0 (a - f x) := by
  by_cases hxa : f x ≤ a
  · rw [min_eq_left (sub_nonneg.mpr hxa), MulZeroClass.mul_zero, F.map_zero_apply, add_zero]
  · have hax : a ≤ f x := (lt_of_not_ge hxa).le
    rw [min_eq_right (sub_nonpos.mpr hax)]
    apply hF x _ ⟨hax, hx⟩
    have htime : u * (a - f x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.1 (sub_nonpos.mpr hax)
    have hprod : 0 ≤ (1 - u) * (f x - a) := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hax)
    exact ⟨by nlinarith, by linarith⟩

/-- The deformation stays inside the larger sublevel. -/
theorem FlowConstruction.sublevel_deformation_mem {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t) {x : M}
    (hx : f x ≤ b) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : f (F (u * Min.min 0 (a - f x)) x) ≤ b :=
  by
  rw [sublevel_deformation_height F hF hx hu]
  exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hu.1 (min_le_left _ _))).trans hx

/-- The endpoint of the deformation lies in the smaller sublevel. -/
theorem FlowConstruction.sublevel_retraction_mem {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t) {x : M}
    (hx : f x ≤ b) : f (F (Min.min 0 (a - f x)) x) ≤ a := by
  have h :=
    sublevel_deformation_height F hF hx (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  simp only [one_mul] at h
  rw [h]
  have hm := min_le_right (0 : ℝ) (a - f x)
  linarith

/-- The flow retraction of the larger sublevel onto the smaller. -/
def FlowConstruction.sublevelRetraction {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t)
    (hf : Continuous f) : C({ x : M // f x ≤ b }, { x : M // f x ≤ a })
    where
  toFun x := ⟨F (Min.min 0 (a - f x.1)) x.1, sublevel_retraction_mem F hF x.2⟩
  continuous_toFun :=
    (F.continuous (continuous_const.min (continuous_const.sub (hf.comp continuous_subtype_val)))
          continuous_subtype_val).subtype_mk
      _

/-- The retraction fixes the smaller sublevel. -/
theorem FlowConstruction.sublevelRetraction_inclusion {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t)
    (hf : Continuous f) (hab : a ≤ b) (x : { x : M // f x ≤ a }) :
    sublevelRetraction F hF hf (sublevelInclusion hab x) = x := by
  apply Subtype.ext
  change F (Min.min 0 (a - f x.1)) x.1 = x.1
  rw [min_eq_left (sub_nonneg.mpr x.2), F.map_zero_apply]

/-- The retraction is homotopic to the identity rel the smaller sublevel. -/
def FlowConstruction.sublevelDeformation {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t)
    (hf : Continuous f) (hab : a ≤ b) :
    (ContinuousMap.id { x : M // f x ≤ b }).HomotopyRel
      ((sublevelInclusion hab).comp (sublevelRetraction F hF hf)) {x | f x.1 ≤ a}
    where
  toFun
    p := ⟨F (p.1.1 * Min.min 0 (a - f p.2.1)) p.2.1, sublevel_deformation_mem F hF p.2.2 p.1.2⟩
  continuous_toFun :=
    (F.continuous
          ((continuous_subtype_val.comp continuous_fst).mul
            (continuous_const.min
              (continuous_const.sub (hf.comp (continuous_subtype_val.comp continuous_snd)))))
          (continuous_subtype_val.comp continuous_snd)).subtype_mk
      _
  map_zero_left
    x := by
    apply Subtype.ext
    change F ((0 : ℝ) * Min.min 0 (a - f x.1)) x.1 = x.1
    rw [MulZeroClass.zero_mul, F.map_zero_apply]
  map_one_left
    x := by
    apply Subtype.ext
    change F ((1 : ℝ) * Min.min 0 (a - f x.1)) x.1 = F (Min.min 0 (a - f x.1)) x.1
    rw [one_mul]
  prop' u x
    hx := by
    apply Subtype.ext
    change F (u.1 * Min.min 0 (a - f x.1)) x.1 = x.1
    rw [min_eq_left (sub_nonneg.mpr hx), MulZeroClass.mul_zero, F.map_zero_apply]

/-- Regular sublevels across a flow band are homotopy equivalent. -/
def FlowConstruction.regularSublevelHomotopyEquivOfFlow {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t)
    (hf : Continuous f) (hab : a ≤ b) : { x : M // f x ≤ a } ≃ₕ { x : M // f x ≤ b }
    where
  toFun := sublevelInclusion hab
  invFun := sublevelRetraction F hF hf
  left_inv := by
    have heq :
      (sublevelRetraction F hF hf).comp (sublevelInclusion hab) =
        ContinuousMap.id { x : M // f x ≤ a } := by
      apply ContinuousMap.ext
      intro x
      exact sublevelRetraction_inclusion F hF hf hab x
    rw [heq]
  right_inv := ⟨(sublevelDeformation F hF hf hab).toHomotopy.symm⟩
