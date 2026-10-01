/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The cubic birth–death model

On `MorseCancellation.Model m = ℝ × (Fin m → ℝ)` the one-parameter family
`MorseCancellation.cubic σ t (x, y) = x³/3 + t x + ∑ i, σ i * y i ^ 2` is the standard model of the
birth or cancellation of a pair of nondegenerate critical points (cf. Milnor, *Lectures on the
h-cobordism theorem*, §5; the birth–death singularity).  For `σ i ≠ 0`:

* its derivative is `MorseCancellation.differential` (`hasFDerivAt_cubic`, `fderiv_cubic`), and a
  point is critical iff `x² + t = 0` and `y = 0` (`critical_iff`);
* for `t > 0` there is no critical point (`positive_parameter_no_critical`), for `t = 0` exactly
  the origin (`cubic_zero_unique_critical`), and for `t = -a²` exactly `(±a, 0)`
  (`negative_parameter_critical_iff`), with critical values `∓ 2a³/3` (`cubic_critical_values`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The model space `ℝ × (Fin m → ℝ)` of the cubic birth–death family: one axis coordinate and `m`
transverse coordinates. -/
abbrev MorseCancellation.Model (m : ℕ) :=
  ℝ × (Fin m → ℝ)

/-- The cubic family `cubic σ t (x, y) = x ^ 3 / 3 + t * x + ∑ i, σ i * y i ^ 2` on `Model m`. -/
def MorseCancellation.cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : ℝ :=
  p.1 ^ 3 / 3 + t * p.1 + ∑ i, σ i * (p.2 i) ^ 2

/-- The derivative of `cubic σ t` at `p = (x, y)` (see `hasFDerivAt_cubic`): the continuous linear
form `v ↦ (x ^ 2 + t) * v.1 + ∑ i, 2 * σ i * y i * v.2 i`. -/
def MorseCancellation.differential {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : Model m →L[ℝ] ℝ :=
  (p.1 ^ 2 + t) • ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) +
    ∑ i,
      (2 * σ i * p.2 i) •
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))

/-- `differential σ t p v = (p.1 ^ 2 + t) * v.1 + ∑ i, 2 * σ i * p.2 i * v.2 i`. -/
theorem MorseCancellation.differential_apply {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p v : Model m) :
    differential σ t p v = (p.1 ^ 2 + t) * v.1 + ∑ i, 2 * σ i * p.2 i * v.2 i := by
  simp [differential]

/-- The cubic family is smooth jointly in the parameter and the point: `(t, p) ↦ cubic σ t p` is
`C^∞`. -/
theorem MorseCancellation.contDiff_cubic_family {m : ℕ} (σ : Fin m → ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Model m => cubic σ p.1 p.2) := by
  unfold cubic
  fun_prop

/-- For fixed `σ` and `t` the function `cubic σ t` is `C^∞`. -/
theorem MorseCancellation.contDiff_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) : ContDiff ℝ ∞ (cubic σ t) :=
  (contDiff_cubic_family σ).comp (contDiff_const.prodMk contDiff_id)

/-- `cubic σ t` has Fréchet derivative `differential σ t p` at `p`. -/
theorem MorseCancellation.hasFDerivAt_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    HasFDerivAt (cubic σ t) (differential σ t p) p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  have hy (i : Fin m) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).hasFDerivAt
      (x := p)
  have hq := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ((hy i).pow 2).const_mul (σ i))
  convert! (((hx.pow 3).mul_const (1 / 3)).add (hx.const_mul t)).add hq using 1
  · funext q
    simp [cubic, div_eq_mul_inv]
  · apply ContinuousLinearMap.ext
    intro v
    simp [differential]
    ring_nf

/-- `fderiv ℝ (cubic σ t) p = differential σ t p`. -/
theorem MorseCancellation.fderiv_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    fderiv ℝ (cubic σ t) p = differential σ t p :=
  (hasFDerivAt_cubic σ t p).fderiv

/-- If all `σ i ≠ 0`, then `p` is a critical point of `cubic σ t` iff `p.1 ^ 2 + t = 0` and `p.2 =
0`. -/
theorem MorseCancellation.critical_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) (t : ℝ)
    (p : Model m) : fderiv ℝ (cubic σ t) p = 0 ↔ p.1 ^ 2 + t = 0 ∧ p.2 = 0 := by
  rw [fderiv_cubic]
  constructor
  · intro h
    have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) h
    have hx' : p.1 ^ 2 + t = 0 := by simpa [differential_apply] using hx
    refine ⟨hx', ?_⟩
    funext i
    have hy := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) h
    have hy' : 2 * σ i * p.2 i = 0 := by simpa [differential_apply, Pi.single_apply] using hy
    exact (mul_eq_zero.mp hy').resolve_left (mul_ne_zero (by norm_num) (hσ i))
  · rintro ⟨hx, hy⟩
    apply ContinuousLinearMap.ext
    intro v
    simp [differential_apply, hx, hy]

/-- If all `σ i ≠ 0`, then `p` is a critical point of `cubic σ 0` iff `p = 0`. -/
theorem MorseCancellation.cubic_zero_unique_critical {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (p : Model m) : fderiv ℝ (cubic σ 0) p = 0 ↔ p = 0 := by
  rw [critical_iff σ hσ]
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : p.1 = 0 := by nlinarith [sq_nonneg p.1]
    exact Prod.ext hx' hy
  · rintro rfl
    simp

/-- If all `σ i ≠ 0` and `0 < t`, then `cubic σ t` has no critical point. -/
theorem MorseCancellation.positive_parameter_no_critical {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {t : ℝ} (ht : 0 < t) (p : Model m) : fderiv ℝ (cubic σ t) p ≠ 0 := by
  intro h
  have hx := ((critical_iff σ hσ t p).mp h).1
  nlinarith [sq_nonneg p.1]

/-- If all `σ i ≠ 0`, the critical points of `cubic σ (-a ^ 2)` are exactly `(a, 0)` and `(-a, 0)`.
-/
theorem MorseCancellation.negative_parameter_critical_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (a : ℝ) (p : Model m) : fderiv ℝ (cubic σ (-(a ^ 2))) p = 0 ↔ p = (a, 0) ∨ p = (-a, 0) := by
  rw [critical_iff σ hσ]
  constructor
  · rintro ⟨hx, hy⟩
    have hs : p.1 = a ∨ p.1 = -a := by
      have he : (p.1 - a) * (p.1 + a) = 0 := by nlinarith
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    exact hs.elim (fun h => Or.inl (Prod.ext h hy)) (fun h => Or.inr (Prod.ext h hy))
  · rintro (rfl | rfl) <;> simp

/-- The values of `cubic σ (-a ^ 2)` at `(a, 0)` and `(-a, 0)` are `-(2 * a ^ 3 / 3)` and `2 * a ^ 3
/ 3`. -/
theorem MorseCancellation.cubic_critical_values {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) :
    cubic σ (-(a ^ 2)) (a, 0) = -(2 * a ^ 3 / 3) ∧ cubic σ (-(a ^ 2)) (-a, 0) = 2 * a ^ 3 / 3 := by
  constructor <;> simp [cubic] <;> ring
