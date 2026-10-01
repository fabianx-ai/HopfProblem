/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.Morse.Cubic.Model
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Morse charts at the two critical points of the cubic model

At the critical point `(e a, 0)`, `e = ±1`, `a > 0`, of `cubic σ (-a²)` the substitution
`u = (s - e a) √(a + e (s - e a) / 3)` (`MorseCancellation.endpointCoordinate`, defined on
`endpointDomain a e`) turns the cubic into its Morse normal form
`cubic σ (-a²) (s, y) = (critical value) + e u² + ∑ i, σ i * y i ^ 2` (`cubic_endpoint_square`).
The substitution is a local diffeomorphism of `ℝ` near `e a` (`exists_endpoint_scalar_chart`),
and its product with the identity (`scalarProductChart`) is a Morse chart of the model at the
critical point (`exists_endpoint_product_chart`).  This is the explicit Morse lemma for
`x³/3 - a² x`, cf. Milnor, *Morse Theory*, Lemma 2.2.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The Morse coordinate `u = (s - e * a) * √(a + e * (s - e * a) / 3)` of the cubic `s ^ 3 / 3 - a
^ 2 * s` at its critical point `e * a`, `e = ±1` (see `cubic_endpoint_square`). -/
def MorseCancellation.endpointCoordinate (a e s : ℝ) : ℝ :=
  (s - e * a) * Real.sqrt (a + e * (s - e * a) / 3)

/-- The set `{s | 0 < a + e * (s - e * a) / 3}`, on which `endpointCoordinate a e` is smooth. -/
def MorseCancellation.endpointDomain (a e : ℝ) : Set ℝ :=
  {s | 0 < a + e * (s - e * a) / 3}

/-- `endpointDomain a e` is open. -/
theorem MorseCancellation.endpointDomain_open (a e : ℝ) : IsOpen (endpointDomain a e) := by
  apply isOpen_lt continuous_const
  fun_prop

/-- For `0 < a` the point `e * a` lies in `endpointDomain a e`. -/
theorem MorseCancellation.endpoint_mem_domain {a : ℝ} (ha : 0 < a) (e : ℝ) :
    e * a ∈ endpointDomain a e := by simpa [endpointDomain] using ha

/-- `endpointCoordinate a e (e * a) = 0`. -/
theorem MorseCancellation.endpointCoordinate_center (a e : ℝ) : endpointCoordinate a e (e * a) = 0 := by
  simp [endpointCoordinate]

/-- `endpointCoordinate a e` is `C^∞` on `endpointDomain a e`. -/
theorem MorseCancellation.contDiffOn_endpointCoordinate (a e : ℝ) :
    ContDiffOn ℝ ∞ (endpointCoordinate a e) (endpointDomain a e) := by
  intro s hs
  have hlin : ContDiffAt ℝ ∞ (fun t : ℝ => t - e * a) s := contDiffAt_id.sub contDiffAt_const
  exact
    (hlin.mul
        ((contDiffAt_const.add ((contDiffAt_const.mul hlin).div_const 3)).sqrt
          (ne_of_gt hs))).contDiffWithinAt

/-- For `0 < a`, `endpointCoordinate a e` has derivative `√a` at `e * a`. -/
theorem MorseCancellation.hasDerivAt_endpointCoordinate {a : ℝ} (ha : 0 < a) (e : ℝ) :
    HasDerivAt (endpointCoordinate a e) (Real.sqrt a) (e * a) := by
  have hd :=
    ((hasDerivAt_id (e * a)).sub_const (e * a)).mul
      ((((hasDerivAt_id (e * a)).sub_const (e * a)).const_mul e).div_const 3 |>.const_add
          a |>.sqrt
        (by simpa using ha.ne'))
  convert! hd using 1; simp []

/-- Morse normal form of the cubic model: if `e ^ 2 = 1` and `p.1 ∈ endpointDomain a e`, then `cubic
σ (-a ^ 2) p = cubic σ (-a ^ 2) (e * a, 0) + e * u ^ 2 + ∑ i, σ i * p.2 i ^ 2` with `u =
endpointCoordinate a e p.1`. -/
theorem MorseCancellation.cubic_endpoint_square {m : ℕ} (σ : Fin m → ℝ) (a e : ℝ) (he : e ^ 2 = 1)
    {p : Model m} (hp : p.1 ∈ endpointDomain a e) :
    cubic σ (-(a ^ 2)) p =
      cubic σ (-(a ^ 2)) (e * a, 0) + e * endpointCoordinate a e p.1 ^ 2 + ∑ i, σ i * p.2 i ^ 2 :=
  by
  simp only [cubic, endpointCoordinate, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    MulZeroClass.mul_zero, Finset.sum_const_zero, add_zero, mul_pow, Real.sq_sqrt (le_of_lt hp)]
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

/-- For `0 < a` there is a smooth partial diffeomorphism `Φ` of `ℝ` whose source contains `e * a`
and is contained in `endpointDomain a e`, whose underlying function is `endpointCoordinate a e`, and
with `Φ (e * a) = 0`. -/
theorem MorseCancellation.exists_endpoint_scalar_chart {a : ℝ} (ha : 0 < a) (e : ℝ) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      e * a ∈ Φ.source ∧
        Φ.source ⊆ endpointDomain a e ∧ (Φ : ℝ → ℝ) = endpointCoordinate a e ∧ Φ (e * a) = 0 := by
  have hd := (hasDerivAt_endpointCoordinate ha e).hasFDerivAt
  have hi : Function.Injective (fderiv ℝ (endpointCoordinate a e) (e * a)) := by
    rw [hd.fderiv]
    intro x y hxy
    change x * Real.sqrt a = y * Real.sqrt a at hxy
    exact mul_right_cancel₀ (Real.sqrt_pos.mpr ha).ne' hxy
  let A : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (endpointCoordinate a e) (e * a)).toLinearMap
        hi).toContinuousLinearEquiv
  obtain ⟨Φ, hp, hsub, hΦ⟩ :=
    exists_partialDiffeomorph_of_contDiffOn (endpointDomain_open a e)
      (endpoint_mem_domain ha e) (contDiffOn_endpointCoordinate a e) ⟨A, rfl⟩
  exact ⟨Φ, hp, hsub, hΦ, by rw [hΦ, endpointCoordinate_center]⟩

/-- The product of a smooth partial diffeomorphism `Φ` of `ℝ` with the identity of `V`: the partial
diffeomorphism `(s, y) ↦ (Φ s, y)` of `ℝ × V` with source `Φ.source ×ˢ univ`. -/
def MorseCancellation.scalarProductChart {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) (ℝ × V) (ℝ × V) ∞
    where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.prod (OpenPartialHomeomorph.refl V)).toPartialEquiv
  open_source := Φ.open_source.prod isOpen_univ
  open_target := Φ.open_target.prod isOpen_univ
  contMDiffOn_toFun := by
    have h : ContDiffOn ℝ ∞ (fun p : ℝ × V => (Φ p.1, p.2)) (Φ.source ×ˢ Set.univ) :=
      (Φ.contMDiffOn_toFun.contDiffOn.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)).prodMk
        contDiff_snd.contDiffOn
    exact h.contMDiffOn
  contMDiffOn_invFun := by
    have h : ContDiffOn ℝ ∞ (fun p : ℝ × V => (Φ.symm p.1, p.2)) (Φ.target ×ˢ Set.univ) :=
      (Φ.contMDiffOn_invFun.contDiffOn.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)).prodMk
        contDiff_snd.contDiffOn
    exact h.contMDiffOn

/-- For `0 < a` and `e ^ 2 = 1` there is a smooth partial diffeomorphism `P` of `Model m` with `(e *
a, 0) ∈ P.source`, `P (e * a, 0) = 0`, preserving the transverse coordinates, such that for `p ∈
P.source`: `cubic σ (-a ^ 2) p = cubic σ (-a ^ 2) (e * a, 0) + e * (P p).1 ^ 2 + ∑ i, σ i * (P p).2
i ^ 2`. -/
theorem MorseCancellation.exists_endpoint_product_chart {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (e : ℝ) (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) (Model m) (Model m) ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧
        P (e * a, 0) = 0 ∧
          (∀ p, (P p).2 = p.2) ∧
            (∀ p ∈ P.source,
              cubic σ (-(a ^ 2)) p =
                cubic σ (-(a ^ 2)) (e * a, 0) + e * (P p).1 ^ 2 + ∑ i, σ i * (P p).2 i ^ 2) := by
  obtain ⟨Φ, hp, hsource, hΦ, hcenter⟩ := exists_endpoint_scalar_chart ha e
  let P := scalarProductChart (V := Fin m → ℝ) Φ
  have hP (p : Model m) : P p = (endpointCoordinate a e p.1, p.2) :=
    Prod.ext (congrFun hΦ p.1) rfl
  refine ⟨P, ⟨hp, Set.mem_univ _⟩, ?_, fun _ => rfl, ?_⟩
  · rw [hP, endpointCoordinate_center]
    rfl
  · intro p hp
    rw [hP]
    exact cubic_endpoint_square σ a e he (hsource hp.1)
