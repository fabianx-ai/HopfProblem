/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# The complement of a bounded convex set is the complement of a point, up to homotopy

For a bounded convex set `S` in a real normed space `E` and a point `x ∈ S`, the inclusion
`E ∖ S → E ∖ {x}` is a homotopy equivalence (`ConvexComplement.homotopyEquiv`).  Both spaces
deformation retract onto a sphere `{z | ‖z - x‖ = R}` with `S ⊆ ball x R`, by the radial flow
`z ↦ x + ((1 - t) + t R/‖z - x‖) • (z - x)` from `x`; the flow keeps `E ∖ S` invariant because an
outward ray from `x` through a point outside the convex set `S` stays outside `S`
(`flow_notMem`), and the sphere misses `S`.

This replaces the three separate retractions of Hatcher's §3.3 (a ball, a closed ball, a compact
convex set) by one statement: it is used for `H_n(E, E ∖ B) ≅ H_n(E, E ∖ y)`, `y` in an open ball
`B`, in `LocalHomology.lean`, and for `H_n(E, E ∖ K) ≅ H_n(E, E ∖ x)`, `x` in a compact convex `K`,
in Lemma 3.27.  The homology consequence is `ConvexComplement.singularHomologyMap_inclusion_bijective`.

## Main definitions and results

* `ConvexComplement.flow x R t z` : the radial flow, with `flow_zero`, `flow_one_norm`, `flow_ne`,
  `flow_notMem`.
* `ConvexComplement.homotopyEquiv hS hx hR hSR : (Sᶜ : Set E) ≃ₕ ({x}ᶜ : Set E)` whose forward
  map is the inclusion (`homotopyEquiv_toFun`).
* `ConvexComplement.exists_radius` : a bounded `S` lies in some `ball x R`, `R > 0`.
* `ConvexComplement.singularHomologyMap_inclusion_bijective`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3, proof of Lemma 3.27 (2) and the
  discussion before Proposition 3.25

## Tags

convex, deformation retraction, punctured space, homotopy equivalence
-/

open Set Function Topology

@[expose] public noncomputable section

namespace ConvexComplement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The radial flow -/

/-- The scale factor of the radial flow at time `t`: `1` at `t = 0`, `R / ‖z - x‖` at `t = 1`. -/
def scaleFactor (x : E) (R t : ℝ) (z : E) : ℝ := (1 - t) + t * (R / ‖z - x‖)

/-- The radial flow from `x`: at time `1` it projects `z ≠ x` onto the sphere of radius `R`. -/
def flow (x : E) (R t : ℝ) (z : E) : E := x + scaleFactor x R t z • (z - x)

omit [NormedSpace ℝ E] in
theorem scaleFactor_pos {x : E} {R t : ℝ} (hR : 0 < R) (ht : t ∈ Icc (0 : ℝ) 1) {z : E}
    (hz : z ≠ x) : 0 < scaleFactor x R t z := by
  have hnorm : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hdiv : 0 < R / ‖z - x‖ := div_pos hR hnorm
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0; simp [scaleFactor]
  · unfold scaleFactor
    have := mul_pos h0 hdiv
    linarith [ht.2]

theorem flow_zero (x : E) (R : ℝ) (z : E) : flow x R 0 z = z := by
  simp [flow, scaleFactor]

theorem flow_one (x : E) (R : ℝ) (z : E) : flow x R 1 z = x + (R / ‖z - x‖) • (z - x) := by
  simp [flow, scaleFactor]

theorem flow_sub (x : E) (R t : ℝ) (z : E) : flow x R t z - x = scaleFactor x R t z • (z - x) := by
  simp [flow]

theorem norm_flow_sub {x : E} {R t : ℝ} (hR : 0 < R) (ht : t ∈ Icc (0 : ℝ) 1) {z : E} (hz : z ≠ x) :
    ‖flow x R t z - x‖ = (1 - t) * ‖z - x‖ + t * R := by
  have hnorm : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  rw [flow_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (scaleFactor_pos hR ht hz), scaleFactor]
  field_simp

theorem flow_one_norm {x : E} {R : ℝ} (hR : 0 < R) {z : E} (hz : z ≠ x) :
    ‖flow x R 1 z - x‖ = R := by
  rw [norm_flow_sub hR ⟨zero_le_one, le_rfl⟩ hz]
  ring

theorem flow_ne {x : E} {R t : ℝ} (hR : 0 < R) (ht : t ∈ Icc (0 : ℝ) 1) {z : E} (hz : z ≠ x) :
    flow x R t z ≠ x := by
  intro h
  have := norm_flow_sub hR ht hz
  rw [h, sub_self, norm_zero] at this
  have hnorm : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have h1 : 0 ≤ (1 - t) * ‖z - x‖ := mul_nonneg (sub_nonneg.mpr ht.2) hnorm.le
  have h2 : 0 ≤ t * R := mul_nonneg ht.1 hR.le
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    simp at this
    exact hnorm.ne' this.symm
  · nlinarith

/-- An outward ray from a point of a convex set through a point outside it stays outside: the
radial flow preserves the complement of `S` when `S ⊆ ball x R`. -/
theorem flow_notMem {S : Set E} (hS : Convex ℝ S) {x : E} (hx : x ∈ S) {R : ℝ} (hR : 0 < R)
    (hSR : S ⊆ Metric.ball x R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : E} (hz : z ∉ S) :
    flow x R t z ∉ S := by
  have hzx : z ≠ x := fun h => hz (h ▸ hx)
  have hnorm : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
  intro hw
  have hlpos : 0 < scaleFactor x R t z := scaleFactor_pos hR ht hzx
  by_cases hle : ‖z - x‖ ≤ R
  · -- the scale factor is `≥ 1`: `z` lies on the segment from `x` to the flow point.
    have h1 : 1 ≤ scaleFactor x R t z := by
      have hdiv : 1 ≤ R / ‖z - x‖ := (one_le_div hnorm).mpr hle
      unfold scaleFactor
      nlinarith [ht.1, ht.2]
    have hzeq : z = x + (1 / scaleFactor x R t z) • (flow x R t z - x) := by
      rw [flow_sub, smul_smul, one_div, inv_mul_cancel₀ hlpos.ne', one_smul]
      abel
    have hmem : x + (1 / scaleFactor x R t z) • (flow x R t z - x) ∈ S :=
      hS.add_smul_sub_mem hx hw ⟨by positivity, by rw [div_le_one hlpos]; exact h1⟩
    exact hz (hzeq ▸ hmem)
  · -- `‖z - x‖ > R`: the flow point stays at distance `≥ R`, outside the ball.
    push Not at hle
    have hdist : R ≤ ‖flow x R t z - x‖ := by
      rw [norm_flow_sub hR ht hzx]
      nlinarith [ht.1, ht.2]
    have := hSR hw
    rw [Metric.mem_ball, dist_eq_norm] at this
    exact absurd hdist (not_le.mpr this)

/-- The radial flow at time `1` lands outside every `S ⊆ ball x R`. -/
theorem flow_one_notMem {S : Set E} {x : E} {R : ℝ} (hR : 0 < R) (hSR : S ⊆ Metric.ball x R)
    {z : E} (hz : z ≠ x) : flow x R 1 z ∉ S := by
  intro hw
  have := hSR hw
  rw [Metric.mem_ball, dist_eq_norm, flow_one_norm hR hz] at this
  exact lt_irrefl _ this

theorem continuous_flow (x : E) (R : ℝ) :
    Continuous fun p : unitInterval × ({x}ᶜ : Set E) => flow x R (p.1 : ℝ) (p.2 : E) := by
  have ht : Continuous fun p : unitInterval × ({x}ᶜ : Set E) => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : unitInterval × ({x}ᶜ : Set E) => (p.2 : E) :=
    continuous_subtype_val.comp continuous_snd
  have hsub : Continuous fun p : unitInterval × ({x}ᶜ : Set E) => (p.2 : E) - x := hz.sub continuous_const
  have hnorm : ∀ p : unitInterval × ({x}ᶜ : Set E), ‖(p.2 : E) - x‖ ≠ 0 := fun p =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr p.2.2)
  unfold flow scaleFactor
  exact continuous_const.add
    (((continuous_const.sub ht).add (ht.mul (continuous_const.div hsub.norm hnorm))).smul hsub)

/-! ### The homotopy equivalence -/

variable {S : Set E} {x : E} {R : ℝ}

omit [NormedSpace ℝ E] in
/-- A bounded set lies in a ball of positive radius around any point. -/
theorem exists_radius (hb : Bornology.IsBounded S) (x : E) : ∃ R : ℝ, 0 < R ∧ S ⊆ Metric.ball x R := by
  obtain ⟨r, hr⟩ := hb.subset_closedBall x
  refine ⟨max r 0 + 1, by positivity, fun z hz => ?_⟩
  have := hr hz
  rw [Metric.mem_closedBall] at this
  rw [Metric.mem_ball]
  linarith [le_max_left r 0]

/-- The inclusion `E ∖ S → E ∖ {x}` for `x ∈ S`. -/
def inclusion (hx : x ∈ S) : C((Sᶜ : Set E), ({x}ᶜ : Set E)) :=
  ContinuousMap.inclusion (compl_subset_compl.mpr (singleton_subset_iff.mpr hx))

omit [NormedSpace ℝ E] in
@[simp]
theorem inclusion_apply_coe (hx : x ∈ S) (z : (Sᶜ : Set E)) : (inclusion hx z : E) = z := rfl

/-- The radial retraction `E ∖ {x} → E ∖ S` onto the sphere of radius `R`. -/
def retraction (hR : 0 < R) (hSR : S ⊆ Metric.ball x R) : C(({x}ᶜ : Set E), (Sᶜ : Set E)) :=
  ⟨fun z => ⟨flow x R 1 z, flow_one_notMem hR hSR z.2⟩, by
    have : Continuous fun z : ({x}ᶜ : Set E) => flow x R ((1 : unitInterval) : ℝ) (z : E) :=
      (continuous_flow x R).comp (Continuous.prodMk continuous_const continuous_id)
    exact this.subtype_mk _⟩

@[simp]
theorem retraction_apply_coe (hR : 0 < R) (hSR : S ⊆ Metric.ball x R) (z : ({x}ᶜ : Set E)) :
    (retraction hR hSR z : E) = flow x R 1 z := rfl

/-- The flow as a homotopy on `E ∖ {x}` from the identity to inclusion ∘ retraction. -/
def puncturedHomotopy (hx : x ∈ S) (hR : 0 < R) (hSR : S ⊆ Metric.ball x R) :
    ContinuousMap.Homotopy (ContinuousMap.id ({x}ᶜ : Set E)) ((inclusion hx).comp (retraction hR hSR)) where
  toFun p := ⟨flow x R (p.1 : ℝ) p.2, flow_ne hR p.1.2 p.2.2⟩
  continuous_toFun := (continuous_flow x R).subtype_mk _
  map_zero_left z := Subtype.ext (flow_zero x R z)
  map_one_left _ := rfl

/-- The flow as a homotopy on `E ∖ S` from the identity to retraction ∘ inclusion. -/
def complementHomotopy (hS : Convex ℝ S) (hx : x ∈ S) (hR : 0 < R) (hSR : S ⊆ Metric.ball x R) :
    ContinuousMap.Homotopy (ContinuousMap.id (Sᶜ : Set E)) ((retraction hR hSR).comp (inclusion hx)) where
  toFun p := ⟨flow x R (p.1 : ℝ) p.2, flow_notMem hS hx hR hSR p.1.2 p.2.2⟩
  continuous_toFun := by
    have : Continuous fun p : unitInterval × (Sᶜ : Set E) => flow x R (p.1 : ℝ) (p.2 : E) :=
      (continuous_flow x R).comp (Continuous.prodMk continuous_fst
        ((continuous_subtype_val.comp continuous_snd).subtype_mk
          (fun p : unitInterval × (Sᶜ : Set E) => fun h : (p.2 : E) ∈ ({x} : Set E) => p.2.2 (h ▸ hx))))
    exact this.subtype_mk _
  map_zero_left z := Subtype.ext (flow_zero x R z)
  map_one_left _ := rfl

/-- **The complement of a bounded convex set is the complement of a point, up to homotopy**: for
`S` convex with `x ∈ S` and `S ⊆ ball x R`, the inclusion `E ∖ S → E ∖ {x}` is a homotopy
equivalence. -/
def homotopyEquiv (hS : Convex ℝ S) (hx : x ∈ S) (hR : 0 < R) (hSR : S ⊆ Metric.ball x R) :
    ContinuousMap.HomotopyEquiv (Sᶜ : Set E) ({x}ᶜ : Set E) where
  toFun := inclusion hx
  invFun := retraction hR hSR
  left_inv := ⟨(complementHomotopy hS hx hR hSR).symm⟩
  right_inv := ⟨(puncturedHomotopy hx hR hSR).symm⟩

theorem homotopyEquiv_toFun (hS : Convex ℝ S) (hx : x ∈ S) (hR : 0 < R) (hSR : S ⊆ Metric.ball x R) :
    (homotopyEquiv hS hx hR hSR).toFun = inclusion hx := rfl

/-! ### The sphere as a deformation retract of the punctured space -/

omit [NormedSpace ℝ E] in
/-- A point of the sphere of positive radius about `x` is not `x`. -/
theorem mem_compl_singleton_of_mem_sphere (hR : 0 < R) {z : E} (hz : z ∈ Metric.sphere x R) :
    z ∈ ({x}ᶜ : Set E) := by
  intro h
  rw [Set.mem_singleton_iff] at h
  rw [mem_sphere_iff_norm, h, sub_self, norm_zero] at hz
  exact hR.ne hz

/-- The inclusion of the sphere of radius `R` about `x` into `E ∖ {x}`. -/
def sphereInclusion (hR : 0 < R) : C(Metric.sphere x R, ({x}ᶜ : Set E)) :=
  ⟨fun z => ⟨z, mem_compl_singleton_of_mem_sphere hR z.2⟩, continuous_subtype_val.subtype_mk _⟩

omit [NormedSpace ℝ E] in
@[simp]
theorem sphereInclusion_apply_coe (hR : 0 < R) (z : Metric.sphere x R) :
    (sphereInclusion hR z : E) = z := rfl

/-- The radial retraction `E ∖ {x} → sphere x R`. -/
def sphereRetraction (hR : 0 < R) : C(({x}ᶜ : Set E), Metric.sphere x R) :=
  ⟨fun z => ⟨flow x R 1 z, by rw [mem_sphere_iff_norm]; exact flow_one_norm hR z.2⟩, by
    have : Continuous fun z : ({x}ᶜ : Set E) => flow x R ((1 : unitInterval) : ℝ) (z : E) :=
      (continuous_flow x R).comp (Continuous.prodMk continuous_const continuous_id)
    exact this.subtype_mk _⟩

/-- The flow fixes the sphere of radius `R` pointwise. -/
theorem flow_one_of_mem_sphere (hR : 0 < R) {z : E} (hz : z ∈ Metric.sphere x R) :
    flow x R 1 z = z := by
  rw [mem_sphere_iff_norm] at hz
  rw [flow_one, hz, div_self hR.ne', one_smul, add_sub_cancel]

/-- The flow as a homotopy on `E ∖ {x}` from the identity to sphere inclusion ∘ retraction. -/
def puncturedSphereHomotopy (hR : 0 < R) :
    ContinuousMap.Homotopy (ContinuousMap.id ({x}ᶜ : Set E))
      ((sphereInclusion hR).comp (sphereRetraction hR)) where
  toFun p := ⟨flow x R (p.1 : ℝ) p.2, flow_ne hR p.1.2 p.2.2⟩
  continuous_toFun := (continuous_flow x R).subtype_mk _
  map_zero_left z := Subtype.ext (flow_zero x R z)
  map_one_left _ := rfl

/-- **The sphere is a deformation retract of the punctured space**: the inclusion
`sphere x R → E ∖ {x}` is a homotopy equivalence. -/
def sphereHomotopyEquiv (hR : 0 < R) :
    ContinuousMap.HomotopyEquiv (Metric.sphere x R) ({x}ᶜ : Set E) where
  toFun := sphereInclusion hR
  invFun := sphereRetraction hR
  left_inv := by
    have : (sphereRetraction (x := x) hR).comp (sphereInclusion hR) =
        ContinuousMap.id (Metric.sphere x R) := by
      ext z
      exact flow_one_of_mem_sphere hR z.2
    rw [this]
  right_inv := ⟨(puncturedSphereHomotopy (x := x) hR).symm⟩

/-! ### The homology consequence -/

/-- The inclusion `E ∖ S → E ∖ {x}` induces isomorphisms on singular homology, for `S` bounded
convex and `x ∈ S`. -/
theorem singularHomologyMap_inclusion_bijective {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) (hb : Bornology.IsBounded S) {x : E} (hx : x ∈ S) (n : ℕ) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (inclusion hx) n) := by
  obtain ⟨R, hR, hSR⟩ := exists_radius hb x
  exact (SingularHomology.homotopyEquivHomologyEquiv (homotopyEquiv hS hx hR hSR) n).bijective

end ConvexComplement
