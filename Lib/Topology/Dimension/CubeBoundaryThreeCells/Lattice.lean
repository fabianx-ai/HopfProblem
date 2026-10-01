module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Set.Card

/-!
# The uniform mesh of `[-1, 1]`

For `N > 0` and `h = 2 / N`, the mesh lattice `lattice N h` is the set of points `-1 + k h` with
`0 ≤ k ≤ N`.  It lies in `[-1, 1]`, contains both endpoints, has exactly `N + 1` points, distinct
points are at least `h` apart, and every lattice point `t ≤ 1 - h` has the successor `t + h`.

Every `t ∈ [-1, 1]` lies in a mesh interval `[a, a + h]` whose lower endpoint `a` is a lattice point
different from `1`: take `a = -1 + k h` with `k = min ⌊(t + 1) / h⌋ (N - 1)` (the floor index,
clipped so that `t = 1` falls into the last interval).

This is the one-dimensional subdivision from which the cubical subdivision of `∂[-1,1]³` is built.

## References

* R. Engelking, *Dimension Theory*, §1.8
* W. Hurewicz and H. Wallman, *Dimension Theory*, Chapter IV
-/

set_option warningAsError true
set_option autoImplicit false

open Set

namespace TopologicalSpace.CubeBoundaryThree

/-- The lattice consists of the mesh points `-1 + k h` for integer indices `0 ≤ k ≤ N`. -/
@[expose] public def lattice (N : ℕ) (h : ℝ) : Set ℝ :=
  {t | ∃ k : ℤ, k ∈ Set.Icc 0 (N : ℤ) ∧ t = -1 + (k : ℝ) * h}
/-- The lower lattice deletes the top endpoint, leaving precisely the indices `k < N`. -/
@[expose] public def latticeBelowTop (N : ℕ) (h : ℝ) : Set ℝ := lattice N h \ {1}
/-- From `N > 0` and `h = 2/N`, the mesh is positive, satisfies `N h = 2`, and is at most two. -/
public theorem mesh_identities (N : ℕ) (h : ℝ) (hN : 0 < N) (hh : h = 2 / (N : ℝ)) :
  0 < h ∧ (N : ℝ) * h = 2 ∧ h ≤ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  subst h
  constructor
  · exact div_pos (by norm_num) hNr
  constructor
  · field_simp
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hN))
    exact (div_le_iff₀ hNr).2 (by nlinarith)
/-- For `N > 0` and `h = 2 / N`, the mesh `h` is positive. -/
public theorem mesh_pos {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ)) : 0 < h :=
  (mesh_identities N h hN hh).1
/-- Every indexed mesh point lies between `-1` and `1`. -/
public theorem lattice_subset_interval {N : ℕ} {h : ℝ} (hN : 0 < N)
  (hh : h = 2 / (N : ℝ)) : lattice N h ⊆ Set.Icc (-1) 1 := by
  rintro t ⟨k, hk, rfl⟩
  have hh' := (mesh_identities N h hN hh).2.1
  constructor
  · have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk.1
    exact le_add_of_nonneg_right (mul_nonneg hk0 (le_of_lt (mesh_pos hN hh)))
  · have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.2
    nlinarith [mul_le_mul_of_nonneg_right hkN (le_of_lt (mesh_pos hN hh))]
/-- The lattice is the image of a finite integer interval and is therefore finite. -/
public theorem finite_lattice (N : ℕ) (h : ℝ) : (lattice N h).Finite := by
  have hf := Set.Finite.image (fun k : ℤ => -1 + (k : ℝ) * h) (Set.finite_Icc 0 (N : ℤ))
  refine hf.subset ?_
  rintro t ⟨k, hk, rfl⟩
  exact ⟨k, hk, rfl⟩
/-- For `N > 0` and `h = 2 / N`, both `-1` (index `0`) and `1` (index `N`) are lattice points. -/
public theorem lattice_endpoints {N : ℕ} {h : ℝ} (hN : 0 < N)
  (hh : h = 2 / (N : ℝ)) : (-1 : ℝ) ∈ lattice N h ∧ (1 : ℝ) ∈ lattice N h := by
  constructor
  · exact ⟨0, by simp, by simp⟩
  · refine ⟨N, by simp, ?_⟩
    have hm := (mesh_identities N h hN hh).2.1
    norm_num at hm ⊢
    linarith
/-- Distinct integer indices differ by at least one, hence their mesh points are separated by at least `h`. -/
public theorem lattice_separation {N : ℕ} {h : ℝ} (hN : 0 < N)
  (hh : h = 2 / (N : ℝ)) {a b : ℝ} (ha : a ∈ lattice N h)
  (hb : b ∈ lattice N h) (hab : a ≠ b) : h ≤ |a - b| := by
  obtain ⟨ka, hka, rfl⟩ := ha
  obtain ⟨kb, hkb, rfl⟩ := hb
  have hk : ka ≠ kb := by
    intro e
    apply hab
    rw [e]
  have hkdiff : ka - kb ≠ 0 := sub_ne_zero.mpr hk
  have habsi : (1 : ℝ) ≤ |((ka - kb : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast (Int.one_le_abs hkdiff)
  have hhpos := mesh_pos hN hh
  rw [show (-1 + (ka : ℝ) * h) - (-1 + (kb : ℝ) * h) = ((ka - kb : ℤ) : ℝ) * h by push_cast; ring,
    abs_mul, abs_of_pos hhpos]
  exact le_mul_of_one_le_left (le_of_lt hhpos) habsi
/-- A lattice point below `1-h` has index below `N`, so adding `h` gives its successor in the lattice. -/
public theorem lattice_successor {N : ℕ} {h : ℝ} (hN : 0 < N)
  (hh : h = 2 / (N : ℝ)) {t : ℝ} (ht : t ∈ lattice N h) (hle : t ≤ 1 - h) :
  t + h ∈ lattice N h := by
  obtain ⟨k, hk, rfl⟩ := ht
  refine ⟨k + 1, ?_, ?_⟩
  · constructor
    · exact add_nonneg hk.1 (by norm_num)
    · have hm := (mesh_identities N h hN hh).2.1
      have hp := mesh_pos hN hh
      have hkR : (k : ℝ) * h ≤ (N : ℝ) * h - h := by linarith
      have hkN : (k : ℝ) + 1 ≤ (N : ℝ) := by nlinarith
      exact_mod_cast hkN
  · push_cast
    ring

/-- Normalize a coordinate by shifting its lower endpoint to zero and dividing by the mesh. -/
noncomputable def normalizedFloorInput (h t : ℝ) : ℝ := (t + 1) / h
/-- The floor of the normalized coordinate selects its integer mesh index. -/
noncomputable def unclippedFloorIndex (h t : ℝ) : ℤ := ⌊normalizedFloorInput h t⌋
/-- Clip the floor index at the last lower mesh index. -/
noncomputable def clippedFloorIndex (N : ℕ) (h t : ℝ) : ℤ :=
  min (unclippedFloorIndex h t) ((N : ℤ) - 1)
/-- The lattice point `-1 + k h` for the clipped floor index `k = min ⌊(t + 1) / h⌋ (N - 1)`: the
lower endpoint of a mesh interval containing `t` (see `clipped_floor_enclosure`). -/
public noncomputable def latticeLowerEndpoint (N : ℕ) (h t : ℝ) : ℝ :=
  -1 + (clippedFloorIndex N h t : ℝ) * h

/-- The defining floor inequalities enclose a real number between consecutive integers. -/
theorem floor_real_bounds (u : ℝ) :
    ((⌊u⌋ : ℤ) : ℝ) ≤ u ∧ u < ((⌊u⌋ : ℤ) : ℝ) + 1 := by
  exact ⟨Int.floor_le u, Int.lt_floor_add_one u⟩

/-- Casting the last integer index to the reals preserves subtraction of one. -/
theorem cast_int_nat_sub_one (N : ℕ) :
    (((N : ℤ) - 1 : ℤ) : ℝ) = (N : ℝ) - 1 := by
  push_cast
  ring

/-- A positive number of intervals has a nonnegative last lower index. -/
theorem int_nat_sub_one_nonneg {N : ℕ} (hN : 0 < N) :
    (0 : ℤ) ≤ (N : ℤ) - 1 := by omega

/-- An integer at most N is either below N or equal to N. -/
theorem int_floor_top_split {N : ℕ} {z : ℤ} (hz : z ≤ (N : ℤ)) :
    z ≤ (N : ℤ) - 1 ∨ z = (N : ℤ) := by omega

/-- Multiplying the floor inequalities by the positive mesh encloses the shifted coordinate. -/
theorem scale_floor_inequalities {h u t : ℝ} {z : ℤ} (hh : 0 < h)
    (hu : u * h = t + 1) (hzlow : (z : ℝ) ≤ u) (hzup : u < (z : ℝ) + 1) :
    (z : ℝ) * h ≤ t + 1 ∧ t + 1 < (z : ℝ) * h + h := by
  constructor
  · rw [← hu]; exact mul_le_mul_of_nonneg_right hzlow (le_of_lt hh)
  · rw [← hu]
    have := mul_lt_mul_of_pos_right hzup hh
    nlinarith

/-- The last lower mesh point is one minus the mesh and its successor is one. -/
theorem top_endpoint_cast_algebra {N : ℕ} {h : ℝ} (hmul : (N : ℝ) * h = 2) :
    -1 + ((((N : ℤ) - 1 : ℤ) : ℝ)) * h = 1 - h ∧
      (-1 + ((((N : ℤ) - 1 : ℤ) : ℝ)) * h) + h = 1 := by
  rw [cast_int_nat_sub_one]
  constructor <;> nlinarith

/-- Normalizing an interval coordinate puts it between zero and N. -/
theorem normalizedFloorInput_bounds {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    normalizedFloorInput h t ∈ Set.Icc (0 : ℝ) N := by
  have hm := mesh_identities N h hN hh
  constructor
  · exact div_nonneg (by linarith [ht.1]) hm.1.le
  · rw [normalizedFloorInput, div_le_iff₀ hm.1]
    linarith [hm.2.1, ht.2]

/-- The normalized floor index is an integer between zero and N. -/
theorem unclippedFloorIndex_bounds {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ unclippedFloorIndex h t ∧ unclippedFloorIndex h t ≤ (N : ℤ) := by
  have hb := normalizedFloorInput_bounds hN hh ht
  constructor
  · exact Int.floor_nonneg.mpr hb.1
  · have hle : (unclippedFloorIndex h t : ℝ) ≤ (N : ℝ) :=
      le_trans (floor_real_bounds (normalizedFloorInput h t)).1 hb.2
    exact_mod_cast hle

/-- Clipping leaves every ordinary floor index unchanged. -/
theorem clippedFloorIndex_eq_floor {N : ℕ} {h t : ℝ}
    (hle : unclippedFloorIndex h t ≤ (N : ℤ) - 1) :
    clippedFloorIndex N h t = unclippedFloorIndex h t := by
  simp [clippedFloorIndex, min_eq_left hle]

/-- Clipping an index at or above the last lower index returns that last index. -/
theorem clippedFloorIndex_eq_top {N : ℕ} {h t : ℝ}
    (hle : (N : ℤ) - 1 ≤ unclippedFloorIndex h t) :
    clippedFloorIndex N h t = (N : ℤ) - 1 := by
  simp [clippedFloorIndex, min_eq_right hle]

/-- The clipped integer index lies between zero and N minus one. -/
theorem clippedFloorIndex_bounds {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ clippedFloorIndex N h t ∧ clippedFloorIndex N h t ≤ (N : ℤ) - 1 := by
  have hb := unclippedFloorIndex_bounds hN hh ht
  exact ⟨le_min hb.1 (int_nat_sub_one_nonneg hN), min_le_right _ _⟩

/-- The selected endpoint is a lattice point below the top and leaves room for one mesh step. -/
public theorem latticeLowerEndpoint_data {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    latticeLowerEndpoint N h t ∈ latticeBelowTop N h ∧
    latticeLowerEndpoint N h t ≤ 1 - h := by
  have hb := clippedFloorIndex_bounds hN hh ht
  have hm := mesh_identities N h hN hh
  have hcast : (clippedFloorIndex N h t : ℝ) ≤ (((N : ℤ) - 1 : ℤ) : ℝ) := by
    exact_mod_cast hb.2
  rw [cast_int_nat_sub_one] at hcast
  have hupper : latticeLowerEndpoint N h t ≤ 1 - h := by
    dsimp [latticeLowerEndpoint]
    nlinarith [mul_le_mul_of_nonneg_right hcast hm.1.le, hm.2.1]
  refine ⟨⟨?_, ?_⟩, hupper⟩
  · exact ⟨clippedFloorIndex N h t, ⟨hb.1, by omega⟩, rfl⟩
  · simp only [Set.mem_singleton_iff]
    linarith [hm.1]

/-- In the ordinary floor case, scaling its inequalities encloses the shifted coordinate. -/
theorem ordinary_floor_enclosure {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hle : unclippedFloorIndex h t ≤ (N : ℤ) - 1) :
    (clippedFloorIndex N h t : ℝ) * h ≤ t + 1 ∧
    t + 1 < (clippedFloorIndex N h t : ℝ) * h + h := by
  have _ := unclippedFloorIndex_bounds hN hh ht
  have hp := (mesh_identities N h hN hh).1
  have hb := floor_real_bounds (normalizedFloorInput h t)
  rw [clippedFloorIndex_eq_floor hle]
  exact scale_floor_inequalities hp (div_mul_cancel₀ _ (ne_of_gt hp)) hb.1 hb.2

/-- The top floor value forces t to equal one and selects the final mesh interval. -/
theorem top_floor_case {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hfloor : unclippedFloorIndex h t = (N : ℤ)) :
    t = 1 ∧ clippedFloorIndex N h t = (N : ℤ) - 1 ∧
    latticeLowerEndpoint N h t = 1 - h ∧ latticeLowerEndpoint N h t + h = 1 := by
  have _ := unclippedFloorIndex_bounds hN hh ht
  have hm := mesh_identities N h hN hh
  have hl : (N : ℝ) ≤ normalizedFloorInput h t := by
    have hb := (floor_real_bounds (normalizedFloorInput h t)).1
    change (unclippedFloorIndex h t : ℝ) ≤ _ at hb
    rw [hfloor] at hb
    exact_mod_cast hb
  have hu : normalizedFloorInput h t * h = t + 1 :=
    div_mul_cancel₀ _ (ne_of_gt hm.1)
  have htone : t = 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hl hm.1.le, hm.2.1, ht.2]
  have hc := clippedFloorIndex_eq_top (N := N) (h := h) (t := t) (by omega)
  refine ⟨htone, hc, ?_⟩
  simpa only [latticeLowerEndpoint, hc] using top_endpoint_cast_algebra hm.2.1

/-- For `N > 0`, `h = 2 / N` and `t ∈ [-1, 1]`, the point `t` lies in the mesh interval
`[a, a + h]` with `a = latticeLowerEndpoint N h t`. -/
public theorem clipped_floor_enclosure {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    t ∈ Set.Icc (latticeLowerEndpoint N h t) (latticeLowerEndpoint N h t + h) := by
  rcases int_floor_top_split (unclippedFloorIndex_bounds hN hh ht).2 with hlow | htop
  · have hb := ordinary_floor_enclosure hN hh ht hlow
    dsimp [latticeLowerEndpoint]
    constructor <;> linarith [hb.1, hb.2]
  · obtain ⟨htone, _hc, hlower, hupper⟩ := top_floor_case hN hh ht htop
    have hp := (mesh_identities N h hN hh).1
    constructor <;> linarith

end TopologicalSpace.CubeBoundaryThree
