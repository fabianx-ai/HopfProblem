module

public import Lib.Topology.Dimension.CubeBoundaryThreeCells.Faces

/-!
# Relative interiors of distinct mesh squares are disjoint

Two mesh squares of `∂[-1,1]³` whose relative interiors meet are equal
(`square_eq_of_relInterior_inter_nonempty`): a common relative-interior point determines the fixed
coordinate, the two moving directions, and, since distinct open mesh intervals with lattice lower
endpoints are disjoint, the lower corner.

## References

* R. Engelking, *Dimension Theory*, §1.8
* W. Hurewicz and H. Wallman, *Dimension Theory*, Chapter IV
-/

set_option warningAsError true
set_option autoImplicit false

open Set

namespace TopologicalSpace.CubeBoundaryThree

/-- An open interval above a bounded lattice point stays strictly in the cube. -/
private theorem open_mesh_coordinate_abs_lt {N : ℕ} {h a x : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (ha : a ∈ lattice N h) (hau : a ≤ 1 - h)
    (hx : x ∈ Set.Ioo a (a + h)) : |x| < 1 := by
  rw [abs_lt]
  have hab := lattice_subset_interval hN hh ha
  rcases hab with ⟨hab₀, hab₁⟩
  rcases hx with ⟨hx₀, hx₁⟩
  constructor <;> linarith

/-- The two moving directions are determined by a common remaining index. -/
private theorem ordered_pair_eq_of_same_remaining {j k p q i : Fin 3}
    (hjk : j < k) (hpq : p < q) (hij : i ≠ j) (hik : i ≠ k)
    (hip : i ≠ p) (hiq : i ≠ q) : j = p ∧ k = q := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases p <;> fin_cases q <;> omega

/-- A point open in both coordinate rectangles forces their fixed indices to agree. -/
private theorem common_open_point_fixed_index_eq
    {x v w : Ambient} {j k i p q r : Fin 3}
    (hjk : j < k) (hpq : p < q)
    (hij : i ≠ j) (hik : i ≠ k) (hrp : r ≠ p) (hrq : r ≠ q)
    (hvi : |v i| = 1) (hwr : |w r| = 1)
    (hx : x i = v i ∧ |x j| < 1 ∧ |x k| < 1)
    (hx' : x r = w r ∧ |x p| < 1 ∧ |x q| < 1) : i = r := by
  by_contra hir
  fin_cases i <;> fin_cases r <;> fin_cases j <;> fin_cases k <;>
    fin_cases p <;> fin_cases q <;> simp_all

/-- Overlapping open mesh intervals with lattice lower endpoints coincide. -/
private theorem lattice_open_intervals_overlap_eq {N : ℕ} {h a b x : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (ha : a ∈ lattice N h) (hb : b ∈ lattice N h)
    (hxa : x ∈ Set.Ioo a (a + h)) (hxb : x ∈ Set.Ioo b (b + h)) : a = b := by
  by_contra hab
  have hsep := lattice_separation hN hh ha hb hab
  rcases le_total a b with hab' | hba'
  · rw [abs_of_nonpos (sub_nonpos.mpr hab')] at hsep
    linarith [hxb.1, hxa.2]
  · rw [abs_of_nonneg (sub_nonneg.mpr hba')] at hsep
    linarith [hxa.1, hxb.2]

/-- Fixed coordinate plus the two coincident lower intervals identify lower corners. -/
private theorem square_lower_vertices_eq_of_common_open
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    {x v w : Ambient} {j k i : Fin 3}
    (hv : v ∈ vertices N h) (hw : w ∈ vertices N h)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hfix : x i = v i ∧ x i = w i)
    (hj : x j ∈ Set.Ioo (v j) (v j + h) ∧ x j ∈ Set.Ioo (w j) (w j + h))
    (hk : x k ∈ Set.Ioo (v k) (v k + h) ∧ x k ∈ Set.Ioo (w k) (w k + h)) :
    v = w := by
  have hi : v i = w i := hfix.1.symm.trans hfix.2
  have hj' := lattice_open_intervals_overlap_eq hN hh (hv.1 j) (hw.1 j) hj.1 hj.2
  have hk' := lattice_open_intervals_overlap_eq hN hh (hv.1 k) (hw.1 k) hk.1 hk.2
  ext r
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases r <;> simp_all

/-- For `N > 0` and `h = 2 / N`, two mesh squares whose relative interiors meet are equal. -/
public theorem square_eq_of_relInterior_inter_nonempty
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    {s t : Set Ambient} (hs : s ∈ squares N h) (ht : t ∈ squares N h)
    (hinter : (squareRelInterior N h ⟨s, hs⟩ ∩
      squareRelInterior N h ⟨t, ht⟩).Nonempty) : s = t := by
  obtain ⟨x, hxs, hxt⟩ := hinter
  obtain ⟨v, j, k, i, hv, hjk, hvj, hvk, hij, hik, hvi, hsclosed, hsopen, _⟩ :=
    square_coordinate_description hN hh hs
  obtain ⟨w, p, q, r, hw, hpq, hwp, hwq, hrp, hrq, hwr, htclosed, htopen, _⟩ :=
    square_coordinate_description hN hh ht
  rw [hsopen] at hxs
  rw [htopen] at hxt
  have hjabs := open_mesh_coordinate_abs_lt hN hh (hv.1 j) hvj hxs.2.1
  have hkabs := open_mesh_coordinate_abs_lt hN hh (hv.1 k) hvk hxs.2.2
  have hpabs := open_mesh_coordinate_abs_lt hN hh (hw.1 p) hwp hxt.2.1
  have hqabs := open_mesh_coordinate_abs_lt hN hh (hw.1 q) hwq hxt.2.2
  have hir := common_open_point_fixed_index_eq hjk hpq hij hik hrp hrq hvi hwr
    ⟨hxs.1, hjabs, hkabs⟩ ⟨hxt.1, hpabs, hqabs⟩
  subst r
  obtain ⟨hjp, hkq⟩ := ordered_pair_eq_of_same_remaining hjk hpq hij hik hrp hrq
  subst p
  subst q
  have hvw := square_lower_vertices_eq_of_common_open hN hh hv hw hij hik (ne_of_lt hjk)
    ⟨hxs.1, hxt.1⟩ ⟨hxs.2.1, hxt.2.1⟩ ⟨hxs.2.2, hxt.2.2⟩
  subst w
  rw [hsclosed, htclosed]

end TopologicalSpace.CubeBoundaryThree
