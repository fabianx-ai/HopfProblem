module

public import Lib.Topology.Dimension.CubeBoundaryThreeCells.Faces

/-!
# Every boundary point of the three-cube lies in a mesh square

A point `x` of `∂[-1,1]³` has a coordinate `x i = ±1`; keeping it and replacing the other two
coordinates by the lower endpoints of their mesh intervals gives a vertex from which a mesh square
containing `x` starts (`exists_square_mem`).

## References

* R. Engelking, *Dimension Theory*, §1.8
* W. Hurewicz and H. Wallman, *Dimension Theory*, Chapter IV
-/

set_option warningAsError true
set_option autoImplicit false

open Set

namespace TopologicalSpace.CubeBoundaryThree

/-- After choosing a fixed index, the other two coordinates admit an increasing order. -/
theorem other_two_ordered (i : Fin 3) :
    ∃ j k : Fin 3, j < k ∧ i ≠ j ∧ i ≠ k ∧
      ∀ r : Fin 3, r = i ∨ r = j ∨ r = k := by
  fin_cases i
  · exact ⟨1, 2, by decide, by decide, by decide, by intro r; fin_cases r <;> simp⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by intro r; fin_cases r <;> simp⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by intro r; fin_cases r <;> simp⟩

/-- Two complementary directions exhausting the coordinates with the fixed index are distinct. -/
theorem complementary_directions_ne {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hexhaust : ∀ r : Fin 3, r = i ∨ r = j ∨ r = k) : j ≠ k := by
  intro hjk
  subst k
  have h0 := hexhaust 0
  have h1 := hexhaust 1
  have h2 := hexhaust 2
  fin_cases i <;> fin_cases j <;> simp_all

/-- Assemble an ambient point from prescribed values at the three chosen indices. -/
def ambientOfThreeCoordinates (i j k : Fin 3) (xi xj xk : ℝ) : Ambient :=
  WithLp.toLp 2 (fun r : Fin 3 =>
    if r = i then xi else if r = j then xj else if r = k then xk else 0)

/-- The assembled point takes its first prescribed coordinate value. -/
theorem ambientOfThreeCoordinates_apply_i (i j k : Fin 3) (xi xj xk : ℝ) :
    ambientOfThreeCoordinates i j k xi xj xk i = xi := by simp [ambientOfThreeCoordinates]
/-- Distinctness from the first index recovers the second prescribed value. -/
theorem ambientOfThreeCoordinates_apply_j {i j k : Fin 3} (hji : j ≠ i) (xi xj xk : ℝ) :
    ambientOfThreeCoordinates i j k xi xj xk j = xj := by simp [ambientOfThreeCoordinates, hji]
/-- Distinctness from the preceding indices recovers the third prescribed value. -/
theorem ambientOfThreeCoordinates_apply_k {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (xi xj xk : ℝ) : ambientOfThreeCoordinates i j k xi xj xk k = xk := by
  simp [ambientOfThreeCoordinates, hki, hkj]

/-- Retain the saturated coordinate and replace the other two by their lower mesh endpoints. -/
noncomputable def coverageVertex (N : ℕ) (h : ℝ) (x : Ambient) (i j k : Fin 3) : Ambient :=
  ambientOfThreeCoordinates i j k (x i) (latticeLowerEndpoint N h (x j))
    (latticeLowerEndpoint N h (x k))

/-- The coverage vertex retains the original fixed coordinate. -/
theorem coverageVertex_apply_i (N : ℕ) (h : ℝ) (x : Ambient) (i j k : Fin 3) :
    coverageVertex N h x i j k i = x i := by
  simp [coverageVertex, ambientOfThreeCoordinates]

/-- The coverage vertex uses the lower mesh endpoint in the first moving direction. -/
theorem coverageVertex_apply_j {N : ℕ} {h : ℝ} {x : Ambient} {i j k : Fin 3}
    (hji : j ≠ i) :
    coverageVertex N h x i j k j = latticeLowerEndpoint N h (x j) := by
  simp [coverageVertex, ambientOfThreeCoordinates, hji]

/-- The coverage vertex uses the lower mesh endpoint in the second moving direction. -/
theorem coverageVertex_apply_k {N : ℕ} {h : ℝ} {x : Ambient} {i j k : Fin 3}
    (hki : k ≠ i) (hkj : k ≠ j) :
    coverageVertex N h x i j k k = latticeLowerEndpoint N h (x k) := by
  simp [coverageVertex, ambientOfThreeCoordinates, hki, hkj]

/-- A boundary point has a signed saturated coordinate and all coordinates in [-1,1]. -/
theorem boundary_face_coordinate_data {x : Ambient} (hx : x ∈ boundary) :
    ∃ (i : Fin 3) (σ : {r : ℝ // r = -1 ∨ r = 1}),
      x ∈ face i σ ∧ x i = σ.1 ∧ ∀ r : Fin 3, x r ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨i, σ, hface⟩ := exists_mem_face hx
  refine ⟨i, σ, hface, (mem_face_iff x i σ).mp hface |>.2, ?_⟩
  intro r
  apply abs_le.mp
  rw [← (show maxAbs x = 1 from hx)]
  fin_cases r <;> simp [maxAbs]

/-- Either signed endpoint belongs to the mesh lattice. -/
theorem face_coordinate_mem_lattice {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {x : Ambient} {i : Fin 3}
    {σ : {r : ℝ // r = -1 ∨ r = 1}} (hxi : x i = σ.1) : x i ∈ lattice N h := by
  rw [hxi]
  rcases σ.property with hneg | hpos
  · rw [hneg]; exact (lattice_endpoints hN hh).1
  · rw [hpos]; exact (lattice_endpoints hN hh).2

/-- The fixed lattice coordinate and the two lower endpoints make all vertex coordinates lattice points. -/
theorem coverageVertex_all_lattice {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {x : Ambient} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hexhaust : ∀ r : Fin 3, r = i ∨ r = j ∨ r = k)
    (hxi : x i ∈ lattice N h) (hxj : x j ∈ Set.Icc (-1 : ℝ) 1)
    (hxk : x k ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ r : Fin 3, coverageVertex N h x i j k r ∈ lattice N h := by
  have hjk := complementary_directions_ne hij hik hexhaust
  intro r
  rcases hexhaust r with rfl | rfl | rfl
  · change (if r = r then x r else _) ∈ lattice N h
    rw [if_pos rfl]
    exact hxi
  · rw [coverageVertex_apply_j (Ne.symm hij)]
    exact (latticeLowerEndpoint_data hN hh hxj).1.1
  · rw [coverageVertex_apply_k (Ne.symm hik) (Ne.symm hjk)]
    exact (latticeLowerEndpoint_data hN hh hxk).1.1

/-- Lattice bounds and the retained saturated coordinate put the constructed vertex on the boundary. -/
theorem coverageVertex_boundary {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {x : Ambient} {i j k : Fin 3}
    {σ : {r : ℝ // r = -1 ∨ r = 1}} (hxi : x i = σ.1)
    (hlattice : ∀ r : Fin 3, coverageVertex N h x i j k r ∈ lattice N h) :
    coverageVertex N h x i j k ∈ boundary := by
  have hb : ∀ r, |coverageVertex N h x i j k r| ≤ 1 := fun r =>
    abs_le.mpr (lattice_subset_interval hN hh (hlattice r))
  have hfixed : |coverageVertex N h x i j k i| = 1 := by
    rw [coverageVertex_apply_i, hxi]
    rcases σ.property with he | he <;> rw [he] <;> norm_num
  change maxAbs _ = 1
  apply le_antisymm (max_le (hb 0) (max_le (hb 1) (hb 2)))
  calc
    1 = |coverageVertex N h x i j k i| := hfixed.symm
    _ ≤ maxAbs _ := by fin_cases i <;> simp [maxAbs]

/-- Coordinatewise lattice membership together with boundary membership defines a vertex. -/
theorem coverageVertex_mem_vertices {N : ℕ} {h : ℝ} {x : Ambient} {i j k : Fin 3}
    (hlattice : ∀ r : Fin 3, coverageVertex N h x i j k r ∈ lattice N h)
    (hboundary : coverageVertex N h x i j k ∈ boundary) :
    coverageVertex N h x i j k ∈ vertices N h := ⟨hlattice, hboundary⟩

/-- Both selected lower endpoints leave room for one mesh step in their moving directions. -/
theorem coverageVertex_direction_bounds {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {x : Ambient} {i j k : Fin 3}
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hxj : x j ∈ Set.Icc (-1 : ℝ) 1) (hxk : x k ∈ Set.Icc (-1 : ℝ) 1) :
    coverageVertex N h x i j k j ≤ 1 - h ∧ coverageVertex N h x i j k k ≤ 1 - h := by
  rw [coverageVertex_apply_j hji, coverageVertex_apply_k hki hkj]
  exact ⟨(latticeLowerEndpoint_data hN hh hxj).2, (latticeLowerEndpoint_data hN hh hxk).2⟩

/-- The saturated fixed coordinate and the direction bounds make the coverage square admissible. -/
theorem coverageSquareParam {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {x : Ambient} {i j k : Fin 3}
    (hjk : j < k) (hij : i ≠ j) (hik : i ≠ k)
    (hv : coverageVertex N h x i j k ∈ vertices N h)
    (hvj : coverageVertex N h x i j k j ≤ 1 - h)
    (hvk : coverageVertex N h x i j k k ≤ 1 - h) (habs : |x i| = 1) :
    SquareParam N h (coverageVertex N h x i j k) j k := by
  refine ⟨hv, hjk, hvj, hvk,
    (square_subset_boundary_iff hN hh hv hjk hvj hvk hij hik).mpr ?_⟩
  rw [coverageVertex_apply_i]
  exact habs

/-- An admissible coverage parameter supplies a member of the square family. -/
theorem coverageSquare_mem_squares {N : ℕ} {h : ℝ} {x : Ambient} {i j k : Fin 3}
    (hp : SquareParam N h (coverageVertex N h x i j k) j k) :
    squareGeom h (coverageVertex N h x i j k) j k ∈ squares N h :=
  ⟨coverageVertex N h x i j k, j, k, hp, rfl⟩

/-- The fixed coordinate equation and two floor enclosures place the original point in its square. -/
theorem point_mem_coverageSquare {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {x : Ambient} {i j k : Fin 3}
    (hjk : j < k) (hij : i ≠ j) (hik : i ≠ k)
    (hxi : coverageVertex N h x i j k i = x i)
    (hxj : x j ∈ Set.Icc (latticeLowerEndpoint N h (x j))
      (latticeLowerEndpoint N h (x j) + h))
    (hxk : x k ∈ Set.Icc (latticeLowerEndpoint N h (x k))
      (latticeLowerEndpoint N h (x k) + h)) :
    x ∈ squareGeom h (coverageVertex N h x i j k) j k := by
  rw [square_closed_coordinate_rectangle (mesh_pos hN hh) hjk hij hik]
  refine ⟨hxi.symm, ?_, ?_⟩
  · simpa only [coverageVertex_apply_j (Ne.symm hij)] using hxj
  · simpa only [coverageVertex_apply_k (Ne.symm hik) (ne_of_lt hjk).symm] using hxk

/-- Retaining a saturated coordinate and taking two clipped lower endpoints covers each boundary point by a square. -/
public theorem exists_square_mem {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {x : Ambient} (hx : x ∈ boundary) :
    ∃ s : Set Ambient, s ∈ squares N h ∧ x ∈ s := by
  obtain ⟨i, σ, _hface, hxi, hbounds⟩ := boundary_face_coordinate_data hx
  obtain ⟨j, k, hjk, hij, hik, hexhaust⟩ := other_two_ordered i
  have hfixed := face_coordinate_mem_lattice hN hh hxi
  have hlattice := coverageVertex_all_lattice hN hh hij hik hexhaust hfixed
    (hbounds j) (hbounds k)
  have hboundary := coverageVertex_boundary hN hh hxi hlattice
  have hv := coverageVertex_mem_vertices hlattice hboundary
  obtain ⟨hvj, hvk⟩ := coverageVertex_direction_bounds hN hh (Ne.symm hij) (Ne.symm hik)
    (ne_of_lt hjk).symm (hbounds j) (hbounds k)
  have habs : |x i| = 1 := by
    rw [hxi]
    rcases σ.property with he | he <;> rw [he] <;> norm_num
  have hp := coverageSquareParam hN hh hjk hij hik hv hvj hvk habs
  refine ⟨squareGeom h (coverageVertex N h x i j k) j k, coverageSquare_mem_squares hp, ?_⟩
  exact point_mem_coverageSquare hN hh hjk hij hik (coverageVertex_apply_i N h x i j k)
    (clipped_floor_enclosure hN hh (hbounds j)) (clipped_floor_enclosure hN hh (hbounds k))

end TopologicalSpace.CubeBoundaryThree
