module

public import Lib.Topology.Dimension.CubeBoundaryThreeCells.Cells

/-!
# Mesh cells in the faces of the three-cube

A mesh square `v + [0, h] e_j + [0, h] e_k` of `∂[-1,1]³` keeps its third coordinate `i` fixed;
it lies in the boundary if and only if `|v i| = 1`, and then it lies in the face `{x | x i = v i}`,
which is the unique face containing it.  Likewise an edge lies in the boundary as soon as one of
its two fixed coordinates is `±1`.  The closed and relative-open squares are the coordinate
rectangles `{x i = v i, x j ∈ [v j, v j + h], x k ∈ [v k, v k + h]}` (open intervals for the
relative interior); `square_coordinate_description` collects this for every member of
`squares N h`.

## References

* R. Engelking, *Dimension Theory*, §1.8
* W. Hurewicz and H. Wallman, *Dimension Theory*, Chapter IV
-/

set_option warningAsError true
set_option autoImplicit false

open Set

namespace TopologicalSpace.CubeBoundaryThree

/-- The square midpoint uses the two half-mesh displacements from its initial vertex. -/
noncomputable def squareMidpoint (h : ℝ) (v : Ambient) (j k : Fin 3) : Ambient :=
  v + ((1 / 2 : ℝ) * h) • EuclideanSpace.single j 1 + ((1 / 2 : ℝ) * h) • EuclideanSpace.single k 1
/-- Adding half a positive mesh in both moving directions gives a point of the square whose two moving coordinates lie strictly between `-1` and `1`. -/
theorem square_midpoint_bounds {h : ℝ} (hh : 0 < h) {v : Ambient} {j k : Fin 3}
  (hjk : j < k) (hv : v ∈ boundary) (hvj : v j ≤ 1 - h) (hvk : v k ≤ 1 - h) :
  (∀ r, -1 ≤ v r ∧ v r ≤ 1) ∧ squareMidpoint h v j k ∈ squareGeom h v j k ∧
  squareMidpoint h v j k j = v j + h / 2 ∧ squareMidpoint h v j k k = v k + h / 2 ∧
  (-1 < -1 + h / 2 ∧ -1 + h / 2 ≤ squareMidpoint h v j k j ∧
    squareMidpoint h v j k j ≤ 1 - h / 2 ∧ 1 - h / 2 < 1) ∧
  (-1 < -1 + h / 2 ∧ -1 + h / 2 ≤ squareMidpoint h v j k k ∧
    squareMidpoint h v j k k ≤ 1 - h / 2 ∧ 1 - h / 2 < 1) ∧
  |squareMidpoint h v j k j| < 1 ∧ |squareMidpoint h v j k k| < 1 := by
  have hvabs : ∀ r, |v r| ≤ 1 := by
    intro r
    rw [← hv]
    fin_cases r <;> simp [maxAbs]
  have hvbounds : ∀ r, -1 ≤ v r ∧ v r ≤ 1 := fun r => abs_le.mp (hvabs r)
  have hjne : j ≠ k := ne_of_lt hjk
  have hmj : squareMidpoint h v j k j = v j + h / 2 := by
    simp [squareMidpoint, hjne, div_eq_mul_inv]
    ring
  have hmk : squareMidpoint h v j k k = v k + h / 2 := by
    simp [squareMidpoint, hjne, div_eq_mul_inv]
    ring
  have hmem : squareMidpoint h v j k ∈ squareGeom h v j k := by
    refine ⟨1 / 2, by norm_num, 1 / 2, by norm_num, ?_⟩
    simp [squareMidpoint]
  have hb1 : -1 < -1 + h / 2 := by linarith
  have hb4 : 1 - h / 2 < 1 := by linarith
  have hbj : -1 + h / 2 ≤ squareMidpoint h v j k j ∧
      squareMidpoint h v j k j ≤ 1 - h / 2 := by rw [hmj]; constructor <;> linarith [hvbounds j]
  have hbk : -1 + h / 2 ≤ squareMidpoint h v j k k ∧
      squareMidpoint h v j k k ≤ 1 - h / 2 := by rw [hmk]; constructor <;> linarith [hvbounds k]
  refine ⟨hvbounds, hmem, hmj, hmk, ⟨hb1, hbj.1, hbj.2, hb4⟩,
    ⟨hb1, hbk.1, hbk.2, hb4⟩, ?_, ?_⟩
  · rw [abs_lt]; exact ⟨lt_of_lt_of_le hb1 hbj.1, lt_of_le_of_lt hbj.2 hb4⟩
  · rw [abs_lt]; exact ⟨lt_of_lt_of_le hb1 hbk.1, lt_of_le_of_lt hbk.2 hb4⟩
/-- A boundary point of the cube has maximum absolute coordinate equal to one. -/
theorem boundary_maxAbs_eq {x : Ambient} (hx : x ∈ boundary) : maxAbs x = 1 := hx
/-- If two coordinates have absolute value below one while the maximum is one, the remaining coordinate has absolute value one. -/
theorem remaining_abs_of_maxAbs {x : Ambient} {j k i : Fin 3}
  (hindices : ({j, k, i} : Set (Fin 3)) = Set.univ) (hj : |x j| < 1) (hk : |x k| < 1)
  (hx : maxAbs x = 1) : |x i| = 1 := by
  have hile : |x i| ≤ 1 := by
    rw [← hx]
    fin_cases i <;> simp [maxAbs]
  apply le_antisymm hile
  by_contra hn
  have hi : |x i| < 1 := lt_of_not_ge hn
  have hall : ∀ r : Fin 3, |x r| < 1 := by
    intro r
    have : r ∈ ({j, k, i} : Set (Fin 3)) := by rw [hindices]; trivial
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with rfl | rfl | rfl <;> assumption
  have : maxAbs x < 1 := max_lt (hall 0) (max_lt (hall 1) (hall 2))
  linarith
/-- The square midpoint remains on the boundary, keeps the remaining coordinate fixed, and forces its absolute value to one. -/
theorem square_midpoint_remaining_abs {N : ℕ} {h : ℝ} (hh : 0 < h) {v : Ambient} {j k i : Fin 3}
  (hp : SquareParam N h v j k) (hij : i ≠ j) (hik : i ≠ k) :
  squareMidpoint h v j k ∈ boundary ∧ squareMidpoint h v j k i = v i ∧ |v i| = 1 := by
  have hb := square_midpoint_bounds hh hp.2.1 hp.1.2 hp.2.2.1 hp.2.2.2.1
  have hmBoundary := hp.2.2.2.2 hb.2.1
  have hmi := square_remaining_coordinate hij hik hb.2.1
  have hjk := hp.2.1
  have hindices : ({j, k, i} : Set (Fin 3)) = Set.univ := by
    ext r
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    fin_cases r <;> omega
  have hai := remaining_abs_of_maxAbs hindices hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2
    (boundary_maxAbs_eq hmBoundary)
  exact ⟨hmBoundary, hmi, hmi ▸ hai⟩
/-- A boundary point whose `i`th coordinate is a sign lies in the corresponding signed face. -/
theorem face_membership_from_sign {x : Ambient} {i : Fin 3} {σ : {r : ℝ // r = -1 ∨ r = 1}}
  (hx : x ∈ boundary) (hxi : x i = σ.1) : x ∈ face i σ := ⟨hx, hxi⟩
/-- The saturated remaining coordinate determines a sign, and constancy of that coordinate puts the whole square in its face. -/
theorem square_face_sign_and_containment {N : ℕ} {h : ℝ} (hh : 0 < h) {v : Ambient} {j k i : Fin 3}
  (hp : SquareParam N h v j k) (hij : i ≠ j) (hik : i ≠ k) : ∃ σ : {r : ℝ // r = -1 ∨ r = 1},
    σ.1 = v i ∧ squareGeom h v j k ⊆ face i σ := by
  have habs := (square_midpoint_remaining_abs hh hp hij hik).2.2
  have hsign : v i = -1 ∨ v i = 1 := by
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at habs
    exact habs.elim Or.inr Or.inl
  let σ : {r : ℝ // r = -1 ∨ r = 1} := ⟨v i, hsign⟩
  refine ⟨σ, rfl, ?_⟩
  intro x hx
  apply face_membership_from_sign (hp.2.2.2.2 hx)
  exact (square_remaining_coordinate hij hik hx).trans rfl
/-- A point lying in two signed faces with the same coordinate forces the two signs to agree. -/
theorem face_sign_eq_of_mem {x : Ambient} {i : Fin 3}
  {σ τ : {r : ℝ // r = -1 ∨ r = 1}} (hxσ : x ∈ face i σ) (hxτ : x ∈ face i τ) : σ = τ := by
  apply Subtype.ext
  exact hxσ.2.symm.trans hxτ.2
/-- Variation in directions `j,k` excludes those face coordinates; the unique remaining coordinate and its sign determine the containing face. -/
theorem square_intrinsic_face {N : ℕ} {h : ℝ} (hh : 0 < h) {v : Ambient} {j k : Fin 3}
  (hp : SquareParam N h v j k) : ∃! p : Fin 3 × {r : ℝ // r = -1 ∨ r = 1}, squareGeom h v j k ⊆ face p.1 p.2 := by
  obtain ⟨i, hi, hiuniq⟩ := square_remaining_index hp.2.1
  obtain ⟨σ, hσ, hcontain⟩ := square_face_sign_and_containment hh hp hi.1 hi.2
  refine ⟨(i, σ), hcontain, ?_⟩
  rintro ⟨r, τ⟩ hr
  have hvτ := hr (square_zero_mem h v j k)
  have hrj : r ≠ j := by
    intro e
    subst r
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (square_nonconstant_coordinates hh hp.2.1 j).2 (Or.inl rfl)
    exact hxy ((hr hx).2.trans (hr hy).2.symm)
  have hrk : r ≠ k := by
    intro e
    subst r
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (square_nonconstant_coordinates hh hp.2.1 k).2 (Or.inr rfl)
    exact hxy ((hr hx).2.trans (hr hy).2.symm)
  have hir : r = i := hiuniq r ⟨hrj, hrk⟩
  subst r
  have hvσ := hcontain (square_zero_mem h v j k)
  have hστ : σ = τ := face_sign_eq_of_mem hvσ hvτ
  subst τ
  rfl
/-- When `N=1`, the mesh is two, admissible lower coordinates are `-1`, and square midpoint coordinates are strictly interior. -/
theorem square_unit_mesh_endpoint_case {h : ℝ} (hh : h = 2 / ((1 : ℕ) : ℝ))
  {v : Ambient} {j k : Fin 3} (hjk : j < k) (hv : v ∈ boundary)
  (hvj : v j ≤ 1 - h) (hvk : v k ≤ 1 - h) :
  h = 2 ∧ 0 < h ∧ v j = -1 ∧ v k = -1 ∧
  squareMidpoint h v j k j = 0 ∧ squareMidpoint h v j k k = 0 ∧
  (-1 < squareMidpoint h v j k j ∧ squareMidpoint h v j k j < 1) ∧
  (-1 < squareMidpoint h v j k k ∧ squareMidpoint h v j k k < 1) ∧
  |squareMidpoint h v j k j| < 1 ∧ |squareMidpoint h v j k k| < 1 := by
  have htwo := mesh_two_of_one hh
  have hpos : 0 < h := htwo ▸ (by norm_num)
  have hb := square_midpoint_bounds hpos hjk hv hvj hvk
  have hvjlow := (hb.1 j).1
  have hvklow := (hb.1 k).1
  have hvjeq : v j = -1 := by rw [htwo] at hvj; linarith
  have hvkeq : v k = -1 := by rw [htwo] at hvk; linarith
  refine ⟨htwo, hpos, hvjeq, hvkeq, ?_, ?_, ?_, ?_, hb.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2⟩
  · rw [hb.2.2.1, hvjeq, htwo]; norm_num
  · rw [hb.2.2.2.1, hvkeq, htwo]; norm_num
  · rw [hb.2.2.1, hvjeq, htwo]; norm_num
  · rw [hb.2.2.2.1, hvkeq, htwo]; norm_num

/-- A fixed saturated coordinate and interval bounds keep the edge on the boundary. -/
theorem edge_saturated_coordinate_suffices {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v : Ambient} {j i : Fin 3}
    (hv : v ∈ vertices N h) (hvj : v j ≤ 1 - h) (hij : i ≠ j) (hi : |v i| = 1) :
    edgeGeom h v j ⊆ boundary := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := edge_parameter_extract hx
  have hp := (mesh_identities N h hN hh).1
  have hb : ∀ r, |(v + (t * h) • EuclideanSpace.single j 1 : Ambient) r| ≤ 1 := by
    intro r
    rw [edge_coordinate_formula]
    split_ifs with hr
    · have hvb := lattice_subset_interval hN hh (hv.1 j)
      rw [abs_le]
      constructor <;> nlinarith [hvb.1, ht.2, mul_nonneg ht.1 hp.le]
    · exact abs_le.mpr (lattice_subset_interval hN hh (hv.1 r))
  have hfixed : |(v + (t * h) • EuclideanSpace.single j 1 : Ambient) i| = 1 := by
    rw [edge_coordinate_formula, if_neg hij, hi]
  change maxAbs _ = 1
  apply le_antisymm (max_le (hb 0) (max_le (hb 1) (hb 2)))
  calc
    1 = |(v + (t * h) • EuclideanSpace.single j 1 : Ambient) i| := hfixed.symm
    _ ≤ maxAbs _ := by fin_cases i <;> simp [maxAbs]

/-- If no fixed coordinate is saturated, the moving coordinate is the lower endpoint. -/
theorem edge_no_other_saturated_forces_moving_neg_one {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) {v : Ambient} {j : Fin 3}
    (hv : v ∈ vertices N h) (hvj : v j ≤ 1 - h)
    (hother : ∀ i : Fin 3, i ≠ j → |v i| < 1) : v j = -1 := by
  have hp := (mesh_identities N h hN hh).1
  have hvb : maxAbs v = 1 := vertex_mem_boundary hv
  have hjle : |v j| ≤ 1 := by
    rw [← hvb]
    fin_cases j <;> simp [maxAbs]
  have hjabs : |v j| = 1 := by
    apply le_antisymm hjle
    by_contra hn
    have hall : ∀ r : Fin 3, |v r| < 1 := by
      intro r
      by_cases hr : r = j
      · subst r; exact lt_of_not_ge hn
      · exact hother r hr
    have hm : maxAbs v < 1 := max_lt (hall 0) (max_lt (hall 1) (hall 2))
    linarith
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hjabs with hj | hj
  · linarith
  · exact hj

/-- The edge midpoint advances the moving coordinate by half a mesh. -/
noncomputable def edgeMidpoint (h : ℝ) (v : Ambient) (j : Fin 3) : Ambient :=
  v + ((1 / 2 : ℝ) * h) • EuclideanSpace.single j 1

/-- The parameter one half places the midpoint on the edge. -/
theorem edgeMidpoint_mem (h : ℝ) (v : Ambient) (j : Fin 3) :
    edgeMidpoint h v j ∈ edgeGeom h v j := by
  rw [edgeGeom]
  rw [segment_eq_image']
  refine ⟨1 / 2, by norm_num, ?_⟩
  simp [edgeMidpoint, smul_smul]

/-- The half-mesh step from minus one makes every midpoint coordinate strictly interior. -/
theorem edge_midpoint_all_abs_lt {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v : Ambient} {j : Fin 3}
    (hv : v ∈ vertices N h) (hvj : v j ≤ 1 - h)
    (hother : ∀ i : Fin 3, i ≠ j → |v i| < 1) :
    ∀ r : Fin 3, |edgeMidpoint h v j r| < 1 := by
  have hj := edge_no_other_saturated_forces_moving_neg_one hN hh hv hvj hother
  have hm := mesh_identities N h hN hh
  intro r
  rw [edgeMidpoint, edge_coordinate_formula]
  split_ifs with hr
  · rw [hj, abs_lt]
    constructor <;> linarith [hm.1, hm.2.2]
  · exact hother r hr

/-- Three strictly interior absolute coordinates have maximum below one. -/
theorem all_abs_lt_not_boundary {x : Ambient} (hall : ∀ r : Fin 3, |x r| < 1) :
    x ∉ boundary := by
  intro hx
  have hm : maxAbs x < 1 := max_lt (hall 0) (max_lt (hall 1) (hall 2))
  change maxAbs x = 1 at hx
  linarith

/-- Edge containment is equivalent to saturation of a fixed coordinate. -/
theorem edge_subset_boundary_iff {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v : Ambient} {j : Fin 3}
    (hv : v ∈ vertices N h) (hvj : v j ≤ 1 - h) :
    edgeGeom h v j ⊆ boundary ↔ ∃ i : Fin 3, i ≠ j ∧ |v i| = 1 := by
  constructor
  · intro hsub
    by_contra hn
    have hother : ∀ i : Fin 3, i ≠ j → |v i| < 1 := by
      intro i hij
      have hne : |v i| ≠ 1 := fun hi => hn ⟨i, hij, hi⟩
      have hle : |v i| ≤ 1 := by
        rw [← (show maxAbs v = 1 from hv.2)]
        fin_cases i <;> simp [maxAbs]
      exact lt_of_le_of_ne hle hne
    exact all_abs_lt_not_boundary (edge_midpoint_all_abs_lt hN hh hv hvj hother)
      (hsub (edgeMidpoint_mem h v j))
  · rintro ⟨i, hij, hi⟩
    exact edge_saturated_coordinate_suffices hN hh hv hvj hij hi

/-- A saturated remaining coordinate keeps every square point on the boundary. -/
theorem square_saturated_remaining_suffices {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v : Ambient} {j k i : Fin 3}
    (hv : v ∈ vertices N h) (hjk : j < k)
    (hvj : v j ≤ 1 - h) (hvk : v k ≤ 1 - h) (hij : i ≠ j) (hik : i ≠ k)
    (hi : |v i| = 1) : squareGeom h v j k ⊆ boundary := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := square_parameter_extract hx
  have hp := (mesh_identities N h hN hh).1
  have hall : ∀ r, |(v + (a * h) • EuclideanSpace.single j 1 +
      (b * h) • EuclideanSpace.single k 1 : Ambient) r| ≤ 1 := by
    intro r
    rw [square_coordinate_formula h a b v j k r (ne_of_lt hjk)]
    split_ifs with hrj hrk
    · have hvb := lattice_subset_interval hN hh (hv.1 j)
      rw [abs_le]
      constructor <;> nlinarith [hvb.1, ha.2, mul_nonneg ha.1 hp.le]
    · have hvb := lattice_subset_interval hN hh (hv.1 k)
      rw [abs_le]
      constructor <;> nlinarith [hvb.1, hb.2, mul_nonneg hb.1 hp.le]
    · exact abs_le.mpr (lattice_subset_interval hN hh (hv.1 r))
  have hfixed : |(v + (a * h) • EuclideanSpace.single j 1 +
      (b * h) • EuclideanSpace.single k 1 : Ambient) i| = 1 := by
    rw [square_coordinate_formula h a b v j k i (ne_of_lt hjk), if_neg hij, if_neg hik, hi]
  change maxAbs _ = 1
  apply le_antisymm (max_le (hall 0) (max_le (hall 1) (hall 2)))
  calc
    1 = |(v + (a * h) • EuclideanSpace.single j 1 +
        (b * h) • EuclideanSpace.single k 1 : Ambient) i| := hfixed.symm
    _ ≤ maxAbs _ := by fin_cases i <;> simp [maxAbs]

/-- Vertex data, ordered directions, room bounds and containment form a square parameter. -/
theorem squareParamOfContainment {N : ℕ} {h : ℝ} {v : Ambient} {j k : Fin 3}
    (hv : v ∈ vertices N h) (hjk : j < k) (hvj : v j ≤ 1 - h)
    (hvk : v k ≤ 1 - h) (hsub : squareGeom h v j k ⊆ boundary) :
    SquareParam N h v j k := ⟨hv, hjk, hvj, hvk, hsub⟩

/-- The boundary midpoint forces saturation of the unchanged remaining coordinate. -/
theorem square_containment_forces_remaining_abs {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v : Ambient} {j k i : Fin 3}
    (hv : v ∈ vertices N h) (hjk : j < k) (hvj : v j ≤ 1 - h)
    (hvk : v k ≤ 1 - h) (hij : i ≠ j) (hik : i ≠ k)
    (hsub : squareGeom h v j k ⊆ boundary) : |v i| = 1 := by
  exact (square_midpoint_remaining_abs (mesh_pos hN hh)
    (squareParamOfContainment hv hjk hvj hvk hsub) hij hik).2.2

/-- For `N > 0`, `h = 2 / N`, a vertex `v`, directions `j < k` with `v j ≤ 1 - h`, `v k ≤ 1 - h` and
the third index `i`, the square `squareGeom h v j k` lies in the boundary iff `|v i| = 1`. -/
public theorem square_subset_boundary_iff {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v : Ambient} {j k i : Fin 3}
    (hv : v ∈ vertices N h) (hjk : j < k) (hvj : v j ≤ 1 - h)
    (hvk : v k ≤ 1 - h) (hij : i ≠ j) (hik : i ≠ k) :
    squareGeom h v j k ⊆ boundary ↔ |v i| = 1 :=
  ⟨square_containment_forces_remaining_abs hN hh hv hjk hvj hvk hij hik,
    square_saturated_remaining_suffices hN hh hv hjk hvj hvk hij hik⟩

/-- Divide a coordinate displacement by the mesh to recover its closed parameter. -/
noncomputable def closedParameter (h : ℝ) (v x : Ambient) (j : Fin 3) : ℝ :=
  (x j - v j) / h

/-- A coordinate in the closed mesh interval has parameter between zero and one. -/
theorem closedParameter_mem_Icc {h : ℝ} (hh : 0 < h) {v x : Ambient} {j : Fin 3}
    (hx : x j ∈ Set.Icc (v j) (v j + h)) : closedParameter h v x j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hh)
  · rw [closedParameter, div_le_one hh]
    linarith [hx.2]

/-- Multiplying the recovered closed parameter by the mesh reconstructs the coordinate. -/
theorem closedParameter_reconstruct {h : ℝ} (hh : 0 < h) {v x : Ambient} {j : Fin 3} :
    v j + closedParameter h v x j * h = x j := by
  rw [closedParameter, div_mul_cancel₀ _ (ne_of_gt hh)]
  ring

/-- Equality at three exhaustive coordinates gives equality of ambient points. -/
public theorem Ambient_ext_of_three {x y : Ambient} {i j k : Fin 3}
    (hexhaust : ∀ r : Fin 3, r = i ∨ r = j ∨ r = k)
    (hi : x i = y i) (hj : x j = y j) (hk : x k = y k) : x = y := by
  ext r
  rcases hexhaust r with rfl | rfl | rfl
  · exact hi
  · exact hj
  · exact hk

/-- The two ordered directions and their remaining index exhaust the three coordinates. -/
public theorem square_indices_exhaust {i j k : Fin 3} (hjk : j < k)
    (hij : i ≠ j) (hik : i ≠ k) :
    ∀ r : Fin 3, r = i ∨ r = j ∨ r = k := by
  intro r
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases r <;> omega

/-- The closed square is exactly the rectangle with one fixed and two interval coordinates. -/
public theorem square_closed_coordinate_rectangle {h : ℝ} (hh : 0 < h)
    {v : Ambient} {j k i : Fin 3} (hjk : j < k) (hij : i ≠ j) (hik : i ≠ k) :
    squareGeom h v j k =
      {x : Ambient | x i = v i ∧ x j ∈ Set.Icc (v j) (v j + h) ∧
        x k ∈ Set.Icc (v k) (v k + h)} := by
  have hjne := ne_of_lt hjk
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := square_parameter_extract hx
    change _ = _ ∧ _ ∈ Set.Icc _ _ ∧ _ ∈ Set.Icc _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [square_coordinate_formula h a b v j k i hjne, if_neg hij, if_neg hik]
    · rw [square_coordinate_formula h a b v j k j hjne, if_pos rfl]
      constructor <;> nlinarith [ha.1, ha.2]
    · rw [square_coordinate_formula h a b v j k k hjne, if_neg (Ne.symm hjne), if_pos rfl]
      constructor <;> nlinarith [hb.1, hb.2]
  · rintro ⟨hxi, hxj, hxk⟩
    refine ⟨closedParameter h v x j, closedParameter_mem_Icc hh hxj,
      closedParameter h v x k, closedParameter_mem_Icc hh hxk, ?_⟩
    apply Ambient_ext_of_three (square_indices_exhaust hjk hij hik)
    · rw [square_coordinate_formula h _ _ v j k i hjne, if_neg hij, if_neg hik]
      exact hxi
    · rw [square_coordinate_formula h _ _ v j k j hjne, if_pos rfl]
      exact (closedParameter_reconstruct hh).symm
    · rw [square_coordinate_formula h _ _ v j k k hjne, if_neg (Ne.symm hjne), if_pos rfl]
      exact (closedParameter_reconstruct hh).symm

/-- Divide an interior coordinate displacement by the mesh to recover its open parameter. -/
noncomputable def openParameter (h : ℝ) (v x : Ambient) (j : Fin 3) : ℝ :=
  (x j - v j) / h

/-- An interior mesh coordinate has parameter strictly between zero and one. -/
theorem openParameter_mem_Ioo {h : ℝ} (hh : 0 < h) {v x : Ambient} {j : Fin 3}
    (hx : x j ∈ Set.Ioo (v j) (v j + h)) : openParameter h v x j ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact div_pos (sub_pos.mpr hx.1) hh
  · rw [openParameter, div_lt_one hh]
    linarith [hx.2]

/-- Multiplying the recovered open parameter by the mesh reconstructs the coordinate. -/
theorem openParameter_reconstruct {h : ℝ} (hh : 0 < h) {v x : Ambient} {j : Fin 3} :
    v j + openParameter h v x j * h = x j := by
  rw [openParameter, div_mul_cancel₀ _ (ne_of_gt hh)]
  ring

/-- The open square is exactly the rectangle with two strict interval coordinates. -/
theorem square_open_coordinate_rectangle {h : ℝ} (hh : 0 < h)
    {v : Ambient} {j k i : Fin 3} (hjk : j < k) (hij : i ≠ j) (hik : i ≠ k) :
    squareOpenGeom h v j k =
      {x : Ambient | x i = v i ∧ x j ∈ Set.Ioo (v j) (v j + h) ∧
        x k ∈ Set.Ioo (v k) (v k + h)} := by
  have hjne := ne_of_lt hjk
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    change _ = _ ∧ _ ∈ Set.Ioo _ _ ∧ _ ∈ Set.Ioo _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [square_coordinate_formula h a b v j k i hjne, if_neg hij, if_neg hik]
    · rw [square_coordinate_formula h a b v j k j hjne, if_pos rfl]
      constructor <;> nlinarith [ha.1, ha.2]
    · rw [square_coordinate_formula h a b v j k k hjne, if_neg (Ne.symm hjne), if_pos rfl]
      constructor <;> nlinarith [hb.1, hb.2]
  · rintro ⟨hxi, hxj, hxk⟩
    refine ⟨openParameter h v x j, openParameter_mem_Ioo hh hxj,
      openParameter h v x k, openParameter_mem_Ioo hh hxk, ?_⟩
    apply Ambient_ext_of_three (square_indices_exhaust hjk hij hik)
    · rw [square_coordinate_formula h _ _ v j k i hjne, if_neg hij, if_neg hik]
      exact hxi
    · rw [square_coordinate_formula h _ _ v j k j hjne, if_pos rfl]
      exact (openParameter_reconstruct hh).symm
    · rw [square_coordinate_formula h _ _ v j k k hjne, if_neg (Ne.symm hjne), if_pos rfl]
      exact (openParameter_reconstruct hh).symm

/-- Each admissible square has closed and relative-open coordinate rectangles in a fixed signed face. -/
public theorem square_coordinate_description {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {s : Set Ambient} (hs : s ∈ squares N h) :
    ∃ (v : Ambient) (j k i : Fin 3),
      v ∈ vertices N h ∧ j < k ∧ v j ≤ 1 - h ∧ v k ≤ 1 - h ∧
      i ≠ j ∧ i ≠ k ∧ |v i| = 1 ∧
      s = {x : Ambient | x i = v i ∧ x j ∈ Set.Icc (v j) (v j + h) ∧
        x k ∈ Set.Icc (v k) (v k + h)} ∧
      squareRelInterior N h ⟨s, hs⟩ =
        {x : Ambient | x i = v i ∧ x j ∈ Set.Ioo (v j) (v j + h) ∧
          x k ∈ Set.Ioo (v k) (v k + h)} ∧
      ∃ σ : {r : ℝ // r = -1 ∨ r = 1}, σ.1 = v i ∧ s ⊆ face i σ := by
  obtain ⟨v, j, k, hv, hjk, hvj, hvk, hsub, hsgeom, _hopen⟩ := square_presentation hN hh hs
  obtain ⟨i, ⟨hij, hik⟩, _hunique⟩ := square_remaining_index hjk
  have hp : SquareParam N h v j k := ⟨hv, hjk, hvj, hvk, hsub⟩
  have hpos := mesh_pos hN hh
  refine ⟨v, j, k, i, hv, hjk, hvj, hvk, hij, hik,
    (square_subset_boundary_iff hN hh hv hjk hvj hvk hij hik).mp hsub,
    hsgeom.trans (square_closed_coordinate_rectangle hpos hjk hij hik),
    (square_relInterior_coherent hN hh ⟨s, hs⟩ hp hsgeom).trans
      (square_open_coordinate_rectangle hpos hjk hij hik), ?_⟩
  obtain ⟨σ, hσ, hface⟩ := square_face_sign_and_containment hpos hp hij hik
  exact ⟨σ, hσ, hsgeom ▸ hface⟩

end TopologicalSpace.CubeBoundaryThree
