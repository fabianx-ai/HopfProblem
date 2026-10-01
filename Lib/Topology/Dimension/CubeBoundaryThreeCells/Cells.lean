module

public import Lib.Topology.Dimension.CubeBoundaryThreeCells.Lattice

/-!
# Vertices, edges and squares of the subdivided boundary of the three-cube

The mesh-`h` subdivision of `∂[-1,1]³ ⊆ ℝ³` (`h = 2 / N`) has three families of cells:

* `vertices N h`: boundary points all of whose coordinates are mesh lattice points;
* `edges N h`: segments `[v, v + h e_j]` from a vertex `v` with `v j ≤ 1 - h` lying in the boundary;
* `squares N h`: squares `v + [0, h] e_j + [0, h] e_k`, `j < k`, from a vertex with room in both
  directions, lying in the boundary.

For positive mesh a cell determines its presentation: the initial vertex is the unique
coordinatewise lower corner of the cell, and the directions are the coordinates that vary on it.
Hence the relative interior `squareRelInterior` of a square and the endpoint set `edgeEndpoints`
of an edge, defined through a chosen presentation, agree with the ones of every presentation.
Each of the three families is finite, and the endpoints of an edge are vertices.

## References

* R. Engelking, *Dimension Theory*, §1.8
* W. Hurewicz and H. Wallman, *Dimension Theory*, Chapter IV
-/

set_option warningAsError true
set_option autoImplicit false

open Set

namespace TopologicalSpace.CubeBoundaryThree

/-- A vertex parameter has three lattice coordinates and lies on the cube boundary. -/
@[expose] public def VertexParam (N : ℕ) (h : ℝ) (v : Ambient) : Prop :=
  (∀ i, v i ∈ lattice N h) ∧ v ∈ boundary
/-- The vertices of the mesh-`h` subdivision of the cube boundary: boundary points all of whose
coordinates lie in `lattice N h`. -/
@[expose] public def vertices (N : ℕ) (h : ℝ) : Set Ambient := {v | VertexParam N h v}
/-- Every mesh vertex lies on the cube boundary. -/
public theorem vertex_mem_boundary {N : ℕ} {h : ℝ} {v : Ambient}
    (hv : v ∈ vertices N h) : v ∈ boundary := hv.2
/-- An edge is the segment from `v` to `v+h e_j`. -/
@[expose] public def edgeGeom (h : ℝ) (v : Ambient) (j : Fin 3) : Set Ambient :=
  segment ℝ v (v + h • EuclideanSpace.single j 1)
/-- An admissible edge starts at a vertex, has room for one mesh step in direction `j`, and stays in the boundary. -/
@[expose] public def EdgeParam (N : ℕ) (h : ℝ) (v : Ambient) (j : Fin 3) : Prop :=
  v ∈ vertices N h ∧ v j ≤ 1 - h ∧ edgeGeom h v j ⊆ boundary
/-- The edge family is the collection of geometric segments arising from admissible edge parameters. -/
public def edges (N : ℕ) (h : ℝ) : Set (Set Ambient) :=
  {e | ∃ v j, EdgeParam N h v j ∧ e = edgeGeom h v j}
/-- Membership in the edge family is exactly presentation by an admissible initial vertex and direction. -/
public theorem edge_mem_iff {N : ℕ} {h : ℝ} {e : Set Ambient} :
    e ∈ edges N h ↔ ∃ v j, EdgeParam N h v j ∧ e = edgeGeom h v j := Iff.rfl
/-- A closed square independently moves from `v` through one mesh step in directions `j` and `k`. -/
@[expose] public def squareGeom (h : ℝ) (v : Ambient) (j k : Fin 3) : Set Ambient :=
  {x | ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
    x = v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1}
/-- The relative-open square uses the same parametrization with both parameters strictly between zero and one. -/
@[expose] public def squareOpenGeom (h : ℝ) (v : Ambient) (j k : Fin 3) : Set Ambient :=
  {x | ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ b ∈ Set.Ioo (0 : ℝ) 1,
    x = v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1}
/-- An admissible square has ordered distinct directions, a vertex start, upper bounds in both directions, and boundary containment. -/
@[expose] public def SquareParam (N : ℕ) (h : ℝ) (v : Ambient) (j k : Fin 3) : Prop :=
  v ∈ vertices N h ∧ j < k ∧ v j ≤ 1 - h ∧ v k ≤ 1 - h ∧ squareGeom h v j k ⊆ boundary
/-- The square family collects the closed images of all admissible square parameters. -/
@[expose] public def squares (N : ℕ) (h : ℝ) : Set (Set Ambient) :=
  {s | ∃ v j k, SquareParam N h v j k ∧ s = squareGeom h v j k}
/-- A lower corner belongs to the set and is coordinatewise below every point of it. -/
def coordinateLowerCorner (C : Set Ambient) (v : Ambient) : Prop :=
  v ∈ C ∧ ∀ r x, x ∈ C → v r ≤ x r
/-- A coordinate is nonconstant exactly when two points of the set have different values there. -/
@[expose] public def coordinateNonconstant (C : Set Ambient) (r : Fin 3) : Prop :=
  ∃ x ∈ C, ∃ y ∈ C, x r ≠ y r
/-- Two coordinatewise lower corners bound one another, hence agree in every coordinate and are equal. -/
theorem coordinateLowerCorner_unique {C : Set Ambient} {v w : Ambient}
  (hv : coordinateLowerCorner C v) (hw : coordinateLowerCorner C w) : v = w := by
  ext r
  exact le_antisymm (hv.2 r w hw.1) (hw.2 r v hv.1)
/-- Along an edge only coordinate `j` changes, by the amount `t h`. -/
public theorem edge_coordinate_formula (h t : ℝ) (v : Ambient) (j r : Fin 3) :
  (v + (t * h) • EuclideanSpace.single j 1 : Ambient) r =
    if r = j then v j + t * h else v r := by
  split_ifs with hr
  · subst r; simp
  · simp [hr]
/-- The parameter value zero places the initial point `v` on its edge. -/
theorem edge_zero_mem (h : ℝ) (v : Ambient) (j : Fin 3) : v ∈ edgeGeom h v j := by
  rw [edgeGeom]
  exact left_mem_segment ℝ v _
/-- Every point of the segment has the affine form `v+(t h)e_j` with `0≤t≤1`. -/
public theorem edge_parameter_extract {h : ℝ} {v : Ambient} {j : Fin 3} {x : Ambient}
  (hx : x ∈ edgeGeom h v j) : ∃ t ∈ Set.Icc (0 : ℝ) 1,
    x = v + (t * h) • EuclideanSpace.single j 1 := by
  rw [edgeGeom, segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t, ht, by module⟩
/-- Nonnegative mesh and segment parameter make the initial point a coordinatewise lower corner. -/
theorem edge_initial_lowerCorner {h : ℝ} (hh : 0 ≤ h) (v : Ambient) (j : Fin 3) :
  coordinateLowerCorner (edgeGeom h v j) v := by
  refine ⟨edge_zero_mem h v j, ?_⟩
  intro r x hx
  obtain ⟨t, ht, rfl⟩ := edge_parameter_extract hx
  rw [edge_coordinate_formula]
  split_ifs with hr
  · subst r
    exact le_add_of_nonneg_right (mul_nonneg ht.1 hh)
  · exact le_rfl
/-- On a square, coordinates `j` and `k` change independently by `a h` and `b h`. -/
public theorem square_coordinate_formula (h a b : ℝ) (v : Ambient) (j k r : Fin 3) (hjk : j ≠ k) :
  (v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1 : Ambient) r =
    if r = j then v j + a * h else if r = k then v k + b * h else v r := by
  by_cases hrj : r = j
  · subst r
    simp [hjk]
  · by_cases hrk : r = k
    · subst r
      simp [hrj]
    · simp [hrj, hrk]
/-- Parameters `(0,0)` place the initial point `v` in the square. -/
public theorem square_zero_mem (h : ℝ) (v : Ambient) (j k : Fin 3) : v ∈ squareGeom h v j k := by
  exact ⟨0, by simp, 0, by simp, by simp⟩
/-- Parameters `(1,0)` place the first adjacent corner `v+h e_j` in the square. -/
theorem square_first_corner_mem (h : ℝ) (v : Ambient) (j k : Fin 3) :
  v + h • EuclideanSpace.single j 1 ∈ squareGeom h v j k := by
  refine ⟨1, by simp, 0, by simp, ?_⟩
  module
/-- Parameters `(0,1)` place the second adjacent corner `v+h e_k` in the square. -/
theorem square_second_corner_mem (h : ℝ) (v : Ambient) (j k : Fin 3) :
  v + h • EuclideanSpace.single k 1 ∈ squareGeom h v j k := by
  refine ⟨0, by simp, 1, by simp, ?_⟩
  module
/-- Every square point has parameters `a,b∈[0,1]` in the defining affine formula. -/
public theorem square_parameter_extract {h : ℝ} {v : Ambient} {j k : Fin 3} {x : Ambient}
  (hx : x ∈ squareGeom h v j k) : ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
    x = v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1 := hx
/-- Nonnegative mesh and square parameters make `v` a coordinatewise lower corner. -/
theorem square_initial_lowerCorner {h : ℝ} (hh : 0 ≤ h) {v : Ambient} {j k : Fin 3} (hjk : j < k) :
  coordinateLowerCorner (squareGeom h v j k) v := by
  refine ⟨square_zero_mem h v j k, ?_⟩
  intro r x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := square_parameter_extract hx
  rw [square_coordinate_formula h a b v j k r (ne_of_lt hjk)]
  split_ifs with hrj hrk
  · subst r
    exact le_add_of_nonneg_right (mul_nonneg ha.1 hh)
  · subst r
    exact le_add_of_nonneg_right (mul_nonneg hb.1 hh)
  · exact le_rfl
/-- The initial vertex attains every coordinate minimum on a nonnegative-mesh edge. -/
theorem edge_coordinate_minima_attained {h : ℝ} (hh : 0 ≤ h) (v : Ambient) (j r : Fin 3) :
  v ∈ edgeGeom h v j ∧ (∀ x ∈ edgeGeom h v j, v r ≤ x r) :=
  ⟨(edge_initial_lowerCorner hh v j).1, (edge_initial_lowerCorner hh v j).2 r⟩
/-- The initial vertex attains every coordinate minimum on a nonnegative-mesh square. -/
theorem square_coordinate_minima_attained {h : ℝ} (hh : 0 ≤ h) {v : Ambient} {j k : Fin 3}
  (hjk : j < k) (r : Fin 3) : v ∈ squareGeom h v j k ∧ (∀ x ∈ squareGeom h v j k, v r ≤ x r) :=
  ⟨(square_initial_lowerCorner hh hjk).1, (square_initial_lowerCorner hh hjk).2 r⟩
/-- Equal nonnegative-mesh edges have the same unique coordinatewise lower corner. -/
theorem edge_initial_eq_of_set_eq {h : ℝ} (hh : 0 ≤ h) {v w : Ambient} {j l : Fin 3}
  (heq : edgeGeom h v j = edgeGeom h w l) : v = w := by
  apply coordinateLowerCorner_unique (C := edgeGeom h v j)
  · exact edge_initial_lowerCorner hh v j
  · rw [heq]
    exact edge_initial_lowerCorner hh w l
/-- Equal ordered nonnegative-mesh squares have the same unique coordinatewise lower corner. -/
theorem square_initial_eq_of_set_eq {h : ℝ} (hh : 0 ≤ h) {v w : Ambient} {j k p q : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q) : v = w := by
  apply coordinateLowerCorner_unique (C := squareGeom h v j k)
  · exact square_initial_lowerCorner hh hjk
  · rw [heq]
    exact square_initial_lowerCorner hh hpq
/-- Parameter one places the terminal point `v+h e_j` on the edge. -/
theorem edge_terminal_mem (h : ℝ) (v : Ambient) (j : Fin 3) :
  v + h • EuclideanSpace.single j 1 ∈ edgeGeom h v j := by
  rw [edgeGeom]
  exact right_mem_segment ℝ _ _
/-- After equal positive edges share their initial point, terminal-coordinate variation forces their directions to agree. -/
theorem edge_direction_eq_of_set_eq {h : ℝ} (hh : 0 < h) {v w : Ambient} {j l : Fin 3}
  (heq : edgeGeom h v j = edgeGeom h w l) : j = l := by
  have hvw := edge_initial_eq_of_set_eq (le_of_lt hh) heq
  subst w
  by_contra hjl
  have hx : v + h • EuclideanSpace.single j 1 ∈ edgeGeom h v l := by
    rw [← heq]
    exact edge_terminal_mem h v j
  obtain ⟨t, ht, hxt⟩ := edge_parameter_extract hx
  have hc := congrArg (fun x : Ambient => x j) hxt
  simp [hjl] at hc
  linarith
/-- Admissible presentations of the same positive edge have identical starts and directions. -/
theorem edge_presentation_unique {N : ℕ} {h : ℝ} (hh : 0 < h) {e : Set Ambient}
  {v w : Ambient} {j l : Fin 3} (hp : EdgeParam N h v j) (he : e = edgeGeom h v j)
  (hp' : EdgeParam N h w l) (he' : e = edgeGeom h w l) : v = w ∧ j = l := by
  have _ := hp.1
  have _ := hp'.1
  have hgeom : edgeGeom h v j = edgeGeom h w l := he.symm.trans he'
  exact ⟨edge_initial_eq_of_set_eq (le_of_lt hh) hgeom, edge_direction_eq_of_set_eq hh hgeom⟩
/-- For positive mesh, an edge varies in exactly its defining coordinate `j`. -/
theorem edge_nonconstant_coordinates {h : ℝ} (hh : 0 < h) (v : Ambient) (j r : Fin 3) :
  coordinateNonconstant (edgeGeom h v j) r ↔ r = j := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    by_contra hrj
    obtain ⟨a, ha, rfl⟩ := edge_parameter_extract hx
    obtain ⟨b, hb, rfl⟩ := edge_parameter_extract hy
    simp [hrj] at hxy
  · intro hr
    subst r
    refine ⟨v, edge_zero_mem h v j, v + h • EuclideanSpace.single j 1,
      edge_terminal_mem h v j, ?_⟩
    simpa using ne_of_gt hh
/-- Equality of positive square images forces each source moving direction to be one of the target directions. -/
theorem square_directions_mem_of_set_eq {h : ℝ} (hh : 0 < h) {v w : Ambient} {j k p q : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q) :
  (j = p ∨ j = q) ∧ (k = p ∨ k = q) := by
  have hvw := square_initial_eq_of_set_eq (le_of_lt hh) hjk hpq heq
  subst w
  constructor
  · by_contra hn
    push Not at hn
    have hx : v + h • EuclideanSpace.single j 1 ∈ squareGeom h v p q := by
      rw [← heq]
      exact square_first_corner_mem h v j k
    obtain ⟨a, ha, b, hb, hxab⟩ := square_parameter_extract hx
    have hc := congrArg (fun x : Ambient => x j) hxab
    simp [hn.1, hn.2] at hc
    linarith
  · by_contra hn
    push Not at hn
    have hx : v + h • EuclideanSpace.single k 1 ∈ squareGeom h v p q := by
      rw [← heq]
      exact square_second_corner_mem h v j k
    obtain ⟨a, ha, b, hb, hxab⟩ := square_parameter_extract hx
    have hc := congrArg (fun x : Ambient => x k) hxab
    simp [hn.1, hn.2] at hc
    linarith
/-- Two increasing pairs with the same two members agree coordinate by coordinate. -/
theorem square_ordered_directions_eq {j k p q : Fin 3} (hjk : j < k) (hpq : p < q)
  (hj : j = p ∨ j = q) (hk : k = p ∨ k = q) : j = p ∧ k = q := by
  omega
/-- Admissible presentations of the same positive square have identical starts and ordered directions. -/
theorem square_presentation_unique {N : ℕ} {h : ℝ} (hh : 0 < h) {s : Set Ambient}
  {v w : Ambient} {j k p q : Fin 3} (hp : SquareParam N h v j k) (hs : s = squareGeom h v j k)
  (hp' : SquareParam N h w p q) (hs' : s = squareGeom h w p q) : v = w ∧ j = p ∧ k = q := by
  have heq := hs.symm.trans hs'
  have hvw := square_initial_eq_of_set_eq (le_of_lt hh) hp.2.1 hp'.2.1 heq
  have hd := square_directions_mem_of_set_eq hh hp.2.1 hp'.2.1 heq
  exact ⟨hvw, square_ordered_directions_eq hp.2.1 hp'.2.1 hd.1 hd.2⟩
/-- For positive mesh, a square varies in exactly its two defining coordinates `j` and `k`. -/
public theorem square_nonconstant_coordinates {h : ℝ} (hh : 0 < h) {v : Ambient} {j k : Fin 3}
  (hjk : j < k) (r : Fin 3) : coordinateNonconstant (squareGeom h v j k) r ↔ r = j ∨ r = k := by
  have _ := hjk
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    by_contra hr
    push Not at hr
    obtain ⟨a, ha, b, hb, rfl⟩ := square_parameter_extract hx
    obtain ⟨c, hc, d, hd, rfl⟩ := square_parameter_extract hy
    simp [hr.1, hr.2] at hxy
  · intro hr
    rcases hr with hr | hr
    · rw [hr]
      refine ⟨v, square_zero_mem h v j k, v + h • EuclideanSpace.single j 1,
        square_first_corner_mem h v j k, ?_⟩
      simpa using ne_of_gt hh
    · rw [hr]
      refine ⟨v, square_zero_mem h v j k, v + h • EuclideanSpace.single k 1,
        square_second_corner_mem h v j k, ?_⟩
      simpa using ne_of_gt hh
/-- Equality of sets transports the existence of two points differing in a chosen coordinate. -/
theorem coordinate_variation_of_set_eq {C D : Set Ambient} (hCD : C = D) (r : Fin 3) :
  coordinateNonconstant C r ↔ coordinateNonconstant D r := by subst D; rfl
/-- Equality of sets transports the assertion that a chosen coordinate has a fixed value. -/
theorem coordinate_constant_value_transport {C D : Set Ambient} (hCD : C = D)
  (r : Fin 3) (c : ℝ) : (∀ x ∈ C, x r = c) ↔ (∀ x ∈ D, x r = c) := by subst D; rfl
/-- Equal two-element direction sets with increasing enumerations have the same ordered pair. -/
theorem increasing_pair_eq_of_direction_set_eq {j k p q : Fin 3} (hjk : j < k) (hpq : p < q)
  (hset : ({j, k} : Set (Fin 3)) = {p, q}) : j = p ∧ k = q := by
  apply square_ordered_directions_eq hjk hpq
  · have : j ∈ ({p, q} : Set (Fin 3)) := by rw [← hset]; simp
    simpa using this
  · have : k ∈ ({p, q} : Set (Fin 3)) := by rw [← hset]; simp
    simpa using this
/-- Equal positive edge presentations determine the same unordered pair of endpoints. -/
theorem edge_endpoints_coherent {h : ℝ} (hh : 0 < h) {v w : Ambient} {j l : Fin 3}
  (heq : edgeGeom h v j = edgeGeom h w l) :
  ({v, v + h • EuclideanSpace.single j 1} : Set Ambient) = {w, w + h • EuclideanSpace.single l 1} := by
  rw [edge_initial_eq_of_set_eq (le_of_lt hh) heq, edge_direction_eq_of_set_eq hh heq]
/-- Variation in the defining coordinate of a positive edge prevents its two endpoints from coinciding. -/
theorem edge_endpoints_distinct {h : ℝ} (hh : 0 < h) (v : Ambient) (j : Fin 3) :
  v ≠ v + h • EuclideanSpace.single j 1 := by
  have hvar : coordinateNonconstant (edgeGeom h v j) j :=
    (edge_nonconstant_coordinates hh v j j).2 rfl
  intro hend
  obtain ⟨x, hx, y, hy, hxy⟩ := hvar
  have hedge : edgeGeom h v j = {v} := by rw [edgeGeom, ← hend, segment_same]
  rw [hedge] at hx hy
  simp only [Set.mem_singleton_iff] at hx hy
  exact hxy (by rw [hx, hy])
/-- Uniqueness of positive square presentations makes the relative-open image independent of the chosen presentation. -/
theorem square_relInterior_coherent_raw {h : ℝ} (hh : 0 < h) {v w : Ambient} {j k p q : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q) :
  squareOpenGeom h v j k = squareOpenGeom h w p q := by
  have hvw := square_initial_eq_of_set_eq (le_of_lt hh) hjk hpq heq
  have hd := square_directions_mem_of_set_eq hh hjk hpq heq
  have hord := square_ordered_directions_eq hjk hpq hd.1 hd.2
  subst w
  rw [hord.1, hord.2]
/-- Two distinct coordinates of `Fin 3` leave a unique third coordinate. -/
public theorem square_remaining_index {j k : Fin 3} (hjk : j < k) :
  ∃! i : Fin 3, i ≠ j ∧ i ≠ k := by
  have hc : (j = 0 ∧ k = 1) ∨ (j = 0 ∧ k = 2) ∨ (j = 1 ∧ k = 2) := by omega
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨2, by decide, ?_⟩
    intro y hy
    fin_cases y <;> simp_all
  · refine ⟨1, by decide, ?_⟩
    intro y hy
    fin_cases y <;> simp_all
  · refine ⟨0, by decide, ?_⟩
    intro y hy
    fin_cases y <;> simp_all
/-- Enumerating the three increasing coordinate pairs identifies their respective remaining coordinates. -/
theorem square_remaining_index_cases {j k : Fin 3} (hjk : j < k) :
  (j = 0 ∧ k = 1 ∧ Classical.choose (square_remaining_index hjk) = 2) ∨
  (j = 0 ∧ k = 2 ∧ Classical.choose (square_remaining_index hjk) = 1) ∨
  (j = 1 ∧ k = 2 ∧ Classical.choose (square_remaining_index hjk) = 0) := by
  have hc : (j = 0 ∧ k = 1) ∨ (j = 0 ∧ k = 2) ∨ (j = 1 ∧ k = 2) := by omega
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    refine ⟨rfl, rfl, ?_⟩
    exact ((square_remaining_index (j := 0) (k := 1) (by decide)).unique (by decide)
      (Classical.choose_spec (square_remaining_index (j := 0) (k := 1) (by decide))).1).symm
  · right; left
    refine ⟨rfl, rfl, ?_⟩
    exact ((square_remaining_index (j := 0) (k := 2) (by decide)).unique (by decide)
      (Classical.choose_spec (square_remaining_index (j := 0) (k := 2) (by decide))).1).symm
  · right; right
    refine ⟨rfl, rfl, ?_⟩
    exact ((square_remaining_index (j := 1) (k := 2) (by decide)).unique (by decide)
      (Classical.choose_spec (square_remaining_index (j := 1) (k := 2) (by decide))).1).symm
/-- The coordinate outside `j,k` is unchanged at every point of the square. -/
public theorem square_remaining_coordinate {h : ℝ} {v : Ambient} {j k i : Fin 3}
  (hij : i ≠ j) (hik : i ≠ k) {x : Ambient} (hx : x ∈ squareGeom h v j k) : x i = v i := by
  obtain ⟨a, ha, b, hb, rfl⟩ := square_parameter_extract hx
  simp [hij, hik]
/-- Equal positive squares have the same remaining coordinate and the same constant value there. -/
theorem square_remaining_intrinsic {h : ℝ} (hh : 0 < h) {v w : Ambient} {j k p q i i' : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q)
  (hi : i ≠ j ∧ i ≠ k) (hi' : i' ≠ p ∧ i' ≠ q) : i = i' ∧ v i = w i' := by
  have hd := square_directions_mem_of_set_eq hh hjk hpq heq
  have hord := square_ordered_directions_eq hjk hpq hd.1 hd.2
  have hvw := square_initial_eq_of_set_eq (le_of_lt hh) hjk hpq heq
  have hii : i = i' := by
    apply (square_remaining_index hjk).unique hi
    rwa [← hord.1, ← hord.2] at hi'
  subst w
  subst i'
  exact ⟨rfl, rfl⟩
/-- Zero mesh collapses the edge, closed square, and relative-open square images to the singleton `{v}`. -/
theorem zero_mesh_images (v : Ambient) (j k : Fin 3) :
  edgeGeom 0 v j = {v} ∧ squareGeom 0 v j k = {v} ∧ squareOpenGeom 0 v j k = {v} := by
  constructor
  · rw [edgeGeom]
    simp
  constructor <;> ext x
  · constructor
    · rintro ⟨a, ha, b, hb, hx⟩
      simpa using hx
    · intro hx
      subst x
      exact ⟨0, by simp, 0, by simp, by simp⟩
  · constructor
    · rintro ⟨a, ha, b, hb, hx⟩
      simpa using hx
    · intro hx
      subst x
      exact ⟨1 / 2, by norm_num, 1 / 2, by norm_num, by simp⟩
/-- At zero mesh, distinct directions present the same collapsed edge. -/
theorem zero_mesh_edge_nonunique : ∃ (v : Ambient) (j l : Fin 3), j ≠ l ∧ edgeGeom 0 v j = edgeGeom 0 v l := by
  exact ⟨0, 0, 1, by decide, (zero_mesh_images 0 0 0).1.trans (zero_mesh_images 0 1 1).1.symm⟩
/-- At zero mesh, distinct ordered direction pairs present the same collapsed square. -/
theorem zero_mesh_square_nonunique : ∃ (v : Ambient) (j k p q : Fin 3),
  j < k ∧ p < q ∧ (j, k) ≠ (p, q) ∧ squareGeom 0 v j k = squareGeom 0 v p q := by
  exact ⟨0, 0, 1, 0, 2, by decide, by decide, by decide,
    (zero_mesh_images 0 0 1).2.1.trans (zero_mesh_images 0 0 2).2.1.symm⟩
/-- Swapping the two square parameters and commuting the displacements leaves both the closed and open images unchanged. -/
theorem square_parameter_swap (h : ℝ) (v : Ambient) (j k : Fin 3) :
  squareGeom h v j k = squareGeom h v k j ∧ squareOpenGeom h v j k = squareOpenGeom h v k j := by
  constructor <;> ext x <;> constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, by module⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, by module⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, by module⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, by module⟩
/-- For distinct directions, reversing an ordered pair produces a different pair. -/
theorem swapped_ordered_pair_ne {j k : Fin 3} (hjk : j ≠ k) : (j, k) ≠ (k, j) := by
  intro hp
  exact hjk (congrArg Prod.fst hp)
/-- Requiring increasing directions removes the swap ambiguity from square presentations. -/
theorem square_order_suffices {h : ℝ} (hh : 0 < h) {v w : Ambient} {j k p q : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q) : j = p ∧ k = q := by
  have hd := square_directions_mem_of_set_eq hh hjk hpq heq
  exact square_ordered_directions_eq hjk hpq hd.1 hd.2
/-- A shared positive edge has presentation data, direction, and endpoints independent of which incident face supplies it. -/
theorem shared_edge_presentation_identity {h : ℝ} (hh : 0 < h) {v w : Ambient} {j l : Fin 3}
  (heq : edgeGeom h v j = edgeGeom h w l) :
  v = w ∧ j = l ∧ ({v, v + h • EuclideanSpace.single j 1} : Set Ambient) = {w, w + h • EuclideanSpace.single l 1} :=
  ⟨edge_initial_eq_of_set_eq (le_of_lt hh) heq, edge_direction_eq_of_set_eq hh heq,
    edge_endpoints_coherent hh heq⟩
/-- The raw relative interior uses a chosen admissible presentation of the square. -/
noncomputable def squareRelInteriorRaw (N : ℕ) (h : ℝ) (s : {s : Set Ambient // s ∈ squares N h}) : Set Ambient :=
  squareOpenGeom h (Classical.choose s.property) (Classical.choose (Classical.choose_spec s.property))
    (Classical.choose (Classical.choose_spec (Classical.choose_spec s.property)))
/-- The relative interior of a mesh square `s`: the open square `squareOpenGeom h v j k` of a chosen
admissible presentation `(v, j, k)` of `s`; by `square_presentation` it is the open square of every
admissible presentation. -/
public noncomputable def squareRelInterior (N : ℕ) (h : ℝ) (s : {s : Set Ambient // s ∈ squares N h}) : Set Ambient := squareRelInteriorRaw N h s
/-- For `N > 0` and `h = 2 / N`, if `(v, j, k)` is an admissible presentation of the mesh square `s`,
then `squareRelInterior N h s = squareOpenGeom h v j k`. -/
public theorem square_relInterior_coherent {N : ℕ} {h : ℝ} (_hN : 0 < N) (_hh : h = 2 / (N : ℝ))
  (s : {s : Set Ambient // s ∈ squares N h}) {v : Ambient} {j k : Fin 3} (hp : SquareParam N h v j k)
  (hs : (s : Set Ambient) = squareGeom h v j k) : squareRelInterior N h s = squareOpenGeom h v j k := by
  let v' := Classical.choose s.property
  let j' := Classical.choose (Classical.choose_spec s.property)
  let k' := Classical.choose (Classical.choose_spec (Classical.choose_spec s.property))
  have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec s.property))
  simp only [squareRelInterior, squareRelInteriorRaw]
  exact square_relInterior_coherent_raw (mesh_pos _hN _hh) hspec.1.2.1 hp.2.1
    (hspec.2.symm.trans hs)
/-- For `N > 0` and `h = 2 / N`, every mesh square `s` has a presentation: a vertex `v` and
directions `j < k` with `v j ≤ 1 - h`, `v k ≤ 1 - h`, such that `s` is the closed square
`{v + (a h) e_j + (b h) e_k | a, b ∈ [0, 1]}`, this square lies in the boundary, and
`squareRelInterior N h s` is the same set with `a, b ∈ (0, 1)`. -/
public theorem square_presentation {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
  {s : Set Ambient} (hs : s ∈ squares N h) : ∃ (v : Ambient) (j k : Fin 3), v ∈ vertices N h ∧ j < k ∧
  v j ≤ 1-h ∧ v k ≤ 1-h ∧
  {x | ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
    x = v + (a*h) • EuclideanSpace.single j 1 + (b*h) • EuclideanSpace.single k 1} ⊆ boundary ∧
  s = {x | ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
    x = v + (a*h) • EuclideanSpace.single j 1 + (b*h) • EuclideanSpace.single k 1} ∧
  squareRelInterior N h ⟨s, hs⟩ = {x | ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ b ∈ Set.Ioo (0 : ℝ) 1,
    x = v + (a*h) • EuclideanSpace.single j 1 + (b*h) • EuclideanSpace.single k 1} := by
  let hs0 := hs
  obtain ⟨v, j, k, hp, heq⟩ := hs
  exact ⟨v, j, k, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, heq,
    square_relInterior_coherent hN hh ⟨s, hs0⟩ hp heq⟩
/-- The raw endpoint assignment uses the initial and terminal points of a chosen admissible edge presentation. -/
noncomputable def edgeEndpointsRaw (N : ℕ) (h : ℝ) (e : {e : Set Ambient // e ∈ edges N h}) : Set Ambient :=
  let v := Classical.choose e.property; let j := Classical.choose (Classical.choose_spec e.property); {v, v + h • EuclideanSpace.single j 1}
/-- The endpoint set `{v, v + h e_j}` of a mesh edge, for a chosen admissible presentation `(v, j)`;
by `edge_presentation` it is the endpoint set of every admissible presentation. -/
public noncomputable def edgeEndpoints (N : ℕ) (h : ℝ) (e : {e : Set Ambient // e ∈ edges N h}) : Set Ambient := edgeEndpointsRaw N h e
/-- For `N > 0` and `h = 2 / N`, every mesh edge `e` has a presentation: a vertex `v` and a
direction `j` with `v j ≤ 1 - h` such that `e` is the segment `[v, v + h e_j]`, this segment lies in
the boundary, and `edgeEndpoints N h e = {v, v + h e_j}`. -/
public theorem edge_presentation {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
  {e : Set Ambient} (he : e ∈ edges N h) : ∃ (v : Ambient) (j : Fin 3), v ∈ vertices N h ∧ v j ≤ 1-h ∧
  segment ℝ v (v + h • EuclideanSpace.single j 1) ⊆ boundary ∧ e = segment ℝ v (v + h • EuclideanSpace.single j 1) ∧
  edgeEndpoints N h ⟨e, he⟩ = {v, v + h • EuclideanSpace.single j 1} := by
  let he0 := he
  obtain ⟨v, j, hp, heq⟩ := he
  refine ⟨v, j, hp.1, hp.2.1, hp.2.2, heq, ?_⟩
  let v' := Classical.choose he0
  let j' := Classical.choose (Classical.choose_spec he0)
  have hspec := Classical.choose_spec (Classical.choose_spec he0)
  simp only [edgeEndpoints, edgeEndpointsRaw]
  exact edge_endpoints_coherent (mesh_pos hN hh) (hspec.2.symm.trans heq)
/-- A finite coordinatewise product transfers from ordinary functions to the ambient `WithLp` space. -/
theorem finite_Ambient_coordinate_bridge {A : Fin 3 → Set ℝ} (hA : ∀ i, (A i).Finite) :
  ({v : Ambient | ∀ i, v i ∈ A i}).Finite := by
  let T : Set (Fin 3 → ℝ) := {f | ∀ i, f i ∈ A i}
  have hT : T.Finite := Set.Finite.pi' hA
  have hEq : {v : Ambient | ∀ i, v i ∈ A i} = WithLp.toLp 2 '' T := by
    ext v
    constructor
    · intro hv; exact ⟨v.ofLp, hv, rfl⟩
    · rintro ⟨f, hf, rfl⟩; exact hf
  rw [hEq]
  exact hT.image (WithLp.toLp 2)
/-- The threefold product of the finite lattice is finite. -/
theorem finite_vertex_product (N : ℕ) (h : ℝ) :
  ({v : Ambient | ∀ i, v i ∈ lattice N h}).Finite :=
  finite_Ambient_coordinate_bridge (fun _ => finite_lattice N h)
/-- The set of mesh vertices is finite. -/
public theorem finite_vertices (N : ℕ) (h : ℝ) : (vertices N h).Finite := by
  apply (finite_vertex_product N h).subset
  intro v hv
  exact hv.1
/-- The edge-parameter set records admissible pairs of a vertex and a coordinate direction. -/
def edgeParamSet (N : ℕ) (h : ℝ) : Set (Ambient × Fin 3) := {p | EdgeParam N h p.1 p.2}
/-- Edge parameters form a subset of the finite product of vertices with `Fin 3`. -/
theorem finite_edge_parameters (N : ℕ) (h : ℝ) : (edgeParamSet N h).Finite := by
  apply ((finite_vertices N h).prod Set.finite_univ).subset
  rintro ⟨v, j⟩ hp
  exact ⟨hp.1, Set.mem_univ j⟩
/-- The edge family is the image of its finite parameter set under the segment construction. -/
theorem edges_eq_image (N : ℕ) (h : ℝ) :
  edges N h = (fun p : Ambient × Fin 3 => edgeGeom h p.1 p.2) '' edgeParamSet N h := by
  ext e
  constructor
  · rintro ⟨v, j, hp, rfl⟩; exact ⟨(v, j), hp, rfl⟩
  · rintro ⟨⟨v, j⟩, hp, rfl⟩; exact ⟨v, j, hp, rfl⟩
/-- The family of mesh edges is finite. -/
public theorem finite_edges (N : ℕ) (h : ℝ) : (edges N h).Finite := by
  rw [edges_eq_image]
  exact (finite_edge_parameters N h).image _
/-- The square-parameter set records admissible triples of a vertex and two directions. -/
def squareParamSet (N : ℕ) (h : ℝ) : Set (Ambient × Fin 3 × Fin 3) := {p | SquareParam N h p.1 p.2.1 p.2.2}
/-- Square parameters form a subset of the finite product of vertices with two copies of `Fin 3`. -/
theorem finite_square_parameters (N : ℕ) (h : ℝ) : (squareParamSet N h).Finite := by
  apply ((finite_vertices N h).prod (Set.finite_univ.prod Set.finite_univ)).subset
  rintro ⟨v, j, k⟩ hp
  exact ⟨hp.1, Set.mem_univ j, Set.mem_univ k⟩
/-- The square family is the image of its finite parameter set under the closed-square construction. -/
theorem squares_eq_image (N : ℕ) (h : ℝ) :
  squares N h = (fun p : Ambient × Fin 3 × Fin 3 => squareGeom h p.1 p.2.1 p.2.2) '' squareParamSet N h := by
  ext s
  constructor
  · rintro ⟨v, j, k, hp, rfl⟩; exact ⟨(v, j, k), hp, rfl⟩
  · rintro ⟨⟨v, j, k⟩, hp, rfl⟩; exact ⟨v, j, k, hp, rfl⟩
/-- The family of mesh squares is finite. -/
public theorem finite_squares (N : ℕ) (h : ℝ) : (squares N h).Finite := by
  rw [squares_eq_image]
  exact (finite_square_parameters N h).image _
/-- The terminal coordinate is the next lattice point, the other coordinates are unchanged, and boundary containment makes the terminal point a vertex. -/
theorem edge_terminal_is_vertex {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
  {v : Ambient} {j : Fin 3} (hp : EdgeParam N h v j) :
  v + h • EuclideanSpace.single j 1 ∈ vertices N h := by
  constructor
  · intro r
    by_cases hr : r = j
    · subst r
      simpa using lattice_successor hN hh (hp.1.1 j) hp.2.1
    · simpa [hr] using hp.1.1 r
  · exact hp.2.2 (edge_terminal_mem h v j)
/-- For `N > 0` and `h = 2 / N`, both endpoints of every mesh edge are mesh vertices. -/
public theorem edge_endpoints_vertices {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
  (e : {e : Set Ambient // e ∈ edges N h}) : edgeEndpoints N h e ⊆ vertices N h := by
  obtain ⟨v, j, hv, hvj, hface, hedge, hend⟩ := edge_presentation hN hh e.property
  intro x hx
  rw [hend] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hv
  · exact edge_terminal_is_vertex hN hh ⟨hv, hvj, hface⟩

end TopologicalSpace.CubeBoundaryThree
