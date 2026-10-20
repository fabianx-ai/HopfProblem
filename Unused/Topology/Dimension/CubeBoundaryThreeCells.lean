module

public import Lib.Topology.Dimension.CubeBoundaryThreeCells.Coverage
public import Lib.Topology.Dimension.CubeBoundaryThreeCells.SquareBoundary
import all Lib.Topology.Dimension.CubeBoundaryThreeCells.Lattice
import all Lib.Topology.Dimension.CubeBoundaryThreeCells.Cells
import all Lib.Topology.Dimension.CubeBoundaryThreeCells.Faces
import all Lib.Topology.Dimension.CubeBoundaryThreeCells.Coverage
import all Lib.Topology.Dimension.CubeBoundaryThreeCells.SquareBoundary

/-!
# Unused lemmas on the grid of the boundary of the three-cube

The grid of mesh `h = 2 / N` on the boundary `∂[-1,1]³` of the cube in `ℝ³`
(`Lib.Topology.Dimension.CubeBoundaryThreeCells`): vertices `v` with coordinates in the lattice
`{-1 + k h}`, edges `v + [0,h] e_j`, squares `v + [0,h] e_j + [0,h] e_k`.  This file holds the
statements about that grid that no other declaration of the project uses:

* lattice cardinality: the mesh of `[-1,1]` has `N + 1` points (`card_lattice`), and `h = 2`
  for `N = 1`;
* uniqueness of cell presentations: for `h > 0` an edge or a square determines its initial vertex
  and its directions (`edge_presentation_unique`, `square_presentation_unique`), via the
  coordinates in which it varies and its coordinatewise minimum; the remaining coordinate of a
  square is intrinsic; for `h = 0` presentations are not unique (`zero_mesh_*`); swapping the two
  directions of a square, and the ordering `j < k` that removes that ambiguity;
* which cells lie in the boundary: a square lies in exactly one face (`square_intrinsic_face`),
  an edge lies in the boundary iff one of its fixed coordinates is `±1`
  (`edge_subset_boundary_iff`, through the edge midpoint);
* transport lemmas: coordinate variation and constant coordinates along an equality of sets,
  coordinate evaluation of `ambientOfThreeCoordinates`, the two descriptions of the opposite
  corner of a square.

Nothing uses them.  They were moved here verbatim from the pieces of
`Lib.Topology.Dimension.CubeBoundaryThreeCells` (receipt `Lib/reports/unused/cube3.md`); the
private helpers of those pieces they need are reached through `import all`.
-/

set_option warningAsError true
set_option autoImplicit false

open Set

namespace TopologicalSpace.CubeBoundaryThree

/-! ### From `Lib.Topology.Dimension.CubeBoundaryThreeCells.Lattice` -/

/-- The affine index map is injective, so the lattice has exactly `N+1` points. -/
theorem card_lattice {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ)) :
  (lattice N h).ncard = N + 1 := by
  let f : ℤ → ℝ := fun k => -1 + (k : ℝ) * h
  have hset : lattice N h = f '' Set.Icc 0 (N : ℤ) := by
    ext t
    simp only [lattice, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Icc, f]
    aesop
  rw [hset, Set.ncard_image_of_injective]
  · rw [show Set.Icc (0 : ℤ) N = (↑(Finset.Icc (0 : ℤ) N) : Set ℤ) by
        ext z; simp,
      Set.ncard_coe_finset, Int.card_Icc]
    simp
  · intro a b hab
    have hh0 : h ≠ 0 := ne_of_gt (mesh_pos hN hh)
    dsimp [f] at hab
    have : (a : ℝ) = (b : ℝ) := by
      apply mul_right_cancel₀ hh0
      linarith
    exact_mod_cast this

/-- When `N=1`, the identity `h=2/N` reduces the mesh to two. -/
theorem mesh_two_of_one {h : ℝ} (hh : h = 2 / ((1 : ℕ) : ℝ)) : h = 2 := by norm_num at hh ⊢; exact hh

/-! ### From `Lib.Topology.Dimension.CubeBoundaryThreeCells.Cells` -/

/-- A coordinate is nonconstant exactly when two points of the set have different values there. -/
def coordinateNonconstant (C : Set Ambient) (r : Fin 3) : Prop :=
  ∃ x ∈ C, ∃ y ∈ C, x r ≠ y r

/-- The initial vertex attains every coordinate minimum on a nonnegative-mesh edge. -/
theorem edge_coordinate_minima_attained {h : ℝ} (hh : 0 ≤ h) (v : Ambient) (j r : Fin 3) :
  v ∈ edgeGeom h v j ∧ (∀ x ∈ edgeGeom h v j, v r ≤ x r) :=
  ⟨(edge_initial_lowerCorner hh v j).1, (edge_initial_lowerCorner hh v j).2 r⟩
/-- The initial vertex attains every coordinate minimum on a nonnegative-mesh square. -/
theorem square_coordinate_minima_attained {h : ℝ} (hh : 0 ≤ h) {v : Ambient} {j k : Fin 3}
  (hjk : j < k) (r : Fin 3) : v ∈ squareGeom h v j k ∧ (∀ x ∈ squareGeom h v j k, v r ≤ x r) :=
  ⟨(square_initial_lowerCorner hh hjk).1, (square_initial_lowerCorner hh hjk).2 r⟩

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

/-- Admissible presentations of the same positive square have identical starts and ordered directions. -/
theorem square_presentation_unique {N : ℕ} {h : ℝ} (hh : 0 < h) {s : Set Ambient}
  {v w : Ambient} {j k p q : Fin 3} (hp : SquareParam N h v j k) (hs : s = squareGeom h v j k)
  (hp' : SquareParam N h w p q) (hs' : s = squareGeom h w p q) : v = w ∧ j = p ∧ k = q := by
  have heq := hs.symm.trans hs'
  have hvw := square_initial_eq_of_set_eq (le_of_lt hh) hp.2.1 hp'.2.1 heq
  have hd := square_directions_mem_of_set_eq hh hp.2.1 hp'.2.1 heq
  exact ⟨hvw, square_ordered_directions_eq hp.2.1 hp'.2.1 hd.1 hd.2⟩
/-- For positive mesh, a square varies in exactly its two defining coordinates `j` and `k`. -/
theorem square_nonconstant_coordinates {h : ℝ} (hh : 0 < h) {v : Ambient} {j k : Fin 3}
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

/-! ### From `Lib.Topology.Dimension.CubeBoundaryThreeCells.Faces` -/

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

/-! ### From `Lib.Topology.Dimension.CubeBoundaryThreeCells.Coverage` -/

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

/-! ### From `Lib.Topology.Dimension.CubeBoundaryThreeCells.SquareBoundary` -/

/-- The two descriptions of the opposite square corner coincide. -/
private theorem shifted_corner_commutes (h : ℝ) (v : Ambient) (j k : Fin 3) :
    shiftedVertexK h (shiftedVertexJ h v j) k =
      shiftedVertexJ h (shiftedVertexK h v k) j := by
  simp only [shiftedVertexJ, shiftedVertexK]
  module
end TopologicalSpace.CubeBoundaryThree

/-! ### Axiom probes

The moved theorems are private to this module, so they are probed here rather than from a
separate audit file: each must depend on at most `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms TopologicalSpace.CubeBoundaryThree.card_lattice
#print axioms TopologicalSpace.CubeBoundaryThree.mesh_two_of_one
#print axioms TopologicalSpace.CubeBoundaryThree.edge_coordinate_minima_attained
#print axioms TopologicalSpace.CubeBoundaryThree.square_coordinate_minima_attained
#print axioms TopologicalSpace.CubeBoundaryThree.edge_presentation_unique
#print axioms TopologicalSpace.CubeBoundaryThree.edge_nonconstant_coordinates
#print axioms TopologicalSpace.CubeBoundaryThree.square_presentation_unique
#print axioms TopologicalSpace.CubeBoundaryThree.square_nonconstant_coordinates
#print axioms TopologicalSpace.CubeBoundaryThree.coordinate_variation_of_set_eq
#print axioms TopologicalSpace.CubeBoundaryThree.coordinate_constant_value_transport
#print axioms TopologicalSpace.CubeBoundaryThree.increasing_pair_eq_of_direction_set_eq
#print axioms TopologicalSpace.CubeBoundaryThree.edge_endpoints_distinct
#print axioms TopologicalSpace.CubeBoundaryThree.square_remaining_index_cases
#print axioms TopologicalSpace.CubeBoundaryThree.square_remaining_intrinsic
#print axioms TopologicalSpace.CubeBoundaryThree.zero_mesh_images
#print axioms TopologicalSpace.CubeBoundaryThree.zero_mesh_edge_nonunique
#print axioms TopologicalSpace.CubeBoundaryThree.zero_mesh_square_nonunique
#print axioms TopologicalSpace.CubeBoundaryThree.square_parameter_swap
#print axioms TopologicalSpace.CubeBoundaryThree.swapped_ordered_pair_ne
#print axioms TopologicalSpace.CubeBoundaryThree.square_order_suffices
#print axioms TopologicalSpace.CubeBoundaryThree.shared_edge_presentation_identity
#print axioms TopologicalSpace.CubeBoundaryThree.face_sign_eq_of_mem
#print axioms TopologicalSpace.CubeBoundaryThree.square_intrinsic_face
#print axioms TopologicalSpace.CubeBoundaryThree.square_unit_mesh_endpoint_case
#print axioms TopologicalSpace.CubeBoundaryThree.edge_saturated_coordinate_suffices
#print axioms TopologicalSpace.CubeBoundaryThree.edge_no_other_saturated_forces_moving_neg_one
#print axioms TopologicalSpace.CubeBoundaryThree.edgeMidpoint_mem
#print axioms TopologicalSpace.CubeBoundaryThree.edge_midpoint_all_abs_lt
#print axioms TopologicalSpace.CubeBoundaryThree.all_abs_lt_not_boundary
#print axioms TopologicalSpace.CubeBoundaryThree.edge_subset_boundary_iff
#print axioms TopologicalSpace.CubeBoundaryThree.ambientOfThreeCoordinates_apply_i
#print axioms TopologicalSpace.CubeBoundaryThree.ambientOfThreeCoordinates_apply_j
#print axioms TopologicalSpace.CubeBoundaryThree.ambientOfThreeCoordinates_apply_k
#print axioms TopologicalSpace.CubeBoundaryThree.shifted_corner_commutes
