module

public import Lib.Topology.Dimension.CubeBoundaryThree
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Data.Int.Interval

set_option warningAsError true
set_option autoImplicit false
open Set
namespace TopologicalSpace.CubeBoundaryThree

/-!
Textbook Section 3, Definition 3.1 and coherence expansion, canonical lines 1368–1620.
The declarations below follow the reviewed order L0–L4, D1–D3, C01–C22, H2/H1, F1–F3, E0.
C01–C05: coordinatewise lower corners and equality of initial points.
C06–C13: direction recovery, coordinate variation, endpoints and open-square coherence.
C14–C17: remaining coordinate, midpoint bounds, face sign/containment and unique face.
C18–C22: hypothesis audit, zero mesh, parameter swap, N=1, shared edges, background inventory.
Finiteness and endpoint-vertex receipts close the included boundary; Lemma 3.2 is excluded.
-/

/- Textbook L0 / 1368–1372 (D001): the lattice consists of the mesh points `-1 + k h` for integer indices `0 ≤ k ≤ N`. -/
def lattice (N : ℕ) (h : ℝ) : Set ℝ :=
  {t | ∃ k : ℤ, k ∈ Set.Icc 0 (N : ℤ) ∧ t = -1 + (k : ℝ) * h}
/- Textbook L0 / 1368–1372 (D002): the lower lattice deletes the top endpoint, leaving precisely the indices `k < N`. -/
def latticeBelowTop (N : ℕ) (h : ℝ) : Set ℝ := lattice N h \ {1}
/- Textbook L0 / 1368–1372 (D003): from `N > 0` and `h = 2/N`, the mesh is positive, satisfies `N h = 2`, and is at most two. -/
theorem mesh_identities (N : ℕ) (h : ℝ) (hN : 0 < N) (hh : h = 2 / (N : ℝ)) :
  0 < h ∧ (N : ℝ) * h = 2 ∧ h ≤ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  subst h
  constructor
  · exact div_pos (by norm_num) hNr
  constructor
  · field_simp
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hN))
    exact (div_le_iff₀ hNr).2 (by nlinarith)
/- Textbook L0 / 1368–1372 (D004): the mesh identities immediately supply the positivity of `h`. -/
theorem mesh_pos {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ)) : 0 < h :=
  (mesh_identities N h hN hh).1
/- Textbook L1 / 1368–1372 (D005): every indexed mesh point lies between `-1` and `1`. -/
theorem lattice_subset_interval {N : ℕ} {h : ℝ} (hN : 0 < N)
  (hh : h = 2 / (N : ℝ)) : lattice N h ⊆ Set.Icc (-1) 1 := by
  rintro t ⟨k, hk, rfl⟩
  have hh' := (mesh_identities N h hN hh).2.1
  constructor
  · have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk.1
    exact le_add_of_nonneg_right (mul_nonneg hk0 (le_of_lt (mesh_pos hN hh)))
  · have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.2
    nlinarith [mul_le_mul_of_nonneg_right hkN (le_of_lt (mesh_pos hN hh))]
/- Textbook L2 / 1368–1372 (D006): the lattice is the image of a finite integer interval and is therefore finite. -/
theorem finite_lattice (N : ℕ) (h : ℝ) : (lattice N h).Finite := by
  have hf := Set.Finite.image (fun k : ℤ => -1 + (k : ℝ) * h) (Set.finite_Icc 0 (N : ℤ))
  refine hf.subset ?_
  rintro t ⟨k, hk, rfl⟩
  exact ⟨k, hk, rfl⟩
/- Textbook L3 / 1368–1372 (D007): the affine index map is injective, so the lattice has exactly `N+1` points. -/
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
/- Textbook L3 / 1368–1372 (D008): the indices zero and `N` give the two endpoints `-1` and `1`. -/
theorem lattice_endpoints {N : ℕ} {h : ℝ} (hN : 0 < N)
  (hh : h = 2 / (N : ℝ)) : (-1 : ℝ) ∈ lattice N h ∧ (1 : ℝ) ∈ lattice N h := by
  constructor
  · exact ⟨0, by simp, by simp⟩
  · refine ⟨N, by simp, ?_⟩
    have hm := (mesh_identities N h hN hh).2.1
    norm_num at hm ⊢
    linarith
/- Textbook L4 / 1368–1372 (D009): distinct integer indices differ by at least one, hence their mesh points are separated by at least `h`. -/
theorem lattice_separation {N : ℕ} {h : ℝ} (hN : 0 < N)
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
/- Textbook L4 / 1368–1372 (D010): a lattice point below `1-h` has index below `N`, so adding `h` gives its successor in the lattice. -/
theorem lattice_successor {N : ℕ} {h : ℝ} (hN : 0 < N)
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
/- Textbook L4 / 1368–1372 (D011): when `N=1`, the identity `h=2/N` reduces the mesh to two. -/
theorem mesh_two_of_one {h : ℝ} (hh : h = 2 / ((1 : ℕ) : ℝ)) : h = 2 := by norm_num at hh ⊢; exact hh
/- Textbook D1 / 1374–1376 (D012): a vertex parameter has three lattice coordinates and lies on the cube boundary. -/
def VertexParam (N : ℕ) (h : ℝ) (v : Ambient) : Prop :=
  (∀ i, v i ∈ lattice N h) ∧ v ∈ boundary
/- Textbook D1 / 1374–1376 (D013): the vertex set collects all ambient points satisfying the vertex parameter. -/
public def vertices (N : ℕ) (h : ℝ) : Set Ambient := {v | VertexParam N h v}
/- Textbook D1 / 1374–1376 (D014): the boundary clause of a vertex parameter places every vertex on the cube boundary. -/
public theorem vertex_mem_boundary {N : ℕ} {h : ℝ} {v : Ambient}
    (hv : v ∈ vertices N h) : v ∈ boundary := hv.2
/- Textbook D2 / 1376–1379 (D015): an edge is the segment from `v` to `v+h e_j`. -/
def edgeGeom (h : ℝ) (v : Ambient) (j : Fin 3) : Set Ambient :=
  segment ℝ v (v + h • EuclideanSpace.single j 1)
/- Textbook D2 / 1376–1379 (D016): an admissible edge starts at a vertex, has room for one mesh step in direction `j`, and stays in the boundary. -/
def EdgeParam (N : ℕ) (h : ℝ) (v : Ambient) (j : Fin 3) : Prop :=
  v ∈ vertices N h ∧ v j ≤ 1 - h ∧ edgeGeom h v j ⊆ boundary
/- Textbook D2 / 1376–1379 (D017): the edge family is the collection of geometric segments arising from admissible edge parameters. -/
public def edges (N : ℕ) (h : ℝ) : Set (Set Ambient) :=
  {e | ∃ v j, EdgeParam N h v j ∧ e = edgeGeom h v j}
/- Textbook D2 / 1376–1379 (D018): membership in the edge family is exactly presentation by an admissible initial vertex and direction. -/
theorem edge_mem_iff {N : ℕ} {h : ℝ} {e : Set Ambient} :
    e ∈ edges N h ↔ ∃ v j, EdgeParam N h v j ∧ e = edgeGeom h v j := Iff.rfl
/- Textbook D3 / 1379–1382 (D019): a closed square independently moves from `v` through one mesh step in directions `j` and `k`. -/
def squareGeom (h : ℝ) (v : Ambient) (j k : Fin 3) : Set Ambient :=
  {x | ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
    x = v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1}
/- Textbook D3 / 1379–1382 (D020): the relative-open square uses the same parametrization with both parameters strictly between zero and one. -/
def squareOpenGeom (h : ℝ) (v : Ambient) (j k : Fin 3) : Set Ambient :=
  {x | ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ b ∈ Set.Ioo (0 : ℝ) 1,
    x = v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1}
/- Textbook D3 / 1379–1382 (D021): an admissible square has ordered distinct directions, a vertex start, upper bounds in both directions, and boundary containment. -/
def SquareParam (N : ℕ) (h : ℝ) (v : Ambient) (j k : Fin 3) : Prop :=
  v ∈ vertices N h ∧ j < k ∧ v j ≤ 1 - h ∧ v k ≤ 1 - h ∧ squareGeom h v j k ⊆ boundary
/- Textbook D3 / 1379–1382 (D022): the square family collects the closed images of all admissible square parameters. -/
public def squares (N : ℕ) (h : ℝ) : Set (Set Ambient) :=
  {s | ∃ v j k, SquareParam N h v j k ∧ s = squareGeom h v j k}
/- Textbook C01 / 1410–1421 (D023): a lower corner belongs to the set and is coordinatewise below every point of it. -/
def coordinateLowerCorner (C : Set Ambient) (v : Ambient) : Prop :=
  v ∈ C ∧ ∀ r x, x ∈ C → v r ≤ x r
/- Textbook C01 / 1410–1421 (D024): a coordinate is nonconstant exactly when two points of the set have different values there. -/
def coordinateNonconstant (C : Set Ambient) (r : Fin 3) : Prop :=
  ∃ x ∈ C, ∃ y ∈ C, x r ≠ y r
/- Textbook C01 / 1410–1421 (D025): two coordinatewise lower corners bound one another, hence agree in every coordinate and are equal. -/
theorem coordinateLowerCorner_unique {C : Set Ambient} {v w : Ambient}
  (hv : coordinateLowerCorner C v) (hw : coordinateLowerCorner C w) : v = w := by
  ext r
  exact le_antisymm (hv.2 r w hw.1) (hw.2 r v hv.1)
/- Textbook C02 / 1423–1435 (D026): along an edge only coordinate `j` changes, by the amount `t h`. -/
theorem edge_coordinate_formula (h t : ℝ) (v : Ambient) (j r : Fin 3) :
  (v + (t * h) • EuclideanSpace.single j 1 : Ambient) r =
    if r = j then v j + t * h else v r := by
  split_ifs with hr
  · subst r; simp
  · simp [hr]
/- Textbook C02 / 1423–1435 (D027): the parameter value zero places the initial point `v` on its edge. -/
theorem edge_zero_mem (h : ℝ) (v : Ambient) (j : Fin 3) : v ∈ edgeGeom h v j := by
  rw [edgeGeom]
  exact left_mem_segment ℝ v _
/- Textbook C02 / 1423–1435 (D028): every point of the segment has the affine form `v+(t h)e_j` with `0≤t≤1`. -/
theorem edge_parameter_extract {h : ℝ} {v : Ambient} {j : Fin 3} {x : Ambient}
  (hx : x ∈ edgeGeom h v j) : ∃ t ∈ Set.Icc (0 : ℝ) 1,
    x = v + (t * h) • EuclideanSpace.single j 1 := by
  rw [edgeGeom, segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t, ht, by module⟩
/- Textbook C02 / 1423–1435 (D029): nonnegative mesh and segment parameter make the initial point a coordinatewise lower corner. -/
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
/- Textbook C03 / 1436–1448 (D030): on a square, coordinates `j` and `k` change independently by `a h` and `b h`. -/
theorem square_coordinate_formula (h a b : ℝ) (v : Ambient) (j k r : Fin 3) (hjk : j ≠ k) :
  (v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1 : Ambient) r =
    if r = j then v j + a * h else if r = k then v k + b * h else v r := by
  by_cases hrj : r = j
  · subst r
    simp [hjk]
  · by_cases hrk : r = k
    · subst r
      simp [hrj]
    · simp [hrj, hrk]
/- Textbook C03 / 1436–1448 (D031): parameters `(0,0)` place the initial point `v` in the square. -/
theorem square_zero_mem (h : ℝ) (v : Ambient) (j k : Fin 3) : v ∈ squareGeom h v j k := by
  exact ⟨0, by simp, 0, by simp, by simp⟩
/- Textbook C03 / 1436–1448 (D032): parameters `(1,0)` place the first adjacent corner `v+h e_j` in the square. -/
theorem square_first_corner_mem (h : ℝ) (v : Ambient) (j k : Fin 3) :
  v + h • EuclideanSpace.single j 1 ∈ squareGeom h v j k := by
  refine ⟨1, by simp, 0, by simp, ?_⟩
  module
/- Textbook C03 / 1436–1448 (D033): parameters `(0,1)` place the second adjacent corner `v+h e_k` in the square. -/
theorem square_second_corner_mem (h : ℝ) (v : Ambient) (j k : Fin 3) :
  v + h • EuclideanSpace.single k 1 ∈ squareGeom h v j k := by
  refine ⟨0, by simp, 1, by simp, ?_⟩
  module
/- Textbook C03 / 1436–1448 (D034): every square point has parameters `a,b∈[0,1]` in the defining affine formula. -/
theorem square_parameter_extract {h : ℝ} {v : Ambient} {j k : Fin 3} {x : Ambient}
  (hx : x ∈ squareGeom h v j k) : ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
    x = v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1 := hx
/- Textbook C03 / 1436–1448 (D035): nonnegative mesh and square parameters make `v` a coordinatewise lower corner. -/
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
/- Textbook C04 / 1448–1452 (D036): the initial vertex attains every coordinate minimum on a nonnegative-mesh edge. -/
theorem edge_coordinate_minima_attained {h : ℝ} (hh : 0 ≤ h) (v : Ambient) (j r : Fin 3) :
  v ∈ edgeGeom h v j ∧ (∀ x ∈ edgeGeom h v j, v r ≤ x r) :=
  ⟨(edge_initial_lowerCorner hh v j).1, (edge_initial_lowerCorner hh v j).2 r⟩
/- Textbook C04 / 1448–1452 (D037): the initial vertex attains every coordinate minimum on a nonnegative-mesh square. -/
theorem square_coordinate_minima_attained {h : ℝ} (hh : 0 ≤ h) {v : Ambient} {j k : Fin 3}
  (hjk : j < k) (r : Fin 3) : v ∈ squareGeom h v j k ∧ (∀ x ∈ squareGeom h v j k, v r ≤ x r) :=
  ⟨(square_initial_lowerCorner hh hjk).1, (square_initial_lowerCorner hh hjk).2 r⟩
/- Textbook C05 / 1454–1459 (D038): equal nonnegative-mesh edges have the same unique coordinatewise lower corner. -/
theorem edge_initial_eq_of_set_eq {h : ℝ} (hh : 0 ≤ h) {v w : Ambient} {j l : Fin 3}
  (heq : edgeGeom h v j = edgeGeom h w l) : v = w := by
  apply coordinateLowerCorner_unique (C := edgeGeom h v j)
  · exact edge_initial_lowerCorner hh v j
  · rw [heq]
    exact edge_initial_lowerCorner hh w l
/- Textbook C05 / 1454–1459 (D039): equal ordered nonnegative-mesh squares have the same unique coordinatewise lower corner. -/
theorem square_initial_eq_of_set_eq {h : ℝ} (hh : 0 ≤ h) {v w : Ambient} {j k p q : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q) : v = w := by
  apply coordinateLowerCorner_unique (C := squareGeom h v j k)
  · exact square_initial_lowerCorner hh hjk
  · rw [heq]
    exact square_initial_lowerCorner hh hpq
/- Textbook C06 / 1461–1469 (D040): parameter one places the terminal point `v+h e_j` on the edge. -/
theorem edge_terminal_mem (h : ℝ) (v : Ambient) (j : Fin 3) :
  v + h • EuclideanSpace.single j 1 ∈ edgeGeom h v j := by
  rw [edgeGeom]
  exact right_mem_segment ℝ _ _
/- Textbook C06 / 1461–1469 (D041): after equal positive edges share their initial point, terminal-coordinate variation forces their directions to agree. -/
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
/- Textbook C06 / 1461–1469 (D042): admissible presentations of the same positive edge have identical starts and directions. -/
theorem edge_presentation_unique {N : ℕ} {h : ℝ} (hh : 0 < h) {e : Set Ambient}
  {v w : Ambient} {j l : Fin 3} (hp : EdgeParam N h v j) (he : e = edgeGeom h v j)
  (hp' : EdgeParam N h w l) (he' : e = edgeGeom h w l) : v = w ∧ j = l := by
  have _ := hp.1
  have _ := hp'.1
  have hgeom : edgeGeom h v j = edgeGeom h w l := he.symm.trans he'
  exact ⟨edge_initial_eq_of_set_eq (le_of_lt hh) hgeom, edge_direction_eq_of_set_eq hh hgeom⟩
/- Textbook C07 / 1471–1476 (D043): for positive mesh, an edge varies in exactly its defining coordinate `j`. -/
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
/- Textbook C08 / 1478–1488 (D044): equality of positive square images forces each source moving direction to be one of the target directions. -/
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
/- Textbook C09 / 1490–1496 (D045): two increasing pairs with the same two members agree coordinate by coordinate. -/
theorem square_ordered_directions_eq {j k p q : Fin 3} (hjk : j < k) (hpq : p < q)
  (hj : j = p ∨ j = q) (hk : k = p ∨ k = q) : j = p ∧ k = q := by
  omega
/- Textbook C09 / 1490–1496 (D046): admissible presentations of the same positive square have identical starts and ordered directions. -/
theorem square_presentation_unique {N : ℕ} {h : ℝ} (hh : 0 < h) {s : Set Ambient}
  {v w : Ambient} {j k p q : Fin 3} (hp : SquareParam N h v j k) (hs : s = squareGeom h v j k)
  (hp' : SquareParam N h w p q) (hs' : s = squareGeom h w p q) : v = w ∧ j = p ∧ k = q := by
  have heq := hs.symm.trans hs'
  have hvw := square_initial_eq_of_set_eq (le_of_lt hh) hp.2.1 hp'.2.1 heq
  have hd := square_directions_mem_of_set_eq hh hp.2.1 hp'.2.1 heq
  exact ⟨hvw, square_ordered_directions_eq hp.2.1 hp'.2.1 hd.1 hd.2⟩
/- Textbook C10 / 1498–1504 (D047): for positive mesh, a square varies in exactly its two defining coordinates `j` and `k`. -/
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
/- Textbook C11 / 1504–1509 (D048): equality of sets transports the existence of two points differing in a chosen coordinate. -/
theorem coordinate_variation_of_set_eq {C D : Set Ambient} (hCD : C = D) (r : Fin 3) :
  coordinateNonconstant C r ↔ coordinateNonconstant D r := by subst D; rfl
/- Textbook C11 / 1504–1509 (D049): equality of sets transports the assertion that a chosen coordinate has a fixed value. -/
theorem coordinate_constant_value_transport {C D : Set Ambient} (hCD : C = D)
  (r : Fin 3) (c : ℝ) : (∀ x ∈ C, x r = c) ↔ (∀ x ∈ D, x r = c) := by subst D; rfl
/- Textbook C11 / 1504–1509 (D050): equal two-element direction sets with increasing enumerations have the same ordered pair. -/
theorem increasing_pair_eq_of_direction_set_eq {j k p q : Fin 3} (hjk : j < k) (hpq : p < q)
  (hset : ({j, k} : Set (Fin 3)) = {p, q}) : j = p ∧ k = q := by
  apply square_ordered_directions_eq hjk hpq
  · have : j ∈ ({p, q} : Set (Fin 3)) := by rw [← hset]; simp
    simpa using this
  · have : k ∈ ({p, q} : Set (Fin 3)) := by rw [← hset]; simp
    simpa using this
/- Textbook C12 / 1511–1519 (D051): equal positive edge presentations determine the same unordered pair of endpoints. -/
theorem edge_endpoints_coherent {h : ℝ} (hh : 0 < h) {v w : Ambient} {j l : Fin 3}
  (heq : edgeGeom h v j = edgeGeom h w l) :
  ({v, v + h • EuclideanSpace.single j 1} : Set Ambient) = {w, w + h • EuclideanSpace.single l 1} := by
  rw [edge_initial_eq_of_set_eq (le_of_lt hh) heq, edge_direction_eq_of_set_eq hh heq]
/- Textbook C12 / 1511–1519 (D052): variation in the defining coordinate of a positive edge prevents its two endpoints from coinciding. -/
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
/- Textbook C13 / 1519–1529 (D053): uniqueness of positive square presentations makes the relative-open image independent of the chosen presentation. -/
theorem square_relInterior_coherent_raw {h : ℝ} (hh : 0 < h) {v w : Ambient} {j k p q : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q) :
  squareOpenGeom h v j k = squareOpenGeom h w p q := by
  have hvw := square_initial_eq_of_set_eq (le_of_lt hh) hjk hpq heq
  have hd := square_directions_mem_of_set_eq hh hjk hpq heq
  have hord := square_ordered_directions_eq hjk hpq hd.1 hd.2
  subst w
  rw [hord.1, hord.2]
/- Textbook C14 / 1531–1538 (D054): two distinct coordinates of `Fin 3` leave a unique third coordinate. -/
theorem square_remaining_index {j k : Fin 3} (hjk : j < k) :
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
/- Textbook C14 / 1531–1538 (D055): enumerating the three increasing coordinate pairs identifies their respective remaining coordinates. -/
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
/- Textbook C14 / 1531–1538 (D056): the coordinate outside `j,k` is unchanged at every point of the square. -/
theorem square_remaining_coordinate {h : ℝ} {v : Ambient} {j k i : Fin 3}
  (hij : i ≠ j) (hik : i ≠ k) {x : Ambient} (hx : x ∈ squareGeom h v j k) : x i = v i := by
  obtain ⟨a, ha, b, hb, rfl⟩ := square_parameter_extract hx
  simp [hij, hik]
/- Textbook C14 / 1531–1538 (D057): equal positive squares have the same remaining coordinate and the same constant value there. -/
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
/- Textbook C15 / 1540–1553 (D058): the square midpoint uses the two half-mesh displacements from its initial vertex. -/
noncomputable def squareMidpoint (h : ℝ) (v : Ambient) (j k : Fin 3) : Ambient :=
  v + ((1 / 2 : ℝ) * h) • EuclideanSpace.single j 1 + ((1 / 2 : ℝ) * h) • EuclideanSpace.single k 1
/- Textbook C15 / 1540–1553 (D059): adding half a positive mesh in both moving directions gives a point of the square whose two moving coordinates lie strictly between `-1` and `1`. -/
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
/- Textbook C16 / 1553–1559 (D060): a boundary point of the cube has maximum absolute coordinate equal to one. -/
theorem boundary_maxAbs_eq {x : Ambient} (hx : x ∈ boundary) : maxAbs x = 1 := hx
/- Textbook C16 / 1553–1559 (D061): if two coordinates have absolute value below one while the maximum is one, the remaining coordinate has absolute value one. -/
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
/- Textbook C16 / 1553–1559 (D062): the square midpoint remains on the boundary, keeps the remaining coordinate fixed, and forces its absolute value to one. -/
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
/- Textbook C16 / 1553–1559 (D063): a boundary point whose `i`th coordinate is a sign lies in the corresponding signed face. -/
theorem face_membership_from_sign {x : Ambient} {i : Fin 3} {σ : {r : ℝ // r = -1 ∨ r = 1}}
  (hx : x ∈ boundary) (hxi : x i = σ.1) : x ∈ face i σ := ⟨hx, hxi⟩
/- Textbook C16 / 1553–1559 (D064): the saturated remaining coordinate determines a sign, and constancy of that coordinate puts the whole square in its face. -/
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
/- Textbook C17 / 1561–1568 (D065): a point lying in two signed faces with the same coordinate forces the two signs to agree. -/
theorem face_sign_eq_of_mem {x : Ambient} {i : Fin 3}
  {σ τ : {r : ℝ // r = -1 ∨ r = 1}} (hxσ : x ∈ face i σ) (hxτ : x ∈ face i τ) : σ = τ := by
  apply Subtype.ext
  exact hxσ.2.symm.trans hxτ.2
/- Textbook C17 / 1561–1568 (D066): variation in directions `j,k` excludes those face coordinates; the unique remaining coordinate and its sign determine the containing face. -/
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
/- Textbook C18 / 1570–1581 (D067): zero mesh collapses the edge, closed square, and relative-open square images to the singleton `{v}`. -/
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
/- Textbook C18 / 1570–1581 (D068): at zero mesh, distinct directions present the same collapsed edge. -/
theorem zero_mesh_edge_nonunique : ∃ (v : Ambient) (j l : Fin 3), j ≠ l ∧ edgeGeom 0 v j = edgeGeom 0 v l := by
  exact ⟨0, 0, 1, by decide, (zero_mesh_images 0 0 0).1.trans (zero_mesh_images 0 1 1).1.symm⟩
/- Textbook C18 / 1570–1581 (D069): at zero mesh, distinct ordered direction pairs present the same collapsed square. -/
theorem zero_mesh_square_nonunique : ∃ (v : Ambient) (j k p q : Fin 3),
  j < k ∧ p < q ∧ (j, k) ≠ (p, q) ∧ squareGeom 0 v j k = squareGeom 0 v p q := by
  exact ⟨0, 0, 1, 0, 2, by decide, by decide, by decide,
    (zero_mesh_images 0 0 1).2.1.trans (zero_mesh_images 0 0 2).2.1.symm⟩
/- Textbook C19 / 1583–1587 (D070): swapping the two square parameters and commuting the displacements leaves both the closed and open images unchanged. -/
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
/- Textbook C19 / 1583–1587 (D071): for distinct directions, reversing an ordered pair produces a different pair. -/
theorem swapped_ordered_pair_ne {j k : Fin 3} (hjk : j ≠ k) : (j, k) ≠ (k, j) := by
  intro hp
  exact hjk (congrArg Prod.fst hp)
/- Textbook C19 / 1583–1587 (D072): requiring increasing directions removes the swap ambiguity from square presentations. -/
theorem square_order_suffices {h : ℝ} (hh : 0 < h) {v w : Ambient} {j k p q : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q) : j = p ∧ k = q := by
  have hd := square_directions_mem_of_set_eq hh hjk hpq heq
  exact square_ordered_directions_eq hjk hpq hd.1 hd.2
/- Textbook C20 / 1589–1593 (D073): when `N=1`, the mesh is two, admissible lower coordinates are `-1`, and square midpoint coordinates are strictly interior. -/
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
/- Textbook C21 / 1593–1598 (D074): a shared positive edge has presentation data, direction, and endpoints independent of which incident face supplies it. -/
theorem shared_edge_presentation_identity {h : ℝ} (hh : 0 < h) {v w : Ambient} {j l : Fin 3}
  (heq : edgeGeom h v j = edgeGeom h w l) :
  v = w ∧ j = l ∧ ({v, v + h • EuclideanSpace.single j 1} : Set Ambient) = {w, w + h • EuclideanSpace.single l 1} :=
  ⟨edge_initial_eq_of_set_eq (le_of_lt hh) heq, edge_direction_eq_of_set_eq hh heq,
    edge_endpoints_coherent hh heq⟩
/- Textbook H2 / 1384–1408; 1519–1529 (D075): the raw relative interior uses a chosen admissible presentation of the square. -/
noncomputable def squareRelInteriorRaw (N : ℕ) (h : ℝ) (s : {s : Set Ambient // s ∈ squares N h}) : Set Ambient :=
  squareOpenGeom h (Classical.choose s.property) (Classical.choose (Classical.choose_spec s.property))
    (Classical.choose (Classical.choose_spec (Classical.choose_spec s.property)))
/- Textbook H2 / 1384–1408; 1519–1529 (D076): the public relative interior packages the raw chosen-presentation construction. -/
public noncomputable def squareRelInterior (N : ℕ) (h : ℝ) (s : {s : Set Ambient // s ∈ squares N h}) : Set Ambient := squareRelInteriorRaw N h s
/- Textbook H2 / 1384–1408; 1519–1529 (D077): presentation uniqueness identifies the public relative interior with the open image of every admissible presentation. -/
theorem square_relInterior_coherent {N : ℕ} {h : ℝ} (_hN : 0 < N) (_hh : h = 2 / (N : ℝ))
  (s : {s : Set Ambient // s ∈ squares N h}) {v : Ambient} {j k : Fin 3} (hp : SquareParam N h v j k)
  (hs : (s : Set Ambient) = squareGeom h v j k) : squareRelInterior N h s = squareOpenGeom h v j k := by
  let v' := Classical.choose s.property
  let j' := Classical.choose (Classical.choose_spec s.property)
  let k' := Classical.choose (Classical.choose_spec (Classical.choose_spec s.property))
  have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec s.property))
  simp only [squareRelInterior, squareRelInteriorRaw]
  exact square_relInterior_coherent_raw (mesh_pos _hN _hh) hspec.1.2.1 hp.2.1
    (hspec.2.symm.trans hs)
/- Textbook H2 / 1384–1408; 1519–1529 (D078): every square admits a vertex, ordered directions, coordinate bounds, boundary containment, equality to its image, and the coherent interior. -/
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
/- Textbook H1 / 1384–1408; 1511–1519 (D079): the raw endpoint assignment uses the initial and terminal points of a chosen admissible edge presentation. -/
noncomputable def edgeEndpointsRaw (N : ℕ) (h : ℝ) (e : {e : Set Ambient // e ∈ edges N h}) : Set Ambient :=
  let v := Classical.choose e.property; let j := Classical.choose (Classical.choose_spec e.property); {v, v + h • EuclideanSpace.single j 1}
/- Textbook H1 / 1384–1408; 1511–1519 (D080): the public endpoint set packages the raw chosen-presentation assignment. -/
public noncomputable def edgeEndpoints (N : ℕ) (h : ℝ) (e : {e : Set Ambient // e ∈ edges N h}) : Set Ambient := edgeEndpointsRaw N h e
/- Textbook H1 / 1384–1408; 1511–1519 (D081): every edge admits a vertex, direction, coordinate bound, boundary containment, equality to its segment, and coherent endpoints. -/
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
/- Textbook C22 (lines 1600–1612): coordinate evaluation/extensionality, set transport,
real order/cancellation, half-mesh positivity, absolute-value/sign, maximum, and Fin 3 cases. -/
/- Textbook F1 / 1614–1616 (D082): a finite coordinatewise product transfers from ordinary functions to the ambient `WithLp` space. -/
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
/- Textbook F1 / 1614–1616 (D083): the threefold product of the finite lattice is finite. -/
theorem finite_vertex_product (N : ℕ) (h : ℝ) :
  ({v : Ambient | ∀ i, v i ∈ lattice N h}).Finite :=
  finite_Ambient_coordinate_bridge (fun _ => finite_lattice N h)
/- Textbook F1 / 1614–1616 (D084): the vertex set is a subset of the finite coordinatewise lattice product. -/
public theorem finite_vertices (N : ℕ) (h : ℝ) : (vertices N h).Finite := by
  apply (finite_vertex_product N h).subset
  intro v hv
  exact hv.1
/- Textbook F2 / 1614–1616 (D085): the edge-parameter set records admissible pairs of a vertex and a coordinate direction. -/
def edgeParamSet (N : ℕ) (h : ℝ) : Set (Ambient × Fin 3) := {p | EdgeParam N h p.1 p.2}
/- Textbook F2 / 1614–1616 (D086): edge parameters form a subset of the finite product of vertices with `Fin 3`. -/
theorem finite_edge_parameters (N : ℕ) (h : ℝ) : (edgeParamSet N h).Finite := by
  apply ((finite_vertices N h).prod Set.finite_univ).subset
  rintro ⟨v, j⟩ hp
  exact ⟨hp.1, Set.mem_univ j⟩
/- Textbook F2 / 1614–1616 (D087): the edge family is the image of its finite parameter set under the segment construction. -/
theorem edges_eq_image (N : ℕ) (h : ℝ) :
  edges N h = (fun p : Ambient × Fin 3 => edgeGeom h p.1 p.2) '' edgeParamSet N h := by
  ext e
  constructor
  · rintro ⟨v, j, hp, rfl⟩; exact ⟨(v, j), hp, rfl⟩
  · rintro ⟨⟨v, j⟩, hp, rfl⟩; exact ⟨v, j, hp, rfl⟩
/- Textbook F2 / 1614–1616 (D088): the image description makes the edge family finite. -/
public theorem finite_edges (N : ℕ) (h : ℝ) : (edges N h).Finite := by
  rw [edges_eq_image]
  exact (finite_edge_parameters N h).image _
/- Textbook F3 / 1614–1616 (D089): the square-parameter set records admissible triples of a vertex and two directions. -/
def squareParamSet (N : ℕ) (h : ℝ) : Set (Ambient × Fin 3 × Fin 3) := {p | SquareParam N h p.1 p.2.1 p.2.2}
/- Textbook F3 / 1614–1616 (D090): square parameters form a subset of the finite product of vertices with two copies of `Fin 3`. -/
theorem finite_square_parameters (N : ℕ) (h : ℝ) : (squareParamSet N h).Finite := by
  apply ((finite_vertices N h).prod (Set.finite_univ.prod Set.finite_univ)).subset
  rintro ⟨v, j, k⟩ hp
  exact ⟨hp.1, Set.mem_univ j, Set.mem_univ k⟩
/- Textbook F3 / 1614–1616 (D091): the square family is the image of its finite parameter set under the closed-square construction. -/
theorem squares_eq_image (N : ℕ) (h : ℝ) :
  squares N h = (fun p : Ambient × Fin 3 × Fin 3 => squareGeom h p.1 p.2.1 p.2.2) '' squareParamSet N h := by
  ext s
  constructor
  · rintro ⟨v, j, k, hp, rfl⟩; exact ⟨(v, j, k), hp, rfl⟩
  · rintro ⟨⟨v, j, k⟩, hp, rfl⟩; exact ⟨v, j, k, hp, rfl⟩
/- Textbook F3 / 1614–1616 (D092): the image description makes the square family finite. -/
public theorem finite_squares (N : ℕ) (h : ℝ) : (squares N h).Finite := by
  rw [squares_eq_image]
  exact (finite_square_parameters N h).image _
/- Textbook E0 / 1618–1620 (D093): the terminal coordinate is the next lattice point, the other coordinates are unchanged, and boundary containment makes the terminal point a vertex. -/
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
/- Textbook E0 / 1618–1620 (D094): an edge presentation identifies its endpoint set with the initial and terminal vertices, the latter supplied by the terminal-vertex lemma. -/
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

namespace TopologicalSpace.CubeBoundaryThree

/-- Textbook Q1, 1622–1634: a fixed saturated coordinate and interval bounds keep the edge on the boundary. -/
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

/-- Textbook Q1, 1622–1634: if no fixed coordinate is saturated, the moving coordinate is the lower endpoint. -/
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

/-- Textbook Q1, 1622–1634: the edge midpoint advances the moving coordinate by half a mesh. -/
noncomputable def edgeMidpoint (h : ℝ) (v : Ambient) (j : Fin 3) : Ambient :=
  v + ((1 / 2 : ℝ) * h) • EuclideanSpace.single j 1

/-- Textbook Q1, 1622–1634: the parameter one half places the midpoint on the edge. -/
theorem edgeMidpoint_mem (h : ℝ) (v : Ambient) (j : Fin 3) :
    edgeMidpoint h v j ∈ edgeGeom h v j := by
  rw [edgeGeom]
  rw [segment_eq_image']
  refine ⟨1 / 2, by norm_num, ?_⟩
  simp [edgeMidpoint, smul_smul]

/-- Textbook Q1, 1622–1634: the half-mesh step from minus one makes every midpoint coordinate strictly interior. -/
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

/-- Textbook Q1, 1622–1634: three strictly interior absolute coordinates have maximum below one. -/
theorem all_abs_lt_not_boundary {x : Ambient} (hall : ∀ r : Fin 3, |x r| < 1) :
    x ∉ boundary := by
  intro hx
  have hm : maxAbs x < 1 := max_lt (hall 0) (max_lt (hall 1) (hall 2))
  change maxAbs x = 1 at hx
  linarith

/-- Textbook Q1, 1622–1634: edge containment is equivalent to saturation of a fixed coordinate. -/
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

/-- Textbook Q2, 1622–1641: a saturated remaining coordinate keeps every square point on the boundary. -/
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

/-- Textbook Q2, 1622–1641: vertex data, ordered directions, room bounds and containment form a square parameter. -/
theorem squareParamOfContainment {N : ℕ} {h : ℝ} {v : Ambient} {j k : Fin 3}
    (hv : v ∈ vertices N h) (hjk : j < k) (hvj : v j ≤ 1 - h)
    (hvk : v k ≤ 1 - h) (hsub : squareGeom h v j k ⊆ boundary) :
    SquareParam N h v j k := ⟨hv, hjk, hvj, hvk, hsub⟩

/-- Textbook Q2, 1622–1641: the boundary midpoint forces saturation of the unchanged remaining coordinate. -/
theorem square_containment_forces_remaining_abs {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v : Ambient} {j k i : Fin 3}
    (hv : v ∈ vertices N h) (hjk : j < k) (hvj : v j ≤ 1 - h)
    (hvk : v k ≤ 1 - h) (hij : i ≠ j) (hik : i ≠ k)
    (hsub : squareGeom h v j k ⊆ boundary) : |v i| = 1 := by
  exact (square_midpoint_remaining_abs (mesh_pos hN hh)
    (squareParamOfContainment hv hjk hvj hvk hsub) hij hik).2.2

/-- Textbook Q2, 1622–1641: square containment is equivalent to saturation of the remaining coordinate. -/
theorem square_subset_boundary_iff {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v : Ambient} {j k i : Fin 3}
    (hv : v ∈ vertices N h) (hjk : j < k) (hvj : v j ≤ 1 - h)
    (hvk : v k ≤ 1 - h) (hij : i ≠ j) (hik : i ≠ k) :
    squareGeom h v j k ⊆ boundary ↔ |v i| = 1 :=
  ⟨square_containment_forces_remaining_abs hN hh hv hjk hvj hvk hij hik,
    square_saturated_remaining_suffices hN hh hv hjk hvj hvk hij hik⟩

/-- Textbook Q3, 1625–1641: divide a coordinate displacement by the mesh to recover its closed parameter. -/
noncomputable def closedParameter (h : ℝ) (v x : Ambient) (j : Fin 3) : ℝ :=
  (x j - v j) / h

/-- Textbook Q3, 1625–1641: a coordinate in the closed mesh interval has parameter between zero and one. -/
theorem closedParameter_mem_Icc {h : ℝ} (hh : 0 < h) {v x : Ambient} {j : Fin 3}
    (hx : x j ∈ Set.Icc (v j) (v j + h)) : closedParameter h v x j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hh)
  · rw [closedParameter, div_le_one hh]
    linarith [hx.2]

/-- Textbook Q3, 1625–1641: multiplying the recovered closed parameter by the mesh reconstructs the coordinate. -/
theorem closedParameter_reconstruct {h : ℝ} (hh : 0 < h) {v x : Ambient} {j : Fin 3} :
    v j + closedParameter h v x j * h = x j := by
  rw [closedParameter, div_mul_cancel₀ _ (ne_of_gt hh)]
  ring

/-- Textbook Q3, 1625–1641: equality at three exhaustive coordinates gives equality of ambient points. -/
theorem Ambient_ext_of_three {x y : Ambient} {i j k : Fin 3}
    (hexhaust : ∀ r : Fin 3, r = i ∨ r = j ∨ r = k)
    (hi : x i = y i) (hj : x j = y j) (hk : x k = y k) : x = y := by
  ext r
  rcases hexhaust r with rfl | rfl | rfl
  · exact hi
  · exact hj
  · exact hk

/-- Textbook Q3, 1625–1641: the two ordered directions and their remaining index exhaust the three coordinates. -/
theorem square_indices_exhaust {i j k : Fin 3} (hjk : j < k)
    (hij : i ≠ j) (hik : i ≠ k) :
    ∀ r : Fin 3, r = i ∨ r = j ∨ r = k := by
  intro r
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases r <;> omega

/-- Textbook Q3, 1625–1641: the closed square is exactly the rectangle with one fixed and two interval coordinates. -/
theorem square_closed_coordinate_rectangle {h : ℝ} (hh : 0 < h)
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

/-- Textbook Q3, 1625–1641: divide an interior coordinate displacement by the mesh to recover its open parameter. -/
noncomputable def openParameter (h : ℝ) (v x : Ambient) (j : Fin 3) : ℝ :=
  (x j - v j) / h

/-- Textbook Q3, 1625–1641: an interior mesh coordinate has parameter strictly between zero and one. -/
theorem openParameter_mem_Ioo {h : ℝ} (hh : 0 < h) {v x : Ambient} {j : Fin 3}
    (hx : x j ∈ Set.Ioo (v j) (v j + h)) : openParameter h v x j ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact div_pos (sub_pos.mpr hx.1) hh
  · rw [openParameter, div_lt_one hh]
    linarith [hx.2]

/-- Textbook Q3, 1625–1641: multiplying the recovered open parameter by the mesh reconstructs the coordinate. -/
theorem openParameter_reconstruct {h : ℝ} (hh : 0 < h) {v x : Ambient} {j : Fin 3} :
    v j + openParameter h v x j * h = x j := by
  rw [openParameter, div_mul_cancel₀ _ (ne_of_gt hh)]
  ring

/-- Textbook Q3, 1625–1641: the open square is exactly the rectangle with two strict interval coordinates. -/
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

/-- Textbook Q3, 1625–1641: each admissible square has closed and relative-open coordinate rectangles in a fixed signed face. -/
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

/-- Textbook C1, 1643–1652: normalize a coordinate by shifting its lower endpoint to zero and dividing by the mesh. -/
noncomputable def normalizedFloorInput (h t : ℝ) : ℝ := (t + 1) / h
/-- Textbook C1, 1643–1652: the floor of the normalized coordinate selects its integer mesh index. -/
noncomputable def unclippedFloorIndex (h t : ℝ) : ℤ := ⌊normalizedFloorInput h t⌋
/-- Textbook C1, 1643–1652: clip the floor index at the last lower mesh index. -/
noncomputable def clippedFloorIndex (N : ℕ) (h t : ℝ) : ℤ :=
  min (unclippedFloorIndex h t) ((N : ℤ) - 1)
/-- Textbook C1, 1643–1652: the clipped index determines the lower endpoint of a mesh interval. -/
noncomputable def latticeLowerEndpoint (N : ℕ) (h t : ℝ) : ℝ :=
  -1 + (clippedFloorIndex N h t : ℝ) * h

/-- Textbook C1, 1643–1652: the defining floor inequalities enclose a real number between consecutive integers. -/
theorem floor_real_bounds (u : ℝ) :
    ((⌊u⌋ : ℤ) : ℝ) ≤ u ∧ u < ((⌊u⌋ : ℤ) : ℝ) + 1 := by
  exact ⟨Int.floor_le u, Int.lt_floor_add_one u⟩

/-- Textbook C1, 1643–1652: casting the last integer index to the reals preserves subtraction of one. -/
theorem cast_int_nat_sub_one (N : ℕ) :
    (((N : ℤ) - 1 : ℤ) : ℝ) = (N : ℝ) - 1 := by
  push_cast
  ring

/-- Textbook C1, 1643–1652: a positive number of intervals has a nonnegative last lower index. -/
theorem int_nat_sub_one_nonneg {N : ℕ} (hN : 0 < N) :
    (0 : ℤ) ≤ (N : ℤ) - 1 := by omega

/-- Textbook C2, 1648–1653: an integer at most N is either below N or equal to N. -/
theorem int_floor_top_split {N : ℕ} {z : ℤ} (hz : z ≤ (N : ℤ)) :
    z ≤ (N : ℤ) - 1 ∨ z = (N : ℤ) := by omega

/-- Textbook C2, 1648–1653: multiplying the floor inequalities by the positive mesh encloses the shifted coordinate. -/
theorem scale_floor_inequalities {h u t : ℝ} {z : ℤ} (hh : 0 < h)
    (hu : u * h = t + 1) (hzlow : (z : ℝ) ≤ u) (hzup : u < (z : ℝ) + 1) :
    (z : ℝ) * h ≤ t + 1 ∧ t + 1 < (z : ℝ) * h + h := by
  constructor
  · rw [← hu]; exact mul_le_mul_of_nonneg_right hzlow (le_of_lt hh)
  · rw [← hu]
    have := mul_lt_mul_of_pos_right hzup hh
    nlinarith

/-- Textbook C2, 1648–1653: the last lower mesh point is one minus the mesh and its successor is one. -/
theorem top_endpoint_cast_algebra {N : ℕ} {h : ℝ} (hmul : (N : ℝ) * h = 2) :
    -1 + ((((N : ℤ) - 1 : ℤ) : ℝ)) * h = 1 - h ∧
      (-1 + ((((N : ℤ) - 1 : ℤ) : ℝ)) * h) + h = 1 := by
  rw [cast_int_nat_sub_one]
  constructor <;> nlinarith

/-- Textbook C1, 1643–1652: normalizing an interval coordinate puts it between zero and N. -/
theorem normalizedFloorInput_bounds {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    normalizedFloorInput h t ∈ Set.Icc (0 : ℝ) N := by
  have hm := mesh_identities N h hN hh
  constructor
  · exact div_nonneg (by linarith [ht.1]) hm.1.le
  · rw [normalizedFloorInput, div_le_iff₀ hm.1]
    linarith [hm.2.1, ht.2]

/-- Textbook C1, 1643–1652: the normalized floor index is an integer between zero and N. -/
theorem unclippedFloorIndex_bounds {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ unclippedFloorIndex h t ∧ unclippedFloorIndex h t ≤ (N : ℤ) := by
  have hb := normalizedFloorInput_bounds hN hh ht
  constructor
  · exact Int.floor_nonneg.mpr hb.1
  · have hle : (unclippedFloorIndex h t : ℝ) ≤ (N : ℝ) :=
      le_trans (floor_real_bounds (normalizedFloorInput h t)).1 hb.2
    exact_mod_cast hle

/-- Textbook C1, 1643–1652: clipping leaves every ordinary floor index unchanged. -/
theorem clippedFloorIndex_eq_floor {N : ℕ} {h t : ℝ}
    (hle : unclippedFloorIndex h t ≤ (N : ℤ) - 1) :
    clippedFloorIndex N h t = unclippedFloorIndex h t := by
  simp [clippedFloorIndex, min_eq_left hle]

/-- Textbook C2, 1648–1653: clipping an index at or above the last lower index returns that last index. -/
theorem clippedFloorIndex_eq_top {N : ℕ} {h t : ℝ}
    (hle : (N : ℤ) - 1 ≤ unclippedFloorIndex h t) :
    clippedFloorIndex N h t = (N : ℤ) - 1 := by
  simp [clippedFloorIndex, min_eq_right hle]

/-- Textbook C1, 1643–1652: the clipped integer index lies between zero and N minus one. -/
theorem clippedFloorIndex_bounds {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ clippedFloorIndex N h t ∧ clippedFloorIndex N h t ≤ (N : ℤ) - 1 := by
  have hb := unclippedFloorIndex_bounds hN hh ht
  exact ⟨le_min hb.1 (int_nat_sub_one_nonneg hN), min_le_right _ _⟩

/-- Textbook C1, 1643–1652: the selected endpoint is a lattice point below the top and leaves room for one mesh step. -/
theorem latticeLowerEndpoint_data {N : ℕ} {h t : ℝ} (hN : 0 < N)
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

/-- Textbook C2, 1648–1653: in the ordinary floor case, scaling its inequalities encloses the shifted coordinate. -/
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

/-- Textbook C2, 1648–1653: the top floor value forces t to equal one and selects the final mesh interval. -/
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

/-- Textbook C2, 1648–1653: either the ordinary floor interval or the final interval contains the original coordinate. -/
theorem clipped_floor_enclosure {N : ℕ} {h t : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    t ∈ Set.Icc (latticeLowerEndpoint N h t) (latticeLowerEndpoint N h t + h) := by
  rcases int_floor_top_split (unclippedFloorIndex_bounds hN hh ht).2 with hlow | htop
  · have hb := ordinary_floor_enclosure hN hh ht hlow
    dsimp [latticeLowerEndpoint]
    constructor <;> linarith [hb.1, hb.2]
  · obtain ⟨htone, _hc, hlower, hupper⟩ := top_floor_case hN hh ht htop
    have hp := (mesh_identities N h hN hh).1
    constructor <;> linarith

/-- Textbook C3, 1643–1656: after choosing a fixed index, the other two coordinates admit an increasing order. -/
theorem other_two_ordered (i : Fin 3) :
    ∃ j k : Fin 3, j < k ∧ i ≠ j ∧ i ≠ k ∧
      ∀ r : Fin 3, r = i ∨ r = j ∨ r = k := by
  fin_cases i
  · exact ⟨1, 2, by decide, by decide, by decide, by intro r; fin_cases r <;> simp⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by intro r; fin_cases r <;> simp⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by intro r; fin_cases r <;> simp⟩

/-- Textbook C3, 1643–1656: two complementary directions exhausting the coordinates with the fixed index are distinct. -/
theorem complementary_directions_ne {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hexhaust : ∀ r : Fin 3, r = i ∨ r = j ∨ r = k) : j ≠ k := by
  intro hjk
  subst k
  have h0 := hexhaust 0
  have h1 := hexhaust 1
  have h2 := hexhaust 2
  fin_cases i <;> fin_cases j <;> simp_all

/-- Textbook C3, 1643–1656: assemble an ambient point from prescribed values at the three chosen indices. -/
def ambientOfThreeCoordinates (i j k : Fin 3) (xi xj xk : ℝ) : Ambient :=
  WithLp.toLp 2 (fun r : Fin 3 =>
    if r = i then xi else if r = j then xj else if r = k then xk else 0)

/-- Textbook C3, 1643–1656: the assembled point takes its first prescribed coordinate value. -/
theorem ambientOfThreeCoordinates_apply_i (i j k : Fin 3) (xi xj xk : ℝ) :
    ambientOfThreeCoordinates i j k xi xj xk i = xi := by simp [ambientOfThreeCoordinates]
/-- Textbook C3, 1643–1656: distinctness from the first index recovers the second prescribed value. -/
theorem ambientOfThreeCoordinates_apply_j {i j k : Fin 3} (hji : j ≠ i) (xi xj xk : ℝ) :
    ambientOfThreeCoordinates i j k xi xj xk j = xj := by simp [ambientOfThreeCoordinates, hji]
/-- Textbook C3, 1643–1656: distinctness from the preceding indices recovers the third prescribed value. -/
theorem ambientOfThreeCoordinates_apply_k {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (xi xj xk : ℝ) : ambientOfThreeCoordinates i j k xi xj xk k = xk := by
  simp [ambientOfThreeCoordinates, hki, hkj]

/-- Textbook C3, 1643–1656: retain the saturated coordinate and replace the other two by their lower mesh endpoints. -/
noncomputable def coverageVertex (N : ℕ) (h : ℝ) (x : Ambient) (i j k : Fin 3) : Ambient :=
  ambientOfThreeCoordinates i j k (x i) (latticeLowerEndpoint N h (x j))
    (latticeLowerEndpoint N h (x k))

/-- Textbook C3, 1643–1656: the coverage vertex retains the original fixed coordinate. -/
theorem coverageVertex_apply_i (N : ℕ) (h : ℝ) (x : Ambient) (i j k : Fin 3) :
    coverageVertex N h x i j k i = x i := by
  simp [coverageVertex, ambientOfThreeCoordinates]

/-- Textbook C3, 1643–1656: the coverage vertex uses the lower mesh endpoint in the first moving direction. -/
theorem coverageVertex_apply_j {N : ℕ} {h : ℝ} {x : Ambient} {i j k : Fin 3}
    (hji : j ≠ i) :
    coverageVertex N h x i j k j = latticeLowerEndpoint N h (x j) := by
  simp [coverageVertex, ambientOfThreeCoordinates, hji]

/-- Textbook C3, 1643–1656: the coverage vertex uses the lower mesh endpoint in the second moving direction. -/
theorem coverageVertex_apply_k {N : ℕ} {h : ℝ} {x : Ambient} {i j k : Fin 3}
    (hki : k ≠ i) (hkj : k ≠ j) :
    coverageVertex N h x i j k k = latticeLowerEndpoint N h (x k) := by
  simp [coverageVertex, ambientOfThreeCoordinates, hki, hkj]

/-- Textbook C3, 1643–1656: a boundary point has a signed saturated coordinate and all coordinates in [-1,1]. -/
theorem boundary_face_coordinate_data {x : Ambient} (hx : x ∈ boundary) :
    ∃ (i : Fin 3) (σ : {r : ℝ // r = -1 ∨ r = 1}),
      x ∈ face i σ ∧ x i = σ.1 ∧ ∀ r : Fin 3, x r ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨i, σ, hface⟩ := exists_mem_face hx
  refine ⟨i, σ, hface, (mem_face_iff x i σ).mp hface |>.2, ?_⟩
  intro r
  apply abs_le.mp
  rw [← (show maxAbs x = 1 from hx)]
  fin_cases r <;> simp [maxAbs]

/-- Textbook C3, 1643–1656: either signed endpoint belongs to the mesh lattice. -/
theorem face_coordinate_mem_lattice {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {x : Ambient} {i : Fin 3}
    {σ : {r : ℝ // r = -1 ∨ r = 1}} (hxi : x i = σ.1) : x i ∈ lattice N h := by
  rw [hxi]
  rcases σ.property with hneg | hpos
  · rw [hneg]; exact (lattice_endpoints hN hh).1
  · rw [hpos]; exact (lattice_endpoints hN hh).2

/-- Textbook C3, 1643–1656: the fixed lattice coordinate and the two lower endpoints make all vertex coordinates lattice points. -/
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

/-- Textbook C3, 1643–1656: lattice bounds and the retained saturated coordinate put the constructed vertex on the boundary. -/
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

/-- Textbook C3, 1643–1656: coordinatewise lattice membership together with boundary membership defines a vertex. -/
theorem coverageVertex_mem_vertices {N : ℕ} {h : ℝ} {x : Ambient} {i j k : Fin 3}
    (hlattice : ∀ r : Fin 3, coverageVertex N h x i j k r ∈ lattice N h)
    (hboundary : coverageVertex N h x i j k ∈ boundary) :
    coverageVertex N h x i j k ∈ vertices N h := ⟨hlattice, hboundary⟩

/-- Textbook C3, 1643–1656: both selected lower endpoints leave room for one mesh step in their moving directions. -/
theorem coverageVertex_direction_bounds {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {x : Ambient} {i j k : Fin 3}
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hxj : x j ∈ Set.Icc (-1 : ℝ) 1) (hxk : x k ∈ Set.Icc (-1 : ℝ) 1) :
    coverageVertex N h x i j k j ≤ 1 - h ∧ coverageVertex N h x i j k k ≤ 1 - h := by
  rw [coverageVertex_apply_j hji, coverageVertex_apply_k hki hkj]
  exact ⟨(latticeLowerEndpoint_data hN hh hxj).2, (latticeLowerEndpoint_data hN hh hxk).2⟩

/-- Textbook C3, 1643–1656: the saturated fixed coordinate and the direction bounds make the coverage square admissible. -/
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

/-- Textbook C3, 1643–1656: an admissible coverage parameter supplies a member of the square family. -/
theorem coverageSquare_mem_squares {N : ℕ} {h : ℝ} {x : Ambient} {i j k : Fin 3}
    (hp : SquareParam N h (coverageVertex N h x i j k) j k) :
    squareGeom h (coverageVertex N h x i j k) j k ∈ squares N h :=
  ⟨coverageVertex N h x i j k, j, k, hp, rfl⟩

/-- Textbook C3, 1643–1656: the fixed coordinate equation and two floor enclosures place the original point in its square. -/
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

/-- Textbook C3, 1643–1656 (Lemma 3.3): retaining a saturated coordinate and taking two clipped lower endpoints covers each boundary point by a square. -/
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

/-! CD10C-I implements ordinary textbook Lemma 3.4 (I1, lines 1658–1668) and Lemma 3.5
(I2, lines 1670–1682). Every I1 declaration below formalizes a stated coordinate, interval, or
assembly step of lines 1658–1668; every I2 declaration formalizes a parameter, side, vertex, or
edge step of lines 1670–1682. -/

/-- I1 representation: an open interval above a bounded lattice point stays strictly in the cube. -/
private theorem open_mesh_coordinate_abs_lt {N : ℕ} {h a x : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (ha : a ∈ lattice N h) (hau : a ≤ 1 - h)
    (hx : x ∈ Set.Ioo a (a + h)) : |x| < 1 := by
  rw [abs_lt]
  have hab := lattice_subset_interval hN hh ha
  rcases hab with ⟨hab₀, hab₁⟩
  rcases hx with ⟨hx₀, hx₁⟩
  constructor <;> linarith

/-- I1 representation: the two moving directions are determined by a common remaining index. -/
private theorem ordered_pair_eq_of_same_remaining {j k p q i : Fin 3}
    (hjk : j < k) (hpq : p < q) (hij : i ≠ j) (hik : i ≠ k)
    (hip : i ≠ p) (hiq : i ≠ q) : j = p ∧ k = q := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases p <;> fin_cases q <;> omega

/-- I1 representation: a point open in both coordinate rectangles forces their fixed indices to agree. -/
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

/-- I1 interval arithmetic: overlapping open mesh intervals with lattice lower endpoints coincide. -/
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

/-- I1 assembly: fixed coordinate plus the two coincident lower intervals identify lower corners. -/
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

/-- Textbook I1: intrinsic relative interiors of distinct permitted squares are disjoint. -/
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

/-- I2 scalar representation: a closed unit parameter outside the open unit interval is an endpoint. -/
private theorem closed_not_open_endpoint {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hna : a ∉ Set.Ioo (0 : ℝ) 1) : a = 0 ∨ a = 1 := by
  rcases ha with ⟨ha0, ha1⟩
  simp only [Set.mem_Ioo, not_and_or, not_lt] at hna
  rcases hna with ha0' | ha1'
  · exact Or.inl (le_antisymm ha0' ha0)
  · exact Or.inr (le_antisymm ha1 ha1')

/-- I2 representation: closed parameters for a square boundary point, with an endpoint case. -/
private theorem square_boundary_parameter_case
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    {s : Set Ambient} (hs : s ∈ squares N h) {x : Ambient}
    (hxs : x ∈ s) (hxopen : x ∉ squareRelInterior N h ⟨s, hs⟩) :
    ∃ (v : Ambient) (j k : Fin 3) (a b : ℝ),
      SquareParam N h v j k ∧ s = squareGeom h v j k ∧
      a ∈ Set.Icc (0 : ℝ) 1 ∧ b ∈ Set.Icc (0 : ℝ) 1 ∧
      x = v + (a * h) • EuclideanSpace.single j 1 +
        (b * h) • EuclideanSpace.single k 1 ∧
      (a = 0 ∨ a = 1 ∨ b = 0 ∨ b = 1) := by
  obtain ⟨v, j, k, hv, hjk, hvj, hvk, hsub, hsgeom, hsopen⟩ := square_presentation hN hh hs
  rw [hsgeom] at hxs
  obtain ⟨a, ha, b, hb, hx⟩ := hxs
  have hend : a = 0 ∨ a = 1 ∨ b = 0 ∨ b = 1 := by
    by_cases hao : a ∈ Set.Ioo (0 : ℝ) 1
    · by_cases hbo : b ∈ Set.Ioo (0 : ℝ) 1
      · exact False.elim (hxopen (hsopen.symm ▸ ⟨a, hao, b, hbo, hx⟩))
      · rcases closed_not_open_endpoint hb hbo with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    · rcases closed_not_open_endpoint ha hao with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  exact ⟨v, j, k, a, b, ⟨hv, hjk, hvj, hvk, hsub⟩, hsgeom, ha, hb, hx, hend⟩

/-- Textbook I2 representation: the initial point of the upper k-edge is one j-mesh step from v. -/
private noncomputable def shiftedVertexJ (h : ℝ) (v : Ambient) (j : Fin 3) : Ambient :=
  v + h • EuclideanSpace.single j 1
/-- Textbook I2 representation: the initial point of the upper j-edge is one k-mesh step from v. -/
private noncomputable def shiftedVertexK (h : ℝ) (v : Ambient) (k : Fin 3) : Ambient :=
  v + h • EuclideanSpace.single k 1

/-- Textbook I2 representation: the j-shift raises coordinate j by exactly h. -/
private theorem shiftedVertexJ_apply_same (h : ℝ) (v : Ambient) (j : Fin 3) :
    shiftedVertexJ h v j j = v j + h := by simp [shiftedVertexJ]
/-- Textbook I2 representation: the j-shift preserves every coordinate other than j. -/
private theorem shiftedVertexJ_apply_ne (h : ℝ) (v : Ambient) {j r : Fin 3} (hr : r ≠ j) :
    shiftedVertexJ h v j r = v r := by simp [shiftedVertexJ, hr]
/-- Textbook I2 representation: the k-shift raises coordinate k by exactly h. -/
private theorem shiftedVertexK_apply_same (h : ℝ) (v : Ambient) (k : Fin 3) :
    shiftedVertexK h v k k = v k + h := by simp [shiftedVertexK]
/-- Textbook I2 representation: the k-shift preserves every coordinate other than k. -/
private theorem shiftedVertexK_apply_ne (h : ℝ) (v : Ambient) {k r : Fin 3} (hr : r ≠ k) :
    shiftedVertexK h v k r = v r := by simp [shiftedVertexK, hr]

/-- Textbook I2, lines 1670–1682: the two descriptions of the opposite square corner coincide. -/
private theorem shifted_corner_commutes (h : ℝ) (v : Ambient) (j k : Fin 3) :
    shiftedVertexK h (shiftedVertexJ h v j) k =
      shiftedVertexJ h (shiftedVertexK h v k) j := by
  simp only [shiftedVertexJ, shiftedVertexK]
  module

/-- Textbook I2 representation: the lower j-edge line map is square parameter (t,0). -/
private theorem bottomJ_lineMap_embedding (h t : ℝ) (v : Ambient) (j k : Fin 3)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap v (v + h • EuclideanSpace.single j 1) t ∈
        segment ℝ v (v + h • EuclideanSpace.single j 1) ∧
      AffineMap.lineMap v (v + h • EuclideanSpace.single j 1) t =
        v + (t * h) • EuclideanSpace.single j 1 +
          ((0 : ℝ) * h) • EuclideanSpace.single k 1 := by
  constructor
  · exact lineMap_mem_segment ℝ v _ ht
  · rw [AffineMap.lineMap_apply_module]
    module

/-- Textbook I2 representation: the lower k-edge line map is square parameter (0,t). -/
private theorem bottomK_lineMap_embedding (h t : ℝ) (v : Ambient) (j k : Fin 3)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap v (v + h • EuclideanSpace.single k 1) t ∈
        segment ℝ v (v + h • EuclideanSpace.single k 1) ∧
      AffineMap.lineMap v (v + h • EuclideanSpace.single k 1) t =
        v + ((0 : ℝ) * h) • EuclideanSpace.single j 1 +
          (t * h) • EuclideanSpace.single k 1 := by
  constructor
  · exact lineMap_mem_segment ℝ v _ ht
  · rw [AffineMap.lineMap_apply_module]
    module

/-- Textbook I2 representation: the upper j-edge from the k-shift is square parameter (t,1). -/
private theorem topJ_lineMap_embedding (h t : ℝ) (v : Ambient) (j k : Fin 3)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (v + h • EuclideanSpace.single k 1)
        (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) t ∈
        segment ℝ (v + h • EuclideanSpace.single k 1)
          (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) ∧
      AffineMap.lineMap (v + h • EuclideanSpace.single k 1)
        (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) t =
        v + (t * h) • EuclideanSpace.single j 1 +
          ((1 : ℝ) * h) • EuclideanSpace.single k 1 := by
  constructor
  · exact lineMap_mem_segment ℝ _ _ ht
  · rw [AffineMap.lineMap_apply_module]
    module

/-- Textbook I2 representation: the upper k-edge from the j-shift is square parameter (1,t). -/
private theorem topK_lineMap_embedding (h t : ℝ) (v : Ambient) (j k : Fin 3)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (v + h • EuclideanSpace.single j 1)
        (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1) t ∈
        segment ℝ (v + h • EuclideanSpace.single j 1)
          (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1) ∧
      AffineMap.lineMap (v + h • EuclideanSpace.single j 1)
        (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1) t =
        v + ((1 : ℝ) * h) • EuclideanSpace.single j 1 +
          (t * h) • EuclideanSpace.single k 1 := by
  constructor
  · exact lineMap_mem_segment ℝ _ _ ht
  · rw [AffineMap.lineMap_apply_module]
    module

/-- Textbook I2 representation: every point of the lower j-segment has square parameters (t,0). -/
private theorem bottomJ_segment_extract {h : ℝ} {v y : Ambient} {j k : Fin 3}
    (hy : y ∈ segment ℝ v (v + h • EuclideanSpace.single j 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      y = v + (t * h) • EuclideanSpace.single j 1 +
        ((0 : ℝ) * h) • EuclideanSpace.single k 1 := by
  rw [segment_eq_image_lineMap ℝ] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨t, ht, (bottomJ_lineMap_embedding h t v j k ht).2⟩

/-- Textbook I2 representation: every point of the lower k-segment has square parameters (0,t). -/
private theorem bottomK_segment_extract {h : ℝ} {v y : Ambient} {j k : Fin 3}
    (hy : y ∈ segment ℝ v (v + h • EuclideanSpace.single k 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      y = v + ((0 : ℝ) * h) • EuclideanSpace.single j 1 +
        (t * h) • EuclideanSpace.single k 1 := by
  rw [segment_eq_image_lineMap ℝ] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨t, ht, (bottomK_lineMap_embedding h t v j k ht).2⟩

/-- Textbook I2 representation: every point of the upper j-segment has square parameters (t,1). -/
private theorem topJ_segment_extract {h : ℝ} {v y : Ambient} {j k : Fin 3}
    (hy : y ∈ segment ℝ (v + h • EuclideanSpace.single k 1)
      (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      y = v + (t * h) • EuclideanSpace.single j 1 +
        ((1 : ℝ) * h) • EuclideanSpace.single k 1 := by
  rw [segment_eq_image_lineMap ℝ] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨t, ht, (topJ_lineMap_embedding h t v j k ht).2⟩

/-- Textbook I2 representation: every point of the upper k-segment has square parameters (1,t). -/
private theorem topK_segment_extract {h : ℝ} {v y : Ambient} {j k : Fin 3}
    (hy : y ∈ segment ℝ (v + h • EuclideanSpace.single j 1)
      (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      y = v + ((1 : ℝ) * h) • EuclideanSpace.single j 1 +
        (t * h) • EuclideanSpace.single k 1 := by
  rw [segment_eq_image_lineMap ℝ] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨t, ht, (topK_lineMap_embedding h t v j k ht).2⟩

/-- Textbook I2 representation: admissible lower-j edge data constructs the literal edge. -/
private theorem bottomJ_edge_constructor {N : ℕ} {h : ℝ} {v : Ambient} {j : Fin 3}
    (hv : v ∈ vertices N h) (hvj : v j ≤ 1 - h)
    (hsub : segment ℝ v (v + h • EuclideanSpace.single j 1) ⊆ boundary) :
    segment ℝ v (v + h • EuclideanSpace.single j 1) ∈ edges N h :=
  edge_mem_iff.mpr ⟨v, j, ⟨hv, hvj, hsub⟩, rfl⟩

/-- Textbook I2 representation: admissible lower-k edge data constructs the literal edge. -/
private theorem bottomK_edge_constructor {N : ℕ} {h : ℝ} {v : Ambient} {k : Fin 3}
    (hv : v ∈ vertices N h) (hvk : v k ≤ 1 - h)
    (hsub : segment ℝ v (v + h • EuclideanSpace.single k 1) ⊆ boundary) :
    segment ℝ v (v + h • EuclideanSpace.single k 1) ∈ edges N h :=
  edge_mem_iff.mpr ⟨v, k, ⟨hv, hvk, hsub⟩, rfl⟩

/-- Textbook I2 representation: admissible k-shift/j-direction data constructs the upper j-edge. -/
private theorem topJ_edge_constructor {N : ℕ} {h : ℝ} {v : Ambient} {j k : Fin 3}
    (hv : v + h • EuclideanSpace.single k 1 ∈ vertices N h)
    (hvj : (v + h • EuclideanSpace.single k 1 : Ambient) j ≤ 1 - h)
    (hsub : segment ℝ (v + h • EuclideanSpace.single k 1)
      (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) ⊆ boundary) :
    segment ℝ (v + h • EuclideanSpace.single k 1)
      (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) ∈ edges N h :=
  edge_mem_iff.mpr ⟨v + h • EuclideanSpace.single k 1, j, ⟨hv, hvj, hsub⟩, rfl⟩

/-- Textbook I2 representation: admissible j-shift/k-direction data constructs the upper k-edge. -/
private theorem topK_edge_constructor {N : ℕ} {h : ℝ} {v : Ambient} {j k : Fin 3}
    (hv : v + h • EuclideanSpace.single j 1 ∈ vertices N h)
    (hvk : (v + h • EuclideanSpace.single j 1 : Ambient) k ≤ 1 - h)
    (hsub : segment ℝ (v + h • EuclideanSpace.single j 1)
      (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1) ⊆ boundary) :
    segment ℝ (v + h • EuclideanSpace.single j 1)
      (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1) ∈ edges N h :=
  edge_mem_iff.mpr ⟨v + h • EuclideanSpace.single j 1, k, ⟨hv, hvk, hsub⟩, rfl⟩

set_option linter.unusedVariables false in
/-- I2 validity: the two lower sides are permitted edges. -/
private theorem bottom_square_edges_valid
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    {v : Ambient} {j k : Fin 3} (hp : SquareParam N h v j k) :
    segment ℝ v (v + h • EuclideanSpace.single j 1) ∈ edges N h ∧
    segment ℝ v (v + h • EuclideanSpace.single k 1) ∈ edges N h := by
  apply And.intro
  · apply bottomJ_edge_constructor hp.1 hp.2.2.1
    intro y hy
    obtain ⟨t, ht, rfl⟩ := bottomJ_segment_extract (k := k) hy
    exact hp.2.2.2.2 ⟨t, ht, 0, by simp, rfl⟩
  · apply bottomK_edge_constructor hp.1 hp.2.2.2.1
    intro y hy
    obtain ⟨t, ht, rfl⟩ := bottomK_segment_extract (j := j) hy
    exact hp.2.2.2.2 ⟨0, by simp, t, ht, rfl⟩

/-- I2 validity: stepping to either upper-side initial point gives a vertex. -/
private theorem shifted_square_vertices_valid
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    {v : Ambient} {j k : Fin 3} (hp : SquareParam N h v j k) :
    shiftedVertexJ h v j ∈ vertices N h ∧ shiftedVertexK h v k ∈ vertices N h := by
  constructor
  · constructor
    · intro r; by_cases hr : r = j
      · subst r; simpa [shiftedVertexJ_apply_same] using lattice_successor hN hh (hp.1.1 j) hp.2.2.1
      · simpa [shiftedVertexJ_apply_ne h v hr] using hp.1.1 r
    · have H := bottomJ_lineMap_embedding h 1 v j k (by norm_num)
      have heq : v + h • EuclideanSpace.single j 1 =
          v + ((1 : ℝ) * h) • EuclideanSpace.single j 1 +
            ((0 : ℝ) * h) • EuclideanSpace.single k 1 := by
        calc
          v + h • EuclideanSpace.single j 1 =
              AffineMap.lineMap v (v + h • EuclideanSpace.single j 1) 1 := by
                rw [AffineMap.lineMap_apply_one]
          _ = _ := H.2
      exact hp.2.2.2.2 ⟨1, by norm_num, 0, by norm_num, heq⟩
  · constructor
    · intro r; by_cases hr : r = k
      · subst r; simpa [shiftedVertexK_apply_same] using lattice_successor hN hh (hp.1.1 k) hp.2.2.2.1
      · simpa [shiftedVertexK_apply_ne h v hr] using hp.1.1 r
    · have H := bottomK_lineMap_embedding h 1 v j k (by norm_num)
      have heq : v + h • EuclideanSpace.single k 1 =
          v + ((0 : ℝ) * h) • EuclideanSpace.single j 1 +
            ((1 : ℝ) * h) • EuclideanSpace.single k 1 := by
        calc
          v + h • EuclideanSpace.single k 1 =
              AffineMap.lineMap v (v + h • EuclideanSpace.single k 1) 1 := by
                rw [AffineMap.lineMap_apply_one]
          _ = _ := H.2
      exact hp.2.2.2.2 ⟨0, by norm_num, 1, by norm_num, heq⟩

/-- I2 validity: the two translated upper sides are permitted edges. -/
private theorem top_square_edges_valid
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    {v : Ambient} {j k : Fin 3} (hp : SquareParam N h v j k) :
    segment ℝ (v + h • EuclideanSpace.single k 1)
      (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) ∈ edges N h ∧
    segment ℝ (v + h • EuclideanSpace.single j 1)
      (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1) ∈ edges N h := by
  obtain ⟨hvj, hvk⟩ := shifted_square_vertices_valid hN hh hp
  constructor
  · apply topJ_edge_constructor hvk
      ((shiftedVertexK_apply_ne h v (ne_of_lt hp.2.1)).trans_le hp.2.2.1)
    intro y hy
    obtain ⟨t, ht, rfl⟩ := topJ_segment_extract hy
    exact hp.2.2.2.2 ⟨t, ht, 1, by simp, rfl⟩
  · apply topK_edge_constructor hvj
      ((shiftedVertexJ_apply_ne h v (ne_of_lt hp.2.1).symm).trans_le hp.2.2.2.1)
    intro y hy
    obtain ⟨t, ht, rfl⟩ := topK_segment_extract hy
    exact hp.2.2.2.2 ⟨1, by simp, t, ht, rfl⟩

/-- I2 representation: an endpoint parameter places the point on one displayed side. -/
private theorem square_boundary_mem_four_segments
    {h a b : ℝ} {x v : Ambient} {j k : Fin 3}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hx : x = v + (a * h) • EuclideanSpace.single j 1 +
      (b * h) • EuclideanSpace.single k 1)
    (hend : a = 0 ∨ a = 1 ∨ b = 0 ∨ b = 1) :
    x ∈ segment ℝ v (v + h • EuclideanSpace.single j 1) ∨
    x ∈ segment ℝ v (v + h • EuclideanSpace.single k 1) ∨
    x ∈ segment ℝ (v + h • EuclideanSpace.single k 1)
      (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) ∨
    x ∈ segment ℝ (v + h • EuclideanSpace.single j 1)
      (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1) := by
  rcases hend with rfl | rfl | rfl | rfl
  · right; left
    have H := bottomK_lineMap_embedding h b v j k hb
    rw [hx, ← H.2]
    exact H.1
  · right; right; right
    have H := topK_lineMap_embedding h b v j k hb
    rw [hx, ← H.2]
    exact H.1
  · left
    have H := bottomJ_lineMap_embedding h a v j k ha
    rw [hx, ← H.2]
    exact H.1
  · right; right; left
    have H := topJ_lineMap_embedding h a v j k ha
    rw [hx, ← H.2]
    exact H.1

/-- Textbook I2: the square boundary is carried by its complete four-edge receipt. -/
public theorem square_boundary_edges
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    {s : Set Ambient} (hs : s ∈ squares N h) {x : Ambient}
    (hxs : x ∈ s) (hxopen : x ∉ squareRelInterior N h ⟨s, hs⟩) :
    ∃ (v : Ambient) (j k : Fin 3),
      v ∈ vertices N h ∧ j < k ∧ v j ≤ 1 - h ∧ v k ≤ 1 - h ∧
      s = {y : Ambient | ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
        y = v + (a * h) • EuclideanSpace.single j 1 +
          (b * h) • EuclideanSpace.single k 1} ∧
      segment ℝ v (v + h • EuclideanSpace.single j 1) ∈ edges N h ∧
      segment ℝ v (v + h • EuclideanSpace.single k 1) ∈ edges N h ∧
      segment ℝ (v + h • EuclideanSpace.single k 1)
        (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) ∈ edges N h ∧
      segment ℝ (v + h • EuclideanSpace.single j 1)
        (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1) ∈ edges N h ∧
      (x ∈ segment ℝ v (v + h • EuclideanSpace.single j 1) ∨
       x ∈ segment ℝ v (v + h • EuclideanSpace.single k 1) ∨
       x ∈ segment ℝ (v + h • EuclideanSpace.single k 1)
         (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) ∨
       x ∈ segment ℝ (v + h • EuclideanSpace.single j 1)
         (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1)) := by
  obtain ⟨v, j, k, a, b, hp, hsgeom, ha, hb, hx, hend⟩ :=
    square_boundary_parameter_case hN hh hs hxs hxopen
  obtain ⟨hej, hek⟩ := bottom_square_edges_valid hN hh hp
  obtain ⟨heJ, heK⟩ := top_square_edges_valid hN hh hp
  exact ⟨v, j, k, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hsgeom,
    hej, hek, heJ, heK, square_boundary_mem_four_segments ha hb hx hend⟩

/-- Textbook Lemma 3.6, lines 1684–1688: every coordinate of a mesh vertex belongs to the
one-dimensional mesh lattice. -/
private theorem vertex_coordinate_mem_lattice {N : ℕ} {h : ℝ} {v : Ambient}
    (hv : v ∈ vertices N h) (i : Fin 3) : v i ∈ lattice N h :=
  hv.1 i

/-- Textbook Lemma 3.6, lines 1684–1688: two unequal points in three-coordinate space differ in
at least one coordinate. -/
private theorem exists_ne_coordinate {v w : Ambient} (hvw : v ≠ w) :
    ∃ i : Fin 3, v i ≠ w i := by
  by_contra h
  push Not at h
  exact hvw (PiLp.ext h)

/-- Textbook Lemma 3.6, lines 1684–1688: unequal coordinates of two mesh vertices are separated
by at least one mesh length. -/
private theorem vertex_coordinate_separation {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v w : Ambient} (hv : v ∈ vertices N h)
    (hw : w ∈ vertices N h) {i : Fin 3} (hi : v i ≠ w i) : h ≤ |v i - w i| :=
  lattice_separation hN hh (vertex_coordinate_mem_lattice hv i)
    (vertex_coordinate_mem_lattice hw i) hi

/-- Textbook Lemma 3.6, lines 1684–1688: the absolute value of any coordinate is bounded by the
maximum absolute coordinate. -/
private theorem abs_apply_le_maxAbs (x : Ambient) (i : Fin 3) : |x i| ≤ maxAbs x := by
  fin_cases i <;> simp [maxAbs]

/-- Textbook Lemma 3.6, lines 1684–1688: distinct mesh vertices are separated by one mesh length
in maximum-coordinate distance, which is bounded above by Euclidean distance. -/
public theorem vertex_separation {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v w : Ambient} (hv : v ∈ vertices N h)
    (hw : w ∈ vertices N h) (hvw : v ≠ w) :
    h ≤ maxAbs (v - w) ∧ maxAbs (v - w) ≤ ‖v - w‖ := by
  obtain ⟨i, hi⟩ := exists_ne_coordinate hvw
  constructor
  · exact le_trans (vertex_coordinate_separation hN hh hv hw hi)
      (by simpa using abs_apply_le_maxAbs (v - w) i)
  · exact maxAbs_le_norm (v - w)

/-- Textbook Lemma 3.7(a), lines 1690–1696 and 1700–1712: an oriented edge direction is a
positive or negative coordinate unit vector. -/
private def SignedCoordinateUnit (u : Ambient) : Prop :=
  ∃ i : Fin 3, u = EuclideanSpace.single i 1 ∨ u = -EuclideanSpace.single i 1

/-- Textbook Lemma 3.7(a), lines 1690–1696 and 1700–1712: an edge can be oriented away from
either chosen endpoint as `w + t u`, for `0 ≤ t ≤ h` and a signed coordinate direction. -/
private theorem edge_orientation_from_endpoint {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {e : Set Ambient} (he : e ∈ edges N h) {w : Ambient}
    (hw : w ∈ edgeEndpoints N h ⟨e, he⟩) :
    ∃ u : Ambient, SignedCoordinateUnit u ∧
      e = {p : Ambient | ∃ t ∈ Set.Icc (0 : ℝ) h, p = w + t • u} := by
  obtain ⟨v, j, _hv, _hvj, _hface, hedge, hend⟩ := edge_presentation hN hh he
  have hpos := mesh_pos hN hh
  rw [hend] at hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · refine ⟨EuclideanSpace.single j 1, ⟨j, Or.inl rfl⟩, ?_⟩
    rw [hedge]
    ext p
    constructor
    · intro hp
      obtain ⟨a, ha, rfl⟩ := edge_parameter_extract hp
      exact ⟨a * h, ⟨mul_nonneg ha.1 hpos.le,
        by simpa using mul_le_mul_of_nonneg_right ha.2 hpos.le⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      rw [segment_eq_image]
      refine ⟨t / h, ⟨div_nonneg ht.1 hpos.le, (div_le_one hpos).2 ht.2⟩, ?_⟩
      apply PiLp.ext
      intro k
      simp only [PiLp.add_apply, PiLp.smul_apply]
      ring_nf
      simp [ne_of_gt hpos]
  · refine ⟨-EuclideanSpace.single j 1, ⟨j, Or.inr rfl⟩, ?_⟩
    rw [hedge]
    ext p
    constructor
    · intro hp
      obtain ⟨a, ha, rfl⟩ := edge_parameter_extract hp
      refine ⟨(1 - a) * h, ⟨mul_nonneg (sub_nonneg.mpr ha.2) hpos.le, ?_⟩, ?_⟩
      · simpa using mul_le_mul_of_nonneg_right (by linarith [ha.1] : 1 - a ≤ 1) hpos.le
      · module
    · rintro ⟨t, ht, rfl⟩
      rw [segment_eq_image]
      refine ⟨1 - t / h,
        ⟨sub_nonneg.mpr ((div_le_one hpos).2 ht.2), by linarith [div_nonneg ht.1 hpos.le]⟩, ?_⟩
      apply PiLp.ext
      intro k
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply]
      ring_nf
      simp [ne_of_gt hpos]

/-- Textbook Lemma 3.7(a), lines 1690–1696 and 1700–1712: two distinct edges oriented from
the same endpoint cannot have the same direction. -/
private theorem distinct_edge_orientations {h : ℝ} {e e' : Set Ambient} {w u u' : Ambient}
    (heq : e = {p : Ambient | ∃ t ∈ Set.Icc (0 : ℝ) h, p = w + t • u})
    (heq' : e' = {p : Ambient | ∃ t ∈ Set.Icc (0 : ℝ) h, p = w + t • u'})
    (hee' : e ≠ e') : u ≠ u' := by
  intro huu
  apply hee'
  rw [heq, heq', huu]

/-- Textbook Lemma 3.7(a), lines 1702–1712: every signed coordinate direction has Euclidean
norm one. -/
private theorem signedCoordinateUnit_norm {u : Ambient} (hu : SignedCoordinateUnit u) : ‖u‖ = 1 := by
  rcases hu with ⟨i, rfl | rfl⟩ <;> simp [PiLp.norm_single]

/-- Textbook Lemma 3.7(a), lines 1702–1712: unequal signed coordinate directions are orthogonal
or oppositely collinear, so their real inner product is nonpositive. -/
private theorem signedCoordinateUnit_inner_nonpos {u u' : Ambient}
    (hu : SignedCoordinateUnit u) (hu' : SignedCoordinateUnit u') (hne : u ≠ u') :
    inner ℝ u u' ≤ 0 := by
  rcases hu with ⟨i, rfl | rfl⟩ <;> rcases hu' with ⟨j, rfl | rfl⟩
  · by_cases hij : i = j
    · subst j; exact False.elim (hne rfl)
    · simp [hij, EuclideanSpace.inner_single_left]
  · by_cases hij : i = j <;> simp [hij, EuclideanSpace.inner_single_left]
  · by_cases hij : i = j <;> simp [hij, EuclideanSpace.inner_single_left]
  · by_cases hij : i = j
    · subst j; exact False.elim (hne rfl)
    · simp [hij, EuclideanSpace.inner_single_left]

/-- Textbook Lemma 3.7(a), lines 1702–1712: for nonnegative radial parameters and nonpositive
cross term, the norm-square expansion makes radial distance no larger than cross-edge distance. -/
private theorem oriented_distance_le {t t' : ℝ} {u u' : Ambient}
    (ht : 0 ≤ t) (ht' : 0 ≤ t') (hu : SignedCoordinateUnit u)
    (hu' : SignedCoordinateUnit u') (hinner : inner ℝ u u' ≤ 0) :
    ‖t • u‖ ≤ ‖t • u - t' • u'‖ := by
  have hun := signedCoordinateUnit_norm hu
  have hun' := signedCoordinateUnit_norm hu'
  have hprod : 0 ≤ 2 * t * t' := mul_nonneg (mul_nonneg (by norm_num) ht) ht'
  have hcross : 0 ≤ -(2 * t * t' * inner ℝ u u') := by
    nlinarith [mul_nonneg hprod (neg_nonneg.mpr hinner)]
  have hexpand : ‖t • u - t' • u'‖ ^ 2 =
      t ^ 2 + t' ^ 2 - 2 * t * t' * inner ℝ u u' := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right,
      hun, hun', real_inner_self_eq_norm_sq, one_pow]
    rw [real_inner_comm u' u]
    ring
  have hrad : ‖t • u‖ ^ 2 = t ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, hun, mul_one, sq_abs]
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [hrad, hexpand]
  nlinarith

/-- Textbook Lemma 3.7(a), lines 1690–1696 and 1700–1712: distinct edges sharing an endpoint
meet only there, and the distance from that endpoint along one edge is bounded by every
cross-edge distance. -/
public theorem edge_common_endpoint_geometry {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {e e' : Set Ambient} (he : e ∈ edges N h)
    (he' : e' ∈ edges N h) (hee' : e ≠ e') {w : Ambient}
    (hw : w ∈ edgeEndpoints N h ⟨e, he⟩)
    (hw' : w ∈ edgeEndpoints N h ⟨e', he'⟩) :
    e ∩ e' = {w} ∧
      ∀ {p p' : Ambient}, p ∈ e → p' ∈ e' → ‖p - w‖ ≤ ‖p - p'‖ := by
  obtain ⟨u, hu, heq⟩ := edge_orientation_from_endpoint hN hh he hw
  obtain ⟨u', hu', heq'⟩ := edge_orientation_from_endpoint hN hh he' hw'
  have hne := distinct_edge_orientations heq heq' hee'
  have hinner := signedCoordinateUnit_inner_nonpos hu hu' hne
  have hinner' := signedCoordinateUnit_inner_nonpos hu' hu hne.symm
  have hpos := (mesh_pos hN hh).le
  constructor
  · ext p
    constructor
    · rintro ⟨hp, hp'⟩
      rw [heq] at hp
      rw [heq'] at hp'
      obtain ⟨t, ht, hpt⟩ := hp
      obtain ⟨t', ht', hpt'⟩ := hp'
      have hz : ‖t • u‖ ≤ ‖(0 : Ambient)‖ := by
        have hd := oriented_distance_le ht.1 ht'.1 hu hu' hinner
        have hz' : t • u - t' • u' = 0 := by
          calc
            t • u - t' • u' = (w + t • u) - (w + t' • u') := by module
            _ = p - p := by rw [← hpt, ← hpt']
            _ = 0 := sub_self p
        rw [hz'] at hd
        exact hd
      have ht0 : t = 0 := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, signedCoordinateUnit_norm hu] at hz
        exact le_antisymm hz ht.1
      have hz' : ‖t' • u'‖ ≤ ‖(0 : Ambient)‖ := by
        have hd := oriented_distance_le ht'.1 ht.1 hu' hu hinner'
        have hz'' : t' • u' - t • u = 0 := by
          calc
            t' • u' - t • u = (w + t' • u') - (w + t • u) := by module
            _ = p - p := by rw [← hpt', ← hpt]
            _ = 0 := sub_self p
        rw [hz''] at hd
        exact hd
      have ht0' : t' = 0 := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1,
          signedCoordinateUnit_norm hu'] at hz'
        exact le_antisymm hz' ht'.1
      have hendpoints : p = w ∧ p = w := by
        constructor
        · simp [hpt, ht0]
        · simp [hpt', ht0']
      exact hendpoints.1
    · intro hp
      have hpw : p = w := by simpa using hp
      subst p
      constructor
      · rw [heq]; exact ⟨0, ⟨le_rfl, hpos⟩, by simp⟩
      · rw [heq']; exact ⟨0, ⟨le_rfl, hpos⟩, by simp⟩
  · intro p p' hp hp'
    rw [heq] at hp
    rw [heq'] at hp'
    obtain ⟨t, ht, rfl⟩ := hp
    obtain ⟨t', ht', rfl⟩ := hp'
    have hd := oriented_distance_le ht.1 ht'.1 hu hu' hinner
    calc
      ‖(w + t • u) - w‖ = ‖t • u‖ := by apply congrArg norm; module
      _ ≤ ‖t • u - t' • u'‖ := hd
      _ = ‖(w + t • u) - (w + t' • u')‖ := by apply congrArg norm; module

end TopologicalSpace.CubeBoundaryThree
