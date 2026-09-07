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
