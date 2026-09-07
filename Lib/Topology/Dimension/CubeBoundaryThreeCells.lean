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

/- Textbook L0 / 1368–1372 (D001): defines the lattice statement used in the cell decomposition. -/
def lattice (N : ℕ) (h : ℝ) : Set ℝ :=
  {t | ∃ k : ℤ, k ∈ Set.Icc 0 (N : ℤ) ∧ t = -1 + (k : ℝ) * h}
/- Textbook L0 / 1368–1372 (D002): defines the latticeBelowTop statement used in the cell decomposition. -/
def latticeBelowTop (N : ℕ) (h : ℝ) : Set ℝ := lattice N h \ {1}
/- Textbook L0 / 1368–1372 (D003): proves the mesh identities statement used in the cell decomposition. -/
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
/- Textbook L0 / 1368–1372 (D004): proves the mesh pos statement used in the cell decomposition. -/
theorem mesh_pos {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ)) : 0 < h :=
  (mesh_identities N h hN hh).1
/- Textbook L1 / 1368–1372 (D005): proves the lattice subset interval statement used in the cell decomposition. -/
theorem lattice_subset_interval {N : ℕ} {h : ℝ} (hN : 0 < N)
  (hh : h = 2 / (N : ℝ)) : lattice N h ⊆ Set.Icc (-1) 1 := by
  rintro t ⟨k, hk, rfl⟩
  have hh' := (mesh_identities N h hN hh).2.1
  constructor
  · have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk.1
    exact le_add_of_nonneg_right (mul_nonneg hk0 (le_of_lt (mesh_pos hN hh)))
  · have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.2
    nlinarith [mul_le_mul_of_nonneg_right hkN (le_of_lt (mesh_pos hN hh))]
/- Textbook L2 / 1368–1372 (D006): proves the finite lattice statement used in the cell decomposition. -/
theorem finite_lattice (N : ℕ) (h : ℝ) : (lattice N h).Finite := by
  have hf := Set.Finite.image (fun k : ℤ => -1 + (k : ℝ) * h) (Set.finite_Icc 0 (N : ℤ))
  refine hf.subset ?_
  rintro t ⟨k, hk, rfl⟩
  exact ⟨k, hk, rfl⟩
/- Textbook L3 / 1368–1372 (D007): proves the card lattice statement used in the cell decomposition. -/
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
/- Textbook L3 / 1368–1372 (D008): proves the lattice endpoints statement used in the cell decomposition. -/
theorem lattice_endpoints {N : ℕ} {h : ℝ} (hN : 0 < N)
  (hh : h = 2 / (N : ℝ)) : (-1 : ℝ) ∈ lattice N h ∧ (1 : ℝ) ∈ lattice N h := by
  constructor
  · exact ⟨0, by simp, by simp⟩
  · refine ⟨N, by simp, ?_⟩
    have hm := (mesh_identities N h hN hh).2.1
    norm_num at hm ⊢
    linarith
/- Textbook L4 / 1368–1372 (D009): proves the lattice separation statement used in the cell decomposition. -/
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
/- Textbook L4 / 1368–1372 (D010): proves the lattice successor statement used in the cell decomposition. -/
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
/- Textbook L4 / 1368–1372 (D011): proves the mesh two of one statement used in the cell decomposition. -/
theorem mesh_two_of_one {h : ℝ} (hh : h = 2 / ((1 : ℕ) : ℝ)) : h = 2 := by norm_num at hh ⊢; exact hh
/- Textbook D1 / 1374–1376 (D012): defines the VertexParam statement used in the cell decomposition. -/
def VertexParam (N : ℕ) (h : ℝ) (v : Ambient) : Prop :=
  (∀ i, v i ∈ lattice N h) ∧ v ∈ boundary
/- Textbook D1 / 1374–1376 (D013): defines the vertices statement used in the cell decomposition. -/
public def vertices (N : ℕ) (h : ℝ) : Set Ambient := {v | VertexParam N h v}
/- Textbook D1 / 1374–1376 (D014): proves the vertex mem boundary statement used in the cell decomposition. -/
public theorem vertex_mem_boundary {N : ℕ} {h : ℝ} {v : Ambient}
    (hv : v ∈ vertices N h) : v ∈ boundary := hv.2
/- Textbook D2 / 1376–1379 (D015): defines the edgeGeom statement used in the cell decomposition. -/
def edgeGeom (h : ℝ) (v : Ambient) (j : Fin 3) : Set Ambient :=
  segment ℝ v (v + h • EuclideanSpace.single j 1)
/- Textbook D2 / 1376–1379 (D016): defines the EdgeParam statement used in the cell decomposition. -/
def EdgeParam (N : ℕ) (h : ℝ) (v : Ambient) (j : Fin 3) : Prop :=
  v ∈ vertices N h ∧ v j ≤ 1 - h ∧ edgeGeom h v j ⊆ boundary
/- Textbook D2 / 1376–1379 (D017): defines the edges statement used in the cell decomposition. -/
public def edges (N : ℕ) (h : ℝ) : Set (Set Ambient) :=
  {e | ∃ v j, EdgeParam N h v j ∧ e = edgeGeom h v j}
/- Textbook D2 / 1376–1379 (D018): proves the edge mem iff statement used in the cell decomposition. -/
theorem edge_mem_iff {N : ℕ} {h : ℝ} {e : Set Ambient} :
    e ∈ edges N h ↔ ∃ v j, EdgeParam N h v j ∧ e = edgeGeom h v j := Iff.rfl
/- Textbook D3 / 1379–1382 (D019): defines the squareGeom statement used in the cell decomposition. -/
def squareGeom (h : ℝ) (v : Ambient) (j k : Fin 3) : Set Ambient :=
  {x | ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
    x = v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1}
/- Textbook D3 / 1379–1382 (D020): defines the squareOpenGeom statement used in the cell decomposition. -/
def squareOpenGeom (h : ℝ) (v : Ambient) (j k : Fin 3) : Set Ambient :=
  {x | ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ b ∈ Set.Ioo (0 : ℝ) 1,
    x = v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1}
/- Textbook D3 / 1379–1382 (D021): defines the SquareParam statement used in the cell decomposition. -/
def SquareParam (N : ℕ) (h : ℝ) (v : Ambient) (j k : Fin 3) : Prop :=
  v ∈ vertices N h ∧ j < k ∧ v j ≤ 1 - h ∧ v k ≤ 1 - h ∧ squareGeom h v j k ⊆ boundary
/- Textbook D3 / 1379–1382 (D022): defines the squares statement used in the cell decomposition. -/
public def squares (N : ℕ) (h : ℝ) : Set (Set Ambient) :=
  {s | ∃ v j k, SquareParam N h v j k ∧ s = squareGeom h v j k}
/- Textbook C01 / 1410–1421 (D023): defines the coordinateLowerCorner statement used in the cell decomposition. -/
def coordinateLowerCorner (C : Set Ambient) (v : Ambient) : Prop :=
  v ∈ C ∧ ∀ r x, x ∈ C → v r ≤ x r
/- Textbook C01 / 1410–1421 (D024): defines the coordinateNonconstant statement used in the cell decomposition. -/
def coordinateNonconstant (C : Set Ambient) (r : Fin 3) : Prop :=
  ∃ x ∈ C, ∃ y ∈ C, x r ≠ y r
/- Textbook C01 / 1410–1421 (D025): proves the coordinateLowerCorner unique statement used in the cell decomposition. -/
theorem coordinateLowerCorner_unique {C : Set Ambient} {v w : Ambient}
  (hv : coordinateLowerCorner C v) (hw : coordinateLowerCorner C w) : v = w := by
  ext r
  exact le_antisymm (hv.2 r w hw.1) (hw.2 r v hv.1)
/- Textbook C02 / 1423–1435 (D026): proves the edge coordinate formula statement used in the cell decomposition. -/
theorem edge_coordinate_formula (h t : ℝ) (v : Ambient) (j r : Fin 3) :
  (v + (t * h) • EuclideanSpace.single j 1 : Ambient) r =
    if r = j then v j + t * h else v r := by
  split_ifs with hr
  · subst r; simp
  · simp [hr]
/- Textbook C02 / 1423–1435 (D027): proves the edge zero mem statement used in the cell decomposition. -/
theorem edge_zero_mem (h : ℝ) (v : Ambient) (j : Fin 3) : v ∈ edgeGeom h v j := by
  rw [edgeGeom]
  exact left_mem_segment ℝ v _
/- Textbook C02 / 1423–1435 (D028): proves the edge parameter extract statement used in the cell decomposition. -/
theorem edge_parameter_extract {h : ℝ} {v : Ambient} {j : Fin 3} {x : Ambient}
  (hx : x ∈ edgeGeom h v j) : ∃ t ∈ Set.Icc (0 : ℝ) 1,
    x = v + (t * h) • EuclideanSpace.single j 1 := by
  rw [edgeGeom, segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t, ht, by module⟩
/- Textbook C02 / 1423–1435 (D029): proves the edge initial lowerCorner statement used in the cell decomposition. -/
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
/- Textbook C03 / 1436–1448 (D030): proves the square coordinate formula statement used in the cell decomposition. -/
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
/- Textbook C03 / 1436–1448 (D031): proves the square zero mem statement used in the cell decomposition. -/
theorem square_zero_mem (h : ℝ) (v : Ambient) (j k : Fin 3) : v ∈ squareGeom h v j k := by
  exact ⟨0, by simp, 0, by simp, by simp⟩
/- Textbook C03 / 1436–1448 (D032): proves the square first corner mem statement used in the cell decomposition. -/
theorem square_first_corner_mem (h : ℝ) (v : Ambient) (j k : Fin 3) :
  v + h • EuclideanSpace.single j 1 ∈ squareGeom h v j k := by
  refine ⟨1, by simp, 0, by simp, ?_⟩
  module
/- Textbook C03 / 1436–1448 (D033): proves the square second corner mem statement used in the cell decomposition. -/
theorem square_second_corner_mem (h : ℝ) (v : Ambient) (j k : Fin 3) :
  v + h • EuclideanSpace.single k 1 ∈ squareGeom h v j k := by
  refine ⟨0, by simp, 1, by simp, ?_⟩
  module
/- Textbook C03 / 1436–1448 (D034): proves the square parameter extract statement used in the cell decomposition. -/
theorem square_parameter_extract {h : ℝ} {v : Ambient} {j k : Fin 3} {x : Ambient}
  (hx : x ∈ squareGeom h v j k) : ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
    x = v + (a * h) • EuclideanSpace.single j 1 + (b * h) • EuclideanSpace.single k 1 := hx
/- Textbook C03 / 1436–1448 (D035): proves the square initial lowerCorner statement used in the cell decomposition. -/
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
/- Textbook C04 / 1448–1452 (D036): proves the edge coordinate minima attained statement used in the cell decomposition. -/
theorem edge_coordinate_minima_attained {h : ℝ} (hh : 0 ≤ h) (v : Ambient) (j r : Fin 3) :
  v ∈ edgeGeom h v j ∧ (∀ x ∈ edgeGeom h v j, v r ≤ x r) :=
  ⟨(edge_initial_lowerCorner hh v j).1, (edge_initial_lowerCorner hh v j).2 r⟩
/- Textbook C04 / 1448–1452 (D037): proves the square coordinate minima attained statement used in the cell decomposition. -/
theorem square_coordinate_minima_attained {h : ℝ} (hh : 0 ≤ h) {v : Ambient} {j k : Fin 3}
  (hjk : j < k) (r : Fin 3) : v ∈ squareGeom h v j k ∧ (∀ x ∈ squareGeom h v j k, v r ≤ x r) :=
  ⟨(square_initial_lowerCorner hh hjk).1, (square_initial_lowerCorner hh hjk).2 r⟩
/- Textbook C05 / 1454–1459 (D038): proves the edge initial eq of set eq statement used in the cell decomposition. -/
theorem edge_initial_eq_of_set_eq {h : ℝ} (hh : 0 ≤ h) {v w : Ambient} {j l : Fin 3}
  (heq : edgeGeom h v j = edgeGeom h w l) : v = w := by
  apply coordinateLowerCorner_unique (C := edgeGeom h v j)
  · exact edge_initial_lowerCorner hh v j
  · rw [heq]
    exact edge_initial_lowerCorner hh w l
/- Textbook C05 / 1454–1459 (D039): proves the square initial eq of set eq statement used in the cell decomposition. -/
theorem square_initial_eq_of_set_eq {h : ℝ} (hh : 0 ≤ h) {v w : Ambient} {j k p q : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q) : v = w := by
  apply coordinateLowerCorner_unique (C := squareGeom h v j k)
  · exact square_initial_lowerCorner hh hjk
  · rw [heq]
    exact square_initial_lowerCorner hh hpq
/- Textbook C06 / 1461–1469 (D040): proves the edge terminal mem statement used in the cell decomposition. -/
theorem edge_terminal_mem (h : ℝ) (v : Ambient) (j : Fin 3) :
  v + h • EuclideanSpace.single j 1 ∈ edgeGeom h v j := by
  rw [edgeGeom]
  exact right_mem_segment ℝ _ _
/- Textbook C06 / 1461–1469 (D041): proves the edge direction eq of set eq statement used in the cell decomposition. -/
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
/- Textbook C06 / 1461–1469 (D042): proves the edge presentation unique statement used in the cell decomposition. -/
theorem edge_presentation_unique {N : ℕ} {h : ℝ} (hh : 0 < h) {e : Set Ambient}
  {v w : Ambient} {j l : Fin 3} (hp : EdgeParam N h v j) (he : e = edgeGeom h v j)
  (hp' : EdgeParam N h w l) (he' : e = edgeGeom h w l) : v = w ∧ j = l := by
  have _ := hp.1
  have _ := hp'.1
  have hgeom : edgeGeom h v j = edgeGeom h w l := he.symm.trans he'
  exact ⟨edge_initial_eq_of_set_eq (le_of_lt hh) hgeom, edge_direction_eq_of_set_eq hh hgeom⟩
/- Textbook C07 / 1471–1476 (D043): proves the edge nonconstant coordinates statement used in the cell decomposition. -/
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
/- Textbook C08 / 1478–1488 (D044): proves the square directions mem of set eq statement used in the cell decomposition. -/
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
/- Textbook C09 / 1490–1496 (D045): proves the square ordered directions eq statement used in the cell decomposition. -/
theorem square_ordered_directions_eq {j k p q : Fin 3} (hjk : j < k) (hpq : p < q)
  (hj : j = p ∨ j = q) (hk : k = p ∨ k = q) : j = p ∧ k = q := by
  omega
/- Textbook C09 / 1490–1496 (D046): proves the square presentation unique statement used in the cell decomposition. -/
theorem square_presentation_unique {N : ℕ} {h : ℝ} (hh : 0 < h) {s : Set Ambient}
  {v w : Ambient} {j k p q : Fin 3} (hp : SquareParam N h v j k) (hs : s = squareGeom h v j k)
  (hp' : SquareParam N h w p q) (hs' : s = squareGeom h w p q) : v = w ∧ j = p ∧ k = q := by
  have heq := hs.symm.trans hs'
  have hvw := square_initial_eq_of_set_eq (le_of_lt hh) hp.2.1 hp'.2.1 heq
  have hd := square_directions_mem_of_set_eq hh hp.2.1 hp'.2.1 heq
  exact ⟨hvw, square_ordered_directions_eq hp.2.1 hp'.2.1 hd.1 hd.2⟩
/- Textbook C10 / 1498–1504 (D047): proves the square nonconstant coordinates statement used in the cell decomposition. -/
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
/- Textbook C11 / 1504–1509 (D048): proves the coordinate variation of set eq statement used in the cell decomposition. -/
theorem coordinate_variation_of_set_eq {C D : Set Ambient} (hCD : C = D) (r : Fin 3) :
  coordinateNonconstant C r ↔ coordinateNonconstant D r := by subst D; rfl
/- Textbook C11 / 1504–1509 (D049): proves the coordinate constant value transport statement used in the cell decomposition. -/
theorem coordinate_constant_value_transport {C D : Set Ambient} (hCD : C = D)
  (r : Fin 3) (c : ℝ) : (∀ x ∈ C, x r = c) ↔ (∀ x ∈ D, x r = c) := by subst D; rfl
/- Textbook C11 / 1504–1509 (D050): proves the increasing pair eq of direction set eq statement used in the cell decomposition. -/
theorem increasing_pair_eq_of_direction_set_eq {j k p q : Fin 3} (hjk : j < k) (hpq : p < q)
  (hset : ({j, k} : Set (Fin 3)) = {p, q}) : j = p ∧ k = q := by
  apply square_ordered_directions_eq hjk hpq
  · have : j ∈ ({p, q} : Set (Fin 3)) := by rw [← hset]; simp
    simpa using this
  · have : k ∈ ({p, q} : Set (Fin 3)) := by rw [← hset]; simp
    simpa using this
/- Textbook C12 / 1511–1519 (D051): proves the edge endpoints coherent statement used in the cell decomposition. -/
theorem edge_endpoints_coherent {h : ℝ} (hh : 0 < h) {v w : Ambient} {j l : Fin 3}
  (heq : edgeGeom h v j = edgeGeom h w l) :
  ({v, v + h • EuclideanSpace.single j 1} : Set Ambient) = {w, w + h • EuclideanSpace.single l 1} := by
  rw [edge_initial_eq_of_set_eq (le_of_lt hh) heq, edge_direction_eq_of_set_eq hh heq]
/- Textbook C12 / 1511–1519 (D052): proves the edge endpoints distinct statement used in the cell decomposition. -/
theorem edge_endpoints_distinct {h : ℝ} (hh : 0 < h) (v : Ambient) (j : Fin 3) :
  v ≠ v + h • EuclideanSpace.single j 1 := by
  intro heq
  have hc := congrArg (fun x : Ambient => x j) heq
  simp at hc
  linarith
/- Textbook C13 / 1519–1529 (D053): proves the square relInterior coherent raw statement used in the cell decomposition. -/
theorem square_relInterior_coherent_raw {h : ℝ} (hh : 0 < h) {v w : Ambient} {j k p q : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q) :
  squareOpenGeom h v j k = squareOpenGeom h w p q := by
  have hvw := square_initial_eq_of_set_eq (le_of_lt hh) hjk hpq heq
  have hd := square_directions_mem_of_set_eq hh hjk hpq heq
  have hord := square_ordered_directions_eq hjk hpq hd.1 hd.2
  subst w
  rw [hord.1, hord.2]
/- Textbook C14 / 1531–1538 (D054): proves the square remaining index statement used in the cell decomposition. -/
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
/- Textbook C14 / 1531–1538 (D055): proves the square remaining index cases statement used in the cell decomposition. -/
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
/- Textbook C14 / 1531–1538 (D056): proves the square remaining coordinate statement used in the cell decomposition. -/
theorem square_remaining_coordinate {h : ℝ} {v : Ambient} {j k i : Fin 3}
  (hij : i ≠ j) (hik : i ≠ k) {x : Ambient} (hx : x ∈ squareGeom h v j k) : x i = v i := by
  obtain ⟨a, ha, b, hb, rfl⟩ := square_parameter_extract hx
  simp [hij, hik]
/- Textbook C14 / 1531–1538 (D057): proves the square remaining intrinsic statement used in the cell decomposition. -/
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
/- Textbook C15 / 1540–1553 (D058): defines the squareMidpoint statement used in the cell decomposition. -/
noncomputable def squareMidpoint (h : ℝ) (v : Ambient) (j k : Fin 3) : Ambient :=
  v + ((1 / 2 : ℝ) * h) • EuclideanSpace.single j 1 + ((1 / 2 : ℝ) * h) • EuclideanSpace.single k 1
/- Textbook C15 / 1540–1553 (D059): proves the square midpoint bounds statement used in the cell decomposition. -/
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
/- Textbook C16 / 1553–1559 (D060): proves the boundary maxAbs eq statement used in the cell decomposition. -/
theorem boundary_maxAbs_eq {x : Ambient} (hx : x ∈ boundary) : maxAbs x = 1 := hx
/- Textbook C16 / 1553–1559 (D061): proves the remaining abs of maxAbs statement used in the cell decomposition. -/
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
/- Textbook C16 / 1553–1559 (D062): proves the square midpoint remaining abs statement used in the cell decomposition. -/
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
/- Textbook C16 / 1553–1559 (D063): proves the face membership from sign statement used in the cell decomposition. -/
theorem face_membership_from_sign {x : Ambient} {i : Fin 3} {σ : {r : ℝ // r = -1 ∨ r = 1}}
  (hx : x ∈ boundary) (hxi : x i = σ.1) : x ∈ face i σ := ⟨hx, hxi⟩
/- Textbook C16 / 1553–1559 (D064): proves the square face sign and containment statement used in the cell decomposition. -/
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
/- Textbook C17 / 1561–1568 (D065): proves the face sign eq of mem statement used in the cell decomposition. -/
theorem face_sign_eq_of_mem {x : Ambient} {i : Fin 3}
  {σ τ : {r : ℝ // r = -1 ∨ r = 1}} (hxσ : x ∈ face i σ) (hxτ : x ∈ face i τ) : σ = τ := by
  apply Subtype.ext
  exact hxσ.2.symm.trans hxτ.2
/- Textbook C17 / 1561–1568 (D066): proves the square intrinsic face statement used in the cell decomposition. -/
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
    have hxτ := hr (square_first_corner_mem h v j k)
    have hvτ' : v j = τ.1 := hvτ.2
    have hxτ' : (v + h • EuclideanSpace.single j 1 : Ambient) j = τ.1 := hxτ.2
    simp at hxτ'
    linarith
  have hrk : r ≠ k := by
    intro e
    subst r
    have hxτ := hr (square_second_corner_mem h v j k)
    have hvτ' : v k = τ.1 := hvτ.2
    have hxτ' : (v + h • EuclideanSpace.single k 1 : Ambient) k = τ.1 := hxτ.2
    simp at hxτ'
    linarith
  have hir : r = i := hiuniq r ⟨hrj, hrk⟩
  subst r
  have hvσ := hcontain (square_zero_mem h v j k)
  have hστ : σ = τ := face_sign_eq_of_mem hvσ hvτ
  subst τ
  rfl
/- Textbook C18 / 1570–1581 (D067): proves the zero mesh images statement used in the cell decomposition. -/
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
/- Textbook C18 / 1570–1581 (D068): proves the zero mesh edge nonunique statement used in the cell decomposition. -/
theorem zero_mesh_edge_nonunique : ∃ (v : Ambient) (j l : Fin 3), j ≠ l ∧ edgeGeom 0 v j = edgeGeom 0 v l := by
  exact ⟨0, 0, 1, by decide, (zero_mesh_images 0 0 0).1.trans (zero_mesh_images 0 1 1).1.symm⟩
/- Textbook C18 / 1570–1581 (D069): proves the zero mesh square nonunique statement used in the cell decomposition. -/
theorem zero_mesh_square_nonunique : ∃ (v : Ambient) (j k p q : Fin 3),
  j < k ∧ p < q ∧ (j, k) ≠ (p, q) ∧ squareGeom 0 v j k = squareGeom 0 v p q := by
  exact ⟨0, 0, 1, 0, 2, by decide, by decide, by decide,
    (zero_mesh_images 0 0 1).2.1.trans (zero_mesh_images 0 0 2).2.1.symm⟩
/- Textbook C19 / 1583–1587 (D070): proves the square parameter swap statement used in the cell decomposition. -/
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
/- Textbook C19 / 1583–1587 (D071): proves the swapped ordered pair ne statement used in the cell decomposition. -/
theorem swapped_ordered_pair_ne {j k : Fin 3} (hjk : j ≠ k) : (j, k) ≠ (k, j) := by
  intro hp
  exact hjk (congrArg Prod.fst hp)
/- Textbook C19 / 1583–1587 (D072): proves the square order suffices statement used in the cell decomposition. -/
theorem square_order_suffices {h : ℝ} (hh : 0 < h) {v w : Ambient} {j k p q : Fin 3}
  (hjk : j < k) (hpq : p < q) (heq : squareGeom h v j k = squareGeom h w p q) : j = p ∧ k = q := by
  have hd := square_directions_mem_of_set_eq hh hjk hpq heq
  exact square_ordered_directions_eq hjk hpq hd.1 hd.2
/- Textbook C20 / 1589–1593 (D073): proves the square unit mesh endpoint case statement used in the cell decomposition. -/
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
/- Textbook C21 / 1593–1598 (D074): proves the shared edge presentation identity statement used in the cell decomposition. -/
theorem shared_edge_presentation_identity {h : ℝ} (hh : 0 < h) {v w : Ambient} {j l : Fin 3}
  (heq : edgeGeom h v j = edgeGeom h w l) :
  v = w ∧ j = l ∧ ({v, v + h • EuclideanSpace.single j 1} : Set Ambient) = {w, w + h • EuclideanSpace.single l 1} :=
  ⟨edge_initial_eq_of_set_eq (le_of_lt hh) heq, edge_direction_eq_of_set_eq hh heq,
    edge_endpoints_coherent hh heq⟩
/- Textbook H2 / 1384–1408; 1519–1529 (D075): defines the squareRelInteriorRaw statement used in the cell decomposition. -/
noncomputable def squareRelInteriorRaw (N : ℕ) (h : ℝ) (s : {s : Set Ambient // s ∈ squares N h}) : Set Ambient :=
  squareOpenGeom h (Classical.choose s.property) (Classical.choose (Classical.choose_spec s.property))
    (Classical.choose (Classical.choose_spec (Classical.choose_spec s.property)))
/- Textbook H2 / 1384–1408; 1519–1529 (D076): defines the squareRelInterior statement used in the cell decomposition. -/
public noncomputable def squareRelInterior (N : ℕ) (h : ℝ) (s : {s : Set Ambient // s ∈ squares N h}) : Set Ambient := squareRelInteriorRaw N h s
/- Textbook H2 / 1384–1408; 1519–1529 (D077): proves the square relInterior coherent statement used in the cell decomposition. -/
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
/- Textbook H2 / 1384–1408; 1519–1529 (D078): proves the square presentation statement used in the cell decomposition. -/
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
/- Textbook H1 / 1384–1408; 1511–1519 (D079): defines the edgeEndpointsRaw statement used in the cell decomposition. -/
noncomputable def edgeEndpointsRaw (N : ℕ) (h : ℝ) (e : {e : Set Ambient // e ∈ edges N h}) : Set Ambient :=
  let v := Classical.choose e.property; let j := Classical.choose (Classical.choose_spec e.property); {v, v + h • EuclideanSpace.single j 1}
/- Textbook H1 / 1384–1408; 1511–1519 (D080): defines the edgeEndpoints statement used in the cell decomposition. -/
public noncomputable def edgeEndpoints (N : ℕ) (h : ℝ) (e : {e : Set Ambient // e ∈ edges N h}) : Set Ambient := edgeEndpointsRaw N h e
/- Textbook H1 / 1384–1408; 1511–1519 (D081): proves the edge presentation statement used in the cell decomposition. -/
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
/- Textbook F1 / 1614–1616 (D082): proves the finite Ambient coordinate bridge statement used in the cell decomposition. -/
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
/- Textbook F1 / 1614–1616 (D083): proves the finite vertex product statement used in the cell decomposition. -/
theorem finite_vertex_product (N : ℕ) (h : ℝ) :
  ({v : Ambient | ∀ i, v i ∈ lattice N h}).Finite :=
  finite_Ambient_coordinate_bridge (fun _ => finite_lattice N h)
/- Textbook F1 / 1614–1616 (D084): proves the finite vertices statement used in the cell decomposition. -/
public theorem finite_vertices (N : ℕ) (h : ℝ) : (vertices N h).Finite := by
  apply (finite_vertex_product N h).subset
  intro v hv
  exact hv.1
/- Textbook F2 / 1614–1616 (D085): defines the edgeParamSet statement used in the cell decomposition. -/
def edgeParamSet (N : ℕ) (h : ℝ) : Set (Ambient × Fin 3) := {p | EdgeParam N h p.1 p.2}
/- Textbook F2 / 1614–1616 (D086): proves the finite edge parameters statement used in the cell decomposition. -/
theorem finite_edge_parameters (N : ℕ) (h : ℝ) : (edgeParamSet N h).Finite := by
  apply ((finite_vertices N h).prod Set.finite_univ).subset
  rintro ⟨v, j⟩ hp
  exact ⟨hp.1, Set.mem_univ j⟩
/- Textbook F2 / 1614–1616 (D087): proves the edges eq image statement used in the cell decomposition. -/
theorem edges_eq_image (N : ℕ) (h : ℝ) :
  edges N h = (fun p : Ambient × Fin 3 => edgeGeom h p.1 p.2) '' edgeParamSet N h := by
  ext e
  constructor
  · rintro ⟨v, j, hp, rfl⟩; exact ⟨(v, j), hp, rfl⟩
  · rintro ⟨⟨v, j⟩, hp, rfl⟩; exact ⟨v, j, hp, rfl⟩
/- Textbook F2 / 1614–1616 (D088): proves the finite edges statement used in the cell decomposition. -/
public theorem finite_edges (N : ℕ) (h : ℝ) : (edges N h).Finite := by
  rw [edges_eq_image]
  exact (finite_edge_parameters N h).image _
/- Textbook F3 / 1614–1616 (D089): defines the squareParamSet statement used in the cell decomposition. -/
def squareParamSet (N : ℕ) (h : ℝ) : Set (Ambient × Fin 3 × Fin 3) := {p | SquareParam N h p.1 p.2.1 p.2.2}
/- Textbook F3 / 1614–1616 (D090): proves the finite square parameters statement used in the cell decomposition. -/
theorem finite_square_parameters (N : ℕ) (h : ℝ) : (squareParamSet N h).Finite := by
  apply ((finite_vertices N h).prod (Set.finite_univ.prod Set.finite_univ)).subset
  rintro ⟨v, j, k⟩ hp
  exact ⟨hp.1, Set.mem_univ j, Set.mem_univ k⟩
/- Textbook F3 / 1614–1616 (D091): proves the squares eq image statement used in the cell decomposition. -/
theorem squares_eq_image (N : ℕ) (h : ℝ) :
  squares N h = (fun p : Ambient × Fin 3 × Fin 3 => squareGeom h p.1 p.2.1 p.2.2) '' squareParamSet N h := by
  ext s
  constructor
  · rintro ⟨v, j, k, hp, rfl⟩; exact ⟨(v, j, k), hp, rfl⟩
  · rintro ⟨⟨v, j, k⟩, hp, rfl⟩; exact ⟨v, j, k, hp, rfl⟩
/- Textbook F3 / 1614–1616 (D092): proves the finite squares statement used in the cell decomposition. -/
public theorem finite_squares (N : ℕ) (h : ℝ) : (squares N h).Finite := by
  rw [squares_eq_image]
  exact (finite_square_parameters N h).image _
/- Textbook E0 / 1618–1620 (D093): proves the edge terminal is vertex statement used in the cell decomposition. -/
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
/- Textbook E0 / 1618–1620 (D094): proves the edge endpoints vertices statement used in the cell decomposition. -/
public theorem edge_endpoints_vertices {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
  (e : {e : Set Ambient // e ∈ edges N h}) : edgeEndpoints N h e ⊆ vertices N h := by
  let v := Classical.choose e.property
  let j := Classical.choose (Classical.choose_spec e.property)
  have hspec := Classical.choose_spec (Classical.choose_spec e.property)
  intro x hx
  simp only [edgeEndpoints, edgeEndpointsRaw, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hspec.1.1
  · exact edge_terminal_is_vertex hN hh hspec.1

/- C22 terminal background/accounting site: the following executable examples and fully qualified
API checks certify only representation conversions. They are not proof inputs to finiteness. -/
example (h : ℝ) (i j : Fin 3) : (h • EuclideanSpace.single j 1 : Ambient) i = h * (if i=j then 1 else 0) := by simp [PiLp.single_apply]
example {A : Fin 3 → Set ℝ} (hA : ∀ i, (A i).Finite) :
    ({v : Ambient | ∀ i, v i ∈ A i}).Finite := by
  let T : Set (Fin 3 → ℝ) := {f | ∀ i, f i ∈ A i}
  have hT : T.Finite := Set.Finite.pi' hA
  have hEq : {v : Ambient | ∀ i, v i ∈ A i} = WithLp.toLp 2 '' T := by
    ext v
    constructor
    · intro hv
      exact ⟨v.ofLp, hv, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact hf
  rw [hEq]
  exact hT.image (WithLp.toLp 2)
example {x y : Ambient} (hxy : ∀ i, x i = y i) : x = y := by
  ext i
  exact hxy i
example (h t : ℝ) (v : Ambient) (j : Fin 3) :
    (1 - t) • v + t • (v + h • EuclideanSpace.single j 1) =
      v + (t * h) • EuclideanSpace.single j 1 := by module
example (h : ℝ) (v : Ambient) (j k : Fin 3) :
    v + ((1 : ℝ) * h) • EuclideanSpace.single j 1 + ((0 : ℝ) * h) • EuclideanSpace.single k 1 =
      v + h • EuclideanSpace.single j 1 := by module
example (h : ℝ) (v : Ambient) (j k : Fin 3) :
    v + ((0 : ℝ) * h) • EuclideanSpace.single j 1 + ((1 : ℝ) * h) • EuclideanSpace.single k 1 =
      v + h • EuclideanSpace.single k 1 := by module
example (h t : ℝ) (v : Ambient) (j : Fin 3) :
    (v + (t * h) • EuclideanSpace.single j 1 : Ambient) j = v j + t * h := by
  simp
example (h t : ℝ) (v : Ambient) {j r : Fin 3} (hrj : r ≠ j) :
    (v + (t * h) • EuclideanSpace.single j 1 : Ambient) r = v r := by
  simp [hrj]
example (h a b : ℝ) (v : Ambient) {j k : Fin 3} (hjk : j ≠ k) :
    (v + (a*h) • EuclideanSpace.single j 1 + (b*h) • EuclideanSpace.single k 1 : Ambient) j =
      v j + a*h := by simp [hjk]
example (h a b : ℝ) (v : Ambient) {j k : Fin 3} (hjk : j ≠ k) :
    (v + (a*h) • EuclideanSpace.single j 1 + (b*h) • EuclideanSpace.single k 1 : Ambient) k =
      v k + b*h := by simp [hjk]
example (h a b : ℝ) (v : Ambient) {j k r : Fin 3} (hrj : r ≠ j) (hrk : r ≠ k) :
    (v + (a*h) • EuclideanSpace.single j 1 + (b*h) • EuclideanSpace.single k 1 : Ambient) r = v r := by
  simp [hrj, hrk]
example {h : ℝ} {v : Ambient} {j : Fin 3} {x : Ambient} (hx : x ∈ edgeGeom h v j) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, x = v + (t*h) • EuclideanSpace.single j 1 := by
  rw [edgeGeom, segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t, ht, by module⟩
example (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega
example {j k : Fin 3} (hjk : j < k) :
    (j = 0 ∧ k = 1 ∧ (2 : Fin 3) ≠ j ∧ (2 : Fin 3) ≠ k) ∨
    (j = 0 ∧ k = 2 ∧ (1 : Fin 3) ≠ j ∧ (1 : Fin 3) ≠ k) ∨
    (j = 1 ∧ k = 2 ∧ (0 : Fin 3) ≠ j ∧ (0 : Fin 3) ≠ k) := by omega
example (x : Ambient) : x ∈ boundary ↔ maxAbs x = 1 := Iff.rfl
example {x : Ambient} (hx : x ∈ boundary) : maxAbs x = 1 := hx
example {x : Ambient} (hx : maxAbs x = 1) : x ∈ boundary := hx
example {x : Ambient} (h0 : |x 0| < 1) (h1 : |x 1| < 1) (h2 : |x 2| < 1) :
    maxAbs x < 1 := by exact max_lt h0 (max_lt h1 h2)
example (x : Ambient) (i : Fin 3) (σ : {r : ℝ // r = -1 ∨ r = 1}) :
    x ∈ face i σ ↔ x ∈ boundary ∧ x i = σ.1 := Iff.rfl
example {x : Ambient} {i : Fin 3} {σ : {r : ℝ // r = -1 ∨ r = 1}}
    (hx : x ∈ boundary) (hxi : x i = σ.1) : x ∈ face i σ := ⟨hx, hxi⟩
example {x : Ambient} {i : Fin 3} {σ τ : {r : ℝ // r = -1 ∨ r = 1}}
    (hxσ : x ∈ face i σ) (hxτ : x ∈ face i τ) : σ = τ := by
  apply Subtype.ext
  exact hxσ.2.symm.trans hxτ.2
example {j k p q : Fin 3} (hjk : j < k) (hpq : p < q)
    (hset : ({j, k} : Set (Fin 3)) = {p, q}) : j = p ∧ k = q := by
  have hjmem : j ∈ ({p, q} : Set (Fin 3)) := by
    rw [← hset]
    simp
  have hkmem : k ∈ ({p, q} : Set (Fin 3)) := by
    rw [← hset]
    simp
  have hj : j = p ∨ j = q := by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hjmem
  have hk : k = p ∨ k = q := by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hkmem
  exact square_ordered_directions_eq hjk hpq hj hk
example {j k : Fin 3} (hjk : j ≠ k) : (j, k) ≠ (k, j) := by
  intro hpair
  exact hjk (congrArg Prod.fst hpair)
example {C D : Set Ambient} (h : C = D) {x : Ambient} : x ∈ C ↔ x ∈ D := by subst h; rfl
example (j k : Fin 3) (hjk : j < k) : j ≠ k := ne_of_lt hjk
example (r : ℝ) : |r| = 1 ↔ r = -1 ∨ r = 1 := by rw [abs_eq (by norm_num : (0:ℝ) ≤ 1)]; aesop
#check div_pos
#check Nat.cast_ne_zero
#check Int.cast_nonneg
#check Int.cast_le
#check mul_le_mul_of_nonneg_right
#check Set.finite_Icc
#check Set.ncard_image_of_injective
#check Int.cast_injective
#check Int.cast_one
#check abs_mul
#check lt_irrefl
#check Set.Finite.pi'
#check Set.Finite.image
#check Set.Finite.subset
#check Set.Finite.prod
#check Set.ncard_coe_finset
#check Int.card_Icc
#check segment_eq_image
#check left_mem_segment
#check right_mem_segment
#check Fin.eq_zero
#check Fin.cases
#check Fin.sum_univ_three
#check abs_lt
#check abs_le
#check abs_eq
#check max_lt
#check max_eq_left
#check max_eq_right
#check mul_nonneg
#check le_antisymm
#check add_le_add_right
#check add_left_cancel
#check half_pos
#check Nat.cast_pos
#check Int.cast_add
#check Int.cast_sub
#check Set.ext
#check Subtype.ext
#check mem_face_iff

end TopologicalSpace.CubeBoundaryThree
