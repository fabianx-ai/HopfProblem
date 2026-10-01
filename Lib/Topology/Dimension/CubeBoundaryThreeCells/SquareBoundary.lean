module

public import Lib.Topology.Dimension.CubeBoundaryThreeCells.Cells

/-!
# The boundary of a mesh square is the union of its four edges

A point of a mesh square of `∂[-1,1]³` outside its relative interior lies on one of the four sides
`[v, v + h e_j]`, `[v, v + h e_k]`, `[v + h e_k, v + h e_k + h e_j]`, `[v + h e_j, v + h e_j + h e_k]`,
and all four sides are mesh edges (`square_boundary_edges`).

## References

* R. Engelking, *Dimension Theory*, §1.8
* W. Hurewicz and H. Wallman, *Dimension Theory*, Chapter IV
-/

set_option warningAsError true
set_option autoImplicit false

open Set

namespace TopologicalSpace.CubeBoundaryThree

/-- A closed unit parameter outside the open unit interval is an endpoint. -/
private theorem closed_not_open_endpoint {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hna : a ∉ Set.Ioo (0 : ℝ) 1) : a = 0 ∨ a = 1 := by
  rcases ha with ⟨ha0, ha1⟩
  simp only [Set.mem_Ioo, not_and_or, not_lt] at hna
  rcases hna with ha0' | ha1'
  · exact Or.inl (le_antisymm ha0' ha0)
  · exact Or.inr (le_antisymm ha1 ha1')

/-- Closed parameters for a square boundary point, with an endpoint case. -/
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

/-- The initial point of the upper k-edge is one j-mesh step from v. -/
private noncomputable def shiftedVertexJ (h : ℝ) (v : Ambient) (j : Fin 3) : Ambient :=
  v + h • EuclideanSpace.single j 1
/-- The initial point of the upper j-edge is one k-mesh step from v. -/
private noncomputable def shiftedVertexK (h : ℝ) (v : Ambient) (k : Fin 3) : Ambient :=
  v + h • EuclideanSpace.single k 1

/-- The j-shift raises coordinate j by exactly h. -/
private theorem shiftedVertexJ_apply_same (h : ℝ) (v : Ambient) (j : Fin 3) :
    shiftedVertexJ h v j j = v j + h := by simp [shiftedVertexJ]
/-- The j-shift preserves every coordinate other than j. -/
private theorem shiftedVertexJ_apply_ne (h : ℝ) (v : Ambient) {j r : Fin 3} (hr : r ≠ j) :
    shiftedVertexJ h v j r = v r := by simp [shiftedVertexJ, hr]
/-- The k-shift raises coordinate k by exactly h. -/
private theorem shiftedVertexK_apply_same (h : ℝ) (v : Ambient) (k : Fin 3) :
    shiftedVertexK h v k k = v k + h := by simp [shiftedVertexK]
/-- The k-shift preserves every coordinate other than k. -/
private theorem shiftedVertexK_apply_ne (h : ℝ) (v : Ambient) {k r : Fin 3} (hr : r ≠ k) :
    shiftedVertexK h v k r = v r := by simp [shiftedVertexK, hr]

/-- The two descriptions of the opposite square corner coincide. -/
private theorem shifted_corner_commutes (h : ℝ) (v : Ambient) (j k : Fin 3) :
    shiftedVertexK h (shiftedVertexJ h v j) k =
      shiftedVertexJ h (shiftedVertexK h v k) j := by
  simp only [shiftedVertexJ, shiftedVertexK]
  module

/-- The lower j-edge line map is square parameter (t,0). -/
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

/-- The lower k-edge line map is square parameter (0,t). -/
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

/-- The upper j-edge from the k-shift is square parameter (t,1). -/
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

/-- The upper k-edge from the j-shift is square parameter (1,t). -/
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

/-- Every point of the lower j-segment has square parameters (t,0). -/
private theorem bottomJ_segment_extract {h : ℝ} {v y : Ambient} {j k : Fin 3}
    (hy : y ∈ segment ℝ v (v + h • EuclideanSpace.single j 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      y = v + (t * h) • EuclideanSpace.single j 1 +
        ((0 : ℝ) * h) • EuclideanSpace.single k 1 := by
  rw [segment_eq_image_lineMap ℝ] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨t, ht, (bottomJ_lineMap_embedding h t v j k ht).2⟩

/-- Every point of the lower k-segment has square parameters (0,t). -/
private theorem bottomK_segment_extract {h : ℝ} {v y : Ambient} {j k : Fin 3}
    (hy : y ∈ segment ℝ v (v + h • EuclideanSpace.single k 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      y = v + ((0 : ℝ) * h) • EuclideanSpace.single j 1 +
        (t * h) • EuclideanSpace.single k 1 := by
  rw [segment_eq_image_lineMap ℝ] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨t, ht, (bottomK_lineMap_embedding h t v j k ht).2⟩

/-- Every point of the upper j-segment has square parameters (t,1). -/
private theorem topJ_segment_extract {h : ℝ} {v y : Ambient} {j k : Fin 3}
    (hy : y ∈ segment ℝ (v + h • EuclideanSpace.single k 1)
      (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      y = v + (t * h) • EuclideanSpace.single j 1 +
        ((1 : ℝ) * h) • EuclideanSpace.single k 1 := by
  rw [segment_eq_image_lineMap ℝ] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨t, ht, (topJ_lineMap_embedding h t v j k ht).2⟩

/-- Every point of the upper k-segment has square parameters (1,t). -/
private theorem topK_segment_extract {h : ℝ} {v y : Ambient} {j k : Fin 3}
    (hy : y ∈ segment ℝ (v + h • EuclideanSpace.single j 1)
      (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      y = v + ((1 : ℝ) * h) • EuclideanSpace.single j 1 +
        (t * h) • EuclideanSpace.single k 1 := by
  rw [segment_eq_image_lineMap ℝ] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨t, ht, (topK_lineMap_embedding h t v j k ht).2⟩

/-- Admissible lower-j edge data constructs the literal edge. -/
private theorem bottomJ_edge_constructor {N : ℕ} {h : ℝ} {v : Ambient} {j : Fin 3}
    (hv : v ∈ vertices N h) (hvj : v j ≤ 1 - h)
    (hsub : segment ℝ v (v + h • EuclideanSpace.single j 1) ⊆ boundary) :
    segment ℝ v (v + h • EuclideanSpace.single j 1) ∈ edges N h :=
  edge_mem_iff.mpr ⟨v, j, ⟨hv, hvj, hsub⟩, rfl⟩

/-- Admissible lower-k edge data constructs the literal edge. -/
private theorem bottomK_edge_constructor {N : ℕ} {h : ℝ} {v : Ambient} {k : Fin 3}
    (hv : v ∈ vertices N h) (hvk : v k ≤ 1 - h)
    (hsub : segment ℝ v (v + h • EuclideanSpace.single k 1) ⊆ boundary) :
    segment ℝ v (v + h • EuclideanSpace.single k 1) ∈ edges N h :=
  edge_mem_iff.mpr ⟨v, k, ⟨hv, hvk, hsub⟩, rfl⟩

/-- Admissible k-shift/j-direction data constructs the upper j-edge. -/
private theorem topJ_edge_constructor {N : ℕ} {h : ℝ} {v : Ambient} {j k : Fin 3}
    (hv : v + h • EuclideanSpace.single k 1 ∈ vertices N h)
    (hvj : (v + h • EuclideanSpace.single k 1 : Ambient) j ≤ 1 - h)
    (hsub : segment ℝ (v + h • EuclideanSpace.single k 1)
      (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) ⊆ boundary) :
    segment ℝ (v + h • EuclideanSpace.single k 1)
      (v + h • EuclideanSpace.single k 1 + h • EuclideanSpace.single j 1) ∈ edges N h :=
  edge_mem_iff.mpr ⟨v + h • EuclideanSpace.single k 1, j, ⟨hv, hvj, hsub⟩, rfl⟩

/-- Admissible j-shift/k-direction data constructs the upper k-edge. -/
private theorem topK_edge_constructor {N : ℕ} {h : ℝ} {v : Ambient} {j k : Fin 3}
    (hv : v + h • EuclideanSpace.single j 1 ∈ vertices N h)
    (hvk : (v + h • EuclideanSpace.single j 1 : Ambient) k ≤ 1 - h)
    (hsub : segment ℝ (v + h • EuclideanSpace.single j 1)
      (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1) ⊆ boundary) :
    segment ℝ (v + h • EuclideanSpace.single j 1)
      (v + h • EuclideanSpace.single j 1 + h • EuclideanSpace.single k 1) ∈ edges N h :=
  edge_mem_iff.mpr ⟨v + h • EuclideanSpace.single j 1, k, ⟨hv, hvk, hsub⟩, rfl⟩

set_option linter.unusedVariables false in
/-- The two lower sides are permitted edges. -/
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

/-- Stepping to either upper-side initial point gives a vertex. -/
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

/-- The two translated upper sides are permitted edges. -/
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

/-- An endpoint parameter places the point on one displayed side. -/
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

/-- The square boundary is the union of its four edges. -/
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

end TopologicalSpace.CubeBoundaryThree
