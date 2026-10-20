module

public import Lib.Topology.Dimension.CubeBoundaryThreeCells.Faces

/-!
# Separation of mesh vertices and mesh edges

In the mesh-`h` subdivision of `∂[-1,1]³`:

* distinct vertices are at least `h` apart in the maximum norm, hence in the Euclidean norm
  (`vertex_separation`);
* two distinct edges with a common endpoint `w` meet only in `w`, and for points `p, p'` on them
  `‖p - w‖ ≤ ‖p - p'‖` (`edge_common_endpoint_geometry`), because their directions are distinct
  signed coordinate unit vectors with nonpositive inner product;
* two distinct edges without a common endpoint are at least `h` apart
  (`edge_dist_ge_mesh_of_no_common_endpoint`).

These estimates let the cells be thickened to open sets of which only cells of different
dimensions can meet.

## References

* R. Engelking, *Dimension Theory*, §1.8
* W. Hurewicz and H. Wallman, *Dimension Theory*, Chapter IV
-/

set_option warningAsError true
set_option autoImplicit false

open Set

namespace TopologicalSpace.CubeBoundaryThree

/-- Every coordinate of a mesh vertex belongs to the
one-dimensional mesh lattice. -/
private theorem vertex_coordinate_mem_lattice {N : ℕ} {h : ℝ} {v : Ambient}
    (hv : v ∈ vertices N h) (i : Fin 3) : v i ∈ lattice N h :=
  hv.1 i

/-- Two unequal points in three-coordinate space differ in
at least one coordinate. -/
private theorem exists_ne_coordinate {v w : Ambient} (hvw : v ≠ w) :
    ∃ i : Fin 3, v i ≠ w i := by
  by_contra h
  push Not at h
  exact hvw (PiLp.ext h)

/-- Unequal coordinates of two mesh vertices are separated
by at least one mesh length. -/
private theorem vertex_coordinate_separation {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v w : Ambient} (hv : v ∈ vertices N h)
    (hw : w ∈ vertices N h) {i : Fin 3} (hi : v i ≠ w i) : h ≤ |v i - w i| :=
  lattice_separation hN hh (vertex_coordinate_mem_lattice hv i)
    (vertex_coordinate_mem_lattice hw i) hi

/-- The absolute value of any coordinate is bounded by the
maximum absolute coordinate. -/
private theorem abs_apply_le_maxAbs (x : Ambient) (i : Fin 3) : |x i| ≤ maxAbs x := by
  fin_cases i <;> simp [maxAbs]

/-- Distinct mesh vertices are separated by one mesh length
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

/-- An oriented edge direction is a
positive or negative coordinate unit vector. -/
private def SignedCoordinateUnit (u : Ambient) : Prop :=
  ∃ i : Fin 3, u = EuclideanSpace.single i 1 ∨ u = -EuclideanSpace.single i 1

/-- An edge can be oriented away from
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

/-- Two distinct edges oriented from
the same endpoint cannot have the same direction. -/
private theorem distinct_edge_orientations {h : ℝ} {e e' : Set Ambient} {w u u' : Ambient}
    (heq : e = {p : Ambient | ∃ t ∈ Set.Icc (0 : ℝ) h, p = w + t • u})
    (heq' : e' = {p : Ambient | ∃ t ∈ Set.Icc (0 : ℝ) h, p = w + t • u'})
    (hee' : e ≠ e') : u ≠ u' := by
  intro huu
  apply hee'
  rw [heq, heq', huu]

/-- Every signed coordinate direction has Euclidean
norm one. -/
private theorem signedCoordinateUnit_norm {u : Ambient} (hu : SignedCoordinateUnit u) : ‖u‖ = 1 := by
  rcases hu with ⟨i, rfl | rfl⟩ <;> simp [PiLp.norm_single]

/-- Unequal signed coordinate directions are orthogonal
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

/-- For nonnegative radial parameters and nonpositive
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

/-- Distinct edges sharing an endpoint
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

/-- For parallel coordinate edges, either some fixed
coordinate of their initial vertices differs, or every fixed coordinate agrees. -/
private theorem fixed_coordinate_dichotomy (v v' : Ambient) (j : Fin 3) :
    (∃ i : Fin 3, i ≠ j ∧ v i ≠ v' i) ∨ ∀ i : Fin 3, i ≠ j → v i = v' i := by
  classical
  by_cases h : ∃ i : Fin 3, i ≠ j ∧ v i ≠ v' i
  · exact Or.inl h
  · refine Or.inr fun i hi => ?_
    by_contra hne
    exact h ⟨i, hi, hne⟩

/-- Every coordinate other than an edge's moving
coordinate is constant along the edge. -/
private theorem edge_fixed_coordinate {h : ℝ} {v p : Ambient} {j i : Fin 3}
    (hi : i ≠ j) (hp : p ∈ edgeGeom h v j) : p i = v i := by
  obtain ⟨a, _ha, rfl⟩ := edge_parameter_extract hp
  simpa only [if_neg hi] using edge_coordinate_formula h a v j i

/-- Differing fixed lattice coordinates of parallel
edges separate every pair of their points by at least one mesh length. -/
private theorem parallel_fixed_coordinate_separation {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) {v v' p p' : Ambient} {j i : Fin 3}
    (hv : v ∈ vertices N h) (hv' : v' ∈ vertices N h) (hi : i ≠ j)
    (hne : v i ≠ v' i) (hp : p ∈ edgeGeom h v j)
    (hp' : p' ∈ edgeGeom h v' j) : h ≤ ‖p - p'‖ := by
  have hs := lattice_separation hN hh (vertex_coordinate_mem_lattice hv i)
    (vertex_coordinate_mem_lattice hv' i) hne
  calc
    h ≤ |v i - v' i| := hs
    _ = |p i - p' i| := by rw [edge_fixed_coordinate hi hp, edge_fixed_coordinate hi hp']
    _ ≤ maxAbs (p - p') := by simpa using abs_apply_le_maxAbs (p - p') i
    _ ≤ ‖p - p'‖ := maxAbs_le_norm (p - p')

/-- Distinct parallel edge presentations agreeing in
all fixed coordinates must have different moving initial coordinates. -/
private theorem same_line_moving_coordinate_ne {h : ℝ} {v v' : Ambient} {j : Fin 3}
    {e e' : Set Ambient} (hfixed : ∀ i : Fin 3, i ≠ j → v i = v' i)
    (heq : e = edgeGeom h v j) (heq' : e' = edgeGeom h v' j)
    (hee' : e ≠ e') : v j ≠ v' j := by
  intro hj
  apply hee'
  have hvv' : v = v' := by
    apply PiLp.ext
    intro i
    by_cases hi : i = j
    · simpa [hi] using hj
    · exact hfixed i hi
  rw [heq, heq', hvv']

/-- Two unequal moving coordinates admit one of the two
strict orders. -/
private theorem moving_coordinate_order {v v' : Ambient} {j : Fin 3}
    (hne : v j ≠ v' j) : v j < v' j ∨ v' j < v j :=
  lt_or_gt_of_ne hne

/-- Disjoint consecutive endpoint pairs forbid the first
edge's terminal moving coordinate from being the second edge's initial coordinate. -/
private theorem same_line_coordinate_nonadjacent {h : ℝ} {v v' : Ambient} {j : Fin 3}
    (hfixed : ∀ i : Fin 3, i ≠ j → v i = v' i)
    (hendne : v + h • EuclideanSpace.single j 1 ≠ v') : v j + h ≠ v' j := by
  intro hadj
  apply hendne
  apply PiLp.ext
  intro i
  have hf := edge_coordinate_formula h 1 v j i
  have hf' : (v + h • EuclideanSpace.single j 1 : Ambient) i =
      if i = j then v j + h else v i := by simpa only [one_mul] using hf
  rw [hf']
  by_cases hi : i = j
  · subst i; simpa using hadj
  · rw [if_neg hi]
    exact hfixed i hi

/-- Ordered lattice points that are not adjacent are at
least two mesh steps apart. -/
private theorem ordered_lattice_two_step {N : ℕ} {h a b : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (ha : a ∈ lattice N h) (hb : b ∈ lattice N h) (ha_upper : a ≤ 1 - h)
    (hab : a < b) (hadj : a + h ≠ b) : a + 2 * h ≤ b := by
  have hs := lattice_separation hN hh ha hb (ne_of_lt hab)
  rw [abs_of_neg (sub_neg.mpr hab)] at hs
  have hab1 : a + h < b := lt_of_le_of_ne (by linarith) hadj
  have hsucc := lattice_successor hN hh ha ha_upper
  have hs2 := lattice_separation hN hh hsucc hb (ne_of_lt hab1)
  rw [abs_of_neg (sub_neg.mpr hab1)] at hs2
  linarith

/-- A two-mesh gap between parallel initial vertices
leaves at least one mesh length between arbitrary points of their unit-parameter segments. -/
private theorem ordered_parallel_segment_separation {h : ℝ} {v v' p p' : Ambient}
    {j : Fin 3} (hh : 0 ≤ h) (hgap : v j + 2 * h ≤ v' j)
    (hp : p ∈ edgeGeom h v j) (hp' : p' ∈ edgeGeom h v' j) : h ≤ ‖p - p'‖ := by
  obtain ⟨a, ha, rfl⟩ := edge_parameter_extract hp
  obtain ⟨b, hb, rfl⟩ := edge_parameter_extract hp'
  have hpa := (edge_coordinate_formula h a v j j).trans (if_pos rfl)
  have hpb := (edge_coordinate_formula h b v' j j).trans (if_pos rfl)
  have ha_upper : a * h ≤ h := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha.2 hh
  have hb_lower : 0 ≤ b * h := mul_nonneg hb.1 hh
  have hscalar : h ≤
      (v' + (b * h) • EuclideanSpace.single j 1 : Ambient) j -
        (v + (a * h) • EuclideanSpace.single j 1 : Ambient) j := by
    rw [hpa, hpb]
    linarith
  have habs : h ≤ |(v' + (b * h) • EuclideanSpace.single j 1 : Ambient) j -
      (v + (a * h) • EuclideanSpace.single j 1 : Ambient) j| :=
    hscalar.trans (le_abs_self _)
  calc
    h ≤ |(v' + (b * h) • EuclideanSpace.single j 1 : Ambient) j -
        (v + (a * h) • EuclideanSpace.single j 1 : Ambient) j| := habs
    _ = |(v + (a * h) • EuclideanSpace.single j 1 -
        (v' + (b * h) • EuclideanSpace.single j 1) : Ambient) j| := by
      simp only [PiLp.sub_apply, abs_sub_comm]
    _ ≤ maxAbs (v + (a * h) • EuclideanSpace.single j 1 -
        (v' + (b * h) • EuclideanSpace.single j 1)) := abs_apply_le_maxAbs _ j
    _ ≤ ‖v + (a * h) • EuclideanSpace.single j 1 -
        (v' + (b * h) • EuclideanSpace.single j 1)‖ := maxAbs_le_norm _

/-- Two distinct moving coordinates have a unique third
coordinate, and together the three indices exhaust the ambient coordinates. -/
private theorem third_coordinate_exhaust {j j' : Fin 3} (hjj' : j ≠ j') :
    ∃ m : Fin 3, m ≠ j ∧ m ≠ j' ∧ ∀ r : Fin 3, r = m ∨ r = j ∨ r = j' := by
  rcases lt_or_gt_of_ne hjj' with hlt | hgt
  · obtain ⟨m, hmj, hmj'⟩ := (square_remaining_index hlt).exists
    exact ⟨m, hmj, hmj', square_indices_exhaust hlt hmj hmj'⟩
  · obtain ⟨m, hmj', hmj⟩ := (square_remaining_index hgt).exists
    refine ⟨m, hmj, hmj', ?_⟩
    intro r
    rcases square_indices_exhaust hgt hmj' hmj r with hm | hj' | hj
    · exact Or.inl hm
    · exact Or.inr (Or.inr hj')
    · exact Or.inr (Or.inl hj)

/-- Differing lattice values at the third coordinate
separate arbitrary points on transverse edges by at least the mesh. -/
private theorem third_coordinate_separation {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    {v v' p p' : Ambient} {j j' m : Fin 3}
    (hv : v ∈ vertices N h) (hv' : v' ∈ vertices N h)
    (hmj : m ≠ j) (hmj' : m ≠ j') (hne : v m ≠ v' m)
    (hp : p ∈ edgeGeom h v j) (hp' : p' ∈ edgeGeom h v' j') : h ≤ ‖p - p'‖ := by
  have hs := lattice_separation hN hh (vertex_coordinate_mem_lattice hv m)
    (vertex_coordinate_mem_lattice hv' m) hne
  calc
    h ≤ |v m - v' m| := hs
    _ = |p m - p' m| := by rw [edge_fixed_coordinate hmj hp, edge_fixed_coordinate hmj' hp']
    _ ≤ maxAbs (p - p') := by simpa using abs_apply_le_maxAbs (p - p') m
    _ ≤ ‖p - p'‖ := maxAbs_le_norm (p - p')

/-- Relative to a lattice interval's lower endpoint,
another lattice point is one of its endpoints or stays at least one mesh from every interval point. -/
private theorem lattice_endpoint_or_gap {N : ℕ} {h a b : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (ha : a ∈ lattice N h) (hb : b ∈ lattice N h) (ha_upper : a ≤ 1 - h) :
    (b = a ∨ b = a + h) ∨ ∀ t ∈ Set.Icc (0 : ℝ) 1, h ≤ |(a + t * h) - b| := by
  by_cases hba : b = a
  · exact Or.inl (Or.inl hba)
  by_cases hbs : b = a + h
  · exact Or.inl (Or.inr hbs)
  have hpos := mesh_pos hN hh
  have hsep0 := lattice_separation hN hh hb ha hba
  rcases lt_or_gt_of_ne hba with hbelow | hab
  · rw [abs_of_neg (sub_neg.mpr hbelow)] at hsep0
    right
    intro t ht
    have ht0 := mul_nonneg ht.1 hpos.le
    rw [abs_of_nonneg] <;> linarith
  · rw [abs_of_pos (sub_pos.mpr hab)] at hsep0
    have hfirst : a + h ≤ b := by linarith
    have hstrict : a + h < b := lt_of_le_of_ne hfirst (Ne.symm hbs)
    have hsucc := lattice_successor hN hh ha ha_upper
    have hsep1 := lattice_separation hN hh hb hsucc hbs
    rw [abs_of_pos (sub_pos.mpr hstrict)] at hsep1
    right
    intro t ht
    have htle : t * h ≤ h := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 hpos.le
    rw [abs_of_nonpos] <;> linarith

/-- A fixed-coordinate mesh gap from an entire edge
implies Euclidean separation from any point having that fixed coordinate. -/
private theorem edge_coordinate_gap_separation {h b : ℝ} {v p p' : Ambient} {j : Fin 3}
    (hgap : ∀ t ∈ Set.Icc (0 : ℝ) 1, h ≤ |(v j + t * h) - b|)
    (hp : p ∈ edgeGeom h v j) (hp' : p' j = b) : h ≤ ‖p - p'‖ := by
  obtain ⟨t, ht, hpt⟩ := edge_parameter_extract hp
  have hs := hgap t ht
  have hcoord : p j = v j + t * h := by
    rw [hpt]
    exact (edge_coordinate_formula h t v j j).trans (if_pos rfl)
  calc
    h ≤ |v j + t * h - b| := hs
    _ = |(p - p') j| := by rw [PiLp.sub_apply, hcoord, hp']
    _ ≤ maxAbs (p - p') := abs_apply_le_maxAbs _ j
    _ ≤ ‖p - p'‖ := maxAbs_le_norm _

/-- Transverse edges whose third coordinate agrees and
whose two cross coordinates are endpoint values share one of their four literal endpoints. -/
private theorem transverse_common_endpoint {h : ℝ} {v v' : Ambient} {j j' m : Fin 3}
    (hjj' : j ≠ j') (hmj : m ≠ j) (hmj' : m ≠ j')
    (hexhaust : ∀ r : Fin 3, r = m ∨ r = j ∨ r = j')
    (hm : v m = v' m) (hj : v' j = v j ∨ v' j = v j + h)
    (hj' : v j' = v' j' ∨ v j' = v' j' + h) :
    ∃ w : Ambient, w ∈ ({v, v + h • EuclideanSpace.single j 1} : Set Ambient) ∧
      w ∈ ({v', v' + h • EuclideanSpace.single j' 1} : Set Ambient) := by
  have hLm : (v + h • EuclideanSpace.single j 1 : Ambient) m = v m := by
    simpa only [one_mul, if_neg hmj] using edge_coordinate_formula h 1 v j m
  have hLj : (v + h • EuclideanSpace.single j 1 : Ambient) j = v j + h := by
    simpa only [one_mul] using (edge_coordinate_formula h 1 v j j).trans (if_pos rfl)
  have hLj' : (v + h • EuclideanSpace.single j 1 : Ambient) j' = v j' := by
    simpa only [one_mul, if_neg hjj'.symm] using edge_coordinate_formula h 1 v j j'
  have hRm : (v' + h • EuclideanSpace.single j' 1 : Ambient) m = v' m := by
    simpa only [one_mul, if_neg hmj'] using edge_coordinate_formula h 1 v' j' m
  have hRj : (v' + h • EuclideanSpace.single j' 1 : Ambient) j = v' j := by
    simpa only [one_mul, if_neg hjj'] using edge_coordinate_formula h 1 v' j' j
  have hRj' : (v' + h • EuclideanSpace.single j' 1 : Ambient) j' = v' j' + h := by
    simpa only [one_mul] using (edge_coordinate_formula h 1 v' j' j').trans (if_pos rfl)
  rcases hj with hj | hj <;> rcases hj' with hj' | hj'
  · have heq : v = v' := Ambient_ext_of_three hexhaust hm hj.symm hj'
    exact ⟨v, by simp, by simp [heq]⟩
  · have heq : v = v' + h • EuclideanSpace.single j' 1 :=
      Ambient_ext_of_three hexhaust (hm.trans hRm.symm)
        (hj.symm.trans hRj.symm) (hj'.trans hRj'.symm)
    exact ⟨v, by simp, by simp [heq]⟩
  · have heq : v + h • EuclideanSpace.single j 1 = v' :=
      Ambient_ext_of_three hexhaust (hLm.trans hm) (hLj.trans hj.symm) (hLj'.trans hj')
    exact ⟨v + h • EuclideanSpace.single j 1, by simp, by simp [heq]⟩
  · have heq : v + h • EuclideanSpace.single j 1 =
        v' + h • EuclideanSpace.single j' 1 :=
      Ambient_ext_of_three hexhaust ((hLm.trans hm).trans hRm.symm)
        ((hLj.trans hj.symm).trans hRj.symm) ((hLj'.trans hj').trans hRj'.symm)
    exact ⟨v + h • EuclideanSpace.single j 1, by simp, by simp [heq]⟩

/-- Two distinct mesh edges with
disjoint endpoint sets keep every pair of their points at least one mesh length apart. -/
public theorem edge_dist_ge_mesh_of_no_common_endpoint {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    {e e' : Set Ambient} (he : e ∈ edges N h) (he' : e' ∈ edges N h) (hee' : e ≠ e')
    (hend : Disjoint (edgeEndpoints N h ⟨e, he⟩) (edgeEndpoints N h ⟨e', he'⟩))
    {p p' : Ambient} (hp : p ∈ e) (hp' : p' ∈ e') : h ≤ ‖p - p'‖ := by
  obtain ⟨v, j, hv, hvj, _hsub, heq, hE⟩ := edge_presentation hN hh he
  obtain ⟨v', j', hv', hvj', _hsub', heq', hE'⟩ := edge_presentation hN hh he'
  change e = edgeGeom h v j at heq
  change e' = edgeGeom h v' j' at heq'
  rw [heq] at hp
  rw [heq'] at hp'
  have hdpair : Disjoint ({v, v + h • EuclideanSpace.single j 1} : Set Ambient)
      ({v', v' + h • EuclideanSpace.single j' 1} : Set Ambient) := by rwa [hE, hE'] at hend
  by_cases hjj' : j = j'
  · subst j'
    rcases fixed_coordinate_dichotomy v v' j with ⟨i, hi, hne⟩ | hfixed
    · exact parallel_fixed_coordinate_separation hN hh hv hv' hi hne hp hp'
    · have hmove := same_line_moving_coordinate_ne hfixed heq heq' hee'
      rcases moving_coordinate_order hmove with hlt | hgt
      · have hendne : v + h • EuclideanSpace.single j 1 ≠ v' := by
          intro hEq
          exact (Set.disjoint_left.mp hdpair)
            (show v + h • EuclideanSpace.single j 1 ∈
              ({v, v + h • EuclideanSpace.single j 1} : Set Ambient) by simp)
            (show v + h • EuclideanSpace.single j 1 ∈
              ({v', v' + h • EuclideanSpace.single j 1} : Set Ambient) by rw [hEq]; simp)
        have hgap := ordered_lattice_two_step hN hh
          (vertex_coordinate_mem_lattice hv j) (vertex_coordinate_mem_lattice hv' j) hvj hlt
          (same_line_coordinate_nonadjacent hfixed hendne)
        exact ordered_parallel_segment_separation (mesh_pos hN hh).le hgap hp hp'
      · have hendne : v' + h • EuclideanSpace.single j 1 ≠ v := by
          intro hEq
          exact (Set.disjoint_left.mp hdpair)
            (show v' + h • EuclideanSpace.single j 1 ∈
              ({v, v + h • EuclideanSpace.single j 1} : Set Ambient) by rw [hEq]; simp)
            (show v' + h • EuclideanSpace.single j 1 ∈
              ({v', v' + h • EuclideanSpace.single j 1} : Set Ambient) by simp)
        have hgap := ordered_lattice_two_step hN hh
          (vertex_coordinate_mem_lattice hv' j) (vertex_coordinate_mem_lattice hv j) hvj' hgt
          (same_line_coordinate_nonadjacent (fun i hi => (hfixed i hi).symm) hendne)
        calc
          h ≤ ‖p' - p‖ := ordered_parallel_segment_separation (mesh_pos hN hh).le hgap hp' hp
          _ = ‖p - p'‖ := norm_sub_rev p' p
  · obtain ⟨m, hmj, hmj', hexhaust⟩ := third_coordinate_exhaust hjj'
    by_cases hm : v m = v' m
    · rcases lattice_endpoint_or_gap hN hh (vertex_coordinate_mem_lattice hv j)
          (vertex_coordinate_mem_lattice hv' j) hvj with hj | hgap
      · rcases lattice_endpoint_or_gap hN hh (vertex_coordinate_mem_lattice hv' j')
            (vertex_coordinate_mem_lattice hv j') hvj' with hj' | hgap'
        · obtain ⟨w, hw, hw'⟩ := transverse_common_endpoint hjj' hmj hmj' hexhaust hm hj hj'
          exact False.elim ((Set.disjoint_left.mp hdpair) hw hw')
        · calc
            h ≤ ‖p' - p‖ := edge_coordinate_gap_separation hgap' hp'
              (edge_fixed_coordinate (Ne.symm hjj') hp)
            _ = ‖p - p'‖ := norm_sub_rev p' p
      · exact edge_coordinate_gap_separation hgap hp (edge_fixed_coordinate hjj' hp')
    · exact third_coordinate_separation hN hh hv hv' hmj hmj' hm hp hp'

end TopologicalSpace.CubeBoundaryThree
