module

public import Lib.Topology.Dimension.CubeBoundaryThreeLebesgue
public import Mathlib.Analysis.Normed.Module.Convex

public import Lib.Topology.Dimension.CubeBoundaryThreeCells
public import Mathlib.Data.Finite.Sum
public import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option warningAsError true
set_option autoImplicit false
open Set
namespace TopologicalSpace.CubeBoundaryThree

/-- Definition 4.1: a brick index remembers the dimension and the actual geometric cell. -/
public inductive BrickIndex (N : ℕ) (h : ℝ)
  | vertex : {v : Ambient // v ∈ vertices N h} → BrickIndex N h
  | edge : {e : Set Ambient // e ∈ edges N h} → BrickIndex N h
  | square : {s : Set Ambient // s ∈ squares N h} → BrickIndex N h

/- Representation-only encoding into the literal nested finite sum. -/
private def brickIndexToSum (N : ℕ) (h : ℝ) : BrickIndex N h →
    {v : Ambient // v ∈ vertices N h} ⊕
      ({e : Set Ambient // e ∈ edges N h} ⊕ {s : Set Ambient // s ∈ squares N h})
  | .vertex v => Sum.inl v
  | .edge e => Sum.inr (Sum.inl e)
  | .square s => Sum.inr (Sum.inr s)

private theorem brickIndexToSum_injective (N : ℕ) (h : ℝ) :
    Function.Injective (brickIndexToSum N h) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [brickIndexToSum]

/-- Definition 4.1: the three-way actual-cell brick index is finite. -/
public theorem finite_brickIndex (N : ℕ) (h : ℝ) : Finite (BrickIndex N h) := by
  let _ : Fintype {v : Ambient // v ∈ vertices N h} := (finite_vertices N h).fintype
  let _ : Fintype {e : Set Ambient // e ∈ edges N h} := (finite_edges N h).fintype
  let _ : Fintype {s : Set Ambient // s ∈ squares N h} := (finite_squares N h).fintype
  exact Finite.of_injective (brickIndexToSum N h) (brickIndexToSum_injective N h)

/-- Definition 4.1: the boundary ball of radius `4 * epsilon` about an actual vertex. -/
public def vertexBrick {N : ℕ} {h : ℝ} (epsilon : ℝ)
    (v : {v : Ambient // v ∈ vertices N h}) : Set Boundary :=
  {x | dist (x : Ambient) (v : Ambient) < 4 * epsilon}

/-- Definition 4.1: the edge tube with exclusion from every intrinsic endpoint. -/
public noncomputable def edgeBrick {N : ℕ} {h : ℝ} (epsilon : ℝ)
    (e : {e : Set Ambient // e ∈ edges N h}) : Set Boundary :=
  {x | Metric.infDist (x : Ambient) (e : Set Ambient) < epsilon ∧
    ∀ w ∈ edgeEndpoints N h e, 3 * epsilon < dist (x : Ambient) w}

/-- Definition 4.1: the square brick is its intrinsic relative interior in the boundary. -/
public noncomputable def squareBrick {N : ℕ} {h : ℝ}
    (s : {s : Set Ambient // s ∈ squares N h}) : Set Boundary :=
  {x | (x : Ambient) ∈ squareRelInterior N h s}

/-- Definition 4.1: dispatch the exact raw brick by its actual-cell tag. -/
public noncomputable def brickSet (N : ℕ) (h epsilon : ℝ) : BrickIndex N h → Set Boundary
  | .vertex v => vertexBrick epsilon v
  | .edge e => edgeBrick epsilon e
  | .square s => squareBrick s

/-- Definition 4.1: Vertex membership is precisely the defining distance inequality. -/
public theorem mem_vertexBrick {N : ℕ} {h epsilon : ℝ}
    (v : {v : Ambient // v ∈ vertices N h}) (x : Boundary) :
    x ∈ vertexBrick epsilon v ↔ dist (x : Ambient) (v : Ambient) < 4 * epsilon := Iff.rfl

/-- Definition 4.1: Edge membership is the tube condition together with all endpoint exclusions. -/
public theorem mem_edgeBrick {N : ℕ} {h epsilon : ℝ}
    (e : {e : Set Ambient // e ∈ edges N h}) (x : Boundary) :
    x ∈ edgeBrick epsilon e ↔ Metric.infDist (x : Ambient) (e : Set Ambient) < epsilon ∧
      ∀ w ∈ edgeEndpoints N h e, 3 * epsilon < dist (x : Ambient) w := Iff.rfl

/-- Definition 4.1: Square membership is membership in the intrinsic relative interior. -/
public theorem mem_squareBrick {N : ℕ} {h : ℝ}
    (s : {s : Set Ambient // s ∈ squares N h}) (x : Boundary) :
    x ∈ squareBrick s ↔ (x : Ambient) ∈ squareRelInterior N h s := Iff.rfl

/-- Definition 4.1: Dispatching a vertex tag returns its vertex brick. -/
public theorem brickSet_vertex {N : ℕ} {h epsilon : ℝ}
    (v : {v : Ambient // v ∈ vertices N h}) :
    brickSet N h epsilon (.vertex v) = vertexBrick epsilon v := by simp [brickSet]

/-- Definition 4.1: Dispatching an edge tag returns its edge brick. -/
public theorem brickSet_edge {N : ℕ} {h epsilon : ℝ}
    (e : {e : Set Ambient // e ∈ edges N h}) :
    brickSet N h epsilon (.edge e) = edgeBrick epsilon e := by simp [brickSet]

/-- Definition 4.1: Dispatching a square tag returns its square brick. -/
public theorem brickSet_square {N : ℕ} {h epsilon : ℝ}
    (s : {s : Set Ambient // s ∈ squares N h}) :
    brickSet N h epsilon (.square s) = squareBrick s := by simp [brickSet]

/- Owner-local: an endpoint presentation expands the unordered endpoint condition to both points. -/
private theorem mem_edgeBrick_of_presentation {N : ℕ} {h epsilon : ℝ}
    (e : {e : Set Ambient // e ∈ edges N h}) {v : Ambient} {j : Fin 3}
    (hend : edgeEndpoints N h e = {v, v + h • EuclideanSpace.single j 1})
    (x : Boundary) :
    x ∈ edgeBrick epsilon e ↔
      Metric.infDist (x : Ambient) (e : Set Ambient) < epsilon ∧
      3 * epsilon < dist (x : Ambient) v ∧
      3 * epsilon < dist (x : Ambient) (v + h • EuclideanSpace.single j 1) := by
  rw [mem_edgeBrick, hend]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

/- Owner-local: the intrinsic square brick is the boundary trace of the signed ambient open box. -/
private theorem squareBrick_ambientOpen_description {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (s : {s : Set Ambient // s ∈ squares N h}) :
    ∃ (v : Ambient) (j k i : Fin 3),
      v ∈ vertices N h ∧ j < k ∧ v j ≤ 1 - h ∧ v k ≤ 1 - h ∧
      i ≠ j ∧ i ≠ k ∧ |v i| = 1 ∧
      squareBrick s = {x : Boundary |
        0 < v i * (x : Ambient) i ∧
        (x : Ambient) j ∈ Set.Ioo (v j) (v j + h) ∧
        (x : Ambient) k ∈ Set.Ioo (v k) (v k + h)} := by
  obtain ⟨v, j, k, i, hv, hjk, hvj, hvk, hij, hik, hvi, _hclosed, hri, _hface⟩ :=
    square_coordinate_description hN hh s.property
  refine ⟨v, j, k, i, hv, hjk, hvj, hvk, hij, hik, hvi, ?_⟩
  -- Each moving coordinate lies strictly between -1 and 1, using the vertex bounds.
  have hstrict (x : Ambient) (r : Fin 3) (hvr : v r ≤ 1 - h)
      (hxr : x r ∈ Set.Ioo (v r) (v r + h)) : |x r| < 1 := by
    rw [abs_lt]
    have hvmax : maxAbs v = 1 := vertex_mem_boundary hv
    have hvabs : |v r| ≤ 1 := by
      rw [← hvmax]
      fin_cases r <;> simp [maxAbs]
    have hvlow : -1 ≤ v r := (abs_le.mp hvabs).1
    constructor <;> linarith [hxr.1, hxr.2]
  -- Three distinct coordinate indices exhaust the ambient coordinates.
  have hexhaust : ∀ r : Fin 3, r = i ∨ r = j ∨ r = k := by
    intro r
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases r <;> omega
  -- On the boundary, the remaining coordinate is saturated; its sign selects the face.
  have hsign : ∀ x : Boundary,
      (x : Ambient) j ∈ Set.Ioo (v j) (v j + h) →
      (x : Ambient) k ∈ Set.Ioo (v k) (v k + h) →
      ((x : Ambient) i = v i ↔ 0 < v i * (x : Ambient) i) := by
    intro x hxj hxk
    have hj := hstrict (x : Ambient) j hvj hxj
    have hk := hstrict (x : Ambient) k hvk hxk
    have hx : maxAbs (x : Ambient) = 1 := x.property
    have hxi : |(x : Ambient) i| = 1 := by
      have hile : |(x : Ambient) i| ≤ 1 := by
        rw [← hx]
        fin_cases i <;> simp [maxAbs]
      apply le_antisymm hile
      by_contra hn
      have hi : |(x : Ambient) i| < 1 := lt_of_not_ge hn
      have hall : ∀ r : Fin 3, |(x : Ambient) r| < 1 := by
        intro r
        rcases hexhaust r with rfl | rfl | rfl <;> assumption
      have : maxAbs (x : Ambient) < 1 := max_lt (hall 0) (max_lt (hall 1) (hall 2))
      linarith
    constructor
    · intro heq
      rw [heq]
      have ha2 : (v i) ^ 2 = 1 := by rw [← sq_abs, hvi]; norm_num
      nlinarith
    · intro hprod
      have ha2 : (v i) ^ 2 = 1 := by rw [← sq_abs, hvi]; norm_num
      have hb2 : ((x : Ambient) i) ^ 2 = 1 := by rw [← sq_abs, hxi]; norm_num
      nlinarith [sq_nonneg (v i - (x : Ambient) i), sq_nonneg (v i + (x : Ambient) i)]
  -- Replace fixed-coordinate equality by this conditional sign equivalence in the rectangle.
  ext x
  change (x : Ambient) ∈ squareRelInterior N h s ↔ _
  rw [hri]
  constructor
  · rintro ⟨hxi, hxj, hxk⟩
    exact ⟨(hsign x hxj hxk).mp hxi, hxj, hxk⟩
  · rintro ⟨hprod, hxj, hxk⟩
    exact ⟨(hsign x hxj hxk).mpr hprod, hxj, hxk⟩

end TopologicalSpace.CubeBoundaryThree

namespace TopologicalSpace.CubeBoundaryThree

/-- A vertex brick is the trace of an ambient open ball under the continuous
boundary inclusion, hence is open in the boundary. (Lemma 4.2.) -/
private theorem isOpen_vertexBrick {N : ℕ} {h epsilon : ℝ}
    (v : {v : Ambient // v ∈ vertices N h}) : IsOpen (vertexBrick epsilon v) := by
  change IsOpen ((fun x : Boundary => (x : Ambient)) ⁻¹'
    Metric.ball (v : Ambient) (4 * epsilon))
  exact IsOpen.preimage continuous_subtype_val Metric.isOpen_ball

/-- Present the edge by its two endpoints. Distance to the edge is continuous
because it is 1-Lipschitz, and distance to either endpoint is continuous. The tube
and both strict endpoint exclusions are therefore open; their intersection pulls
back to the edge brick under the boundary inclusion. (Lemma 4.2.) -/
private theorem isOpen_edgeBrick {N : ℕ} {h epsilon : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (e : {e : Set Ambient // e ∈ edges N h}) : IsOpen (edgeBrick epsilon e) := by
  obtain ⟨v, j, _hv, _hvj, _hsub, _hseg, hend⟩ := edge_presentation hN hh e.property
  have heq : edgeBrick epsilon e = (fun x : Boundary => (x : Ambient)) ⁻¹'
      ({x : Ambient | Metric.infDist x (e : Set Ambient) < epsilon} ∩
        ({x : Ambient | 3 * epsilon < dist x v} ∩
          {x : Ambient | 3 * epsilon < dist x (v + h • EuclideanSpace.single j 1)})) := by
    ext x
    exact mem_edgeBrick_of_presentation e hend x
  rw [heq]
  apply IsOpen.preimage continuous_subtype_val
  have htube : IsOpen {x : Ambient | Metric.infDist x (e : Set Ambient) < epsilon} :=
    isOpen_lt (Metric.continuous_infDist_pt (e : Set Ambient)) continuous_const
  have hfirst : IsOpen {x : Ambient | 3 * epsilon < dist x v} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hlast : IsOpen {x : Ambient |
      3 * epsilon < dist x (v + h • EuclideanSpace.single j 1)} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  exact htube.inter (hfirst.inter hlast)

/-- The square brick is the boundary trace of its signed ambient box. The
positive face-sign condition and both open coordinate intervals are open by
continuity of coordinate evaluation and multiplication. Their intersection has
open preimage in the boundary. (Lemma 4.2.) -/
private theorem isOpen_squareBrick {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (s : {s : Set Ambient // s ∈ squares N h}) : IsOpen (squareBrick s) := by
  obtain ⟨v, j, k, i, _hv, _hjk, _hvj, _hvk, _hij, _hik, _hvi, hdesc⟩ :=
    squareBrick_ambientOpen_description hN hh s
  have heq : squareBrick s = (fun x : Boundary => (x : Ambient)) ⁻¹'
      ({x : Ambient | 0 < v i * x i} ∩
        ((fun x : Ambient => x j) ⁻¹' Set.Ioo (v j) (v j + h) ∩
          (fun x : Ambient => x k) ⁻¹' Set.Ioo (v k) (v k + h))) := hdesc
  rw [heq]
  apply IsOpen.preimage continuous_subtype_val
  have ci := PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i
  have cj := PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j
  have ck := PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k
  have hsign : IsOpen {x : Ambient | 0 < v i * x i} :=
    isOpen_lt continuous_const (continuous_const.mul ci)
  have hj : IsOpen ((fun x : Ambient => x j) ⁻¹' Set.Ioo (v j) (v j + h)) :=
    IsOpen.preimage cj isOpen_Ioo
  have hk : IsOpen ((fun x : Ambient => x k) ⁻¹' Set.Ioo (v k) (v k + h)) :=
    IsOpen.preimage ck isOpen_Ioo
  exact hsign.inter (hj.inter hk)

/-- Each index has exactly one of the vertex, edge, or square tags. The
corresponding openness result therefore proves every raw brick open. (Lemma 4.2.) -/
private theorem isOpen_brickSet {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) (epsilon : ℝ)
    (c : BrickIndex N h) : IsOpen (brickSet N h epsilon c) := by
  cases c with
  | vertex v =>
    rw [brickSet_vertex]
    exact isOpen_vertexBrick v
  | edge e =>
    rw [brickSet_edge]
    exact isOpen_edgeBrick hN hh e
  | square s =>
    rw [brickSet_square]
    exact isOpen_squareBrick hN hh s

/-- The open family consists of precisely the raw bricks, equipped with the
openness proved in Lemma 4.2. -/
public noncomputable def brickOpens {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) (epsilon : ℝ) :
    BrickIndex N h → Opens Boundary :=
  fun c => ⟨brickSet N h epsilon c, isOpen_brickSet hN hh epsilon c⟩

/-- Forgetting openness recovers the same raw brick. -/
public theorem coe_brickOpens {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) (epsilon : ℝ)
    (c : BrickIndex N h) :
    (brickOpens hN hh epsilon c : Set Boundary) = brickSet N h epsilon c := by simp [brickOpens, brickSet]

/-- Membership in the open family is exactly membership in the raw family. -/
public theorem mem_brickOpens {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) (epsilon : ℝ)
    (c : BrickIndex N h) (x : Boundary) :
    x ∈ brickOpens hN hh epsilon c ↔ x ∈ brickSet N h epsilon c := Iff.rfl

/-- The vertex tag has the same underlying vertex brick. -/
public theorem coe_brickOpens_vertex {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) (epsilon : ℝ)
    (v : {v : Ambient // v ∈ vertices N h}) :
    (brickOpens hN hh epsilon (.vertex v) : Set Boundary) = vertexBrick epsilon v := by simp [brickOpens, brickSet]

/-- The edge tag has the same underlying edge brick. -/
public theorem coe_brickOpens_edge {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) (epsilon : ℝ)
    (e : {e : Set Ambient // e ∈ edges N h}) :
    (brickOpens hN hh epsilon (.edge e) : Set Boundary) = edgeBrick epsilon e := by simp [brickOpens, brickSet]

/-- The square tag has the same underlying square brick. -/
public theorem coe_brickOpens_square {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) (epsilon : ℝ)
    (s : {s : Set Ambient // s ∈ squares N h}) :
    (brickOpens hN hh epsilon (.square s) : Set Boundary) = squareBrick s := by simp [brickOpens, brickSet]

/-- The open vertex brick retains the defining radius inequality. -/
public theorem mem_brickOpens_vertex {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) (epsilon : ℝ)
    (v : {v : Ambient // v ∈ vertices N h}) (x : Boundary) :
    x ∈ brickOpens hN hh epsilon (.vertex v) ↔
      dist (x : Ambient) (v : Ambient) < 4 * epsilon := Iff.rfl

/-- The open edge brick retains the tube condition and every endpoint exclusion. -/
public theorem mem_brickOpens_edge {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) (epsilon : ℝ)
    (e : {e : Set Ambient // e ∈ edges N h}) (x : Boundary) :
    x ∈ brickOpens hN hh epsilon (.edge e) ↔
      Metric.infDist (x : Ambient) (e : Set Ambient) < epsilon ∧
      ∀ w ∈ edgeEndpoints N h e, 3 * epsilon < dist (x : Ambient) w := Iff.rfl

/-- The open square brick retains membership in its intrinsic relative interior. -/
public theorem mem_brickOpens_square {N : ℕ} {h : ℝ}
    (hN : 0 < N) (hh : h = 2 / (N : ℝ)) (epsilon : ℝ)
    (s : {s : Set Ambient // s ∈ squares N h}) (x : Boundary) :
    x ∈ brickOpens hN hh epsilon (.square s) ↔
      (x : Ambient) ∈ squareRelInterior N h s := Iff.rfl

end TopologicalSpace.CubeBoundaryThree

namespace TopologicalSpace.CubeBoundaryThree

/- Two points of a vertex brick are each within 4 epsilon of its vertex. The triangle inequality gives 8 epsilon in the ambient image, hence in the boundary subtype (Lemma 4.3). -/
private theorem vertexBrick_diam_le {N : ℕ} {h epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (v : {v : Ambient // v ∈ vertices N h}) :
    Metric.diam (vertexBrick epsilon v) ≤ 8 * epsilon := by
  rw [diam_coe_image]
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg (by norm_num) hepsilon)
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hx' := (mem_vertexBrick v x).mp hx
  have hy' := (mem_vertexBrick v y).mp hy
  have ht := dist_triangle (x : Ambient) (v : Ambient) (y : Ambient)
  rw [dist_comm (v : Ambient) (y : Ambient)] at ht
  linarith

/- An edge is the segment joining its two endpoints, equivalently their finite convex hull; thus it is compact, as used to attain the nearest points in Lemma 4.3. -/
private theorem isCompact_edge {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (e : {e : Set Ambient // e ∈ edges N h}) : IsCompact (e : Set Ambient) := by
  obtain ⟨v, j, _, _, _, he, _⟩ := edge_presentation hN hh e.property
  rw [he, ← convexHull_pair]
  exact ((Set.finite_singleton (v + h • EuclideanSpace.single j 1)).insert v).isCompact_convexHull ℝ

/- The segment contains its left endpoint and is compact. Distance to this nonempty edge is therefore attained, independently of any later brick-nonemptiness result (Lemma 4.3). -/
private theorem edge_infDist_attained {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (e : {e : Set Ambient // e ∈ edges N h}) (x : Ambient) :
    ∃ p ∈ (e : Set Ambient), Metric.infDist x (e : Set Ambient) = dist x p := by
  have hne : (e : Set Ambient).Nonempty := by
    obtain ⟨v, j, _, _, _, he, _⟩ := edge_presentation hN hh e.property
    rw [he]
    exact ⟨v, left_mem_segment ℝ v (v + h • EuclideanSpace.single j 1)⟩
  exact (isCompact_edge hN hh e).exists_infDist_eq_dist hne x

/- The endpoint displacement has one Euclidean coordinate h, so its norm is h for nonnegative h (the edge-length calculation in Lemma 4.3). -/
private theorem edge_endpoint_dist (v : Ambient) (j : Fin 3) (h : ℝ) (hh : 0 ≤ h) :
    dist v (v + h • EuclideanSpace.single j 1) = h := by
  rw [dist_eq_norm]
  simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]

/- The diameter of the segment equals that of its two endpoints, whose distance is h. Every pair of points of the compact edge is therefore at distance at most h (Lemma 4.3). -/
private theorem edge_points_dist_le_mesh {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (e : {e : Set Ambient // e ∈ edges N h})
    {p q : Ambient} (hp : p ∈ (e : Set Ambient)) (hq : q ∈ (e : Set Ambient)) :
    dist p q ≤ h := by
  have hpos : 0 < h := by
    rw [hh]
    exact div_pos (by norm_num) (Nat.cast_pos.mpr hN)
  obtain ⟨v, j, _, _, _, he, _⟩ := edge_presentation hN hh e.property
  calc
    dist p q ≤ Metric.diam (e : Set Ambient) :=
      Metric.dist_le_diam_of_mem (isCompact_edge hN hh e).isBounded hp hq
    _ = h := by
      rw [he, ← convexHull_pair, convexHull_diam, Metric.diam_pair,
        edge_endpoint_dist v j h hpos.le]

/- Choose attained nearest points p and q on the edge. The two outer distances are below epsilon and the segment leg is at most h. Two triangle inequalities give h + 2 epsilon, then diameter transport gives the brick bound (Lemma 4.3). -/
private theorem edgeBrick_diam_le {N : ℕ} {h epsilon : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (hepsilon : 0 ≤ epsilon)
    (e : {e : Set Ambient // e ∈ edges N h}) :
    Metric.diam (edgeBrick epsilon e) ≤ h + 2 * epsilon := by
  have hpos : 0 < h := by
    rw [hh]
    exact div_pos (by norm_num) (Nat.cast_pos.mpr hN)
  rw [diam_coe_image]
  apply Metric.diam_le_of_forall_dist_le
    (add_nonneg hpos.le (mul_nonneg (by norm_num) hepsilon))
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨p, hp, hxp⟩ := edge_infDist_attained hN hh e (x : Ambient)
  obtain ⟨q, hq, hyq⟩ := edge_infDist_attained hN hh e (y : Ambient)
  have hx' := ((mem_edgeBrick e x).mp hx).1
  have hy' := ((mem_edgeBrick e y).mp hy).1
  rw [hxp] at hx'
  rw [hyq] at hy'
  have hpq := edge_points_dist_le_mesh hN hh e hp hq
  have ht₁ := dist_triangle (x : Ambient) p (y : Ambient)
  have ht₂ := dist_triangle p q (y : Ambient)
  rw [dist_comm q (y : Ambient)] at ht₂
  linarith

/- The two points have the same square origin and two distinct coordinate directions. Subtracting cancels the origin and leaves exactly the two parameter differences in the squared Euclidean norm (Lemma 4.3). -/
private theorem square_parameter_dist_sq (v : Ambient) (j k : Fin 3) (hjk : j < k)
    (h a b a' b' : ℝ) :
    dist (v + (a*h) • EuclideanSpace.single j 1 + (b*h) • EuclideanSpace.single k 1)
      (v + (a'*h) • EuclideanSpace.single j 1 + (b'*h) • EuclideanSpace.single k 1) ^ 2 =
      h^2 * ((a-a')^2 + (b-b')^2) := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  fin_cases j <;> fin_cases k
  all_goals simp_all [Fin.sum_univ_succ, PiLp.single_apply]
  all_goals ring

/- Both square parameters lie in [0,1], so each parameter difference has absolute value at most one. Their two squares sum to at most two; the squared-norm formula and nonnegative square root give h sqrt 2 (Lemma 4.3). -/
private theorem square_points_dist_le_mesh_sqrtTwo {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (s : {s : Set Ambient // s ∈ squares N h})
    {p q : Ambient} (hp : p ∈ (s : Set Ambient)) (hq : q ∈ (s : Set Ambient)) :
    dist p q ≤ h * Real.sqrt 2 := by
  have hpos : 0 < h := by
    rw [hh]
    exact div_pos (by norm_num) (Nat.cast_pos.mpr hN)
  obtain ⟨v, j, k, _, hjk, _, _, _, hs, _⟩ := square_presentation hN hh s.property
  rw [hs] at hp hq
  obtain ⟨a, ha, b, hb, rfl⟩ := hp
  obtain ⟨a', ha', b', hb', rfl⟩ := hq
  have haa : |a - a'| ≤ 1 := abs_sub_le_iff.mpr
    ⟨by linarith [ha.1, ha.2, ha'.1, ha'.2],
     by linarith [ha.1, ha.2, ha'.1, ha'.2]⟩
  have hbb : |b - b'| ≤ 1 := abs_sub_le_iff.mpr
    ⟨by linarith [hb.1, hb.2, hb'.1, hb'.2],
     by linarith [hb.1, hb.2, hb'.1, hb'.2]⟩
  have haa₂ := (sq_le_one_iff_abs_le_one (a - a')).mpr haa
  have hbb₂ := (sq_le_one_iff_abs_le_one (b - b')).mpr hbb
  have hsum : (a - a')^2 + (b - b')^2 ≤ 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg h)
  apply le_of_sq_le_sq ?_ (mul_nonneg hpos.le (Real.sqrt_nonneg 2))
  rw [square_parameter_dist_sq v j k hjk h a b a' b', mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact hmul

/- An intrinsic-interior point has the same square parameters in (0,1); weakening the endpoint inequalities places it in the closed square (Lemma 4.3). -/
private theorem squareBrick_coe_mem {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (s : {s : Set Ambient // s ∈ squares N h})
    {x : Boundary} (hx : x ∈ squareBrick s) : (x : Ambient) ∈ (s : Set Ambient) := by
  obtain ⟨v, j, k, _, _, _, _, _, hs, hi⟩ := square_presentation hN hh s.property
  have hx' := (mem_squareBrick s x).mp hx
  rw [hi] at hx'
  obtain ⟨a, ha, b, hb, hx'⟩ := hx'
  rw [hs]
  exact ⟨a, ⟨ha.1.le, ha.2.le⟩, b, ⟨hb.1.le, hb.2.le⟩, hx'⟩

/- Two square-brick points lie in the closed square, where the two-parameter estimate bounds their distance by h sqrt 2. Transport diameter through the boundary inclusion (Lemma 4.3). -/
private theorem squareBrick_diam_le {N : ℕ} {h : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (s : {s : Set Ambient // s ∈ squares N h}) :
    Metric.diam (squareBrick s) ≤ h * Real.sqrt 2 := by
  have hpos : 0 < h := by
    rw [hh]
    exact div_pos (by norm_num) (Nat.cast_pos.mpr hN)
  rw [diam_coe_image]
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg hpos.le (Real.sqrt_nonneg 2))
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact square_points_dist_le_mesh_sqrtTwo hN hh s
    (squareBrick_coe_mem hN hh s hx) (squareBrick_coe_mem hN hh s hy)

/- The three tags have bounds 8 epsilon, h + 2 epsilon and h sqrt 2. Composing each bound with its strict comparison to the same lambda proves the common brick estimate (Lemma 4.3). -/
private theorem brick_diam_lt {N : ℕ} {h epsilon lambda : ℝ} (hN : 0 < N)
    (hh : h = 2 / (N : ℝ)) (hepsilon : 0 ≤ epsilon)
    (hv : 8 * epsilon < lambda) (he : h + 2 * epsilon < lambda)
    (hs : h * Real.sqrt 2 < lambda) (c : BrickIndex N h) :
    Metric.diam (brickSet N h epsilon c) < lambda := by
  cases c with
  | vertex v =>
    rw [brickSet_vertex]
    exact lt_of_le_of_lt (vertexBrick_diam_le hepsilon v) hv
  | edge e =>
    rw [brickSet_edge]
    exact lt_of_le_of_lt (edgeBrick_diam_le hN hh hepsilon e) he
  | square s =>
    rw [brickSet_square]
    exact lt_of_le_of_lt (squareBrick_diam_le hN hh s) hs

end TopologicalSpace.CubeBoundaryThree
