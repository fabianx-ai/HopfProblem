module

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
