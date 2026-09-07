module
public import Lib.Topology.Dimension.CubeBoundaryThreeBricks

set_option autoImplicit false
set_option warningAsError true
open Set
namespace TopologicalSpace.CubeBoundaryThree

/- Lemma 5.1(a): two vertex radii give distance below eight epsilon, hence below
the mesh; distinct vertices have distance at least the mesh. -/
private theorem vertex_eq_of_mem_vertexBrick
    {N : ℕ} {h epsilon : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (h8 : 8 * epsilon < h)
    (v w : {v : Ambient // v ∈ vertices N h}) (x : Boundary)
    (hv : x ∈ vertexBrick epsilon v) (hw : x ∈ vertexBrick epsilon w) : v = w := by
  by_contra hne
  have hsep := vertex_separation hN hh v.property w.property (Subtype.coe_injective.ne hne)
  have hv' := (mem_vertexBrick v x).mp hv
  have hw' := (mem_vertexBrick w x).mp hw
  have htri := dist_triangle (v : Ambient) (x : Ambient) (w : Ambient)
  rw [dist_comm (v : Ambient) (x : Ambient)] at htri
  have hlow : h ≤ dist (v : Ambient) (w : Ambient) := by
    rw [dist_eq_norm]
    exact hsep.1.trans hsep.2
  linarith

/- The nearby-point witnesses in Lemma 5.1(b) lie in actual edges. Each edge is
a closed segment, whose first endpoint supplies its nonemptiness. -/
private theorem edge_nonempty_for_tier
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (e : {e : Set Ambient // e ∈ edges N h}) : (e : Set Ambient).Nonempty := by
  obtain ⟨a, j, _, _, _, heq, _⟩ := edge_presentation hN hh e.property
  exact ⟨a, heq.symm ▸ left_mem_segment ℝ a (a + h • EuclideanSpace.single j 1)⟩

/- Lemma 5.1(b): the strict tube inequality for a nonempty edge gives an actual
point of that edge at distance strictly below epsilon. No minimizing point is needed. -/
private theorem edge_near_point_of_mem_brick
    {N : ℕ} {h epsilon : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (e : {e : Set Ambient // e ∈ edges N h}) (x : Boundary)
    (hx : x ∈ edgeBrick epsilon e) :
    ∃ p ∈ (e : Set Ambient), dist (x : Ambient) p < epsilon := by
  exact (Metric.infDist_lt_iff (edge_nonempty_for_tier hN hh e)).mp
    ((mem_edgeBrick e x).mp hx).1

/- Lemma 5.1(b), common endpoint: the edge geometry bounds p-to-w by p-to-q.
The two nearby points give p-to-q below two epsilon, then x-to-w below three
epsilon, contradicting the exclusion at that same intrinsic endpoint. -/
private theorem edge_common_endpoint_brick_contradiction
    {N : ℕ} {h epsilon : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (e f : {e : Set Ambient // e ∈ edges N h}) (hef : e ≠ f)
    (x : Boundary) (hx : x ∈ edgeBrick epsilon e)
    (hy : x ∈ edgeBrick epsilon f)
    (w : Ambient) (hw : w ∈ edgeEndpoints N h e) (hw' : w ∈ edgeEndpoints N h f)
    (p q : Ambient) (hp : p ∈ (e : Set Ambient)) (hq : q ∈ (f : Set Ambient))
    (hxp : dist (x : Ambient) p < epsilon) (hxq : dist (x : Ambient) q < epsilon) : False := by
  -- Both memberships are retained in the interface; only the first exclusion is needed here.
  have _hy := hy
  have hgeom := (edge_common_endpoint_geometry hN hh e.property f.property
    (Subtype.coe_injective.ne hef) hw hw').2 hp hq
  have hpw : dist p w ≤ dist p q := by simpa only [dist_eq_norm] using hgeom
  have hpq := dist_triangle p (x : Ambient) q
  rw [dist_comm p (x : Ambient)] at hpq
  have hxw := dist_triangle (x : Ambient) p w
  have hexcl := ((mem_edgeBrick e x).mp hx).2 w hw
  linarith

/- Lemma 5.1(b), no common endpoint: actual points of the two edges have distance
at least the mesh. The same nearby witnesses give distance below two epsilon,
which is strictly below that mesh. -/
private theorem edge_disjoint_endpoints_brick_contradiction
    {N : ℕ} {h epsilon : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (h2 : 2 * epsilon < h)
    (e f : {e : Set Ambient // e ∈ edges N h}) (hef : e ≠ f)
    (x : Boundary) (hend : Disjoint (edgeEndpoints N h e) (edgeEndpoints N h f))
    (p q : Ambient) (hp : p ∈ (e : Set Ambient)) (hq : q ∈ (f : Set Ambient))
    (hxp : dist (x : Ambient) p < epsilon) (hxq : dist (x : Ambient) q < epsilon) : False := by
  have hgeom := edge_dist_ge_mesh_of_no_common_endpoint hN hh e.property f.property
    (Subtype.coe_injective.ne hef) hend hp hq
  have hlow : h ≤ dist p q := by simpa only [dist_eq_norm] using hgeom
  have hpq := dist_triangle p (x : Ambient) q
  rw [dist_comm p (x : Ambient)] at hpq
  linarith

/- Lemma 5.1(b): choose the two strict nearby witnesses once. Distinct edges either
have disjoint intrinsic endpoint sets or share an endpoint; each case contradicts
the corresponding distance estimate, so the actual edges coincide. -/
private theorem edge_eq_of_mem_edgeBrick
    {N : ℕ} {h epsilon : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (h2 : 2 * epsilon < h)
    (e f : {e : Set Ambient // e ∈ edges N h}) (x : Boundary)
    (he : x ∈ edgeBrick epsilon e) (hf : x ∈ edgeBrick epsilon f) : e = f := by
  by_contra hef
  obtain ⟨p, hp, hxp⟩ := edge_near_point_of_mem_brick hN hh e x he
  obtain ⟨q, hq, hxq⟩ := edge_near_point_of_mem_brick hN hh f x hf
  by_cases hend : Disjoint (edgeEndpoints N h e) (edgeEndpoints N h f)
  · exact edge_disjoint_endpoints_brick_contradiction hN hh h2 e f hef x hend
      p q hp hq hxp hxq
  · obtain ⟨w, hw, hw'⟩ := Set.not_disjoint_iff.mp hend
    exact edge_common_endpoint_brick_contradiction hN hh e f hef x he hf w hw hw'
      p q hp hq hxp hxq

/- Lemma 5.1(c): the same point lies in both intrinsic square interiors. Their
established disjointness forces equality of the actual squares. -/
private theorem square_eq_of_mem_squareBrick
    {N : ℕ} {h : ℝ} (hN : 0 < N) (hh : h = 2 / (N : ℝ))
    (s t : {s : Set Ambient // s ∈ squares N h}) (x : Boundary)
    (hs : x ∈ squareBrick s) (ht : x ∈ squareBrick t) : s = t := by
  apply Subtype.ext
  exact square_eq_of_relInterior_inter_nonempty hN hh s.property t.property
    ⟨(x : Ambient), (mem_squareBrick s x).mp hs, (mem_squareBrick t x).mp ht⟩

end TopologicalSpace.CubeBoundaryThree
