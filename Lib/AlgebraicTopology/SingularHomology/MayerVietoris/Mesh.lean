/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.AffineSimplex
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Support

/-!
# The mesh of barycentric subdivision and the Lebesgue number

In a real normed space, the barycenter `vertexBarycenter v` of vertices `v : Fin (n + 1) → E`
of pairwise distance at most `D` is within `n/(n+1) · D` of every point of their convex hull
(`dist_vertexBarycenter_convexHull_le`), and the convex hull has diameter at most `D`
(`dist_convexHull_range_le`).  Hence, for centers that are barycenters in coordinates, one
barycentric subdivision multiplies the mesh of a formal chain by `meshFactor n = n/(n+1) < 1`
(`formalSubdivision_mesh`) and the `k`-fold subdivision by `meshFactor n ^ k`
(`formalSubdivision_iterate_mesh`), which tends to `0` (`meshFactor_pow_tendsto`); on the
standard simplex the mesh after `k` subdivisions is at most `meshFactor n ^ k`
(`simplex_formalSubdivision_iterate_mesh`).

The Lebesgue number lemma for a two-set open cover of the image of a compact metric space
(`exists_lebesgue_number_two`) then shows that a finite family of singular simplices becomes
small — every simplex of the subdivision lies in `U` or in `V` — after finitely many
subdivisions (`finite_family_formalSubdivision_eventually_small`).  This is the mesh estimate
`diam ≤ n/(n+1) · diam` of step (1) and the iteration of step (4) in the proof of Hatcher,
*Algebraic Topology*, Proposition 2.21.
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-! ### Mesh estimates -/

/-- The barycenter of a vertex list. -/
def SingularMayerVietoris.vertexBarycenter {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) : E :=
  (1 / ((n : ℝ) + 1)) • ∑ i, v i

/-- The barycenter lies in the convex hull. -/
theorem SingularMayerVietoris.vertexBarycenter_mem_of_convex {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) {s : Set E}
    (hs : Convex ℝ s) (hv : ∀ i, v i ∈ s) : vertexBarycenter v ∈ s := by
  simpa [vertexBarycenter, Finset.centerMass, Nat.cast_add, Nat.cast_one, one_div] using
    hs.centerMass_mem (t := Finset.univ) (w := fun _ : Fin (n + 1) => (1 : ℝ)) (z := v)
      (by intro i hi; exact zero_le_one)
      (by simpa using (Nat.cast_pos.mpr (Nat.succ_pos n) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)))
      (by intro i hi; exact hv i)

/-- The barycenter minus a vertex. -/
theorem SingularMayerVietoris.vertexBarycenter_sub {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) (x : E) :
    vertexBarycenter v - x = (1 / ((n : ℝ) + 1)) • ∑ i, (v i - x) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [vertexBarycenter, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_sub]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hn]

/-- The summed norms of vertex differences bound the diameter. -/
theorem SingularMayerVietoris.sum_norm_vertex_sub_le {E : Type*} [SeminormedAddCommGroup E]
    {n : ℕ} (v : Fin (n + 1) → E) {D : ℝ} (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D)
    (j : Fin (n + 1)) : (∑ i, ‖v i - v j‖) ≤ (n : ℝ) * D := by
  calc
    (∑ i, ‖v i - v j‖) = ∑ i ∈ Finset.univ.erase j, ‖v i - v j‖ := by
      simpa only [sub_self, norm_zero, add_zero] using
        (Finset.sum_erase_add Finset.univ (fun i => ‖v i - v j‖) (Finset.mem_univ j)).symm
    _ ≤ ∑ _i ∈ Finset.univ.erase j, D := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa only [dist_eq_norm] using hpair i j
    _ = (n : ℝ) * D := by simp

/-- The barycenter-to-vertex distance bound. -/
theorem SingularMayerVietoris.dist_vertexBarycenter_vertex_le {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D) (j : Fin (n + 1)) :
    Dist.dist (vertexBarycenter v) (v j) ≤ (n : ℝ) / ((n : ℝ) + 1) * D := by
  have hc : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  rw [dist_eq_norm, vertexBarycenter_sub, norm_smul, Real.norm_of_nonneg hc]
  calc
    _ ≤ (1 / ((n : ℝ) + 1)) * ∑ i, ‖v i - v j‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hc
    _ ≤ (1 / ((n : ℝ) + 1)) * ((n : ℝ) * D) :=
      (mul_le_mul_of_nonneg_left (sum_norm_vertex_sub_le v hpair j) hc)
    _ = (n : ℝ) / ((n : ℝ) + 1) * D := by ring

/-- The barycenter-to-hull distance bound. -/
theorem SingularMayerVietoris.dist_vertexBarycenter_convexHull_le {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D) {x : E} (hx : x ∈ convexHull ℝ (Set.range v)) :
    Dist.dist (vertexBarycenter v) x ≤ (n : ℝ) / ((n : ℝ) + 1) * D := by
  have hball :
    Set.range v ⊆ Metric.closedBall (vertexBarycenter v) ((n : ℝ) / ((n : ℝ) + 1) * D) := by
    rintro _ ⟨j, rfl⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact dist_vertexBarycenter_vertex_le v hpair j
  have h := convexHull_min hball (convex_closedBall _ _) hx
  simpa only [Metric.mem_closedBall, dist_comm] using h

/-- The convex-hull diameter bound. -/
theorem SingularMayerVietoris.dist_convexHull_range_le {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D) {x y : E} (hx : x ∈ convexHull ℝ (Set.range v))
    (hy : y ∈ convexHull ℝ (Set.range v)) : Dist.dist x y ≤ D := by
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, h⟩ := convexHull_exists_dist_ge2 hx hy
  exact h.trans (hpair i j)

/-- A pairwise Lebesgue number for two open covers. -/
theorem SingularMayerVietoris.exists_lebesgue_number_two_pairwise {K X : Type*}
    [PseudoMetricSpace K] [CompactSpace K] [TopologicalSpace X] (σ : C(K, X)) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : Set.range σ ⊆ U ∪ V) :
    ∃ δ > 0, ∀ s : Set K, (∀ x ∈ s, ∀ y ∈ s, Dist.dist x y ≤ δ) → σ '' s ⊆ U ∨ σ '' s ⊆ V := by
  let W : Bool → Set K := fun b => if b then σ ⁻¹' U else σ ⁻¹' V
  have hW : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact hV.preimage σ.continuous
    · exact hU.preimage σ.continuous
  have hWcover : (Set.univ : Set K) ⊆ ⋃ b, W b := by
    intro x _
    rcases hcover ⟨x, rfl⟩ with hx | hx
    · exact Set.mem_iUnion.mpr ⟨Bool.true, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
  obtain ⟨ε, hε, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hW hWcover
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro s hdist
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    obtain ⟨b, hb⟩ := hball x (Set.mem_univ x)
    have hsub : s ⊆ Metric.ball x ε := by
      intro y hy
      exact (hdist y hy x hx).trans_lt (half_lt_self hε)
    cases b
    · right
      rintro _ ⟨y, hy, rfl⟩
      exact hb (hsub hy)
    · left
      rintro _ ⟨y, hy, rfl⟩
      exact hb (hsub hy)
  · left
    rw [Set.not_nonempty_iff_eq_empty.mp hs, Set.image_empty]
    exact Set.empty_subset _

/-- A Lebesgue number for a two-element open cover. -/
theorem SingularMayerVietoris.exists_lebesgue_number_two {K X : Type*} [PseudoMetricSpace K]
    [CompactSpace K] [TopologicalSpace X] (σ : C(K, X)) {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) (hcover : Set.range σ ⊆ U ∪ V) :
    ∃ δ > 0, ∀ s : Set K, Metric.diam s ≤ δ → σ '' s ⊆ U ∨ σ '' s ⊆ V := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_lebesgue_number_two_pairwise σ hU hV hcover
  refine ⟨δ, hδ, fun s hs => hsmall s ?_⟩
  intro x hx y hy
  exact (Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace hx hy).trans hs

/-- The subdivision mesh factor `n/(n+1)`. -/
def SingularMayerVietoris.meshFactor (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) + 1)

/-- The mesh factor is nonnegative. -/
theorem SingularMayerVietoris.meshFactor_nonneg (n : ℕ) : 0 ≤ meshFactor n := by
  exact div_nonneg (Nat.cast_nonneg n) (by positivity)

/-- The mesh factor is less than one. -/
theorem SingularMayerVietoris.meshFactor_lt_one (n : ℕ) : meshFactor n < 1 := by
  apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  linarith

/-- The mesh factor is monotone in the degree. -/
theorem SingularMayerVietoris.meshFactor_mono : Monotone meshFactor := by
  intro n m hnm
  dsimp [meshFactor]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  nlinarith

/-- Mesh factor powers tend to zero. -/
theorem SingularMayerVietoris.meshFactor_pow_tendsto (n : ℕ) :
    Filter.Tendsto (fun k : ℕ => meshFactor n ^ k) Filter.atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (meshFactor_nonneg n) (meshFactor_lt_one n)

/-- Scaled mesh powers tend to zero. -/
theorem SingularMayerVietoris.meshFactor_pow_mul_tendsto (n : ℕ) (D : ℝ) :
    Filter.Tendsto (fun k : ℕ => meshFactor n ^ k * D) Filter.atTop (𝓝 0) := by
  simpa only [MulZeroClass.zero_mul] using (meshFactor_pow_tendsto n).mul_const D

/-- Scaled mesh powers are eventually small. -/
theorem SingularMayerVietoris.eventually_meshFactor_pow_mul_lt (n : ℕ) (D : ℝ) {δ : ℝ}
    (hδ : 0 < δ) : ∃ N : ℕ, ∀ k ≥ N, meshFactor n ^ k * D < δ := by
  apply Filter.eventually_atTop.mp
  exact (meshFactor_pow_mul_tendsto n D).eventually (eventually_lt_nhds hδ)

/-- A Lebesgue number for the preimage cover of the simplex. -/
theorem SingularMayerVietoris.simplex_lebesgue_number_two {X : Type*} [TopologicalSpace X]
    {U V : Set X} {n : ℕ} (σ : C(SingularChains.Simplex n, X)) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : Set.range σ ⊆ U ∪ V) :
    ∃ δ > 0, ∀ s : Set (SingularChains.Simplex n), Metric.diam s ≤ δ → σ '' s ⊆ U ∨ σ '' s ⊆ V :=
  exists_lebesgue_number_two σ hU hV hcover

/-- Simplices below the Lebesgue number are small. -/
theorem SingularMayerVietoris.simplex_lebesgue_number_subsimplices {X : Type*}
    [TopologicalSpace X] {U V : Set X} {n : ℕ} (σ : C(SingularChains.Simplex n, X)) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : Set.range σ ⊆ U ∪ V) :
    ∃ δ > 0,
      ∀ (m : ℕ) (f : C(SingularChains.Simplex m, SingularChains.Simplex n)),
        Metric.diam (Set.range f) ≤ δ → Set.range (σ.comp f) ⊆ U ∨ Set.range (σ.comp f) ⊆ V := by
  obtain ⟨δ, hδ, hsmall⟩ := simplex_lebesgue_number_two σ hU hV hcover
  refine ⟨δ, hδ, ?_⟩
  intro m f hf
  simpa only [ContinuousMap.coe_comp, Set.range_comp] using hsmall (Set.range f) hf

/-- Iterated subdivision eventually makes a simplex small. -/
theorem SingularMayerVietoris.simplex_eventually_small_of_diameter {X : Type*}
    [TopologicalSpace X] {U V : Set X} {n : ℕ} (σ : C(SingularChains.Simplex n, X)) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : Set.range σ ⊆ U ∪ V) (D : ℝ) :
    ∃ N : ℕ,
      ∀ k ≥ N,
        ∀ (m : ℕ) (f : C(SingularChains.Simplex m, SingularChains.Simplex n)),
          Metric.diam (Set.range f) ≤ meshFactor n ^ k * D →
            Set.range (σ.comp f) ⊆ U ∨ Set.range (σ.comp f) ⊆ V := by
  obtain ⟨δ, hδ, hsmall⟩ := simplex_lebesgue_number_subsimplices σ hU hV hcover
  obtain ⟨N, hN⟩ := eventually_meshFactor_pow_mul_lt n D hδ
  refine ⟨N, ?_⟩
  intro k hk m f hf
  exact hsmall m f (hf.trans (hN k hk).le)

/-- A finite family of simplices is eventually simultaneously small. -/
theorem SingularMayerVietoris.finite_family_eventually_small_of_diameter {X : Type*}
    [TopologicalSpace X] {U V : Set X} {n : ℕ} (s : Finset C(SingularChains.Simplex n, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : ∀ σ ∈ s, Set.range σ ⊆ U ∪ V) (D : ℝ) :
    ∃ N : ℕ,
      ∀ k ≥ N,
        ∀ σ ∈ s,
          ∀ (m : ℕ) (f : C(SingularChains.Simplex m, SingularChains.Simplex n)),
            Metric.diam (Set.range f) ≤ meshFactor n ^ k * D →
              Set.range (σ.comp f) ⊆ U ∨ Set.range (σ.comp f) ⊆ V := by
  classical
    induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ _ _ hσ => False.elim (Finset.notMem_empty _ hσ)⟩
  | @insert σ s hσ
    ih =>
    obtain ⟨Nσ, hNσ⟩ :=
      simplex_eventually_small_of_diameter σ hU hV (hcover σ (Finset.mem_insert_self σ s)) D
    obtain ⟨Ns, hNs⟩ := ih (fun τ hτ => hcover τ (Finset.mem_insert_of_mem hτ))
    refine ⟨Max.max Nσ Ns, ?_⟩
    intro k hk τ hτ m f hf
    rcases Finset.mem_insert.mp hτ with rfl | hτ
    · exact hNσ k ((le_max_left _ _).trans hk) m f hf
    · exact hNs k ((le_max_right _ _).trans hk) τ hτ m f hf

/-- The simplex barycenter is the vertex barycenter. -/
theorem SingularMayerVietoris.simplexBarycenter_eq_vertexBarycenter {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) :
    (simplexBarycenter v : Fin (p + 1) → ℝ) =
      vertexBarycenter (fun i => (v i : Fin (p + 1) → ℝ)) := by
  rw [simplexBarycenter_coe]
  simp only [vertexBarycenter, Nat.cast_add, Nat.cast_one, one_div]

/-- Points of an affine simplex are within the vertex diameter. -/
theorem SingularMayerVietoris.dist_affineSimplex_le {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) {D : ℝ} (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D)
    (t u : SingularChains.Simplex n) : Dist.dist (affineSimplex v t) (affineSimplex v u) ≤ D :=
  dist_convexHull_range_le (fun i => (v i : Fin (p + 1) → ℝ)) hpair
    (affineSimplex_mem_convexHull v t) (affineSimplex_mem_convexHull v u)

/-- The affine simplex's diameter is bounded by the vertex diameter. -/
theorem SingularMayerVietoris.affineSimplex_diam_le {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) {D : ℝ}
    (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D) : Metric.diam (Set.range (affineSimplex v)) ≤ D := by
  apply Metric.diam_le_of_forall_dist_le_of_nonempty (Set.range_nonempty (affineSimplex v))
  rintro _ ⟨t, rfl⟩ _ ⟨u, rfl⟩
  exact dist_affineSimplex_le v hpair t u

/-- Vertex-bounded families become small under iteration. -/
theorem SingularMayerVietoris.finite_family_eventually_small_of_vertices {p : ℕ} {X : Type*}
    [TopologicalSpace X] {U V : Set X} (s : Finset C(SingularChains.Simplex p, X)) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : ∀ σ ∈ s, Set.range σ ⊆ U ∪ V) (D : ℝ) :
    ∃ N : ℕ,
      ∀ k ≥ N,
        ∀ σ ∈ s,
          ∀ (m : ℕ) (v : Fin (m + 1) → SingularChains.Simplex p),
            (∀ i j, Dist.dist (v i) (v j) ≤ meshFactor p ^ k * D) →
              Set.range (σ.comp (affineSimplex v)) ⊆ U ∨
                Set.range (σ.comp (affineSimplex v)) ⊆ V := by
  obtain ⟨N, hN⟩ := finite_family_eventually_small_of_diameter s hU hV hcover D
  refine ⟨N, ?_⟩
  intro k hk σ hσ m v hv
  exact hN k hk σ hσ m (affineSimplex v) (affineSimplex_diam_le v hv)

/-- The formal center lies in the convex hull. -/
theorem SingularMayerVietoris.formalCenter_mem_of_convex {V E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (center : FormalCenter V) (coords : V → E)
    (hcenter : ∀ n (v : Fin (n + 1) → V), coords (center n v) = vertexBarycenter (coords ∘ v))
    {S : Set E} (hS : Convex ℝ S) (n : ℕ) (v : Fin (n + 1) → V) (hv : ∀ i, coords (v i) ∈ S) :
    coords (center n v) ∈ S := by
  rw [hcenter]
  exact vertexBarycenter_mem_of_convex (coords ∘ v) hS hv

/-- Subdivision vertices stay in the convex hull. -/
theorem SingularMayerVietoris.formalSubdivision_simplex_vertices_mem_convexHull {V E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (center : FormalCenter V) (coords : V → E)
    (hcenter : ∀ n (v : Fin (n + 1) → V), coords (center n v) = vertexBarycenter (coords ∘ v))
    {n : ℕ} (v : Fin n → V) {w : Fin n → V}
    (hw : w ∈ (formalSubdivision center n (formalSimplex v)).support) (i : Fin n) :
    coords (w i) ∈ convexHull ℝ (Set.range (coords ∘ v)) := by
  let S : Set V := coords ⁻¹' convexHull ℝ (Set.range (coords ∘ v))
  have hv : formalSimplex v ∈ formalChainsSupported S n := by
    apply formalSimplex_mem_supported
    intro j
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  have hS : ∀ k (u : Fin (k + 1) → V), (∀ j, u j ∈ S) → center k u ∈ S := by
    intro k u hu
    exact formalCenter_mem_of_convex center coords hcenter (convex_convexHull ℝ _) k u hu
  have hsub := formalSubdivision_mem_supported center hS n hv
  exact (mem_formalChainsSupported_iff.mp hsub) w hw i

/-- One subdivision scales the mesh by the factor. -/
theorem SingularMayerVietoris.formalSubdivision_simplex_mesh {V E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (center : FormalCenter V) (coords : V → E)
    (hcenter : ∀ n (v : Fin (n + 1) → V), coords (center n v) = vertexBarycenter (coords ∘ v))
    (n : ℕ) :
    ∀ (v : Fin (n + 1) → V) {D : ℝ},
      (∀ i j, Dist.dist (coords (v i)) (coords (v j)) ≤ D) →
        ∀ {w : Fin (n + 1) → V},
          w ∈ (formalSubdivision center (n + 1) (formalSimplex v)).support →
            ∀ i j, Dist.dist (coords (w i)) (coords (w j)) ≤ meshFactor n * D := by
  induction n with
  | zero =>
    intro v D hpair w hw i j
    let : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [meshFactor]
  | succ n ih =>
    intro v D hpair w hw
    have hD : 0 ≤ D := by simpa only [dist_self] using hpair 0 0
    have hHull := formalSubdivision_simplex_vertices_mem_convexHull center coords hcenter v hw
    rw [formalSubdivision_simplex_succ] at hw
    obtain ⟨u, hu, rfl⟩ := formalCone_support_exists (center (n + 1) v) hw
    obtain ⟨face, hface, hu⟩ :=
      formalLinearMap_support_exists (formalSubdivision center (n + 1)) hu
    obtain ⟨r, rfl⟩ := formalBoundary_support_exists (n + 1) v hface
    have huMesh := ih (v ∘ r.succAbove) (fun i j => hpair (r.succAbove i) (r.succAbove j)) hu
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.cons_zero, dist_self] using mul_nonneg (meshFactor_nonneg (n + 1)) hD
      · change Dist.dist (coords (center (n + 1) v)) (coords (u j)) ≤ meshFactor (n + 1) * D
        rw [hcenter]
        exact dist_vertexBarycenter_convexHull_le (coords ∘ v) hpair (hHull j.succ)
    · refine Fin.cases ?_ (fun j => ?_) j
      · change Dist.dist (coords (u i)) (coords (center (n + 1) v)) ≤ meshFactor (n + 1) * D
        rw [dist_comm, hcenter]
        exact dist_vertexBarycenter_convexHull_le (coords ∘ v) hpair (hHull i.succ)
      · change Dist.dist (coords (u i)) (coords (u j)) ≤ meshFactor (n + 1) * D
        exact (huMesh i j).trans (mul_le_mul_of_nonneg_right (meshFactor_mono (Nat.le_succ n)) hD)

/-- Subdivision scales a chain's mesh by the factor. -/
theorem SingularMayerVietoris.formalSubdivision_mesh {V E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (center : FormalCenter V) (coords : V → E)
    (hcenter : ∀ n (v : Fin (n + 1) → V), coords (center n v) = vertexBarycenter (coords ∘ v))
    (n : ℕ) (c : FormalChains V (n + 1)) {D : ℝ}
    (hc : ∀ v ∈ c.support, ∀ i j, Dist.dist (coords (v i)) (coords (v j)) ≤ D) :
    ∀ w ∈ (formalSubdivision center (n + 1) c).support,
      ∀ i j, Dist.dist (coords (w i)) (coords (w j)) ≤ meshFactor n * D := by
  intro w hw
  obtain ⟨v, hv, hw⟩ := formalLinearMap_support_exists (formalSubdivision center (n + 1)) hw
  exact formalSubdivision_simplex_mesh center coords hcenter n v (hc v hv) hw

/-- Iterated subdivision scales the mesh by the power. -/
theorem SingularMayerVietoris.formalSubdivision_iterate_mesh {V E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (center : FormalCenter V) (coords : V → E)
    (hcenter : ∀ n (v : Fin (n + 1) → V), coords (center n v) = vertexBarycenter (coords ∘ v))
    (n k : ℕ) (c : FormalChains V (n + 1)) {D : ℝ}
    (hc : ∀ v ∈ c.support, ∀ i j, Dist.dist (coords (v i)) (coords (v j)) ≤ D) :
    ∀ w ∈ ((formalSubdivision center (n + 1))^[k] c).support,
      ∀ i j, Dist.dist (coords (w i)) (coords (w j)) ≤ meshFactor n ^ k * D := by
  induction k with
  | zero => simpa only [Function.iterate_zero_apply, pow_zero, one_mul] using hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    intro w hw i j
    have h :=
      formalSubdivision_mesh center coords hcenter n ((formalSubdivision center (n + 1))^[k] c) ih
        w hw i j
    simpa only [pow_succ, mul_assoc, mul_left_comm] using h

/-- Points of the standard simplex are within distance one. -/
theorem SingularMayerVietoris.simplex_dist_le_one {p : ℕ} (x y : SingularChains.Simplex p) :
    Dist.dist x y ≤ 1 :=
  (Metric.dist_le_diam_of_mem (bounded_stdSimplex (Fin (p + 1))) x.property y.property).trans
    diam_stdSimplex_le

/-- Iterated subdivision makes the standard simplex's mesh small. -/
theorem SingularMayerVietoris.simplex_formalSubdivision_iterate_mesh {p n : ℕ} (k : ℕ)
    (c : FormalChains (SingularChains.Simplex p) (n + 1)) :
    ∀ w ∈ ((formalSubdivision (fun _ v => simplexBarycenter v) (n + 1))^[k] c).support,
      ∀ i j, Dist.dist (w i) (w j) ≤ meshFactor n ^ k := by
  have h :=
    formalSubdivision_iterate_mesh
      (fun n (v : Fin (n + 1) → SingularChains.Simplex p) => simplexBarycenter v)
      (fun x : SingularChains.Simplex p => (x : Fin (p + 1) → ℝ))
      (fun _ v => simplexBarycenter_eq_vertexBarycenter v) n k c (D := 1)
      (fun v _ i j => simplex_dist_le_one (v i) (v j))
  intro w hw i j
  change Dist.dist (w i : Fin (p + 1) → ℝ) (w j : Fin (p + 1) → ℝ) ≤ meshFactor n ^ k
  simpa only [mul_one] using h w hw i j

/-- A finite family is eventually small under iterated subdivision. -/
theorem SingularMayerVietoris.finite_family_formalSubdivision_eventually_small {p : ℕ} {X : Type*}
    [TopologicalSpace X] {U V : Set X} (s : Finset C(SingularChains.Simplex p, X)) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : ∀ σ ∈ s, Set.range σ ⊆ U ∪ V) :
    ∃ N : ℕ,
      ∀ k ≥ N,
        ∀ σ ∈ s,
          ∀ c : FormalChains (SingularChains.Simplex p) (p + 1),
            ∀ w ∈ ((formalSubdivision (fun _ v => simplexBarycenter v) (p + 1))^[k] c).support,
              Set.range (σ.comp (affineSimplex w)) ⊆ U ∨
                Set.range (σ.comp (affineSimplex w)) ⊆ V := by
  obtain ⟨N, hN⟩ := finite_family_eventually_small_of_vertices s hU hV hcover 1
  refine ⟨N, ?_⟩
  intro k hk σ hσ c w hw
  apply hN k hk σ hσ p w
  simpa only [mul_one] using simplex_formalSubdivision_iterate_mesh k c w hw
