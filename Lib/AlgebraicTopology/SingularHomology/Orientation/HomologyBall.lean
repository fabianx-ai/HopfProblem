/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Orientation.LocalHomology

/-!
# Homology balls in a manifold

The property `IsHomologyBall X n K` (every local restriction `H_n(X, X ∖ K) → H_n(X, X ∖ {x})`,
`x ∈ K`, is bijective) is transported along maps of pairs that induce isomorphisms on the pairs
involved (`isHomologyBall_iff_of_bijective`): along excision into an open subspace
(`isHomologyBall_trace_iff`, for closed `K`) and along homeomorphisms
(`isHomologyBall_image_iff`).  Together with the convex case of `LocalHomology.lean` this gives
the chart balls of a manifold: for every point `x` of a manifold modelled on `ℝⁿ` and every
neighbourhood `U` of `x` there is a compact homology ball `K ⊆ U` with `x ∈ interior K`
(`exists_isHomologyBall`, Hatcher's "balls `B` in a chart" of §3.3).  The local homology of a
manifold point is that of the model (`localHomologyChartEquiv`), hence `ℤ` in the dimension of
the manifold (`localHomologyEquiv`, `localHomology_subsingleton`).

## Main definitions and results

* `ManifoldOrientation.restriction_comp_relativeHomologyMap` : restriction commutes with maps of
  pairs.
* `ManifoldOrientation.isHomologyBall_iff_of_bijective`, `isHomologyBall_trace_iff`,
  `isHomologyBall_image_iff`.
* `ManifoldOrientation.localHomologyOpenEquiv`, `localHomologyHomeomorphEquiv`,
  `localHomologyChartEquiv`.
* `ManifoldOrientation.exists_isHomologyBall`, `ManifoldOrientation.localHomologyEquiv`,
  `ManifoldOrientation.localHomology_subsingleton`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3, the discussion preceding
  Proposition 3.25

## Tags

local homology, homology ball, chart, manifold
-/

open Set Function Topology

@[expose] public noncomputable section

namespace ManifoldOrientation

open SingularChains SingularMayerVietoris RelativeSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Naturality of restriction -/

/-- Restriction commutes with the maps induced by a map of pairs. -/
theorem restriction_comp_relativeHomologyMap (f : C(X, Y)) {A A' : Set X} {B B' : Set Y}
    (h : A ⊆ A') (h' : B ⊆ B') (hf : MapsTo f A B) (hf' : MapsTo f A' B') (n : ℕ) :
    (restriction h' n).comp (relativeHomologyMap f hf n) =
      (relativeHomologyMap f hf' n).comp (restriction h n) := by
  have hB : MapsTo (ContinuousMap.id Y) B B' := fun _ hy => h' hy
  have hA : MapsTo (ContinuousMap.id X) A A' := fun _ hx => h hx
  have h₁ : MapsTo ((ContinuousMap.id Y).comp f) A B' := fun x hx => h' (hf hx)
  have h₂ : MapsTo (f.comp (ContinuousMap.id X)) A B' := fun x hx => hf' (h hx)
  rw [restriction_eq h' hB, restriction_eq h hA, relativeHomologyMap_comp _ _ hf hB h₁,
    relativeHomologyMap_comp _ _ hA hf' h₂]
  exact relativeHomologyMap_congr (by ext; rfl) _ _ n

/-- Bijectivity of a map of pairs is invariant under equal subsets. -/
theorem relativeHomologyMap_bijective_congr (f : C(X, Y)) {A A' : Set X} {B B' : Set Y}
    (hA : A = A') (hB : B = B') (hf : MapsTo f A B) (hf' : MapsTo f A' B') (n : ℕ) :
    Function.Bijective (relativeHomologyMap f hf n) ↔ Function.Bijective (relativeHomologyMap f hf' n) := by
  subst hA hB
  rfl

/-- In a commutative square with bijective vertical maps, the top map is bijective iff the
bottom map is. -/
theorem bijective_iff_of_comm {M₁ M₂ N₁ N₂ : Type*} [AddCommGroup M₁] [Module ℤ M₁]
    [AddCommGroup M₂] [Module ℤ M₂] [AddCommGroup N₁] [Module ℤ N₁] [AddCommGroup N₂] [Module ℤ N₂]
    (g : M₁ →ₗ[ℤ] N₁) (g' : M₂ →ₗ[ℤ] N₂) (v₁ : M₁ →ₗ[ℤ] M₂) (v₂ : N₁ →ₗ[ℤ] N₂)
    (hv₁ : Function.Bijective v₁) (hv₂ : Function.Bijective v₂) (hcomm : g'.comp v₁ = v₂.comp g) :
    Function.Bijective g ↔ Function.Bijective g' := by
  have hfun : ⇑g' ∘ ⇑v₁ = ⇑v₂ ∘ ⇑g := by
    ext x
    exact LinearMap.congr_fun hcomm x
  rw [← Function.Bijective.of_comp_iff' hv₂ g, ← hfun, Function.Bijective.of_comp_iff g' hv₁]

/-! ### Transport of homology balls -/

/-- A map of pairs `f` with `f ⁻¹' L = K`, injective, inducing isomorphisms on `(X, X ∖ K) → (Y, Y ∖ L)`
and on `(X, X ∖ {x}) → (Y, Y ∖ {f x})` for `x ∈ K`, transports the homology-ball property. -/
theorem isHomologyBall_iff_of_bijective (f : C(X, Y)) {K : Set X} {L : Set Y}
    (hKL : ∀ x, x ∈ K ↔ f x ∈ L) (hL : L ⊆ Set.range f) (n : ℕ)
    (hfK : MapsTo f Kᶜ Lᶜ) (hfx : ∀ x, MapsTo f {x}ᶜ {f x}ᶜ)
    (hK : Function.Bijective (relativeHomologyMap f hfK n))
    (hpt : ∀ x ∈ K, Function.Bijective (relativeHomologyMap f (hfx x) n)) :
    IsHomologyBall X n K ↔ IsHomologyBall Y n L := by
  constructor
  · intro hX y hy
    obtain ⟨x, rfl⟩ := hL hy
    have hx : x ∈ K := (hKL x).mpr hy
    exact (bijective_iff_of_comm _ _ _ _ hK (hpt x hx)
      (restriction_comp_relativeHomologyMap f _ _ _ _ n)).mp (hX x hx)
  · intro hY x hx
    exact (bijective_iff_of_comm _ _ _ _ hK (hpt x hx)
      (restriction_comp_relativeHomologyMap f _ _ _ _ n)).mpr (hY (f x) ((hKL x).mp hx))

omit [TopologicalSpace X] in
/-- The trace of the complement of a point of `V` is the complement of the point in `V`. -/
theorem trace_compl_singleton {V : Set X} (x : V) : trace {(x : X)}ᶜ V = {x}ᶜ := by
  ext v
  simp [trace, Subtype.ext_iff]

omit [TopologicalSpace X] in
/-- `Kᶜ ∪ V = univ` for `K ⊆ V`. -/
theorem compl_union_eq_univ_of_subset {K V : Set X} (hKV : K ⊆ V) : Kᶜ ∪ V = Set.univ := by
  ext x
  simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
  by_cases hx : x ∈ K
  · exact Or.inr (hKV hx)
  · exact Or.inl hx

/-- The inclusion of an open subspace `V` induces isomorphisms on the local homology at points
of `V`, for a `T₁` space. -/
theorem mapsTo_subtypeInclusion_compl_singleton {V : Set X} (x : V) :
    MapsTo (subtypeInclusion V) {x}ᶜ {(x : X)}ᶜ :=
  fun _ hy h => hy (Subtype.val_injective h)

theorem mapsTo_subtypeInclusion_compl {V K : Set X} :
    MapsTo (subtypeInclusion V) (trace K V)ᶜ Kᶜ :=
  fun _ hy h => hy h

theorem localHomology_subtypeInclusion_bijective [T1Space X] {V : Set X} (hV : IsOpen V) (x : V) (n : ℕ) :
    Function.Bijective (relativeHomologyMap (subtypeInclusion V)
      (mapsTo_subtypeInclusion_compl_singleton x) n) := by
  rw [relativeHomologyMap_bijective_congr _ (trace_compl_singleton x).symm rfl _
    (mapsTo_subtypeInclusion_trace {(x : X)}ᶜ V)]
  exact excision_bijective {(x : X)}ᶜ V isOpen_compl_singleton hV
    (compl_union_eq_univ_of_subset (singleton_subset_iff.mpr x.2)) n

/-- The local homology of an open subspace at a point is the local homology of the space. -/
def localHomologyOpenEquiv [T1Space X] {V : Set X} (hV : IsOpen V) (x : V) (n : ℕ) :
    localHomology V x n ≃ₗ[ℤ] localHomology X x n :=
  LinearEquiv.ofBijective _ (localHomology_subtypeInclusion_bijective hV x n)

/-- A closed set `K` in an open `V` is a homology ball in `X` iff its trace is one in `V`
(excision). -/
theorem isHomologyBall_trace_iff [T1Space X] {V K : Set X} (hV : IsOpen V) (hKc : IsOpen Kᶜ)
    (hKV : K ⊆ V) (n : ℕ) : IsHomologyBall V n (trace K V) ↔ IsHomologyBall X n K := by
  refine isHomologyBall_iff_of_bijective (K := trace K V) (L := K) (subtypeInclusion V)
    (fun _ => Iff.rfl) (fun y hy => ⟨⟨y, hKV hy⟩, rfl⟩) n mapsTo_subtypeInclusion_compl
    mapsTo_subtypeInclusion_compl_singleton ?_ ?_
  · rw [relativeHomologyMap_bijective_congr _ (show (trace K V)ᶜ = trace Kᶜ V from rfl) rfl _
      (mapsTo_subtypeInclusion_trace Kᶜ V)]
    exact excision_bijective Kᶜ V hKc hV (compl_union_eq_univ_of_subset hKV) n
  · intro x _
    exact localHomology_subtypeInclusion_bijective hV x n

theorem homeomorph_mem_compl_image_iff (e : X ≃ₜ Y) (K : Set X) (x : X) :
    x ∈ Kᶜ ↔ e x ∈ (e '' K)ᶜ := by
  rw [mem_compl_iff, mem_compl_iff, e.injective.mem_set_image]

theorem homeomorph_mem_compl_singleton_iff (e : X ≃ₜ Y) (x y : X) :
    y ∈ ({x}ᶜ : Set X) ↔ e y ∈ ({e x}ᶜ : Set Y) := by
  rw [mem_compl_iff, mem_compl_iff, mem_singleton_iff, mem_singleton_iff, e.injective.eq_iff]

/-- A homeomorphism transports homology balls. -/
theorem isHomologyBall_image_iff (e : X ≃ₜ Y) (K : Set X) (n : ℕ) :
    IsHomologyBall X n K ↔ IsHomologyBall Y n (e '' K) :=
  isHomologyBall_iff_of_bijective (e : C(X, Y)) (fun _ => (e.injective.mem_set_image).symm)
    (fun y _ => ⟨e.symm y, e.apply_symm_apply y⟩) n
    (fun x hx => (homeomorph_mem_compl_image_iff e K x).mp hx)
    (fun x y hy => (homeomorph_mem_compl_singleton_iff e x y).mp hy)
    (relativeHomologyMap_bijective_of_homeomorph e (homeomorph_mem_compl_image_iff e K) n)
    (fun x _ => relativeHomologyMap_bijective_of_homeomorph e (homeomorph_mem_compl_singleton_iff e x) n)

/-- The local homology is invariant under homeomorphisms. -/
def localHomologyHomeomorphEquiv (e : X ≃ₜ Y) (x : X) (n : ℕ) :
    localHomology X x n ≃ₗ[ℤ] localHomology Y (e x) n :=
  relativeHomologyEquivOfHomeomorph e (homeomorph_mem_compl_singleton_iff e x) n

/-! ### Chart balls of a manifold -/

section Manifold

variable {M : Type} [TopologicalSpace M]

/-- The local homology at a point of a manifold is the local homology of the model space at the
chart image of the point. -/
def localHomologyChartEquiv {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (x : M) (k : ℕ) :
    localHomology M x k ≃ₗ[ℤ] localHomology (EuclideanSpace ℝ (Fin n))
      (chartAt (EuclideanSpace ℝ (Fin n)) x x) k :=
  (localHomologyOpenEquiv (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
      ⟨x, mem_chart_source _ x⟩ k).symm.trans
    ((localHomologyHomeomorphEquiv (chartAt (EuclideanSpace ℝ (Fin n)) x).toHomeomorphSourceTarget
        ⟨x, mem_chart_source _ x⟩ k).trans
      (localHomologyOpenEquiv (chartAt (EuclideanSpace ℝ (Fin n)) x).open_target
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).toHomeomorphSourceTarget
          ⟨x, mem_chart_source _ x⟩) k))

/-- The image of the trace of `D ⊆ e.target` under the inverse chart homeomorphism is the trace of
`e.symm '' D` on the source. -/
theorem symm_image_trace {n : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : D ⊆ e.target) :
    e.toHomeomorphSourceTarget.symm '' trace D e.target = trace (e.symm '' D) e.source := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨d, hd, hdv⟩
    refine ⟨⟨d, hD hd⟩, hd, ?_⟩
    apply Subtype.ext
    exact hdv

/-- **Chart balls.** Every neighbourhood of a point `x` of a manifold modelled on `ℝⁿ` contains a
compact homology ball `K` (in every degree) with `x` in its interior: the preimage under a chart
of a small closed ball. -/
theorem exists_isHomologyBall {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (x : M) {U : Set M} (hU : U ∈ 𝓝 x) (k : ℕ) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ x ∈ interior K ∧ IsHomologyBall M k K := by
  set e := chartAt (EuclideanSpace ℝ (Fin n)) x with he
  have hx : x ∈ e.source := mem_chart_source _ x
  have hV : IsOpen (e.source ∩ interior U) := e.open_source.inter isOpen_interior
  have hxV : x ∈ e.source ∩ interior U := ⟨hx, mem_interior_iff_mem_nhds.mpr hU⟩
  have himg : IsOpen (e '' (e.source ∩ interior U)) :=
    e.isOpen_image_of_subset_source hV inter_subset_left
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp himg (e x) ⟨x, hxV, rfl⟩
  set D := Metric.closedBall (e x) (r / 2) with hDdef
  have hDball : D ⊆ Metric.ball (e x) r := Metric.closedBall_subset_ball (by linarith)
  have hDimg : D ⊆ e '' (e.source ∩ interior U) := hDball.trans hball
  have hDt : D ⊆ e.target := fun d hd => by
    obtain ⟨y, hy, rfl⟩ := hDimg hd
    exact e.map_source hy.1
  have hDcompact : IsCompact D := isCompact_closedBall _ _
  have hK : IsCompact (e.symm '' D) := hDcompact.image_of_continuousOn (e.continuousOn_symm.mono hDt)
  have hKsource : e.symm '' D ⊆ e.source ∩ interior U := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hDimg hd
    rw [e.left_inv hy.1]
    exact hy
  refine ⟨e.symm '' D, hK, hKsource.trans (inter_subset_right.trans interior_subset), ?_, ?_⟩
  · -- `e.symm '' ball (e x) (r/2)` is an open neighbourhood of `x` inside `e.symm '' D`.
    have hopen : IsOpen (e.symm '' Metric.ball (e x) (r / 2)) :=
      e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
        (by rw [e.symm_source]; exact (Metric.ball_subset_closedBall.trans hDt))
    apply interior_mono (image_mono Metric.ball_subset_closedBall)
    rw [hopen.interior_eq]
    exact ⟨e x, Metric.mem_ball_self (by linarith), e.left_inv hx⟩
  · have h₁ : IsHomologyBall (EuclideanSpace ℝ (Fin n)) k D := isHomologyBall_closedBall _ _ k
    have h₂ : IsHomologyBall e.target k (trace D e.target) :=
      (isHomologyBall_trace_iff e.open_target (Metric.isClosed_closedBall).isOpen_compl hDt k).mpr h₁
    have h₃ : IsHomologyBall e.source k (trace (e.symm '' D) e.source) := by
      rw [← symm_image_trace e hDt]
      exact (isHomologyBall_image_iff e.toHomeomorphSourceTarget.symm _ k).mp h₂
    exact (isHomologyBall_trace_iff e.open_source hK.isClosed.isOpen_compl
      (hKsource.trans inter_subset_left) k).mp h₃

/-- **The local homology of an `n`-manifold is `ℤ` in degree `n`** (for `n ≥ 2`). -/
theorem localHomology_equiv_int {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (hn : 2 ≤ n) (x : M) :
    Nonempty (localHomology M x n ≃ₗ[ℤ] ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact ⟨(localHomologyChartEquiv x (m + 2)).trans (localHomologyEuclideanEquiv m _)⟩

/-- The local homology of an `n`-manifold vanishes in degrees other than `n` (for `n ≥ 2`). -/
theorem localHomology_subsingleton {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (hn : 2 ≤ n) (x : M) (k : ℕ) (hk : k ≠ n) :
    Subsingleton (localHomology M x k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have := localHomologyEuclidean_subsingleton m (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x x) k hk
  exact (localHomologyChartEquiv (n := m + 2) x k).injective.subsingleton

end Manifold

end ManifoldOrientation
