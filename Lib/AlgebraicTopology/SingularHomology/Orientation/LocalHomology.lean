/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Relative.Excision
public import Lib.AlgebraicTopology.SingularHomology.Orientation.ConvexComplement
public import Lib.AlgebraicTopology.SingularHomology.SphereHomology

/-!
# Local homology

The local homology of a space `M` at a point `x` is `H_n(M, M ∖ {x})` (Hatcher, *Algebraic
Topology*, §3.3, "local orientations"):

* `ManifoldOrientation.localHomology M x n := RelativeHomology M {x}ᶜ n`.

For a subset `K ∋ x` the inclusion of pairs `(M, M ∖ K) ⊆ (M, M ∖ {x})` gives the *local
restriction* `localRestriction hx n : H_n(M, M ∖ K) → H_n(M, M ∖ {x})`, and `K` is a
*homology ball* in degree `n` (`IsHomologyBall M n K`) when this restriction is bijective at every
point of `K`.  Closed balls, and more generally bounded convex sets, of a real normed space are
homology balls in every degree (`isHomologyBall_of_convex`, from
`Orientation/ConvexComplement.lean` and the five lemma); the transport of this property to chart
balls of a manifold is in `Orientation/HomologyBall.lean`.

For Euclidean space `E = ℝ^{m+2}` the local homology is computed: `H_{m+2}(E, E ∖ {x}) ≅ ℤ`
(`localHomologyEuclideanEquiv`) and `H_k(E, E ∖ {x}) = 0` for `k ≠ m + 2`
(`localHomologyEuclidean_subsingleton`), from the long exact sequence of the pair, the
contractibility of `E` and `E ∖ {x} ≃ S^{m+1}` (`puncturedHomotopyEquiv`).  (Dimensions `0` and
`1` are not treated here.)

## Main definitions and results

* `ManifoldOrientation.localHomology`, `ManifoldOrientation.localRestriction`,
  `ManifoldOrientation.IsHomologyBall`.
* `ManifoldOrientation.localRestriction_bijective_of_convex`, `isHomologyBall_of_convex`,
  `isHomologyBall_closedBall`.
* `ManifoldOrientation.localHomologyEuclideanEquiv`, `localHomologyEuclidean_subsingleton`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3, local orientations; the computation
  `H_i(ℝⁿ, ℝⁿ ∖ {0})` after Corollary 2.14

## Tags

local homology, orientation, manifold
-/

open Set Function Topology

@[expose] public noncomputable section

namespace ManifoldOrientation

open SingularChains SingularMayerVietoris RelativeSingularHomology

/-! ### Local homology and local restriction -/

/-- The local homology `H_n(M, M ∖ {x})` of `M` at `x`. -/
abbrev localHomology (M : Type) [TopologicalSpace M] (x : M) (n : ℕ) : Type :=
  RelativeHomology M {x}ᶜ n

variable {M : Type} [TopologicalSpace M]

omit [TopologicalSpace M] in
theorem compl_subset_compl_singleton {K : Set M} {x : M} (hx : x ∈ K) : Kᶜ ⊆ {x}ᶜ :=
  compl_subset_compl.mpr (singleton_subset_iff.mpr hx)

/-- The local restriction `H_n(M, M ∖ K) → H_n(M, M ∖ {x})` for `x ∈ K`. -/
abbrev localRestriction {K : Set M} {x : M} (hx : x ∈ K) (n : ℕ) :
    RelativeHomology M Kᶜ n →ₗ[ℤ] localHomology M x n :=
  restriction (compl_subset_compl_singleton hx) n

/-- `K` is a homology ball in degree `n` if the local restriction `H_n(M, M ∖ K) → H_n(M, M ∖ {x})`
is bijective for every `x ∈ K`. -/
def IsHomologyBall (M : Type) [TopologicalSpace M] (n : ℕ) (K : Set M) : Prop :=
  ∀ x (hx : x ∈ K), Function.Bijective (localRestriction hx n)

/-- The local restriction along `K ⊆ K'` composes. -/
theorem localRestriction_comp_restriction {K K' : Set M} (h : K ⊆ K') {x : M} (hx : x ∈ K) (n : ℕ) :
    (localRestriction hx n).comp (restriction (compl_subset_compl.mpr h) n) =
      localRestriction (h hx) n :=
  restriction_comp _ _ n

/-! ### Bounded convex sets are homology balls -/

/-- The identity induces the identity on singular homology. -/
theorem singularHomologyMap_id_bijective {X : Type} [TopologicalSpace X] (n : ℕ) :
    Function.Bijective (singularHomologyMap (ContinuousMap.id X) n) := by
  have : singularHomologyMap (ContinuousMap.id X) n = LinearMap.id := by
    change homologyLinearMap (singularChainMap (ContinuousMap.id X)) n = LinearMap.id
    rw [singularChainMap_id, homologyLinearMap, HomologicalComplex.homologyMap_id]
    rfl
  rw [this]
  exact Function.bijective_id

/-- For a bounded convex `S ∋ x` in a real normed space, the local restriction
`H_n(E, E ∖ S) → H_n(E, E ∖ {x})` is bijective. -/
theorem localRestriction_bijective_of_convex {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) (hb : Bornology.IsBounded S) {x : E} (hx : x ∈ S) (n : ℕ) :
    Function.Bijective (localRestriction hx n) := by
  have hmaps : MapsTo (ContinuousMap.id E) Sᶜ {x}ᶜ := compl_subset_compl_singleton hx
  rw [localRestriction, restriction_eq _ hmaps]
  apply relativeHomologyMap_bijective_of_bijective (ContinuousMap.id E) hmaps
    (fun k => singularHomologyMap_id_bijective k)
  intro k
  have : pairRestrict (ContinuousMap.id E) hmaps = ConvexComplement.inclusion hx := by
    ext z
    rfl
  rw [this]
  exact ConvexComplement.singularHomologyMap_inclusion_bijective hS hb hx k

/-- A bounded convex set is a homology ball in every degree. -/
theorem isHomologyBall_of_convex {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    (hS : Convex ℝ S) (hb : Bornology.IsBounded S) (n : ℕ) : IsHomologyBall E n S :=
  fun _ hx => localRestriction_bijective_of_convex hS hb hx n

/-- A closed ball is a homology ball in every degree. -/
theorem isHomologyBall_closedBall {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) (r : ℝ)
    (n : ℕ) : IsHomologyBall E n (Metric.closedBall c r) :=
  isHomologyBall_of_convex (convex_closedBall c r) Metric.isBounded_closedBall n

/-! ### The local homology of Euclidean space -/

section Euclidean

variable (m : ℕ)

/-- Euclidean space of dimension `m + 2`. -/
local notation "E" => EuclideanSpace ℝ (Fin (m + 2))

theorem one_lt_rank_euclidean : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (m + 2))) :=
  Module.one_lt_rank_of_one_lt_finrank (by rw [finrank_euclideanSpace_fin]; omega)

theorem add_mem_compl_singleton (x : E) (u : ({0}ᶜ : Set E)) : (u : E) + x ∈ ({x}ᶜ : Set E) := by
  have hu : (u : E) ≠ 0 := u.2
  simpa using hu

theorem sub_mem_compl_singleton_zero (x : E) (z : ({x}ᶜ : Set E)) : (z : E) - x ∈ ({0}ᶜ : Set E) := by
  have hz : (z : E) ≠ x := z.2
  simpa [sub_eq_zero] using hz

/-- The punctured space `E ∖ {0}` is homeomorphic to `E ∖ {x}` by translation. -/
def puncturedTranslate (x : E) : (({0}ᶜ : Set E)) ≃ₜ ({x}ᶜ : Set E) where
  toFun u := ⟨u.1 + x, add_mem_compl_singleton m x u⟩
  invFun z := ⟨z.1 - x, sub_mem_compl_singleton_zero m x z⟩
  left_inv _ := Subtype.ext (add_sub_cancel_right _ _)
  right_inv _ := Subtype.ext (sub_add_cancel _ _)
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

/-- `E ∖ {x}` is homotopy equivalent to the unit sphere `S^{m+1}`. -/
def puncturedHomotopyEquiv (x : E) :
    ContinuousMap.HomotopyEquiv (SphereHomology.UnitSphere (m + 1)) ({x}ᶜ : Set E) :=
  (ConvexComplement.sphereHomotopyEquiv (x := (0 : E)) one_pos).trans
    (puncturedTranslate m x).toHomotopyEquiv

/-- The homology of `E ∖ {x}` is the homology of `S^{m+1}`. -/
def puncturedHomologyEquiv (x : E) (k : ℕ) :
    SingularHomology (SphereHomology.UnitSphere (m + 1)) k ≃ₗ[ℤ] SingularHomology ({x}ᶜ : Set E) k :=
  SingularHomology.homotopyEquivHomologyEquiv (puncturedHomotopyEquiv m x) k

instance punctured_pathConnectedSpace (x : E) : PathConnectedSpace ({x}ᶜ : Set E) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_compl_singleton_of_one_lt_rank (one_lt_rank_euclidean m) x)

/-- Positive-degree homology of Euclidean space vanishes. -/
theorem euclidean_homology_subsingleton (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularHomology (EuclideanSpace ℝ (Fin (m + 2))) k) :=
  SingularHomology.contractible_homology_subsingleton _ k hk

/-- **The local homology of `ℝ^{m+2}` in degree `m + 2` is `ℤ`.** -/
def localHomologyEuclideanEquiv (x : E) :
    localHomology (EuclideanSpace ℝ (Fin (m + 2))) x (m + 2) ≃ₗ[ℤ] ℤ :=
  ((pairConnectingEquiv {x}ᶜ (m + 1) (euclidean_homology_subsingleton m _ (by omega))
      (euclidean_homology_subsingleton m _ (by omega))).trans
    (puncturedHomologyEquiv m x (m + 1)).symm).trans (SphereHomology.unitSphereHomologyTopEquiv m)

/-- The local homology of `ℝ^{m+2}` vanishes in every degree other than `m + 2`. -/
theorem localHomologyEuclidean_subsingleton (x : E) (k : ℕ) (hk : k ≠ m + 2) :
    Subsingleton (localHomology (EuclideanSpace ℝ (Fin (m + 2))) x k) := by
  cases k with
  | zero =>
    exact relativeHomology_zero_subsingleton {x}ᶜ
      (SphereHomology.singularHomologyMap_zero_surjective (subtypeInclusion {x}ᶜ))
  | succ k =>
    apply relativeHomology_succ_subsingleton {x}ᶜ k (euclidean_homology_subsingleton m _ (by omega))
    cases k with
    | zero => exact SphereHomology.singularHomologyMap_zero_injective (subtypeInclusion {x}ᶜ)
    | succ k =>
      have hsph := SphereHomology.unitSphere_homology_subsingleton m (k + 1) (by omega) (by omega)
      have hsub : Subsingleton (SingularHomology ({x}ᶜ : Set E) (k + 1)) :=
        (puncturedHomologyEquiv m x (k + 1)).symm.injective.subsingleton
      intro a b _
      exact Subsingleton.elim a b

end Euclidean

end ManifoldOrientation
