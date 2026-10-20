/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Orientation.ChartConvex
public import Lib.AlgebraicTopology.SingularHomology.Relative.Support

/-!
# The fundamental class of a closed oriented manifold

**Hatcher's Lemma 3.27** for a `T₂` manifold `M` modelled on `ℝⁿ` (`n ≥ 2`): for every compact
`A ⊆ M`, `H_i(M, M ∖ A) = 0` for `i > n`, a class in `H_n(M, M ∖ A)` vanishing at every point of
`A` is zero, and every locally consistent family of local classes is realized on `A` by a class
in `H_n(M, M ∖ A)` (`LocalToGlobal.of_isCompact`).  The proof follows Hatcher's steps (3) and (4)
in the form of the accepted textbook (P17, P18):

3. for a compact `A` inside a chart-convex set `D` (`LocalToGlobal.of_isCompact_subset`): a class
   `α ∈ H_i(M, M ∖ A)` is represented by a chain `c` whose boundary has compact support `C`
   disjoint from `A`; `A` is covered by finitely many chart balls missing `C`, whose union `K`
   is a finite union of chart-convex sets, and `c` represents a class over `K` mapping to `α`
   (`Relative/Support.lean`).  Vanishing and uniqueness for `K` (`ChartConvex.lean`) give them for
   `A`; for uniqueness the balls are chosen inside the open set where the local classes of `c`
   vanish.  Existence comes by restriction from `D`.
4. for an arbitrary compact `A`: `A` is a finite union of the compact sets `A ∩ D_j`, `D_j` chart
   balls at finitely many points, and the class of such sets is closed under intersection, so the
   Mayer–Vietoris induction `LocalToGlobal.of_list` applies.

**Theorem 3.26** then follows for a closed (compact `T₂`) manifold with an orientation `μ`:
the fundamental class `fundamentalClass μ ∈ H_n(M; ℤ)` is the unique class restricting to `μ x`
at every point (`absoluteRestriction_fundamentalClass`, `fundamentalClass_unique`),
`H_i(M; ℤ) = 0` for `i > n` (`homology_subsingleton_of_lt`), and for connected `M` the
restriction `H_n(M; ℤ) → H_n(M, M ∖ {x}; ℤ)` is an isomorphism (`restrictionEquiv`), so
`H_n(M; ℤ) ≅ ℤ` (`exists_homology_equiv_int`).

## Main definitions and results

* `ManifoldOrientation.LocalToGlobal.of_isCompact_subset`, `LocalToGlobal.of_isCompact` :
  **Lemma 3.27**.
* `ManifoldOrientation.absoluteRestriction`, `ManifoldOrientation.fundamentalClass`,
  `absoluteRestriction_fundamentalClass`, `fundamentalClass_unique`, `homology_subsingleton_of_lt`
  : **Theorem 3.26**.
* `ManifoldOrientation.restrictionEquiv`, `ManifoldOrientation.exists_homology_equiv_int` :
  `H_n(M; ℤ) ≅ H_n(M, M ∖ {x}; ℤ) ≅ ℤ` for closed connected oriented `M`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3, Lemma 3.27 and Theorem 3.26

## Tags

fundamental class, orientation, closed manifold, local-to-global
-/

open Set Function Topology

@[expose] public noncomputable section

namespace ManifoldOrientation

open SingularChains SingularMayerVietoris RelativeSingularHomology

variable {M : Type} [TopologicalSpace M] {n : ℕ}

/-! ### Finite covers by chart balls -/

section Chart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {e : OpenPartialHomeomorph M E}

/-- A compact subset of a chart domain inside an open `W` is covered by finitely many chart balls
inside `W`. -/
theorem exists_chartBall_list {A : Set M} (hA : IsCompact A) (hAs : A ⊆ e.source) {W : Set M}
    (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ l : List (Set M), (∀ Q ∈ l, IsChartConvex e Q) ∧ A ⊆ listUnion l ∧ listUnion l ⊆ W := by
  have hball : ∀ a (ha : a ∈ A), ∃ Q : Set M, IsChartConvex e Q ∧ Q ⊆ W ∧ a ∈ interior Q := by
    intro a ha
    obtain ⟨r, _, hrt, hrW, har⟩ := exists_chartBall (hAs ha) (hW.mem_nhds (hAW ha))
    exact ⟨_, isChartConvex_symm_image_closedBall hrt, hrW, har⟩
  choose Q hQ hQW haQ using hball
  obtain ⟨t, ht⟩ := hA.elim_nhds_subcover' (fun a ha => interior (Q a ha))
    (fun a ha => isOpen_interior.mem_nhds (haQ a ha))
  refine ⟨t.toList.map fun a => Q a.1 a.2, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hB
    exact hQ a.1 a.2
  · intro a ha
    obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp (ht ha)
    exact subset_listUnion_of_mem (List.mem_map.mpr ⟨b, Finset.mem_toList.mpr hb, rfl⟩)
      (interior_subset hab)
  · apply listUnion_subset
    intro B hB
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hB
    exact hQW a.1 a.2

end Chart

/-! ### Lemma 3.27, step (3): compact sets inside a chart-convex set -/

section Manifold

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}

omit [T2Space M] in
/-- `∂c ∈ C(M ∖ K)` whenever `K` misses the support of `∂c`. -/
theorem boundary_mem_supported_compl_of_disjoint {i : ℕ} (c : Chains M i) {K : Set M}
    (hK : K ⊆ (chainSupport (((singularComplex M).d i (i - 1)).hom c))ᶜ) :
    ((singularComplex M).d i (i - 1)).hom c ∈ supportedChainSubmodule Kᶜ (i - 1) :=
  (mem_supportedChainSubmodule_iff _ _).mpr fun _ hy hyK => hK hyK hy

/-- **Lemma 3.27 for a compact set inside a chart-convex set** (Hatcher's step (3)). -/
theorem LocalToGlobal.of_isCompact_subset (hn : 2 ≤ n) {A D : Set M} (hA : IsCompact A)
    (hD : IsChartConvex e D) (hAD : A ⊆ D) : LocalToGlobal M n Aᶜ := by
  have hAs : A ⊆ e.source := hAD.trans hD.subset_source
  refine ⟨fun i hi => ?_, fun α hα => ?_, fun s hs => ?_⟩
  · -- vanishing above `n`
    refine ⟨fun α β => ?_⟩
    suffices h : ∀ α : RelativeHomology M Aᶜ i, α = 0 by rw [h α, h β]
    intro α
    obtain ⟨c, hc, rfl⟩ := relativeHomologyClass_surjective Aᶜ i α
    set C := chainSupport (((singularComplex M).d i (i - 1)).hom c) with hCdef
    have hCA : C ⊆ Aᶜ := chainSupport_subset_of_mem hc
    have hW : IsOpen Cᶜ := (isCompact_chainSupport _).isClosed.isOpen_compl
    obtain ⟨l, hl, hAl, hlW⟩ := exists_chartBall_list hA hAs hW (fun a ha h => hCA h ha)
    have hcK := boundary_mem_supported_compl_of_disjoint c hlW
    have hK := LocalToGlobal.of_isChartConvex_list hn l hl
    have hK0 : relativeHomologyClass (listUnion l)ᶜ i c hcK = 0 := (hK.vanish i hi).elim _ _
    rw [← restriction_relativeHomologyClass (compl_subset_compl.mpr hAl) i c hcK, hK0, map_zero]
  · -- uniqueness: the open set where the local classes of a representative vanish
    obtain ⟨c, hc, rfl⟩ := relativeHomologyClass_surjective Aᶜ n α
    set C := chainSupport (((singularComplex M).d n (n - 1)).hom c) with hCdef
    have hCA : C ⊆ Aᶜ := chainSupport_subset_of_mem hc
    have hCclosed : IsClosed C := (isCompact_chainSupport _).isClosed
    let W : Set M := {y | ∃ (_ : y ∈ e.source)
      (hyC : ((singularComplex M).d n (n - 1)).hom c ∈ supportedChainSubmodule {y}ᶜ (n - 1)),
        relativeHomologyClass {y}ᶜ n c hyC = 0}
    have hWC : W ⊆ Cᶜ := by
      rintro y ⟨_, hyC, _⟩ hyC'
      exact chainSupport_subset_of_mem hyC hyC' rfl
    have hWopen : IsOpen W := by
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨hys, hyC, hy0⟩
      have hyCc : y ∈ Cᶜ := hWC ⟨hys, hyC, hy0⟩
      obtain ⟨r, _, hrt, hrW, hyr⟩ := exists_chartBall hys
        (Filter.inter_mem (e.open_source.mem_nhds hys) (hCclosed.isOpen_compl.mem_nhds hyCc))
      set L := e.symm '' Metric.closedBall (e y) r with hLdef
      have hL : IsChartConvex e L := isChartConvex_symm_image_closedBall hrt
      have hLC : L ⊆ Cᶜ := hrW.trans inter_subset_right
      have hcL := boundary_mem_supported_compl_of_disjoint c hLC
      have hyL : y ∈ L := interior_subset hyr
      -- the class over `L` vanishes at `y`, hence vanishes
      have hL0 : relativeHomologyClass Lᶜ n c hcL = 0 := by
        apply (hL.isHomologyBall n y hyL).1
        rw [map_zero, ← pointRestriction_eq_localRestriction, pointRestriction,
          restriction_relativeHomologyClass]
        exact hy0
      apply Filter.mem_of_superset (isOpen_interior.mem_nhds hyr)
      intro z hz
      have hzL : z ∈ L := interior_subset hz
      refine ⟨hL.subset_source hzL, supportedChainSubmodule_mono
        (compl_subset_compl_singleton hzL) (n - 1) hcL, ?_⟩
      rw [← restriction_relativeHomologyClass (compl_subset_compl_singleton hzL) n c hcL, hL0, map_zero]
    have hAW : A ⊆ W := fun x hx => by
      refine ⟨hAs hx, supportedChainSubmodule_mono (compl_subset_compl_singleton hx) (n - 1) hc, ?_⟩
      rw [← restriction_relativeHomologyClass (compl_subset_compl_singleton hx) n c hc]
      exact hα x (not_not.mpr hx)
    obtain ⟨l, hl, hAl, hlW⟩ := exists_chartBall_list hA hAs hWopen hAW
    have hcK := boundary_mem_supported_compl_of_disjoint c (hlW.trans hWC)
    have hK := LocalToGlobal.of_isChartConvex_list hn l hl
    have hK0 : relativeHomologyClass (listUnion l)ᶜ n c hcK = 0 := by
      apply hK.unique
      intro x hx
      obtain ⟨_, hxC, hx0⟩ := hlW (not_not.mp hx)
      rw [pointRestriction, restriction_relativeHomologyClass]
      exact hx0
    rw [← restriction_relativeHomologyClass (compl_subset_compl.mpr hAl) n c hcK, hK0, map_zero]
  · -- existence: restrict from the chart-convex set `D`
    obtain ⟨α, hα⟩ := (LocalToGlobal.of_isChartConvex hn hD).exists_of_consistent s hs
    refine ⟨restriction (compl_subset_compl.mpr hAD) n α, fun x hx => ?_⟩
    rw [pointRestriction_restriction]
    exact hα x fun h => hx (fun hxA => h (hAD hxA))

/-! ### Lemma 3.27, step (4): arbitrary compact sets -/

/-- The class of compact sets contained in a chart-convex set of some chart. -/
def ChartCompact (M : Type) [TopologicalSpace M] (n : ℕ) : Set (Set M) :=
  {A | IsCompact A ∧ ∃ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (D : Set M),
    IsChartConvex e D ∧ A ⊆ D}

/-- **Lemma 3.27** (Hatcher, §3.3): for a compact `A` in a `T₂` manifold modelled on `ℝⁿ`,
`n ≥ 2`: `H_i(M, M ∖ A) = 0` for `i > n`; a class in `H_n(M, M ∖ A)` vanishing at every point of
`A` is zero; and every locally consistent family of local homology classes is realized on `A` by
a class in `H_n(M, M ∖ A)`. -/
theorem LocalToGlobal.of_isCompact (hn : 2 ≤ n) {A : Set M} (hA : IsCompact A) :
    LocalToGlobal M n Aᶜ := by
  -- chart balls around the points of `A`
  have hball : ∀ a (_ : a ∈ A), ∃ D : Set M,
      IsChartConvex (chartAt (EuclideanSpace ℝ (Fin n)) a) D ∧ a ∈ interior D := by
    intro a _
    obtain ⟨r, _, hrt, _, har⟩ := exists_chartBall (mem_chart_source (EuclideanSpace ℝ (Fin n)) a)
      (Filter.univ_mem (f := 𝓝 a))
    exact ⟨_, isChartConvex_symm_image_closedBall hrt, har⟩
  choose D hD haD using hball
  obtain ⟨t, ht⟩ := hA.elim_nhds_subcover' (fun a ha => interior (D a ha))
    (fun a ha => isOpen_interior.mem_nhds (haD a ha))
  set l : List (Set M) := t.toList.map fun a => A ∩ D a.1 a.2 with hldef
  have hl : ∀ B ∈ l, B ∈ ChartCompact M n := by
    intro B hB
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hB
    exact ⟨hA.inter_right (hD a.1 a.2).isCompact.isClosed, _, _, hD a.1 a.2, inter_subset_right⟩
  have hAl : listUnion l = A := by
    apply Subset.antisymm
    · exact listUnion_subset fun B hB => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hB
        exact inter_subset_left
    · intro a ha
      obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp (ht ha)
      exact subset_listUnion_of_mem (List.mem_map.mpr ⟨b, Finset.mem_toList.mpr hb, rfl⟩)
        ⟨ha, interior_subset hab⟩
  have h := LocalToGlobal.of_list (ChartCompact M n)
    (fun B hB => by
      obtain ⟨hBc, e, D', hD', hBD⟩ := hB
      exact ⟨hBc, LocalToGlobal.of_isCompact_subset hn hBc hD' hBD⟩)
    (fun B hB B' hB' => by
      obtain ⟨hBc, e, D', hD', hBD⟩ := hB
      exact ⟨hBc.inter_right hB'.1.isClosed, e, D', hD', inter_subset_left.trans hBD⟩)
    l.length l rfl hl
  rw [hAl] at h
  exact h

/-! ### The fundamental class of a closed oriented manifold -/

variable [CompactSpace M]

/-- Lemma 3.27 for `A = M`: the local-to-global property of the empty open set. -/
theorem localToGlobal_empty (hn : 2 ≤ n) : LocalToGlobal M n (∅ : Set M) :=
  (LocalToGlobal.of_isCompact hn (isCompact_univ : IsCompact (Set.univ : Set M))).congr compl_univ

/-- The restriction `H_i(M) → H_i(M, M ∖ {x})` to the local homology at `x`. -/
def absoluteRestriction (x : M) (i : ℕ) : SingularHomology M i →ₗ[ℤ] localHomology M x i :=
  (pointRestriction (notMem_empty x) i).comp (relativeHomologyEquivOfEmpty M i).toLinearMap

omit [T2Space M] [CompactSpace M] in
theorem absoluteRestriction_apply (x : M) (i : ℕ) (a : SingularHomology M i) :
    absoluteRestriction x i a = pointRestriction (notMem_empty x) i (relativeHomologyEquivOfEmpty M i a) :=
  rfl

/-- **The homology of a closed `n`-manifold vanishes above degree `n`** (Hatcher, Theorem 3.26 (c)),
for `n ≥ 2`. -/
theorem homology_subsingleton_of_lt (hn : 2 ≤ n) (i : ℕ) (hi : n < i) :
    Subsingleton (SingularHomology M i) :=
  letI := (localToGlobal_empty (M := M) hn).vanish i hi
  (relativeHomologyEquivOfEmpty M i).injective.subsingleton

/-- A class of `H_n(M)` vanishing at every point is zero. -/
theorem eq_zero_of_absoluteRestriction_eq_zero (hn : 2 ≤ n) (α : SingularHomology M n)
    (h : ∀ x, absoluteRestriction x n α = 0) : α = 0 := by
  apply (relativeHomologyEquivOfEmpty M n).injective
  rw [map_zero]
  exact (localToGlobal_empty hn).unique _ fun x _ => h x

/-- **The fundamental class** of a closed oriented manifold (Hatcher, Theorem 3.26 (a)): the class
of `H_n(M; ℤ)` restricting to the orientation at every point. -/
def fundamentalClass (hn : 2 ≤ n) (μ : Orientation M n) : SingularHomology M n :=
  (relativeHomologyEquivOfEmpty M n).symm
    (Classical.choose ((localToGlobal_empty hn).exists_of_consistent μ.cls μ.isLocallyConsistent))

/-- The fundamental class restricts to the orientation at every point. -/
theorem absoluteRestriction_fundamentalClass (hn : 2 ≤ n) (μ : Orientation M n) (x : M) :
    absoluteRestriction x n (fundamentalClass hn μ) = μ.cls x := by
  rw [absoluteRestriction_apply, fundamentalClass, LinearEquiv.apply_symm_apply]
  exact Classical.choose_spec ((localToGlobal_empty hn).exists_of_consistent μ.cls
    μ.isLocallyConsistent) x (notMem_empty x)

/-- The fundamental class is the unique class restricting to the orientation at every point. -/
theorem fundamentalClass_unique (hn : 2 ≤ n) (μ : Orientation M n) (α : SingularHomology M n)
    (h : ∀ x, absoluteRestriction x n α = μ.cls x) : α = fundamentalClass hn μ := by
  rw [← sub_eq_zero]
  apply eq_zero_of_absoluteRestriction_eq_zero hn
  intro x
  rw [map_sub, h x, absoluteRestriction_fundamentalClass, sub_self]

/-! ### Connected closed oriented manifolds: `H_n(M) ≅ ℤ` -/

omit [CompactSpace M] in
/-- The zero family is locally consistent. -/
theorem isLocallyConsistent_zero : IsLocallyConsistent (fun x : M => (0 : localHomology M x n)) := by
  intro x
  obtain ⟨K, hK, _, hxK, hKb⟩ := exists_isHomologyBall (n := n) x (Filter.univ_mem (f := 𝓝 x)) n
  exact ⟨K, hK, hKb, hxK, 0, fun _ _ => by rw [map_zero]⟩

omit [CompactSpace M] in
/-- `M` meets balls in balls (every point has small homology balls). -/
theorem meetsBallsInBalls_univ : MeetsBallsInBalls M n Set.univ := by
  intro x _ W hW
  obtain ⟨K, _, _, hxK, hKb⟩ := exists_isHomologyBall (n := n) x hW n
  exact ⟨K, hxK, ‹K ⊆ W›, by simpa using hKb⟩

omit [CompactSpace M] in
/-- On a connected manifold, a class of `H_n(M)` vanishing at one point vanishes at every
point. -/
theorem absoluteRestriction_eq_zero_of_eq_zero [PreconnectedSpace M] (α : SingularHomology M n)
    {x₀ : M} (h₀ : absoluteRestriction x₀ n α = 0) (x : M) : absoluteRestriction x n α = 0 := by
  -- transport `α` to a class over `univ`
  have hle : (∅ : Set M) ⊆ (Set.univ : Set M)ᶜ := empty_subset _
  set α' := restriction hle n (relativeHomologyEquivOfEmpty M n α)
  have hα' : ∀ y (hy : y ∈ Set.univ), localRestriction hy n α' = absoluteRestriction y n α := by
    intro y _
    rw [absoluteRestriction_apply, ← pointRestriction_eq_localRestriction, pointRestriction_restriction]
  have := eqOn_of_agree meetsBallsInBalls_univ isPreconnected_univ α' isLocallyConsistent_zero
    (mem_univ x₀) (by rw [hα']; exact h₀) x (mem_univ x)
  rw [← hα' x (mem_univ x)]
  exact this

/-- On a connected closed manifold the restriction `H_n(M) → H_n(M, M ∖ {x})` is injective. -/
theorem absoluteRestriction_injective [PreconnectedSpace M] (hn : 2 ≤ n) (x : M) :
    Function.Injective (absoluteRestriction x n) := by
  intro a b hab
  rw [← sub_eq_zero]
  apply eq_zero_of_absoluteRestriction_eq_zero hn
  apply absoluteRestriction_eq_zero_of_eq_zero (x₀ := x)
  rw [map_sub, hab, sub_self]

/-- On a closed oriented manifold the restriction `H_n(M) → H_n(M, M ∖ {x})` is surjective: its
image contains the generator `μ x`, the restriction of the fundamental class. -/
theorem absoluteRestriction_surjective (hn : 2 ≤ n) (μ : Orientation M n) (x : M) :
    Function.Surjective (absoluteRestriction x n) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← μ.isGenerator x, Submodule.span_singleton_le_iff_mem]
  exact ⟨fundamentalClass hn μ, absoluteRestriction_fundamentalClass hn μ x⟩

/-- **`H_n(M) ≅ H_n(M, M ∖ {x})` for a closed connected oriented manifold** (Hatcher, Theorem
3.26 (a)). -/
def restrictionEquiv [PreconnectedSpace M] (hn : 2 ≤ n) (μ : Orientation M n) (x : M) :
    SingularHomology M n ≃ₗ[ℤ] localHomology M x n :=
  LinearEquiv.ofBijective _ ⟨absoluteRestriction_injective hn x, absoluteRestriction_surjective hn μ x⟩

/-- **`H_n(M; ℤ) ≅ ℤ` for a closed connected oriented `n`-manifold** (Hatcher, Theorem 3.26). -/
theorem exists_homology_equiv_int [PreconnectedSpace M] [Nonempty M] (hn : 2 ≤ n)
    (μ : Orientation M n) : Nonempty (SingularHomology M n ≃ₗ[ℤ] ℤ) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  obtain ⟨e⟩ := localHomology_equiv_int hn x
  exact ⟨(restrictionEquiv hn μ x).trans e⟩

/-- **`H_n(M; ℤ) ≅ ℤ` for a closed simply connected `n`-manifold**, `n ≥ 2` (Hatcher, Theorem 3.26
with the orientability of simply connected manifolds). -/
theorem exists_homology_equiv_int_of_simplyConnectedSpace [SimplyConnectedSpace M] (hn : 2 ≤ n) :
    Nonempty (SingularHomology M n ≃ₗ[ℤ] ℤ) := by
  obtain ⟨μ⟩ := isOrientable_of_simplyConnectedSpace (M := M) hn
  exact exists_homology_equiv_int hn μ

end Manifold

end ManifoldOrientation
