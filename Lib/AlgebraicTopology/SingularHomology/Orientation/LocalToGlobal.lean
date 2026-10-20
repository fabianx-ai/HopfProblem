/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Orientation.Orientation
public import Lib.AlgebraicTopology.SingularHomology.Relative.MayerVietoris

/-!
# The local-to-global property

Hatcher's Lemma 3.27 (*Algebraic Topology*, §3.3) says that for a compact `A` in an `n`-manifold
`M`: (a) every locally consistent family of local homology classes `x ↦ μ_x` comes from a unique
class in `H_n(M, M ∖ A)`, and (b) `H_i(M, M ∖ A) = 0` for `i > n`.  This file isolates the
property as a predicate on the open set `U = M ∖ A`,

* `ManifoldOrientation.LocalToGlobal M n U` — `vanish` (`H_i(M, U) = 0` for `i > n`),
  `unique` (a class in `H_n(M, U)` vanishing at every point outside `U` is zero, the stronger
  uniqueness of the accepted textbook P14), `exists_of_consistent`,

and proves the two general steps of the lemma:

1. the Mayer–Vietoris step (`LocalToGlobal.inter`): if the property holds for `U`, `V` and
   `U ∪ V` then it holds for `U ∩ V` (Hatcher's step (1), `A ∪ B` from `A`, `B`, `A ∩ B`), from
   the relative Mayer–Vietoris sequence of `Relative/MayerVietoris.lean`;
2. the agreement lemma (`exists_isOpen_agreement`): for a class `α ∈ H_n(M, M ∖ K)` and a locally
   consistent family `s`, the sets of points of `K` where `α|_x = s x` and where `α|_x ≠ s x` are
   relatively open, provided `K` meets small homology balls in homology balls; hence on a
   connected such `K` agreement at one point is agreement everywhere (`eqOn_of_agree`).

The convex case (Hatcher's step (2)) and the compactness argument (steps (3), (4)) are in
`Orientation/FundamentalClass.lean`.

## Main definitions and results

* `ManifoldOrientation.pointRestriction`, `ManifoldOrientation.LocalToGlobal`,
  `LocalToGlobal.univ`, `LocalToGlobal.congr`.
* `ManifoldOrientation.LocalToGlobal.inter` : the Mayer–Vietoris step.
* `ManifoldOrientation.exists_isOpen_agreement`, `ManifoldOrientation.eqOn_of_agree`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.3, Lemma 3.27, steps (1) and (2)

## Tags

local-to-global, fundamental class, Mayer–Vietoris
-/

open Set Function Topology

@[expose] public noncomputable section

namespace ManifoldOrientation

open RelativeSingularHomology

variable {M : Type} [TopologicalSpace M] {n : ℕ}

/-! ### The property -/

omit [TopologicalSpace M] in
theorem subset_compl_singleton_of_notMem {U : Set M} {x : M} (hx : x ∉ U) : U ⊆ {x}ᶜ :=
  fun _ hy h => hx (mem_singleton_iff.mp h ▸ hy)

/-- The restriction `H_i(M, U) → H_i(M, M ∖ {x})` for `x ∉ U`. -/
abbrev pointRestriction {U : Set M} {x : M} (hx : x ∉ U) (i : ℕ) :
    RelativeHomology M U i →ₗ[ℤ] localHomology M x i :=
  restriction (subset_compl_singleton_of_notMem hx) i

theorem pointRestriction_eq_localRestriction {K : Set M} {x : M} (hx : x ∈ K) (i : ℕ) :
    pointRestriction (show x ∉ Kᶜ from not_not.mpr hx) i = localRestriction hx i := rfl

/-- Point restrictions compose with restrictions along `U ⊆ U'`. -/
theorem pointRestriction_comp_restriction {U U' : Set M} (h : U ⊆ U') {x : M} (hx : x ∉ U') (i : ℕ) :
    (pointRestriction hx i).comp (restriction h i) = pointRestriction (fun hxU => hx (h hxU)) i :=
  restriction_comp _ _ i

theorem pointRestriction_restriction {U U' : Set M} (h : U ⊆ U') {x : M} (hx : x ∉ U') (i : ℕ)
    (α : RelativeHomology M U i) :
    pointRestriction hx i (restriction h i α) = pointRestriction (fun hxU => hx (h hxU)) i α :=
  LinearMap.congr_fun (pointRestriction_comp_restriction h hx i) α

/-- **The local-to-global property** of an open set `U = M ∖ A` in degree `n` (Hatcher, Lemma
3.27 for the compact set `A`, in the stronger form of the accepted textbook P14). -/
structure LocalToGlobal (M : Type) [TopologicalSpace M] (n : ℕ) (U : Set M) : Prop where
  /-- `H_i(M, U) = 0` for `i > n`. -/
  vanish : ∀ i, n < i → Subsingleton (RelativeHomology M U i)
  /-- A class of `H_n(M, U)` vanishing at every point outside `U` is zero. -/
  unique : ∀ α : RelativeHomology M U n, (∀ x (hx : x ∉ U), pointRestriction hx n α = 0) → α = 0
  /-- Every locally consistent family is realized outside `U` by a class of `H_n(M, U)`. -/
  exists_of_consistent : ∀ s : ∀ x : M, localHomology M x n, IsLocallyConsistent s →
    ∃ α : RelativeHomology M U n, ∀ x (hx : x ∉ U), pointRestriction hx n α = s x

/-- The property is invariant under equality of sets. -/
theorem LocalToGlobal.congr {U U' : Set M} (h : U = U') (hU : LocalToGlobal M n U) :
    LocalToGlobal M n U' := by
  subst h
  exact hU

/-- The property holds for `U = M` (the empty compact set). -/
theorem LocalToGlobal.univ : LocalToGlobal M n (Set.univ : Set M) where
  vanish i _ := relativeHomology_subsingleton_of_univ i
  unique α _ := (relativeHomology_subsingleton_of_univ n).elim α 0
  exists_of_consistent _ _ := ⟨0, fun x hx => absurd (mem_univ x) hx⟩

/-- Two realizing classes of the same family coincide. -/
theorem LocalToGlobal.eq_of_pointRestriction_eq {U : Set M} (hU : LocalToGlobal M n U)
    {α β : RelativeHomology M U n} (h : ∀ x (hx : x ∉ U), pointRestriction hx n α = pointRestriction hx n β) :
    α = β := by
  rw [← sub_eq_zero]
  apply hU.unique
  intro x hx
  rw [map_sub, h x hx, sub_self]

/-! ### The Mayer–Vietoris step -/

/-- **The Mayer–Vietoris step of Lemma 3.27**: if the local-to-global property holds for open
`U`, `V` and for `U ∪ V`, it holds for `U ∩ V` (for compact `A = Uᶜ`, `B = Vᶜ`: from `A`, `B` and
`A ∩ B` to `A ∪ B`). -/
theorem LocalToGlobal.inter {U V : Set M} (hUo : IsOpen U) (hVo : IsOpen V)
    (hU : LocalToGlobal M n U) (hV : LocalToGlobal M n V) (hUV : LocalToGlobal M n (U ∪ V)) :
    LocalToGlobal M n (U ∩ V) where
  vanish i hi := by
    refine ⟨fun a b => ?_⟩
    -- `H_{i+1}(M, U ∪ V) → H_i(M, U ∩ V) → H_i(M, U) × H_i(M, V)`, outer terms zero
    have hsub : Subsingleton (RelativeHomology M U i × RelativeHomology M V i) :=
      letI := hU.vanish i hi; letI := hV.vanish i hi; inferInstance
    have hker : ∀ c : RelativeHomology M (U ∩ V) i, c ∈ LinearMap.ker (relativeLeftMap U V i) :=
      fun c => Subsingleton.elim _ _
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hrange : ∀ c, c ∈ LinearMap.range (relativeConnecting U V hUo hVo (i' + 1)) := fun c => by
      rw [relative_exact_at_inter]
      exact hker c
    obtain ⟨a', ha⟩ := hrange a
    obtain ⟨b', hb⟩ := hrange b
    have := hUV.vanish (i' + 1 + 1) (by omega)
    rw [← ha, ← hb, Subsingleton.elim a' b']
  unique α hα := by
    -- the images in `H_n(M, U)` and `H_n(M, V)` vanish at every point outside, hence are zero
    have h₁ : restriction (inter_subset_left : U ∩ V ⊆ U) n α = 0 := hU.unique _ fun x hx => by
      rw [pointRestriction_restriction]
      exact hα x fun h => hx h.1
    have h₂ : restriction (inter_subset_right : U ∩ V ⊆ V) n α = 0 := hV.unique _ fun x hx => by
      rw [pointRestriction_restriction]
      exact hα x fun h => hx h.2
    have hleft : relativeLeftMap U V n α = 0 := by
      rw [relativeLeftMap_apply, h₁, h₂, neg_zero]
      rfl
    have hmem : α ∈ LinearMap.range (relativeConnecting U V hUo hVo n) := by
      rw [relative_exact_at_inter]
      exact hleft
    obtain ⟨γ, rfl⟩ := hmem
    have := hUV.vanish (n + 1) (by omega)
    rw [Subsingleton.elim γ 0, map_zero]
  exists_of_consistent s hs := by
    obtain ⟨αU, hαU⟩ := hU.exists_of_consistent s hs
    obtain ⟨αV, hαV⟩ := hV.exists_of_consistent s hs
    -- `(αU, -αV)` lies in the kernel of the right map by uniqueness on `U ∪ V`
    have hker : (αU, -αV) ∈ LinearMap.ker (relativeRightMap U V n) := by
      rw [LinearMap.mem_ker, relativeRightMap_apply]
      apply hUV.unique
      intro x hx
      simp only [map_add, map_neg, pointRestriction_restriction]
      rw [hαU x fun h => hx (Or.inl h), hαV x fun h => hx (Or.inr h), add_neg_cancel]
    rw [← relative_exact_at_pair U V hUo hVo n] at hker
    obtain ⟨α, hα⟩ := hker
    rw [relativeLeftMap_apply, Prod.mk.injEq, neg_inj] at hα
    refine ⟨α, fun x hx => ?_⟩
    by_cases hxU : x ∈ U
    · have hxV : x ∉ V := fun h => hx ⟨hxU, h⟩
      rw [← hαV x hxV, ← hα.2, pointRestriction_restriction]
    · rw [← hαU x hxU, ← hα.1, pointRestriction_restriction]

/-! ### The agreement lemma -/

/-- `K` *meets balls in balls* in degree `n`: every point of `K` has arbitrarily small homology
balls `L` whose intersection with `K` is again a homology ball. -/
def MeetsBallsInBalls (M : Type) [TopologicalSpace M] (n : ℕ) (K : Set M) : Prop :=
  ∀ x ∈ K, ∀ W ∈ 𝓝 x, ∃ L : Set M, x ∈ interior L ∧ L ⊆ W ∧ IsHomologyBall M n (L ∩ K)

/-- **The agreement lemma.**  For `α ∈ H_n(M, M ∖ K)` and a locally consistent family `s`, the set
of points of `K` where `α|_x = s x` is relatively open in `K`, and so is its complement in `K`,
provided `K` meets balls in balls. -/
theorem exists_isOpen_agreement {K : Set M} (hK : MeetsBallsInBalls M n K)
    (α : RelativeHomology M Kᶜ n) {s : ∀ x : M, localHomology M x n} (hs : IsLocallyConsistent s) :
    (∃ T : Set M, IsOpen T ∧ ∀ x (hx : x ∈ K), (x ∈ T ↔ localRestriction hx n α = s x)) ∧
    (∃ T' : Set M, IsOpen T' ∧ ∀ x (hx : x ∈ K), (x ∈ T' ↔ localRestriction hx n α ≠ s x)) := by
  -- at each `x ∈ K`, a ball `L` on which both sides are restrictions of classes over `L ∩ K`
  have key : ∀ x (hx : x ∈ K), ∃ L : Set M, x ∈ interior L ∧
      ∀ y (hy : y ∈ L ∩ K), (localRestriction hy.2 n α = s y ↔ localRestriction hx n α = s x) := by
    intro x hx
    obtain ⟨K', _, _, hxK', β, hβ⟩ := hs x
    obtain ⟨L, hxL, hLK', hLb⟩ := hK x hx (interior K') (isOpen_interior.mem_nhds hxK')
    refine ⟨L, hxL, fun y hy => ?_⟩
    have hLK : L ∩ K ⊆ K := inter_subset_right
    have hLK'' : L ∩ K ⊆ K' := fun z hz => interior_subset (hLK' hz.1)
    set γ₁ := restriction (compl_subset_compl.mpr hLK) n α
    set γ₂ := restriction (compl_subset_compl.mpr hLK'') n β
    have h₁ : ∀ z (hz : z ∈ L ∩ K), localRestriction hz n γ₁ = localRestriction hz.2 n α :=
      fun z hz => LinearMap.congr_fun (localRestriction_comp_restriction hLK hz n) α
    have h₂ : ∀ z (hz : z ∈ L ∩ K), localRestriction hz n γ₂ = s z := fun z hz => by
      rw [hβ z (hLK'' hz)]
      exact LinearMap.congr_fun (localRestriction_comp_restriction hLK'' hz n) β
    -- at every point of `L ∩ K`, agreement is equivalent to `γ₁ = γ₂`
    have hiff : ∀ z (hz : z ∈ L ∩ K), (localRestriction hz.2 n α = s z ↔ γ₁ = γ₂) := fun z hz => by
      rw [← h₁ z hz, ← h₂ z hz]
      exact ⟨fun h => (hLb z hz).1 h, fun h => by rw [h]⟩
    rw [hiff y hy, hiff x ⟨interior_subset hxL, hx⟩]
  choose L hxL hL using key
  constructor
  · refine ⟨⋃ (x : M) (hx : x ∈ K) (_ : localRestriction hx n α = s x), interior (L x hx), ?_, ?_⟩
    · exact isOpen_iUnion fun x => isOpen_iUnion fun hx => isOpen_iUnion fun _ => isOpen_interior
    · intro x hx
      constructor
      · intro hxT
        simp only [mem_iUnion] at hxT
        obtain ⟨x', hx', hagree, hxL'⟩ := hxT
        exact (hL x' hx' x ⟨interior_subset hxL', hx⟩).mpr hagree
      · intro hagree
        simp only [mem_iUnion]
        exact ⟨x, hx, hagree, hxL x hx⟩
  · refine ⟨⋃ (x : M) (hx : x ∈ K) (_ : localRestriction hx n α ≠ s x), interior (L x hx), ?_, ?_⟩
    · exact isOpen_iUnion fun x => isOpen_iUnion fun hx => isOpen_iUnion fun _ => isOpen_interior
    · intro x hx
      constructor
      · intro hxT
        simp only [mem_iUnion] at hxT
        obtain ⟨x', hx', hdis, hxL'⟩ := hxT
        exact fun h => hdis ((hL x' hx' x ⟨interior_subset hxL', hx⟩).mp h)
      · intro hdis
        simp only [mem_iUnion]
        exact ⟨x, hx, hdis, hxL x hx⟩

/-- On a connected `K` meeting balls in balls, a class `α ∈ H_n(M, M ∖ K)` agreeing with a locally
consistent family at one point agrees with it everywhere on `K`. -/
theorem eqOn_of_agree {K : Set M} (hK : MeetsBallsInBalls M n K) (hKc : IsPreconnected K)
    (α : RelativeHomology M Kᶜ n) {s : ∀ x : M, localHomology M x n} (hs : IsLocallyConsistent s)
    {x₀ : M} (hx₀ : x₀ ∈ K) (h₀ : localRestriction hx₀ n α = s x₀) (x : M) (hx : x ∈ K) :
    localRestriction hx n α = s x := by
  obtain ⟨⟨T, hT, hTK⟩, ⟨T', hT', hT'K⟩⟩ := exists_isOpen_agreement hK α hs
  -- `K ⊆ T ∪ T'` with `K ∩ T ∩ T' = ∅`; `K` preconnected and `K ∩ T ≠ ∅` force `K ∩ T' = ∅`
  by_contra hne
  have hxT' : x ∈ T' := (hT'K x hx).mpr hne
  have hx₀T : x₀ ∈ T := (hTK x₀ hx₀).mpr h₀
  have hcover : K ⊆ T ∪ T' := fun y hy => by
    by_cases h : localRestriction hy n α = s y
    · exact Or.inl ((hTK y hy).mpr h)
    · exact Or.inr ((hT'K y hy).mpr h)
  obtain ⟨y, hyK, hyT, hyT'⟩ := hKc T T' hT hT' hcover ⟨x₀, hx₀, hx₀T⟩ ⟨x, hx, hxT'⟩
  exact (hT'K y hyK).mp hyT' ((hTK y hyK).mp hyT)

end ManifoldOrientation
