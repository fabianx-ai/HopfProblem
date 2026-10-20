/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.FormalChains

/-!
# Barycentric subdivision of formal chains

Given centers `center : FormalCenter V` (a vertex for every vertex list), the barycentric
subdivision `formalSubdivision center n` of formal chains is defined by recursion on the degree:
the identity in degree `0`, and `S [v] = b_v * S (∂ [v])` with `b_v = center v` and `*` the
cone (`formalSubdivision_simplex_succ`).  It is a chain map (`formalBoundary_subdivision`),
natural in the vertices (`formalMap_subdivision`), and chain homotopic to the identity through
`formalSubdivisionHomotopy center`, the cone at the first vertex of `[v] − S [v] − T (∂ [v])`,
with `∂ T + T ∂ = 𝟙 − S` (`formalSubdivisionHomotopy_boundary`).  The `k`-fold iterate `S^k`
is chain homotopic to the identity through `formalSubdivisionIteratedHomotopy center k`
(`formalSubdivisionIteratedHomotopy_boundary`), and both homotopies are natural in the vertices.
This is the subdivision operator `S` and homotopy `T` on linear chains of Hatcher, *Algebraic
Topology*, proof of Proposition 2.21, step (2).
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-! ### Barycentric subdivision -/

/-- A center assignment for coning formal simplices. -/
abbrev SingularMayerVietoris.FormalCenter (V : Type*) :=
  ∀ n : ℕ, (Fin (n + 1) → V) → V

/-- The barycentric subdivision of a formal chain. -/
def SingularMayerVietoris.formalSubdivision {V : Type*} (center : FormalCenter V) :
    (n : ℕ) → FormalChains V n →ₗ[ℤ] FormalChains V n
  | 0 => LinearMap.id
  | n + 1 =>
    formalLift fun v =>
      formalCone (center n v) n (formalSubdivision center n (formalBoundary n (formalSimplex v)))

/-- Subdivision of a 0-simplex is the simplex. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivision_zero {V : Type*} (center : FormalCenter V)
    (c : FormalChains V 0) : formalSubdivision center 0 c = c :=
  rfl

/-- Subdivision of a simplex is the cone of the boundary subdivision. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivision_simplex_succ {V : Type*} (center : FormalCenter V)
    (n : ℕ) (v : Fin (n + 1) → V) :
    formalSubdivision center (n + 1) (formalSimplex v) =
      formalCone (center n v) n
        (formalSubdivision center n (formalBoundary n (formalSimplex v))) :=
  formalLift_simplex _ _

/-- Subdivision is a chain map. -/
theorem SingularMayerVietoris.formalBoundary_subdivision {V : Type*} (center : FormalCenter V) :
    ∀ (n : ℕ) (c : FormalChains V (n + 1)),
      formalBoundary n (formalSubdivision center (n + 1) c) =
        formalSubdivision center n (formalBoundary n c) := by
  intro n
  induction n with
  | zero =>
    intro c
    have h :
      (formalBoundary 0).comp (formalSubdivision center 1) =
        (formalSubdivision center 0).comp (formalBoundary 0) := by
      apply formalChains_ext
      intro v
      simp only [LinearMap.comp_apply, formalSubdivision_simplex_succ, formalBoundary_cone_zero]
    exact LinearMap.congr_fun h c
  | succ n ih =>
    intro c
    have h :
      (formalBoundary (n + 1)).comp (formalSubdivision center (n + 2)) =
        (formalSubdivision center (n + 1)).comp (formalBoundary (n + 1)) := by
      apply formalChains_ext
      intro v
      simp only [LinearMap.comp_apply, formalSubdivision_simplex_succ]
      rw [formalBoundary_cone, ih, formalBoundary_boundary, map_zero, map_zero, sub_zero]
    exact LinearMap.congr_fun h c

/-- The formal map commutes with subdivision. -/
theorem SingularMayerVietoris.formalMap_subdivision {V W : Type*} (center : FormalCenter V)
    (center' : FormalCenter W) (f : V → W) (hf : ∀ n v, f (center n v) = center' n (f ∘ v)) :
    ∀ (n : ℕ) (c : FormalChains V n),
      formalMap f n (formalSubdivision center n c) =
        formalSubdivision center' n (formalMap f n c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    have h :
      (formalMap f (n + 1)).comp (formalSubdivision center (n + 1)) =
        (formalSubdivision center' (n + 1)).comp (formalMap f (n + 1)) := by
      apply formalChains_ext
      intro v
      simp only [LinearMap.comp_apply, formalSubdivision_simplex_succ, formalMap_simplex]
      rw [formalMap_cone, ih, formalMap_boundary, formalMap_simplex, hf]
    exact LinearMap.congr_fun h c

/-! ### The subdivision homotopy -/

/-- The formal chain homotopy between subdivision and identity. -/
def SingularMayerVietoris.formalSubdivisionHomotopy {V : Type*} (center : FormalCenter V) :
    (n : ℕ) → FormalChains V n →ₗ[ℤ] FormalChains V (n + 1)
  | 0 => 0
  | n + 1 =>
    formalLift fun v =>
      formalCone (v 0) (n + 1)
        (formalSimplex v - formalSubdivision center (n + 1) (formalSimplex v) -
          formalSubdivisionHomotopy center n (formalBoundary n (formalSimplex v)))

/-- The subdivision homotopy in degree zero. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivisionHomotopy_zero {V : Type*} (center : FormalCenter V)
    (c : FormalChains V 0) : formalSubdivisionHomotopy center 0 c = 0 :=
  rfl

/-- The subdivision homotopy on a simplex. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivisionHomotopy_simplex_succ {V : Type*}
    (center : FormalCenter V) (n : ℕ) (v : Fin (n + 1) → V) :
    formalSubdivisionHomotopy center (n + 1) (formalSimplex v) =
      formalCone (v 0) (n + 1)
        (formalSimplex v - formalSubdivision center (n + 1) (formalSimplex v) -
          formalSubdivisionHomotopy center n (formalBoundary n (formalSimplex v))) :=
  formalLift_simplex _ _

/-- The subdivision homotopy satisfies the chain-homotopy identity. -/
theorem SingularMayerVietoris.formalSubdivisionHomotopy_boundary {V : Type*}
    (center : FormalCenter V) :
    ∀ (n : ℕ) (c : FormalChains V (n + 1)),
      formalBoundary (n + 1) (formalSubdivisionHomotopy center (n + 1) c) +
          formalSubdivisionHomotopy center n (formalBoundary n c) =
        c - formalSubdivision center (n + 1) c := by
  intro n
  induction n with
  | zero =>
    intro c
    have h :
      (formalBoundary 1).comp (formalSubdivisionHomotopy center 1) +
          (formalSubdivisionHomotopy center 0).comp (formalBoundary 0) =
        LinearMap.id - formalSubdivision center 1 := by
      apply formalChains_ext
      intro v
      change
        formalBoundary 1 (formalSubdivisionHomotopy center 1 (formalSimplex v)) +
            formalSubdivisionHomotopy center 0 (formalBoundary 0 (formalSimplex v)) =
          formalSimplex v - formalSubdivision center 1 (formalSimplex v)
      have hc :
        formalBoundary 0
            (formalSimplex v - formalSubdivision center 1 (formalSimplex v) -
              formalSubdivisionHomotopy center 0 (formalBoundary 0 (formalSimplex v))) =
          0 := by
        simp only [map_sub, formalBoundary_subdivision, formalSubdivision_zero,
          formalSubdivisionHomotopy_zero, sub_self, sub_zero]
      rw [formalSubdivisionHomotopy_simplex_succ, formalBoundary_cone, hc, map_zero, sub_zero,
        sub_add_cancel]
    exact LinearMap.congr_fun h c
  | succ n ih =>
    intro c
    have h :
      (formalBoundary (n + 2)).comp (formalSubdivisionHomotopy center (n + 2)) +
          (formalSubdivisionHomotopy center (n + 1)).comp (formalBoundary (n + 1)) =
        LinearMap.id - formalSubdivision center (n + 2) := by
      apply formalChains_ext
      intro v
      change
        formalBoundary (n + 2) (formalSubdivisionHomotopy center (n + 2) (formalSimplex v)) +
            formalSubdivisionHomotopy center (n + 1) (formalBoundary (n + 1) (formalSimplex v)) =
          formalSimplex v - formalSubdivision center (n + 2) (formalSimplex v)
      have hp :
        formalBoundary (n + 1)
            (formalSubdivisionHomotopy center (n + 1)
              (formalBoundary (n + 1) (formalSimplex v))) =
          formalBoundary (n + 1) (formalSimplex v) -
            formalSubdivision center (n + 1) (formalBoundary (n + 1) (formalSimplex v)) := by
        simpa only [formalBoundary_boundary, map_zero, add_zero] using
          ih (formalBoundary (n + 1) (formalSimplex v))
      have hc :
        formalBoundary (n + 1)
            (formalSimplex v - formalSubdivision center (n + 2) (formalSimplex v) -
              formalSubdivisionHomotopy center (n + 1)
                (formalBoundary (n + 1) (formalSimplex v))) =
          0 := by rw [map_sub, map_sub, formalBoundary_subdivision, hp, sub_self]
      rw [formalSubdivisionHomotopy_simplex_succ, formalBoundary_cone, hc, map_zero, sub_zero,
        sub_add_cancel]
    exact LinearMap.congr_fun h c

/-- The formal map commutes with the subdivision homotopy. -/
theorem SingularMayerVietoris.formalMap_subdivisionHomotopy {V W : Type*}
    (center : FormalCenter V) (center' : FormalCenter W) (f : V → W)
    (hf : ∀ n v, f (center n v) = center' n (f ∘ v)) :
    ∀ (n : ℕ) (c : FormalChains V n),
      formalMap f (n + 1) (formalSubdivisionHomotopy center n c) =
        formalSubdivisionHomotopy center' n (formalMap f n c) := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    have h :
      (formalMap f (n + 2)).comp (formalSubdivisionHomotopy center (n + 1)) =
        (formalSubdivisionHomotopy center' (n + 1)).comp (formalMap f (n + 1)) := by
      apply formalChains_ext
      intro v
      simp only [LinearMap.comp_apply, formalSubdivisionHomotopy_simplex_succ, formalMap_simplex]
      rw [formalMap_cone]
      congr 1
      rw [map_sub, map_sub, formalMap_simplex, formalMap_subdivision center center' f hf, ih,
        formalMap_boundary, formalMap_simplex]
    exact LinearMap.congr_fun h c

/-- Iterated subdivision remains a chain map. -/
theorem SingularMayerVietoris.formalBoundary_subdivision_iterate {V : Type*}
    (center : FormalCenter V) (k n : ℕ) (c : FormalChains V (n + 1)) :
    formalBoundary n ((formalSubdivision center (n + 1))^[k] c) =
      (formalSubdivision center n)^[k] (formalBoundary n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', formalBoundary_subdivision,
      ih]

/-- The formal map commutes with iterated subdivision. -/
theorem SingularMayerVietoris.formalMap_subdivision_iterate {V W : Type*}
    (center : FormalCenter V) (center' : FormalCenter W) (f : V → W)
    (hf : ∀ n v, f (center n v) = center' n (f ∘ v)) (k n : ℕ) (c : FormalChains V n) :
    formalMap f n ((formalSubdivision center n)^[k] c) =
      (formalSubdivision center' n)^[k] (formalMap f n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      formalMap_subdivision center center' f hf, ih]

/-- The homotopy between iterated subdivision and identity. -/
def SingularMayerVietoris.formalSubdivisionIteratedHomotopy {V : Type*} (center : FormalCenter V)
    (k n : ℕ) : FormalChains V n →ₗ[ℤ] FormalChains V (n + 1) :=
  ∑ j ∈ Finset.range k,
    (formalSubdivisionHomotopy center n).comp ((formalSubdivision center n) ^ j)

/-- The iterated homotopy computes on a chain. -/
theorem SingularMayerVietoris.formalSubdivisionIteratedHomotopy_apply {V : Type*}
    (center : FormalCenter V) (k n : ℕ) (c : FormalChains V n) :
    formalSubdivisionIteratedHomotopy center k n c =
      ∑ j ∈ Finset.range k,
        formalSubdivisionHomotopy center n ((formalSubdivision center n)^[j] c) := by
  simp only [formalSubdivisionIteratedHomotopy, LinearMap.sum_apply, LinearMap.comp_apply,
    Module.End.pow_apply]

/-- The iterated homotopy in degree zero. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivisionIteratedHomotopy_zero {V : Type*}
    (center : FormalCenter V) (n : ℕ) (c : FormalChains V n) :
    formalSubdivisionIteratedHomotopy center 0 n c = 0 := by
  simp [formalSubdivisionIteratedHomotopy]

/-- The iterated homotopy recursion. -/
theorem SingularMayerVietoris.formalSubdivisionIteratedHomotopy_succ {V : Type*}
    (center : FormalCenter V) (k n : ℕ) (c : FormalChains V n) :
    formalSubdivisionIteratedHomotopy center (k + 1) n c =
      formalSubdivisionIteratedHomotopy center k n c +
        formalSubdivisionHomotopy center n ((formalSubdivision center n)^[k] c) := by
  simp only [formalSubdivisionIteratedHomotopy_apply, Finset.sum_range_succ]

/-- The iterated homotopy is zero in degree zero. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivisionIteratedHomotopy_degree_zero {V : Type*}
    (center : FormalCenter V) (k : ℕ) (c : FormalChains V 0) :
    formalSubdivisionIteratedHomotopy center k 0 c = 0 := by
  simp [formalSubdivisionIteratedHomotopy_apply]

/-- The iterated homotopy satisfies the chain-homotopy identity. -/
theorem SingularMayerVietoris.formalSubdivisionIteratedHomotopy_boundary {V : Type*}
    (center : FormalCenter V) (k n : ℕ) (c : FormalChains V (n + 1)) :
    formalBoundary (n + 1) (formalSubdivisionIteratedHomotopy center k (n + 1) c) +
        formalSubdivisionIteratedHomotopy center k n (formalBoundary n c) =
      c - (formalSubdivision center (n + 1))^[k] c := by
  induction k with
  | zero => simp
  | succ k
    ih =>
    rw [formalSubdivisionIteratedHomotopy_succ, formalSubdivisionIteratedHomotopy_succ, map_add]
    have hh :=
      formalSubdivisionHomotopy_boundary center n ((formalSubdivision center (n + 1))^[k] c)
    rw [formalBoundary_subdivision_iterate] at hh
    calc
      _ =
          (formalBoundary (n + 1) (formalSubdivisionIteratedHomotopy center k (n + 1) c) +
              formalSubdivisionIteratedHomotopy center k n (formalBoundary n c)) +
            (formalBoundary (n + 1)
                (formalSubdivisionHomotopy center (n + 1)
                  ((formalSubdivision center (n + 1))^[k] c)) +
              formalSubdivisionHomotopy center n
                ((formalSubdivision center n)^[k] (formalBoundary n c))) := by abel
      _ =
          (c - (formalSubdivision center (n + 1))^[k] c) +
            ((formalSubdivision center (n + 1))^[k] c -
              formalSubdivision center (n + 1) ((formalSubdivision center (n + 1))^[k] c)) := by
        rw [ih, hh]
      _ = c - (formalSubdivision center (n + 1))^[k + 1] c := by
        rw [Function.iterate_succ_apply']
        abel

/-- The formal map commutes with the iterated homotopy. -/
theorem SingularMayerVietoris.formalMap_subdivisionIteratedHomotopy {V W : Type*}
    (center : FormalCenter V) (center' : FormalCenter W) (f : V → W)
    (hf : ∀ n v, f (center n v) = center' n (f ∘ v)) (k n : ℕ) (c : FormalChains V n) :
    formalMap f (n + 1) (formalSubdivisionIteratedHomotopy center k n c) =
      formalSubdivisionIteratedHomotopy center' k n (formalMap f n c) := by
  simp only [formalSubdivisionIteratedHomotopy_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [formalMap_subdivisionHomotopy center center' f hf,
    formalMap_subdivision_iterate center center' f hf]
