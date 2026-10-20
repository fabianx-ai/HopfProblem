/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# Formal chains on a vertex type

For a type `V` of vertices, `FormalChains V n` is the free `ℤ`-module on the vertex lists
`Fin n → V`; `formalSimplex v` is the generator of a list, `formalLift f` the linear extension
of a function on lists, and `formalMap f n` the functoriality in a vertex map `f : V → W`.
The cone `formalCone a n` prepends the vertex `a`; the boundary `formalBoundary n` is the
alternating sum of the faces (`formalBoundary_simplex`), squares to zero
(`formalBoundary_boundary`), and the cone is a chain contraction:
`∂ (a * c) = c − a * (∂ c)` (`formalBoundary_cone`).  Both commute with `formalMap`.
These are the linear chains `LC_n` and the cone operator `b` of Hatcher, *Algebraic Topology*,
proof of Proposition 2.21, with the indexing shifted by one: `FormalChains V (n + 1)` is the
module of formal `n`-chains.
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-! ### Formal chains -/

/-- Formal chains: finsupp chains on affine simplices. -/
abbrev SingularMayerVietoris.FormalChains (V : Type*) (n : ℕ) :=
  (Fin n → V) →₀ ℤ

/-- A formal simplex as a formal chain. -/
def SingularMayerVietoris.formalSimplex {V : Type*} {n : ℕ} (v : Fin n → V) : FormalChains V n :=
  Finsupp.single v 1

/-- A function on formal simplices lifted to formal chains. -/
def SingularMayerVietoris.formalLift {V M : Type*} {n : ℕ} [AddCommGroup M] [Module ℤ M]
    (f : (Fin n → V) → M) : FormalChains V n →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ f

/-- The formal lift computes the given value on a simplex. -/
@[simp]
theorem SingularMayerVietoris.formalLift_simplex {V M : Type*} {n : ℕ} [AddCommGroup M]
    [modM : Module ℤ M] (f : (Fin n → V) → M) (v : Fin n → V) :
    formalLift f (formalSimplex v) = f v := by
  exact (Finsupp.linearCombination_single ℤ 1 v).trans (modM.one_smul (f v))

/-- Formal-chain maps agreeing on simplices are equal. -/
theorem SingularMayerVietoris.formalChains_ext {V M : Type*} {n : ℕ} [AddCommGroup M] [Module ℤ M]
    {f g : FormalChains V n →ₗ[ℤ] M} (h : ∀ v, f (formalSimplex v) = g (formalSimplex v)) :
    f = g := by
  apply Finsupp.lhom_ext
  intro v z
  have hs : Finsupp.single v z = z • formalSimplex v := by
    simp [formalSimplex, Finsupp.smul_single]
  rw [hs, f.map_smul, g.map_smul, h]

/-- A vertex map induces a map of formal chains. -/
def SingularMayerVietoris.formalMap {V W : Type*} (f : V → W) (n : ℕ) :
    FormalChains V n →ₗ[ℤ] FormalChains W n :=
  Finsupp.lmapDomain ℤ ℤ (fun v => f ∘ v)

/-- The formal map applies the vertex map to a simplex. -/
@[simp]
theorem SingularMayerVietoris.formalMap_simplex {V W : Type*} (f : V → W) {n : ℕ}
    (v : Fin n → V) : formalMap f n (formalSimplex v) = formalSimplex (f ∘ v) := by
  simp [formalMap, formalSimplex]

/-- The cone of a formal simplex on a vertex. -/
def SingularMayerVietoris.formalCone {V : Type*} (a : V) (n : ℕ) :
    FormalChains V n →ₗ[ℤ] FormalChains V (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun v => Fin.cons a v)

/-- The cone prepends the vertex. -/
@[simp]
theorem SingularMayerVietoris.formalCone_simplex {V : Type*} (a : V) {n : ℕ} (v : Fin n → V) :
    formalCone a n (formalSimplex v) = formalSimplex (Fin.cons a v) := by
  simp [formalCone, formalSimplex]

/-- The formal boundary on affine simplices. -/
def SingularMayerVietoris.formalBoundary {V : Type*} (n : ℕ) :
    FormalChains V (n + 1) →ₗ[ℤ] FormalChains V n :=
  formalLift fun v => ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • formalSimplex (v ∘ i.succAbove)

/-- The formal boundary is the alternating face sum. -/
@[simp]
theorem SingularMayerVietoris.formalBoundary_simplex {V : Type*} (n : ℕ) (v : Fin (n + 1) → V) :
    formalBoundary n (formalSimplex v) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • formalSimplex (v ∘ i.succAbove) :=
  formalLift_simplex _ _

/-- The boundary of a cone at degree zero. -/
theorem SingularMayerVietoris.formalBoundary_cone_zero {V : Type*} (a : V)
    (c : FormalChains V 0) : formalBoundary 0 (formalCone a 0 c) = c := by
  have h : (formalBoundary 0).comp (formalCone a 0) = LinearMap.id := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalCone_simplex, formalBoundary_simplex,
      LinearMap.id_apply]
    change
      (∑ i : Fin 1, (-1 : ℤ) ^ i.val • formalSimplex (Fin.cons a v ∘ i.succAbove)) =
        formalSimplex v
    simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul]
    congr 1
  exact LinearMap.congr_fun h c

/-- The cone is a chain contraction of the boundary. -/
theorem SingularMayerVietoris.formalBoundary_cone {V : Type*} (a : V) (n : ℕ)
    (c : FormalChains V (n + 1)) :
    formalBoundary (n + 1) (formalCone a (n + 1) c) = c - formalCone a n (formalBoundary n c) := by
  have h :
    (formalBoundary (n + 1)).comp (formalCone a (n + 1)) =
      LinearMap.id - (formalCone a n).comp (formalBoundary n) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, formalCone_simplex,
      formalBoundary_simplex]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul]
    have hz : Fin.cons a v ∘ (0 : Fin (n + 2)).succAbove = v := by
      funext i
      simp
    rw [hz, sub_eq_add_neg]
    congr 1
    rw [map_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Fin.cons_comp_succ_succAbove,
      map_smul, formalCone_simplex]
    rfl
  exact LinearMap.congr_fun h c

/-- The formal boundary squares to zero. -/
theorem SingularMayerVietoris.formalBoundary_comp {V : Type*} (n : ℕ) :
    (formalBoundary (V := V) n).comp (formalBoundary (n + 1)) = 0 := by
  induction n with
  | zero =>
    apply formalChains_ext
    intro v
    change formalBoundary 0 (formalBoundary 1 (formalSimplex v)) = 0
    have hv : formalSimplex v = formalCone (v 0) 1 (formalSimplex (Fin.tail v)) := by
      rw [formalCone_simplex, Fin.cons_self_tail]
    rw [hv, formalBoundary_cone, map_sub, formalBoundary_cone_zero, sub_self]
  | succ n ih =>
    apply formalChains_ext
    intro v
    change formalBoundary (n + 1) (formalBoundary (n + 2) (formalSimplex v)) = 0
    have hv : formalSimplex v = formalCone (v 0) (n + 2) (formalSimplex (Fin.tail v)) := by
      rw [formalCone_simplex, Fin.cons_self_tail]
    have hb := LinearMap.congr_fun ih (formalSimplex (Fin.tail v))
    change formalBoundary n (formalBoundary (n + 1) (formalSimplex (Fin.tail v))) = 0 at hb
    rw [hv, formalBoundary_cone, map_sub, formalBoundary_cone, hb, map_zero, sub_zero, sub_self]

/-- The formal boundary is a chain-map identity. -/
@[simp]
theorem SingularMayerVietoris.formalBoundary_boundary {V : Type*} (n : ℕ)
    (c : FormalChains V (n + 2)) : formalBoundary n (formalBoundary (n + 1) c) = 0 :=
  LinearMap.congr_fun (formalBoundary_comp n) c

/-- The formal map commutes with the boundary. -/
theorem SingularMayerVietoris.formalMap_boundary {V W : Type*} (f : V → W) (n : ℕ)
    (c : FormalChains V (n + 1)) :
    formalMap f n (formalBoundary n c) = formalBoundary n (formalMap f (n + 1) c) := by
  have h :
    (formalMap f n).comp (formalBoundary n) = (formalBoundary n).comp (formalMap f (n + 1)) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalBoundary_simplex, map_sum, map_smul, formalMap_simplex,
      Function.comp_assoc]
  exact LinearMap.congr_fun h c

/-- The formal map commutes with the cone. -/
theorem SingularMayerVietoris.formalMap_cone {V W : Type*} (f : V → W) (a : V) (n : ℕ)
    (c : FormalChains V n) :
    formalMap f (n + 1) (formalCone a n c) = formalCone (f a) n (formalMap f n c) := by
  have h :
    (formalMap f (n + 1)).comp (formalCone a n) = (formalCone (f a) n).comp (formalMap f n) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalCone_simplex, formalMap_simplex]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  exact LinearMap.congr_fun h c
