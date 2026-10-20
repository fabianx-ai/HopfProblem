/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.FormalSubdivision

/-!
# Supports of formal chains

`formalChainsSupported S n` is the submodule of formal chains all of whose vertex lists lie in
`S : Set V`.  It is preserved by the boundary, by the cone at a vertex of `S`, by a vertex map
sending `S` into `T`, and by barycentric subdivision whenever the center of a list in `S` lies in
`S` (`formalSubdivision_mem_supported`).  The lemmas `*_support_exists` describe the
`Finsupp.support` of a cone, a lift, a linear map and a boundary in terms of the support of the
argument, and `formalLinearMap_mem_of_support` reduces a membership statement about `f c` to
the vertex lists in the support of `c`.  This is the bookkeeping behind the fact that the
simplices of a subdivided linear simplex lie in its convex hull (Hatcher, *Algebraic Topology*,
proof of Proposition 2.21, step (1)).
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-! ### Supported formal chains -/

/-- The formal chains supported on a vertex set. -/
def SingularMayerVietoris.formalChainsSupported {V : Type*} (S : Set V) (n : ℕ) :
    Submodule ℤ (FormalChains V n) :=
  Finsupp.supported ℤ ℤ {v | ∀ i, v i ∈ S}

/-- A formal chain is supported exactly when its support is. -/
theorem SingularMayerVietoris.mem_formalChainsSupported_iff {V : Type*} {n : ℕ} {S : Set V}
    {c : FormalChains V n} : c ∈ formalChainsSupported S n ↔ ∀ v ∈ c.support, ∀ i, v i ∈ S :=
  Iff.rfl

/-- Supported formal chains are monotone in the vertex set. -/
theorem SingularMayerVietoris.formalChainsSupported_mono {V : Type*} {n : ℕ} {S T : Set V}
    (h : S ⊆ T) : formalChainsSupported S n ≤ formalChainsSupported T n := by
  intro c hc v hv i
  exact h (hc hv i)

/-- Every formal chain is supported on all vertices. -/
@[simp]
theorem SingularMayerVietoris.formalChainsSupported_univ {V : Type*} (n : ℕ) :
    formalChainsSupported (Set.univ : Set V) n = ⊤ := by
  apply top_unique
  intro c _ v hv i
  exact Set.mem_univ _

/-- A formal simplex is supported exactly when its vertices are. -/
@[simp]
theorem SingularMayerVietoris.formalSimplex_mem_supported_iff {V : Type*} {n : ℕ} {S : Set V}
    (v : Fin n → V) : formalSimplex v ∈ formalChainsSupported S n ↔ ∀ i, v i ∈ S := by
  classical simp [formalSimplex, formalChainsSupported, Finsupp.mem_supported]

/-- A formal simplex with vertices in the set is supported. -/
theorem SingularMayerVietoris.formalSimplex_mem_supported {V : Type*} {n : ℕ} {S : Set V}
    {v : Fin n → V} (hv : ∀ i, v i ∈ S) : formalSimplex v ∈ formalChainsSupported S n :=
  (formalSimplex_mem_supported_iff v).mpr hv

/-- A vertex set bounding the support gives supportedness. -/
theorem SingularMayerVietoris.formalChainsSupported_le {V : Type*} {n : ℕ} {S : Set V}
    {P : Submodule ℤ (FormalChains V n)} (h : ∀ v, (∀ i, v i ∈ S) → formalSimplex v ∈ P) :
    formalChainsSupported S n ≤ P := by
  rw [formalChainsSupported, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

/-- A formal linear map preserves supportedness. -/
theorem SingularMayerVietoris.formalLinearMap_mem_of_supported {V M : Type*} {n : ℕ}
    [AddCommGroup M] [Module ℤ M] {S : Set V} (f : FormalChains V n →ₗ[ℤ] M) (P : Submodule ℤ M)
    {c : FormalChains V n} (hc : c ∈ formalChainsSupported S n)
    (h : ∀ v, (∀ i, v i ∈ S) → f (formalSimplex v) ∈ P) : f c ∈ P := by
  exact (formalChainsSupported_le (P := P.comap f) h) hc

/-- The formal boundary preserves supportedness. -/
theorem SingularMayerVietoris.formalBoundary_mem_supported {V : Type*} {S : Set V} (n : ℕ)
    {c : FormalChains V (n + 1)} (hc : c ∈ formalChainsSupported S (n + 1)) :
    formalBoundary n c ∈ formalChainsSupported S n := by
  apply formalLinearMap_mem_of_supported (formalBoundary n) (formalChainsSupported S n) hc
  intro v hv
  rw [formalBoundary_simplex]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact formalSimplex_mem_supported fun j => hv (i.succAbove j)

/-- The formal cone preserves supportedness with its center. -/
theorem SingularMayerVietoris.formalCone_mem_supported {V : Type*} {n : ℕ} {S : Set V} {a : V}
    (ha : a ∈ S) {c : FormalChains V n} (hc : c ∈ formalChainsSupported S n) :
    formalCone a n c ∈ formalChainsSupported S (n + 1) := by
  apply formalLinearMap_mem_of_supported (formalCone a n) (formalChainsSupported S (n + 1)) hc
  intro v hv
  rw [formalCone_simplex]
  apply formalSimplex_mem_supported
  intro i
  exact Fin.cases ha hv i

/-- The formal map preserves supportedness. -/
theorem SingularMayerVietoris.formalMap_mem_supported {V W : Type*} {n : ℕ} {S : Set V}
    {T : Set W} (f : V → W) (hf : Set.MapsTo f S T) {c : FormalChains V n}
    (hc : c ∈ formalChainsSupported S n) : formalMap f n c ∈ formalChainsSupported T n := by
  apply formalLinearMap_mem_of_supported (formalMap f n) (formalChainsSupported T n) hc
  intro v hv
  rw [formalMap_simplex]
  exact formalSimplex_mem_supported fun i => hf (hv i)

/-- Subdivision preserves supportedness. -/
theorem SingularMayerVietoris.formalSubdivision_mem_supported {V : Type*}
    (center : FormalCenter V) {S : Set V} (hcenter : ∀ k v, (∀ i, v i ∈ S) → center k v ∈ S) :
    ∀ (n : ℕ) {c : FormalChains V n},
      c ∈ formalChainsSupported S n → formalSubdivision center n c ∈ formalChainsSupported S n := by
  intro n
  induction n with
  | zero =>
    intro c hc
    exact hc
  | succ n ih =>
    intro c hc
    apply
      formalLinearMap_mem_of_supported (formalSubdivision center (n + 1))
        (formalChainsSupported S (n + 1)) hc
    intro v hv
    rw [formalSubdivision_simplex_succ]
    exact
      formalCone_mem_supported (hcenter n v hv)
        (ih (formalBoundary_mem_supported n (formalSimplex_mem_supported hv)))

/-- A cone supported on the convex hull exists. -/
theorem SingularMayerVietoris.formalCone_support_exists {V : Type*} {n : ℕ} (a : V)
    {c : FormalChains V n} {w : Fin (n + 1) → V} (hw : w ∈ (formalCone a n c).support) :
    ∃ v ∈ c.support, w = Fin.cons a v := by
  classical
  change w ∈ (Finsupp.mapDomain (Fin.cons a) c).support at hw
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw)
  exact ⟨v, hv, heq.symm⟩

/-- A lift supported on the convex hull exists. -/
theorem SingularMayerVietoris.formalLift_support_exists {V W : Type*} {n : ℕ} {m : ℕ}
    (f : (Fin n → V) → FormalChains W m) {c : FormalChains V n} {w : Fin m → W}
    (hw : w ∈ (formalLift f c).support) : ∃ v ∈ c.support, w ∈ (f v).support := by
  classical
  change w ∈ (c.sum fun v z => z • f v).support at hw
  obtain ⟨v, hv, hterm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hw)
  exact ⟨v, hv, Finsupp.support_smul hterm⟩

/-- A supported formal map exists. -/
theorem SingularMayerVietoris.formalLinearMap_support_exists {V W : Type*} {n : ℕ} {m : ℕ}
    (f : FormalChains V n →ₗ[ℤ] FormalChains W m) {c : FormalChains V n} {w : Fin m → W}
    (hw : w ∈ (f c).support) : ∃ v ∈ c.support, w ∈ (f (formalSimplex v)).support := by
  have hf : f = formalLift (fun v => f (formalSimplex v)) := by
    apply formalChains_ext
    intro v
    simp only [formalLift_simplex]
  rw [hf] at hw
  exact formalLift_support_exists _ hw

/-- A supported formal boundary exists. -/
theorem SingularMayerVietoris.formalBoundary_support_exists {V : Type*} (n : ℕ)
    (v : Fin (n + 1) → V) {w : Fin n → V}
    (hw : w ∈ (formalBoundary n (formalSimplex v)).support) :
    ∃ i : Fin (n + 1), w = v ∘ i.succAbove := by
  classical
  rw [formalBoundary_simplex] at hw
  obtain ⟨i, hi, hterm⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
  refine ⟨i, ?_⟩
  have hs : w ∈ (formalSimplex (v ∘ i.succAbove)).support := Finsupp.support_smul hterm
  simpa [formalSimplex] using hs

/-- A formal linear map is supported on the convex hull. -/
theorem SingularMayerVietoris.formalLinearMap_mem_of_support {V M : Type*} [AddCommGroup M]
    [Module ℤ M] {n : ℕ} (f : FormalChains V n →ₗ[ℤ] M) (P : Submodule ℤ M) (c : FormalChains V n)
    (hf : ∀ v ∈ c.support, f (formalSimplex v) ∈ P) : f c ∈ P := by
  have h : Finsupp.supported ℤ ℤ (c.support : Set (Fin n → V)) ≤ P.comap f := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    exact hf v hv
  exact h (fun _ hv => hv)
