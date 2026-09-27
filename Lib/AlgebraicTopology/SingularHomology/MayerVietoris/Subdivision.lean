/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.AffineSimplex
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.FormalSubdivision

/-!
# Barycentric subdivision of singular chains

Formal chains on the standard simplex `Δ^p` are realized as singular chains of `Δ^p` by the
affine chain map `affineChainMap p n`, sending a vertex list `v` to the affine simplex
`affineSimplex v`; it is a chain map (`affineChainMap_boundary`) and natural under affine maps
(`inducedChain_affineChainMap`).  With the barycenters as centers (`simplexCenter p`), the
`k`-fold barycentric subdivision of singular chains of a space `X` is `subdivision X k n`: a
singular simplex `σ : Δ^n → X` is sent to `σ_*` of the `k`-fold subdivision of the identity
simplex (`subdivision_simplex`).  It is a chain map (`subdivision_boundary`), natural in `X`
(`inducedChain_subdivision`), and chain homotopic to the identity through
`subdivisionHomotopy X k n` with `∂ D + D ∂ = 𝟙 − S^k` (`subdivisionHomotopy_boundary`).
This is step (3) of the proof of Hatcher, *Algebraic Topology*, Proposition 2.21: the operators
`S` and `T` on singular chains, obtained from the linear ones on the identity simplex.
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-! ### The affine chain map -/

/-- The barycenter of an affine simplex. -/
def SingularMayerVietoris.simplexCenter (p : ℕ) : FormalCenter (SingularChains.Simplex p) :=
  fun _ v => simplexBarycenter v

/-- The chain map realizing formal chains as singular chains. -/
def SingularMayerVietoris.affineChainMap (p n : ℕ) :
    FormalChains (SingularChains.Simplex p) (n + 1) →ₗ[ℤ]
      SingularChains.Chains (SingularChains.Simplex p) n :=
  formalLift fun v => SingularChains.simplexChain (SingularChains.Simplex p) n (affineSimplex v)

/-- The affine chain map sends a formal simplex to its affine simplex. -/
@[simp]
theorem SingularMayerVietoris.affineChainMap_simplex (p n : ℕ)
    (v : Fin (n + 1) → SingularChains.Simplex p) :
    affineChainMap p n (formalSimplex v) =
      SingularChains.simplexChain (SingularChains.Simplex p) n (affineSimplex v) :=
  formalLift_simplex _ _

/-- The affine chain map commutes with the boundary. -/
theorem SingularMayerVietoris.affineChainMap_boundary (p n : ℕ)
    (c : FormalChains (SingularChains.Simplex p) (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p)).d (n + 1) n).hom
        (affineChainMap p (n + 1) c) =
      affineChainMap p n (formalBoundary (n + 1) c) := by
  have h :
    (((SingularChains.singularComplex (SingularChains.Simplex p)).d (n + 1) n).hom).comp
        (affineChainMap p (n + 1)) =
      (affineChainMap p n).comp (formalBoundary (n + 1)) := by
    apply formalChains_ext
    intro v
    change
      ((SingularChains.singularComplex (SingularChains.Simplex p)).d (n + 1) n).hom
          (affineChainMap p (n + 1) (formalSimplex v)) =
        _
    rw [affineChainMap_simplex, SingularChains.boundary_simplex]
    change _ = affineChainMap p n (formalBoundary (n + 1) (formalSimplex v))
    rw [formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, affineChainMap_simplex, affineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

/-- The induced chain of an affine chain map. -/
theorem SingularMayerVietoris.inducedChain_affineChainMap {m n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p)
    (c : FormalChains (SingularChains.Simplex n) (m + 1)) :
    SingularChains.inducedChain (affineSimplex v) m (affineChainMap n m c) =
      affineChainMap p m (formalMap (affineSimplex v) (m + 1) c) := by
  have h :
    (SingularChains.inducedChain (affineSimplex v) m).comp (affineChainMap n m) =
      (affineChainMap p m).comp (formalMap (affineSimplex v) (m + 1)) := by
    apply formalChains_ext
    intro w
    simp only [LinearMap.comp_apply, affineChainMap_simplex, SingularChains.inducedChain_simplex,
      formalMap_simplex, affineSimplex_comp]
    rfl
  exact LinearMap.congr_fun h c

/-- The affine chain of the standard simplex is the identity simplex. -/
@[simp]
theorem SingularMayerVietoris.affineChainMap_stdVertices (n : ℕ) :
    affineChainMap n n (formalSimplex (stdVertices n)) =
      SingularChains.simplexChain (SingularChains.Simplex n) n
        (ContinuousMap.id (SingularChains.Simplex n)) := by
  rw [affineChainMap_simplex, affineSimplex_stdVertices]

/-- The affine map preserves the barycenter. -/
theorem SingularMayerVietoris.affineSimplex_preserves_center {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (m : ℕ)
    (w : Fin (m + 1) → SingularChains.Simplex n) :
    affineSimplex v (simplexCenter n m w) = simplexCenter p m (affineSimplex v ∘ w) :=
  affineSimplex_simplexBarycenter v w

/-! ### Subdivision of singular chains -/

/-- Barycentric subdivision as an iterated chain map: the `k`-fold subdivision of an `n`-chain (Hatcher, Algebraic Topology, barycentric subdivision operator `Sd_k`). -/
def SingularMayerVietoris.subdivision (X : Type) [TopologicalSpace X] (k n : ℕ) :
    SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X n :=
  SingularChains.chainLift X n fun σ =>
    SingularChains.inducedChain σ n
      (affineChainMap n n
        ((formalSubdivision (simplexCenter n) (n + 1))^[k] (formalSimplex (stdVertices n))))

/-- The singular subdivision of a simplex. -/
@[simp]
theorem SingularMayerVietoris.subdivision_simplex (X : Type) [TopologicalSpace X] (k n : ℕ)
    (σ : SingularChains.SingularSimplex X n) :
    subdivision X k n (SingularChains.simplexChain X n σ) =
      SingularChains.inducedChain σ n
        (affineChainMap n n
          ((formalSubdivision (simplexCenter n) (n + 1))^[k] (formalSimplex (stdVertices n)))) :=
  SingularChains.chainLift_simplex X n _ σ

/-- The induced chain of a subdivision. -/
theorem SingularMayerVietoris.inducedChain_subdivision {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (k n : ℕ) (c : SingularChains.Chains X n) :
    SingularChains.inducedChain f n (subdivision X k n c) =
      subdivision Y k n (SingularChains.inducedChain f n c) := by
  have h :
    (SingularChains.inducedChain f n).comp (subdivision X k n) =
      (subdivision Y k n).comp (SingularChains.inducedChain f n) := by
    apply SingularChains.chainMap_ext X n
    intro σ
    simp only [LinearMap.comp_apply, subdivision_simplex, SingularChains.inducedChain_simplex]
    rw [SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun h c

/-- An affine simplex is the affine map of the standard vertices. -/
theorem SingularMayerVietoris.affineSimplex_comp_stdVertices {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) : affineSimplex v ∘ stdVertices n = v := by
  funext i
  exact affineSimplex_vertex v i

/-- Subdivision commutes with the affine chain map. -/
theorem SingularMayerVietoris.subdivision_affineChainMap (p k n : ℕ)
    (c : FormalChains (SingularChains.Simplex p) (n + 1)) :
    subdivision (SingularChains.Simplex p) k n (affineChainMap p n c) =
      affineChainMap p n ((formalSubdivision (simplexCenter p) (n + 1))^[k] c) := by
  have h :
    (subdivision (SingularChains.Simplex p) k n).comp (affineChainMap p n) =
      (affineChainMap p n).comp ((formalSubdivision (simplexCenter p) (n + 1)) ^ k) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, affineChainMap_simplex, subdivision_simplex,
      Module.End.pow_apply]
    rw [inducedChain_affineChainMap,
      formalMap_subdivision_iterate (simplexCenter n) (simplexCenter p) (affineSimplex v)
        (affineSimplex_preserves_center v),
      formalMap_simplex, affineSimplex_comp_stdVertices]
  simpa only [LinearMap.comp_apply, Module.End.pow_apply] using LinearMap.congr_fun h c

/-- Subdivision commutes with the boundary operator: `bd (Sd_k c) = Sd_k (bd c)` (Hatcher, Algebraic Topology, the chain-map property of subdivision). -/
theorem SingularMayerVietoris.subdivision_boundary {X : Type} [TopologicalSpace X] (k n : ℕ)
    (c : SingularChains.Chains X (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (subdivision X k (n + 1) c) =
      subdivision X k n (((SingularChains.singularComplex X).d (n + 1) n).hom c) := by
  have h :
    (((SingularChains.singularComplex X).d (n + 1) n).hom).comp (subdivision X k (n + 1)) =
      (subdivision X k n).comp ((SingularChains.singularComplex X).d (n + 1) n).hom := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro σ
    change
      ((SingularChains.singularComplex X).d (n + 1) n).hom
          (subdivision X k (n + 1) (SingularChains.simplexChain X (n + 1) σ)) =
        _
    rw [subdivision_simplex, ← SingularChains.inducedChain_boundary, affineChainMap_boundary,
      formalBoundary_subdivision_iterate, ← subdivision_affineChainMap, inducedChain_subdivision,
      ← affineChainMap_boundary, SingularChains.inducedChain_boundary, affineChainMap_stdVertices,
      SingularChains.inducedChain_simplex, ContinuousMap.comp_id]
    rfl
  exact LinearMap.congr_fun h c

/-- The chain homotopy between a chain and its subdivision: `Sd_k` is chain homotopic to the identity, the key to smallness after subdivision (Hatcher, Algebraic Topology, proof of Theorem 2.20). -/
def SingularMayerVietoris.subdivisionHomotopy (X : Type) [TopologicalSpace X] (k n : ℕ) :
    SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X (n + 1) :=
  SingularChains.chainLift X n fun σ =>
    SingularChains.inducedChain σ (n + 1)
      (affineChainMap n (n + 1)
        (formalSubdivisionIteratedHomotopy (simplexCenter n) k (n + 1)
          (formalSimplex (stdVertices n))))

/-- The singular subdivision homotopy on a simplex. -/
@[simp]
theorem SingularMayerVietoris.subdivisionHomotopy_simplex (X : Type) [TopologicalSpace X]
    (k n : ℕ) (σ : SingularChains.SingularSimplex X n) :
    subdivisionHomotopy X k n (SingularChains.simplexChain X n σ) =
      SingularChains.inducedChain σ (n + 1)
        (affineChainMap n (n + 1)
          (formalSubdivisionIteratedHomotopy (simplexCenter n) k (n + 1)
            (formalSimplex (stdVertices n)))) :=
  SingularChains.chainLift_simplex X n _ σ

/-- The induced chain of the subdivision homotopy. -/
theorem SingularMayerVietoris.inducedChain_subdivisionHomotopy {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (k n : ℕ) (c : SingularChains.Chains X n) :
    SingularChains.inducedChain f (n + 1) (subdivisionHomotopy X k n c) =
      subdivisionHomotopy Y k n (SingularChains.inducedChain f n c) := by
  have h :
    (SingularChains.inducedChain f (n + 1)).comp (subdivisionHomotopy X k n) =
      (subdivisionHomotopy Y k n).comp (SingularChains.inducedChain f n) := by
    apply SingularChains.chainMap_ext X n
    intro σ
    simp only [LinearMap.comp_apply, subdivisionHomotopy_simplex,
      SingularChains.inducedChain_simplex]
    rw [SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun h c

/-- The subdivision homotopy commutes with the affine chain map. -/
theorem SingularMayerVietoris.subdivisionHomotopy_affineChainMap (p k n : ℕ)
    (c : FormalChains (SingularChains.Simplex p) (n + 1)) :
    subdivisionHomotopy (SingularChains.Simplex p) k n (affineChainMap p n c) =
      affineChainMap p (n + 1)
        (formalSubdivisionIteratedHomotopy (simplexCenter p) k (n + 1) c) := by
  have h :
    (subdivisionHomotopy (SingularChains.Simplex p) k n).comp (affineChainMap p n) =
      (affineChainMap p (n + 1)).comp
        (formalSubdivisionIteratedHomotopy (simplexCenter p) k (n + 1)) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, affineChainMap_simplex, subdivisionHomotopy_simplex]
    rw [inducedChain_affineChainMap,
      formalMap_subdivisionIteratedHomotopy (simplexCenter n) (simplexCenter p) (affineSimplex v)
        (affineSimplex_preserves_center v),
      formalMap_simplex, affineSimplex_comp_stdVertices]
  exact LinearMap.congr_fun h c

/-- The degree-zero boundary of the conjugated homotopy. -/
theorem SingularMayerVietoris.subdivisionHomotopy_boundary_zero_affineChainMap (p k : ℕ)
    (c : FormalChains (SingularChains.Simplex p) 1) :
    ((SingularChains.singularComplex (SingularChains.Simplex p)).d 1 0).hom
        (subdivisionHomotopy (SingularChains.Simplex p) k 0 (affineChainMap p 0 c)) =
      affineChainMap p 0 c - subdivision (SingularChains.Simplex p) k 0 (affineChainMap p 0 c) := by
  rw [subdivisionHomotopy_affineChainMap, affineChainMap_boundary, subdivision_affineChainMap, ←
    map_sub]
  apply congrArg (affineChainMap p 0)
  simpa only [formalSubdivisionIteratedHomotopy_degree_zero, add_zero] using
    formalSubdivisionIteratedHomotopy_boundary (simplexCenter p) k 0 c

/-- The boundary of the conjugated subdivision homotopy. -/
theorem SingularMayerVietoris.subdivisionHomotopy_boundary_affineChainMap (p k n : ℕ)
    (c : FormalChains (SingularChains.Simplex p) (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p)).d (n + 2) (n + 1)).hom
          (subdivisionHomotopy (SingularChains.Simplex p) k (n + 1) (affineChainMap p (n + 1) c)) +
        subdivisionHomotopy (SingularChains.Simplex p) k n
          (((SingularChains.singularComplex (SingularChains.Simplex p)).d (n + 1) n).hom
            (affineChainMap p (n + 1) c)) =
      affineChainMap p (n + 1) c -
        subdivision (SingularChains.Simplex p) k (n + 1) (affineChainMap p (n + 1) c) := by
  rw [subdivisionHomotopy_affineChainMap, affineChainMap_boundary, affineChainMap_boundary,
    subdivisionHomotopy_affineChainMap, subdivision_affineChainMap, ← map_add, ← map_sub]
  exact
    congrArg (affineChainMap p (n + 1))
      (formalSubdivisionIteratedHomotopy_boundary (simplexCenter p) k (n + 1) c)

/-- The subdivision homotopy boundary in degree zero. -/
theorem SingularMayerVietoris.subdivisionHomotopy_boundary_zero {X : Type} [TopologicalSpace X]
    (k : ℕ) (c : SingularChains.Chains X 0) :
    ((SingularChains.singularComplex X).d 1 0).hom (subdivisionHomotopy X k 0 c) =
      c - subdivision X k 0 c := by
  have h :
    (((SingularChains.singularComplex X).d 1 0).hom).comp (subdivisionHomotopy X k 0) =
      LinearMap.id - subdivision X k 0 := by
    apply SingularChains.chainMap_ext X 0
    intro σ
    have hstd :=
      subdivisionHomotopy_boundary_zero_affineChainMap 0 k (formalSimplex (stdVertices 0))
    have hσ := congrArg (SingularChains.inducedChain σ 0) hstd
    simpa only [map_sub, SingularChains.inducedChain_boundary, inducedChain_subdivisionHomotopy,
      inducedChain_subdivision, affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using
      hσ
  exact LinearMap.congr_fun h c

/-- The subdivision homotopy satisfies `∂h + h∂ = sd − id`. -/
theorem SingularMayerVietoris.subdivisionHomotopy_boundary {X : Type} [TopologicalSpace X]
    (k n : ℕ) (c : SingularChains.Chains X (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom
          (subdivisionHomotopy X k (n + 1) c) +
        subdivisionHomotopy X k n (((SingularChains.singularComplex X).d (n + 1) n).hom c) =
      c - subdivision X k (n + 1) c := by
  have h :
    (((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom).comp
          (subdivisionHomotopy X k (n + 1)) +
        (subdivisionHomotopy X k n).comp (((SingularChains.singularComplex X).d (n + 1) n).hom) =
      LinearMap.id - subdivision X k (n + 1) := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro σ
    have hstd :=
      subdivisionHomotopy_boundary_affineChainMap (n + 1) k n
        (formalSimplex (stdVertices (n + 1)))
    have hσ := congrArg (SingularChains.inducedChain σ (n + 1)) hstd
    simpa only [map_add, map_sub, SingularChains.inducedChain_boundary,
      inducedChain_subdivisionHomotopy, inducedChain_subdivision, affineChainMap_stdVertices,
      SingularChains.inducedChain_simplex, ContinuousMap.comp_id, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply] using hσ
  exact LinearMap.congr_fun h c

/-- On a cycle the homotopy boundary is `sd − id`. -/
theorem SingularMayerVietoris.subdivisionHomotopy_boundary_of_cycle {X : Type}
    [TopologicalSpace X] (k n : ℕ) (c : SingularChains.Chains X n)
    (hc : ((SingularChains.singularComplex X).d n (n - 1)).hom c = 0) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (subdivisionHomotopy X k n c) =
      c - subdivision X k n c := by
  cases n with
  | zero => exact subdivisionHomotopy_boundary_zero k c
  | succ
    n =>
    have hc' : ((SingularChains.singularComplex X).d (n + 1) n).hom c = 0 := by
      simpa only [Nat.succ_sub_one] using hc
    simpa only [hc', map_zero, add_zero] using subdivisionHomotopy_boundary k n c
