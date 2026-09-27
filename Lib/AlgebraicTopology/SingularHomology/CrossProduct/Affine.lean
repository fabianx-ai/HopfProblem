/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
public import Lib.AlgebraicTopology.SingularHomology.CrossInsert
public import Lib.AlgebraicTopology.SingularHomology.CircleProduct
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Multilinear

open Set Function Filter Manifold Topology

open scoped BigOperators TensorProduct

/-!
# Affine simplices in products of standard simplices

The bridge from formal chains to singular chains of a product of standard simplices.  For vertex
pairs `v : Fin (n+1) → Δᵖ × Δ^q`, `SingularHomology.productAffineSimplex v` is the affine
`n`-simplex in `Δᵖ × Δ^q` formed componentwise; `SingularHomology.productAffineChainMap p q n`
sends a formal `(n+1)`-chain on `Δᵖ × Δ^q` to the corresponding singular chain.  The file proves
the vertex and face formulas (`SingularHomology.productAffineSimplex_vertex`, `_face`), that the
chain map commutes with the boundary (`SingularHomology.productAffineChainMap_boundary`), and how
it transforms under products of affine maps (`SingularHomology.prodMap_productAffineSimplex`,
`.inducedChain_productAffineChainMap`) and under the factor swap
(`PeriodTorusHigherHomology.prodSwap_productAffineSimplex`,
`.inducedChain_swap_productAffineChainMap`).

The same for triple products `Δᵖ × (Δ^q × Δʳ)`: `PeriodTorusHigherHomology.tripleAffineSimplex`,
`.tripleAffineChainMap` (with `_face`, `_simplex`, `_boundary`), the affine maps of pairs
`PeriodTorusHigherHomology.affineProductLeft`, `.affineProductRight` from `Δᵃ × Δᵇ` into a triple
product, and their compatibility with the affine chain maps
(`PeriodTorusHigherHomology.inducedChain_affineProductLeft`, `.inducedChain_affineProductRight`,
`.inducedChain_tripleAffineChainMap`).

These are the affine (linear) singular simplices of Hatcher, *Algebraic Topology*, §2.1 and §3.B,
in a product of simplices.
-/


@[expose] public noncomputable section


/-! ### Affine simplices in a product -/

/-- The affine simplex on a constant vertex list is the constant map. -/
@[simp]
theorem SingularHomology.affineSimplex_constant {n p : ℕ} (a : SingularChains.Simplex p) :
    SingularMayerVietoris.affineSimplex (fun _ : Fin (n + 1) => a) =
      ContinuousMap.const (SingularChains.Simplex n) a := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (∑ i, t i • (a : Fin (p + 1) → ℝ)) = (a : Fin (p + 1) → ℝ)
  rw [← Finset.sum_smul, stdSimplex.sum_eq_one t, one_smul]

/-- The affine simplex in `Simplex p × Simplex q` with vertex pairs `v`, formed
componentwise. -/
def SingularHomology.productAffineSimplex {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    C(SingularChains.Simplex n, SingularChains.Simplex p × SingularChains.Simplex q) :=
  (SingularMayerVietoris.affineSimplex (fun i => (v i).1)).prodMk
    (SingularMayerVietoris.affineSimplex (fun i => (v i).2))

/-- The `j`-th vertex of `productAffineSimplex v` is the pair `v j`. -/
@[simp]
theorem SingularHomology.productAffineSimplex_vertex {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) (i : Fin (n + 1)) :
    SingularHomology.productAffineSimplex v (SingularMayerVietoris.stdVertices n i) = v i := by
  apply Prod.ext <;> simp [SingularHomology.productAffineSimplex, SingularMayerVietoris.stdVertices]

/-- The `i`-th face of `productAffineSimplex v` is the product affine simplex of the
vertex pairs with `v i` dropped. -/
theorem SingularHomology.productAffineSimplex_face {n p q : ℕ}
    (v : Fin (n + 2) → SingularChains.Simplex p × SingularChains.Simplex q) (i : Fin (n + 2)) :
    (SingularHomology.productAffineSimplex v).comp (SingularChains.simplexFace n i) =
      SingularHomology.productAffineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex n, SingularChains.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_face (fun j => (v j).1) i)
  · exact
      congrArg (fun f : C(SingularChains.Simplex n, SingularChains.Simplex q) => f t)
        (SingularMayerVietoris.affineSimplex_face (fun j => (v j).2) i)

/-- Postcomposing `productAffineSimplex v` with a product map gives the product affine
simplex of the mapped vertex pairs. -/
theorem SingularHomology.prodMap_productAffineSimplex {m p q r s : ℕ}
    (v : Fin (p + 1) → SingularChains.Simplex r) (w : Fin (q + 1) → SingularChains.Simplex s)
    (z : Fin (m + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    ((SingularMayerVietoris.affineSimplex v).prodMap (SingularMayerVietoris.affineSimplex w)).comp
        (SingularHomology.productAffineSimplex z) =
      SingularHomology.productAffineSimplex
        (fun j =>
          (SingularMayerVietoris.affineSimplex v (z j).1,
            SingularMayerVietoris.affineSimplex w (z j).2)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex r) => f t)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (z j).1))
  · exact
      congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex s) => f t)
        (SingularMayerVietoris.affineSimplex_comp w (fun j => (z j).2))

/-- The formal-chain map sending a vertex-pair list to the chain of its product affine
simplex. -/
def SingularHomology.productAffineChainMap (p q n : ℕ) :
    SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q)
        (n + 1) →ₗ[ℤ]
      SingularChains.Chains (SingularChains.Simplex p × SingularChains.Simplex q) n :=
  SingularMayerVietoris.formalLift fun v =>
    SingularChains.simplexChain (SingularChains.Simplex p × SingularChains.Simplex q) n
      (SingularHomology.productAffineSimplex v)

/-- `productAffineChainMap` on a generator `v` is the chain of `productAffineSimplex v`. -/
@[simp]
theorem SingularHomology.productAffineChainMap_simplex (p q n : ℕ)
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    SingularHomology.productAffineChainMap p q n (SingularMayerVietoris.formalSimplex v) =
      SingularChains.simplexChain (SingularChains.Simplex p × SingularChains.Simplex q) n
        (SingularHomology.productAffineSimplex v) :=
  SingularMayerVietoris.formalLift_simplex _ _

/-- The product affine chain map commutes with the formal boundary: `∂` of the affine
chain is the alternating sum of the face affine simplices. -/
theorem SingularHomology.productAffineChainMap_boundary (p q n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q)
        (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d (n + 1)
            n).hom
        (SingularHomology.productAffineChainMap p q (n + 1) c) =
      SingularHomology.productAffineChainMap p q n (SingularMayerVietoris.formalBoundary (n + 1) c) := by
  have h :
    (((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d
              (n + 1) n).hom).comp
        (SingularHomology.productAffineChainMap p q (n + 1)) =
      (SingularHomology.productAffineChainMap p q n).comp (SingularMayerVietoris.formalBoundary (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    change
      ((SingularChains.singularComplex (SingularChains.Simplex p × SingularChains.Simplex q)).d
              (n + 1) n).hom
          (SingularHomology.productAffineChainMap p q (n + 1) (SingularMayerVietoris.formalSimplex v)) =
        _
    rw [SingularHomology.productAffineChainMap_simplex, SingularChains.boundary_simplex]
    change
      _ =
        SingularHomology.productAffineChainMap p q n
          (SingularMayerVietoris.formalBoundary (n + 1) (SingularMayerVietoris.formalSimplex v))
    rw [SingularMayerVietoris.formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, SingularHomology.productAffineChainMap_simplex, SingularHomology.productAffineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

/-- Postcomposing the product affine chain map with the map induced by a product of
continuous maps gives the product affine chain map of the mapped vertices. -/
theorem SingularHomology.inducedChain_productAffineChainMap {m p q r s : ℕ}
    (v : Fin (p + 1) → SingularChains.Simplex r) (w : Fin (q + 1) → SingularChains.Simplex s)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q)
        (m + 1)) :
    SingularChains.inducedChain
        ((SingularMayerVietoris.affineSimplex v).prodMap (SingularMayerVietoris.affineSimplex w))
        m (SingularHomology.productAffineChainMap p q m c) =
      SingularHomology.productAffineChainMap r s m
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            (SingularMayerVietoris.affineSimplex w))
          (m + 1) c) := by
  have h :
    (SingularChains.inducedChain
            ((SingularMayerVietoris.affineSimplex v).prodMap
              (SingularMayerVietoris.affineSimplex w))
            m).comp
        (SingularHomology.productAffineChainMap p q m) =
      (SingularHomology.productAffineChainMap r s m).comp
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            (SingularMayerVietoris.affineSimplex w))
          (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, SingularHomology.productAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      SingularHomology.prodMap_productAffineSimplex]
    rfl
  exact LinearMap.congr_fun h c


/-! ### The factor swap -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Composing the factor swap with a product affine simplex is the product affine simplex of the swapped vertices. -/
theorem PeriodTorusHigherHomology.prodSwap_productAffineSimplex {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    (ContinuousMap.prodSwap :
            C(SingularChains.Simplex p × SingularChains.Simplex q,
              SingularChains.Simplex q × SingularChains.Simplex p)).comp
        (SingularHomology.productAffineSimplex v) =
      SingularHomology.productAffineSimplex (Prod.swap ∘ v) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Chains induced along the factor swap transfer through the product affine chain map. -/
theorem PeriodTorusHigherHomology.inducedChain_swap_productAffineChainMap (p q n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q)
        (n + 1)) :
    SingularChains.inducedChain
        (ContinuousMap.prodSwap :
          C(SingularChains.Simplex p × SingularChains.Simplex q,
            SingularChains.Simplex q × SingularChains.Simplex p))
        n (SingularHomology.productAffineChainMap p q n c) =
      SingularHomology.productAffineChainMap q p n (SingularMayerVietoris.formalMap Prod.swap (n + 1) c) := by
  have h :
    (SingularChains.inducedChain
            (ContinuousMap.prodSwap :
              C(SingularChains.Simplex p × SingularChains.Simplex q,
                SingularChains.Simplex q × SingularChains.Simplex p))
            n).comp
        (SingularHomology.productAffineChainMap p q n) =
      (SingularHomology.productAffineChainMap q p n).comp (SingularMayerVietoris.formalMap Prod.swap (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularHomology.productAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      PeriodTorusHigherHomology.prodSwap_productAffineSimplex]
  exact LinearMap.congr_fun h c


/-! ### Affine simplices in a triple product -/

/-- The triple product affine simplex: the affine `n`-simplex in `Simplex p × (Simplex q × Simplex r)` with the given paired vertices. -/
def PeriodTorusHigherHomology.tripleAffineSimplex {n p q r : ℕ}
    (v :
      Fin (n + 1) →
        SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) :
    C(SingularChains.Simplex n,
      SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) :=
  (SingularMayerVietoris.affineSimplex (fun i => (v i).1)).prodMk
    (SingularHomology.productAffineSimplex (fun i => (v i).2))
/-- Faces of the triple product affine simplex are computed vertexwise. -/
theorem PeriodTorusHigherHomology.tripleAffineSimplex_face {n p q r : ℕ}
    (v :
      Fin (n + 2) → SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r))
    (i : Fin (n + 2)) :
    (PeriodTorusHigherHomology.tripleAffineSimplex v).comp (SingularChains.simplexFace n i) =
      PeriodTorusHigherHomology.tripleAffineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex n, SingularChains.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_face (fun j => (v j).1) i)
  · exact
      congrArg
        (fun f : C(SingularChains.Simplex n, SingularChains.Simplex q × SingularChains.Simplex r) =>
          f t)
        (SingularHomology.productAffineSimplex_face (fun j => (v j).2) i)
/-- The affine chain map on the triple product of standard simplices. -/
def PeriodTorusHigherHomology.tripleAffineChainMap (p q r n : ℕ) :
    SingularMayerVietoris.FormalChains
        (SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r))
        (n + 1) →ₗ[ℤ]
      SingularChains.Chains
        (SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) n :=
  SingularMayerVietoris.formalLift fun v => SingularChains.simplexChain _ n (PeriodTorusHigherHomology.tripleAffineSimplex v)
/-- The triple affine chain map evaluates formal simplices to the chain of the triple affine simplex. -/
@[simp]
theorem PeriodTorusHigherHomology.tripleAffineChainMap_simplex (p q r n : ℕ)
    (v :
      Fin (n + 1) →
        SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) :
    PeriodTorusHigherHomology.tripleAffineChainMap p q r n (SingularMayerVietoris.formalSimplex v) =
      SingularChains.simplexChain _ n (PeriodTorusHigherHomology.tripleAffineSimplex v) :=
  SingularMayerVietoris.formalLift_simplex _ _
/-- The triple affine chain map commutes with the boundary. -/
theorem PeriodTorusHigherHomology.tripleAffineChainMap_boundary (p q r n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains
        (SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) (n + 2)) :
    ((SingularChains.singularComplex
                (SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r))).d
            (n + 1) n).hom
        (PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 1) c) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r n (SingularMayerVietoris.formalBoundary (n + 1) c) := by
  have h :
    (((SingularChains.singularComplex
                  (SingularChains.Simplex p ×
                    (SingularChains.Simplex q × SingularChains.Simplex r))).d
              (n + 1) n).hom).comp
        (PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 1)) =
      (PeriodTorusHigherHomology.tripleAffineChainMap p q r n).comp (SingularMayerVietoris.formalBoundary (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    change
      ((SingularChains.singularComplex
                  (SingularChains.Simplex p ×
                    (SingularChains.Simplex q × SingularChains.Simplex r))).d
              (n + 1) n).hom
          (PeriodTorusHigherHomology.tripleAffineChainMap p q r (n + 1) (SingularMayerVietoris.formalSimplex v)) =
        _
    rw [PeriodTorusHigherHomology.tripleAffineChainMap_simplex, SingularChains.boundary_simplex]
    change
      _ =
        PeriodTorusHigherHomology.tripleAffineChainMap p q r n
          (SingularMayerVietoris.formalBoundary (n + 1) (SingularMayerVietoris.formalSimplex v))
    rw [SingularMayerVietoris.formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, PeriodTorusHigherHomology.tripleAffineChainMap_simplex, PeriodTorusHigherHomology.tripleAffineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c
/-- The affine map of pairs associated to vertex lists on the left-associated product: the map `(x, y) ↦ (affine v x, affine w y)` re-associated to the right. -/
def PeriodTorusHigherHomology.affineProductLeft {a b p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p × SingularChains.Simplex q)
    (w : Fin (b + 1) → SingularChains.Simplex r) :
    C(SingularChains.Simplex a × SingularChains.Simplex b,
      SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) :=
  (Homeomorph.prodAssoc (SingularChains.Simplex p) (SingularChains.Simplex q)
          (SingularChains.Simplex r) :
        C(_, _)).comp
    ((SingularHomology.productAffineSimplex v).prodMap (SingularMayerVietoris.affineSimplex w))
/-- The right-associated analogue: the map of pairs built from a simplex vertex list and a paired vertex list. -/
def PeriodTorusHigherHomology.affineProductRight {a b p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p)
    (w : Fin (b + 1) → SingularChains.Simplex q × SingularChains.Simplex r) :
    C(SingularChains.Simplex a × SingularChains.Simplex b,
      SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r)) :=
  (SingularMayerVietoris.affineSimplex v).prodMap (SingularHomology.productAffineSimplex w)
/-- The left-associated product affine map composed with a product affine simplex is the triple product affine simplex of the combined vertices. -/
theorem PeriodTorusHigherHomology.affineProductLeft_comp {a b m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p × SingularChains.Simplex q)
    (w : Fin (b + 1) → SingularChains.Simplex r)
    (z : Fin (m + 1) → SingularChains.Simplex a × SingularChains.Simplex b) :
    (PeriodTorusHigherHomology.affineProductLeft v w).comp (SingularHomology.productAffineSimplex z) =
      PeriodTorusHigherHomology.tripleAffineSimplex (fun j => PeriodTorusHigherHomology.affineProductLeft v w (z j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_comp (fun j => (v j).1) (fun j => (z j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex q) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (v j).2) (fun j => (z j).1))
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex r) => f t)
          (SingularMayerVietoris.affineSimplex_comp w (fun j => (z j).2))
/-- The right-associated analogue of the composition identity. -/
theorem PeriodTorusHigherHomology.affineProductRight_comp {a b m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p)
    (w : Fin (b + 1) → SingularChains.Simplex q × SingularChains.Simplex r)
    (z : Fin (m + 1) → SingularChains.Simplex a × SingularChains.Simplex b) :
    (PeriodTorusHigherHomology.affineProductRight v w).comp (SingularHomology.productAffineSimplex z) =
      PeriodTorusHigherHomology.tripleAffineSimplex (fun j => PeriodTorusHigherHomology.affineProductRight v w (z j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (z j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex q) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (w j).1) (fun j => (z j).2))
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex r) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (w j).2) (fun j => (z j).2))
/-- Chains induced by the left-associated product affine map transfer through the affine chain structures. -/
theorem PeriodTorusHigherHomology.inducedChain_affineProductLeft {a b m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p × SingularChains.Simplex q)
    (w : Fin (b + 1) → SingularChains.Simplex r)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex a × SingularChains.Simplex b)
        (m + 1)) :
    SingularChains.inducedChain (PeriodTorusHigherHomology.affineProductLeft v w) m (SingularHomology.productAffineChainMap a b m c) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap (PeriodTorusHigherHomology.affineProductLeft v w) (m + 1) c) := by
  have h :
    (SingularChains.inducedChain (PeriodTorusHigherHomology.affineProductLeft v w) m).comp (SingularHomology.productAffineChainMap a b m) =
      (PeriodTorusHigherHomology.tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap (PeriodTorusHigherHomology.affineProductLeft v w) (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, SingularHomology.productAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      PeriodTorusHigherHomology.tripleAffineChainMap_simplex, PeriodTorusHigherHomology.affineProductLeft_comp]
    rfl
  exact LinearMap.congr_fun h c
/-- Chains induced by the right-associated product affine map transfer through the affine chain structures. -/
theorem PeriodTorusHigherHomology.inducedChain_affineProductRight {a b m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p)
    (w : Fin (b + 1) → SingularChains.Simplex q × SingularChains.Simplex r)
    (c :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex a × SingularChains.Simplex b)
        (m + 1)) :
    SingularChains.inducedChain (PeriodTorusHigherHomology.affineProductRight v w) m (SingularHomology.productAffineChainMap a b m c) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap (PeriodTorusHigherHomology.affineProductRight v w) (m + 1) c) := by
  have h :
    (SingularChains.inducedChain (PeriodTorusHigherHomology.affineProductRight v w) m).comp (SingularHomology.productAffineChainMap a b m) =
      (PeriodTorusHigherHomology.tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap (PeriodTorusHigherHomology.affineProductRight v w) (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, SingularHomology.productAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      PeriodTorusHigherHomology.tripleAffineChainMap_simplex, PeriodTorusHigherHomology.affineProductRight_comp]
    rfl
  exact LinearMap.congr_fun h c


/-! ### Products of affine maps on a triple product -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The product affine simplex extends its vertex data: composition with the standard vertices returns the pairs. -/
theorem PeriodTorusHigherHomology.productAffineSimplex_stdVertices_image {n p q : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p × SingularChains.Simplex q) :
    SingularHomology.productAffineSimplex v ∘ SingularMayerVietoris.stdVertices n = v := by
  funext i
  exact SingularHomology.productAffineSimplex_vertex v i

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triple product of affine maps composed with the triple product affine simplex factors through the vertexwise data. -/
theorem PeriodTorusHigherHomology.prodMap_tripleAffineSimplex {a b c m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p) (w : Fin (b + 1) → SingularChains.Simplex q)
    (z : Fin (c + 1) → SingularChains.Simplex r)
    (t :
      Fin (m + 1) →
        SingularChains.Simplex a × (SingularChains.Simplex b × SingularChains.Simplex c)) :
    ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z))).comp
        (PeriodTorusHigherHomology.tripleAffineSimplex t) =
      PeriodTorusHigherHomology.tripleAffineSimplex
        (fun j =>
          (SingularMayerVietoris.affineSimplex v (t j).1,
            (SingularMayerVietoris.affineSimplex w (t j).2.1,
              SingularMayerVietoris.affineSimplex z (t j).2.2))) := by
  apply ContinuousMap.ext
  intro s
  apply Prod.ext
  · exact
      congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex p) => f s)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (t j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex q) => f s)
          (SingularMayerVietoris.affineSimplex_comp w (fun j => (t j).2.1))
    · exact
        congrArg (fun f : C(SingularChains.Simplex m, SingularChains.Simplex r) => f s)
          (SingularMayerVietoris.affineSimplex_comp z (fun j => (t j).2.2))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Chains induced by triple products of affine maps transfer through the triple affine chain map. -/
theorem PeriodTorusHigherHomology.inducedChain_tripleAffineChainMap {a b c m p q r : ℕ}
    (v : Fin (a + 1) → SingularChains.Simplex p) (w : Fin (b + 1) → SingularChains.Simplex q)
    (z : Fin (c + 1) → SingularChains.Simplex r)
    (t :
      SingularMayerVietoris.FormalChains
        (SingularChains.Simplex a × (SingularChains.Simplex b × SingularChains.Simplex c)) (m + 1)) :
    SingularChains.inducedChain
        ((SingularMayerVietoris.affineSimplex v).prodMap
          ((SingularMayerVietoris.affineSimplex w).prodMap
            (SingularMayerVietoris.affineSimplex z)))
        m (PeriodTorusHigherHomology.tripleAffineChainMap a b c m t) =
      PeriodTorusHigherHomology.tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z)))
          (m + 1) t) := by
  have h :
    (SingularChains.inducedChain
            ((SingularMayerVietoris.affineSimplex v).prodMap
              ((SingularMayerVietoris.affineSimplex w).prodMap
                (SingularMayerVietoris.affineSimplex z)))
            m).comp
        (PeriodTorusHigherHomology.tripleAffineChainMap a b c m) =
      (PeriodTorusHigherHomology.tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z)))
          (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro s
    simp only [LinearMap.comp_apply, PeriodTorusHigherHomology.tripleAffineChainMap_simplex,
      SingularChains.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      PeriodTorusHigherHomology.prodMap_tripleAffineSimplex]
    rfl
  exact LinearMap.congr_fun h t
